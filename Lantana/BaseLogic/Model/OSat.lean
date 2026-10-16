/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.Algebra.Agree
public import Iris.Instances.Lib.GhostMap
public import Lantana.Algebra.Bank
public import Lantana.BaseLogic.LaterCredits
public import Lantana.BaseLogic.Obligation

/-! # Ghost state of obligations

The ghost state of the obligations of the model and the invariant `osat Ω` that ties the pure
obligation map `Ω : Obls` to it (Rocq `lantana/base_logic/osat.v`). Each obligation `k` has a
persistent fuel bound `OSat.bound k β`, a state (assigned, fractional `OSat.assigned k q`, or
discharged, persistent `OSat.discharged k`) and a bank of fuel: the invariant holds the debt
`OSat.supply k α 1`, and the cash `OSat.fuel k a` in circulation is at most `α`, itself at most
the bound and the model fuel of the obligation. Spending positive cash makes the obligation
progress (`osat_progress_one`, `osat_progress`).

Design (plan M4 §1, differences with Rocq):
* No owner ghost state: the owner of an obligation is read from `Ω`, so an owner change is a
  change of `Ω` (`osat_progress_one_owner`). No boolean flag on the state.
* The state is one ghost map `Oid → Bool` (`false` = assigned, `true` = discharged), whose
  authoritative part is in `osat`; `osat` holds no fraction of the elements.
* `Fuel`-valued cells (the bound, `Agree (DiscreteO Fuel)`, and the bank, `Bank Fuel`) are in
  `Type 2`, which Iris-Lean's ghost maps cannot store. Each obligation gets its own ghost names
  for them (`OblNames`, allocated with the obligation) and a persistent ghost map
  `Oid → OblNames` records them (`OSat.names`). The cameras are included through the
  universe-polymorphic constant functor `constOFP`. This replaces Rocq's reservation maps.
* Maps are `OidMap`; the authoritative maps of `osat` are existentially quantified and related
  to `Ω` pointwise (`OSatWf`).
-/

@[expose] public noncomputable section

namespace Lantana.Model

open Iris Iris.BI Iris.ProofMode Iris.Std LawfulPartialMap
open Ordinals Ordinal

namespace Obl

/-- Whether an obligation is discharged: the status kept by the state ghost map. -/
def isDischarged : Obl → Bool
  | assigned _ _ => false
  | discharged => true

@[simp] theorem isDischarged_assigned {a : Fuel} {t : ThreadId} :
    (assigned a t).isDischarged = false := rfl

@[simp] theorem isDischarged_discharged : discharged.isDischarged = true := rfl

end Obl

/-! ## Ghost state -/

/-- The ghost names of the per-obligation cameras: the bound and the bank. -/
structure OblNames where
  /-- The ghost name of the bound (`Agree (DiscreteO Fuel)`). -/
  bound : GName
  /-- The ghost name of the bank of fuel (`Bank Fuel`). -/
  bank : GName
  deriving DecidableEq

/-- The ghost state of obligations that a world provides: the state map, the name map, and the
per-obligation cameras of the bound and of the bank (in `Type 2`, through `constOFP`). -/
@[lantana_alias osatGpreS] -- Rocq `osatGS.osatGpreS`
class OSatGpreS (GF : BundledGFunctors) where
  [stateG : GhostMapG GF Oid Bool OidMap]
  [namesG : GhostMapG GF Oid OblNames OidMap]
  boundG : ElemG GF (constOFP (Agree (DiscreteO Fuel)))
  bankG : ElemG GF (constOFP (Bank Fuel))

attribute [reducible, instance] OSatGpreS.stateG OSatGpreS.namesG OSatGpreS.boundG
  OSatGpreS.bankG

attribute [lantana_alias osatGpreS_state] OSatGpreS.stateG
attribute [lantana_alias osatGpreS_bound] OSatGpreS.boundG
attribute [lantana_alias osatGpreS_fuel] OSatGpreS.bankG

/-- The ghost state of obligations: the names of the state map and of the name map. -/
@[lantana_alias osatGS] -- Rocq `osatGS.osatGS`; the module prefix would duplicate the namespace
class OSatGS (GF : BundledGFunctors) extends OSatGpreS GF where
  /-- The ghost name of the state map. -/
  stateName : GName
  /-- The ghost name of the map of per-obligation names. -/
  namesName : GName

attribute [lantana_alias osat_inG] OSatGS.toOSatGpreS
attribute [lantana_alias state_name] OSatGS.stateName

#lantana_ignore osatGpreS_owner "no owner ghost state: the owner is read from `Ω`"
#lantana_ignore bound_name "per-obligation names: `OblNames.bound`"
#lantana_ignore fuel_name "per-obligation names: `OblNames.bank`"
#lantana_ignore owner_name "no owner ghost state: the owner is read from `Ω`"
#lantana_ignore «osatΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#lantana_ignore «subG_osatΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#lantana_ignore reservation_map_token_alloc_singleton
  "no reservation maps: per-obligation ghost names (`OSat.names_alloc`)"
#lantana_ignore ord_obl_class "D6/D10: fuel is fixed to `Fuel`"

/-! ## Per-obligation predicates -/

namespace OSat

variable {GF : BundledGFunctors} [OSatGS GF]

/-- The ghost names of the cameras of obligation `k` are `ns` (persistent). -/
def names (k : Oid) (ns : OblNames) : IProp GF :=
  OSatGS.namesName (GF := GF) ↪◯MAP[k]{DFrac.discard} ns

/-- Obligation `k` exists (Rocq `oblG_elem`). -/
@[lantana_alias oblG_elem]
def elem (k : Oid) : IProp GF :=
  iprop(∃ ns, names k ns)

/-- Ownership of the bound camera at the name `γ`. -/
def boundOwn (γ : GName) (β : Fuel) : IProp GF :=
  iOwn (F := constOFP (Agree (DiscreteO Fuel))) γ (toAgree ⟨β⟩)

/-- Ownership of the bank camera at the name `γ`. -/
def bankOwn (γ : GName) (x : Bank Fuel) : IProp GF :=
  iOwn (F := constOFP (Bank Fuel)) γ x

instance boundOwn_persistent (γ : GName) (β : Fuel) : Persistent (boundOwn (GF := GF) γ β) := by
  unfold boundOwn; infer_instance

instance boundOwn_timeless (γ : GName) (β : Fuel) : Timeless (boundOwn (GF := GF) γ β) := by
  unfold boundOwn; infer_instance

instance bankOwn_timeless (γ : GName) (x : Bank Fuel) : Timeless (bankOwn (GF := GF) γ x) := by
  unfold bankOwn; infer_instance

theorem bankOwn_op (γ : GName) (x y : Bank Fuel) :
    bankOwn γ (x • y) ⊣⊢@{IProp GF} bankOwn γ x ∗ bankOwn γ y := by
  unfold bankOwn; exact iOwn_op

theorem bankOwn_valid_2 (γ : GName) (x y : Bank Fuel) :
    bankOwn γ x ∗ bankOwn γ y ⊢@{IProp GF} ⌜✓ (x • y)⌝ := by
  unfold bankOwn
  iintro ⟨H₁, H₂⟩
  icombine H₁ H₂ gives %h
  ipureintro
  exact h

theorem bankOwn_valid (γ : GName) (x : Bank Fuel) :
    bankOwn γ x ⊢@{IProp GF} ⌜✓ x⌝ := by
  unfold bankOwn
  iintro H
  icases iOwn_cmraValid $$ H with %h
  ipureintro
  exact h

theorem bankOwn_update {γ : GName} {x y : Bank Fuel} (h : x ~~> y) :
    bankOwn γ x ⊢@{IProp GF} |==> bankOwn γ y := by
  unfold bankOwn; exact iOwn_update h

theorem bankOwn_updateP {γ : GName} {x : Bank Fuel} {P : Bank Fuel → Prop} (h : x ~~>: P) :
    bankOwn γ x ⊢@{IProp GF} |==> ∃ y, ⌜P y⌝ ∗ bankOwn γ y := by
  unfold bankOwn; exact iOwn_updateP h

theorem boundOwn_agree (γ : GName) (β₁ β₂ : Fuel) :
    boundOwn γ β₁ ∗ boundOwn γ β₂ ⊢@{IProp GF} ⌜β₁ = β₂⌝ := by
  unfold boundOwn
  iintro ⟨H₁, H₂⟩
  icombine H₁ H₂ gives %hv
  ipureintro
  exact DiscreteO.eqv_inj (toAgree_op_valid_iff_eq.mp hv)

/-- The fuel bound of obligation `k` is `β` (persistent; Rocq `oblG_bound`). -/
@[lantana_alias oblG_bound]
def bound (k : Oid) (β : Fuel) : IProp GF :=
  iprop(∃ ns, names k ns ∗ boundOwn ns.bound β)

/-- A fraction `q` of the assigned state of obligation `k` (Rocq `oblG_assigned`, without the
flag). -/
@[lantana_alias oblG_assigned]
def assigned (k : Oid) (q : Qp) : IProp GF :=
  OSatGS.stateName (GF := GF) ↪◯MAP[k]{DFrac.own q} false

/-- Obligation `k` is discharged (persistent; Rocq `oblG_discharged`). -/
@[lantana_alias oblG_discharged]
def discharged (k : Oid) : IProp GF :=
  OSatGS.stateName (GF := GF) ↪◯MAP[k]{DFrac.discard} true

/-- Fuel (cash) `a` of obligation `k` (Rocq `oblG_fuel`). -/
@[lantana_alias oblG_fuel]
def fuel (k : Oid) (a : Fuel) : IProp GF :=
  iprop(∃ ns, names k ns ∗ bankOwn ns.bank (Bank.cash a))

/-- A fraction `q` of the fuel supply (debt) `a` of obligation `k`: the cash of `k` in
circulation is at most `a` (Rocq `oblG_fuel_supply`). -/
@[lantana_alias oblG_fuel_supply]
def supply (k : Oid) (a : Fuel) (q : Qp) : IProp GF :=
  iprop(∃ ns, names k ns ∗ bankOwn ns.bank (Bank.debtOf a q))

/-- The authoritative state map. -/
def stateAuth (S : OidMap Bool) : IProp GF :=
  OSatGS.stateName (GF := GF) ↪●MAP S

/-- The authoritative map of names (Rocq: the local `oblG_bound_auth_id`). -/
@[lantana_alias oblG_bound_auth_id]
def namesAuth (Ns : OidMap OblNames) : IProp GF :=
  OSatGS.namesName (GF := GF) ↪●MAP Ns

#lantana_ignore oblG_state_token_id "no reservation maps: the state map `stateAuth`"
#lantana_ignore oblG_fuel_token_id "no reservation maps: per-obligation bank names"
#lantana_ignore oblG_owner_token_id "no owner ghost state"
#lantana_ignore oblG_owner "no owner ghost state: the owner is read from `Ω`"

/-! ### Instances -/

instance names_persistent (k : Oid) (ns : OblNames) : Persistent (names (GF := GF) k ns) := by
  unfold names; infer_instance

instance names_timeless (k : Oid) (ns : OblNames) : Timeless (names (GF := GF) k ns) := by
  unfold names; infer_instance

@[lantana_alias oblG_elem_persistent]
instance elem_persistent (k : Oid) : Persistent (elem (GF := GF) k) := by
  unfold elem; infer_instance

@[lantana_alias oblG_elem_timeless]
instance elem_timeless (k : Oid) : Timeless (elem (GF := GF) k) := by
  unfold elem; infer_instance

@[lantana_alias oblG_bound_persistent]
instance bound_persistent (k : Oid) (β : Fuel) : Persistent (bound (GF := GF) k β) := by
  unfold bound; infer_instance

@[lantana_alias oblG_bound_timeless]
instance bound_timeless (k : Oid) (β : Fuel) : Timeless (bound (GF := GF) k β) := by
  unfold bound; infer_instance

@[lantana_alias oblG_assigned_timeless]
instance assigned_timeless (k : Oid) (q : Qp) : Timeless (assigned (GF := GF) k q) := by
  unfold assigned; infer_instance

@[lantana_alias oblG_assigned_fractional]
instance assigned_fractional (k : Oid) : Fractional (assigned (GF := GF) k) where
  fractional p q := by
    unfold assigned
    exact (ghost_map_elem_fractional (GF := GF) _ k false).fractional p q

@[lantana_alias oblG_assigned_as_fractional]
instance assigned_asFractional (k : Oid) (q : Qp) {ioΦ ioq : InOut} :
    AsFractional (assigned (GF := GF) k q) ioΦ (assigned k) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := assigned_fractional k

@[lantana_alias oblG_discharged_persistent]
instance discharged_persistent (k : Oid) : Persistent (discharged (GF := GF) k) := by
  unfold discharged; infer_instance

@[lantana_alias oblG_discharged_timeless]
instance discharged_timeless (k : Oid) : Timeless (discharged (GF := GF) k) := by
  unfold discharged; infer_instance

@[lantana_alias oblG_fuel_timeless]
instance fuel_timeless (k : Oid) (a : Fuel) : Timeless (fuel (GF := GF) k a) := by
  unfold fuel; infer_instance

@[lantana_alias oblG_fuel_supply_timeless]
instance supply_timeless (k : Oid) (a : Fuel) (q : Qp) : Timeless (supply (GF := GF) k a q) := by
  unfold supply; infer_instance

instance stateAuth_timeless (S : OidMap Bool) : Timeless (stateAuth (GF := GF) S) := by
  unfold stateAuth; infer_instance

@[lantana_alias oblG_bound_auth_id_timeless]
instance namesAuth_timeless (Ns : OidMap OblNames) : Timeless (namesAuth (GF := GF) Ns) := by
  unfold namesAuth; infer_instance

#lantana_ignore oblG_state_token_id_timeless "no reservation maps: `stateAuth_timeless`"
#lantana_ignore oblG_fuel_token_id_timeless "no reservation maps"
#lantana_ignore oblG_owner_token_id_timeless "no owner ghost state"
#lantana_ignore oblG_owner_timeless "no owner ghost state"
#lantana_ignore oblG_owner_fractional "no owner ghost state"
#lantana_ignore oblG_owner_as_fractional "no owner ghost state"

/-! ### Names -/

theorem names_agree (k : Oid) (ns₁ ns₂ : OblNames) :
    names k ns₁ ∗ names k ns₂ ⊢@{IProp GF} ⌜ns₁ = ns₂⌝ :=
  ghost_map_elem_agree _ _ _ _ _ _

/-- The names of an obligation are in the authoritative map (Rocq `oblG_bound_lookup`, which
looks up the bound in the authoritative map of bounds). -/
@[lantana_alias oblG_bound_lookup]
theorem names_lookup (Ns : OidMap OblNames) (k : Oid) (ns : OblNames) :
    namesAuth Ns ∗ names k ns ⊢@{IProp GF} ⌜get? Ns k = some ns⌝ := by
  unfold namesAuth names
  iintro ⟨Ha, Hn⟩
  iapply ghost_map_lookup $$ Ha Hn

theorem elem_lookup (Ns : OidMap OblNames) (k : Oid) :
    namesAuth Ns ∗ elem k ⊢@{IProp GF} ⌜(get? Ns k).isSome⌝ := by
  unfold elem
  iintro ⟨Ha, %ns, Hn⟩
  icases names_lookup Ns k ns $$ [$Ha $Hn] with %h
  ipureintro
  simp [h]

theorem names_insert {Ns : OidMap OblNames} {k : Oid} (hk : get? Ns k = none) (ns : OblNames) :
    namesAuth Ns ⊢@{IProp GF} |==> (namesAuth (insert Ns k ns) ∗ names k ns) := by
  unfold namesAuth names
  iintro Ha
  iapply ghost_map_insert_persist k ns hk $$ Ha

/-- Allocation of the ghost state of a new obligation `k`: fresh names for its bound `β` and its
bank, with the whole supply `a` and the cash `a` (Rocq `oblG_bound_alloc` and
`oblG_fuel_alloc`). -/
@[lantana_alias oblG_bound_alloc, lantana_alias oblG_fuel_alloc]
theorem names_alloc {Ns : OidMap OblNames} {k : Oid} (hk : get? Ns k = none) (β a : Fuel) :
    namesAuth Ns ⊢@{IProp GF} |==> ∃ ns, namesAuth (insert Ns k ns) ∗ bound k β ∗
      supply k a 1 ∗ fuel k a := by
  iintro Ha
  imod iOwn_alloc (F := constOFP (Agree (DiscreteO Fuel))) (GF := GF) (toAgree ⟨β⟩)
    Agree.toAgree_valid with ⟨%γb, #Hb⟩
  imod iOwn_alloc (F := constOFP (Bank Fuel)) (GF := GF) (Bank.debtOf a 1 • Bank.cash a)
    (Bank.valid_debtOf_cash.mpr ⟨OCM.le_rfl, (Qp.le_iff).mpr (by simp)⟩) with ⟨%γf, Hf⟩
  imod names_insert hk ⟨γb, γf⟩ $$ Ha with ⟨Ha, #Hn⟩
  icases iOwn_op $$ Hf with ⟨Hs, Hc⟩
  imodintro
  iexists ⟨γb, γf⟩
  iframe Ha
  unfold bound supply fuel boundOwn bankOwn
  isplitr
  · iexists ⟨γb, γf⟩
    iframe Hn
    iexact Hb
  isplitl [Hs]
  · iexists ⟨γb, γf⟩
    iframe Hn
    iexact Hs
  · iexists ⟨γb, γf⟩
    iframe Hn
    iexact Hc

/-! ### Bound -/

@[lantana_alias oblG_bound_agree]
theorem bound_agree (k : Oid) (β₁ β₂ : Fuel) :
    bound k β₁ ∗ bound k β₂ ⊢@{IProp GF} ⌜β₁ = β₂⌝ := by
  unfold bound
  iintro ⟨⟨%ns₁, #Hn₁, H₁⟩, ⟨%ns₂, #Hn₂, H₂⟩⟩
  icases names_agree k ns₁ ns₂ $$ [$Hn₁ $Hn₂] with %h
  subst h
  iapply boundOwn_agree $$ [$H₁ $H₂]

@[lantana_alias oblG_bound_elem]
theorem bound_elem (k : Oid) (β : Fuel) : bound k β ⊢@{IProp GF} elem k := by
  unfold bound elem
  iintro ⟨%ns, #Hn, -⟩
  iexists ns
  iexact Hn

/-! ### State -/

@[lantana_alias oblG_assigned_frac_valid]
theorem assigned_frac_valid (k : Oid) (q : Qp) : assigned k q ⊢@{IProp GF} ⌜q ≤ 1⌝ := by
  unfold assigned
  iintro H
  icases ghost_map_elem_valid _ _ _ _ $$ H with %h
  ipureintro
  exact DFrac.valid_own.mp h

@[lantana_alias oblG_assigned_agree]
theorem assigned_agree (k : Oid) (q₁ q₂ : Qp) :
    assigned k q₁ ∗ assigned k q₂ ⊢@{IProp GF} ⌜q₁ + q₂ ≤ 1⌝ := by
  unfold assigned
  iintro ⟨H₁, H₂⟩
  icombine H₁ H₂ gives %⟨h, -⟩
  ipureintro
  exact DFrac.valid_own.mp h

@[lantana_alias oblG_assigned_discharged_false]
theorem assigned_discharged_false (k : Oid) (q : Qp) :
    assigned k q ∗ discharged k ⊢@{IProp GF} False := by
  unfold assigned discharged
  iintro ⟨H₁, H₂⟩
  icases ghost_map_elem_agree _ _ _ _ _ _ $$ [$H₁ $H₂] with %h
  cases h

theorem state_lookup_assigned (S : OidMap Bool) (k : Oid) (q : Qp) :
    stateAuth S ∗ assigned k q ⊢@{IProp GF} ⌜get? S k = some false⌝ := by
  unfold stateAuth assigned
  iintro ⟨Ha, H⟩
  iapply ghost_map_lookup $$ Ha H

theorem state_lookup_discharged (S : OidMap Bool) (k : Oid) :
    stateAuth S ∗ discharged k ⊢@{IProp GF} ⌜get? S k = some true⌝ := by
  unfold stateAuth discharged
  iintro ⟨Ha, H⟩
  iapply ghost_map_lookup $$ Ha H

@[lantana_alias oblG_alloc_assigned]
theorem state_insert_assigned {S : OidMap Bool} {k : Oid} (hk : get? S k = none) :
    stateAuth S ⊢@{IProp GF} |==> (stateAuth (insert S k false) ∗ assigned k 1) := by
  unfold stateAuth assigned
  iintro Ha
  iapply ghost_map_insert k false hk $$ Ha

@[lantana_alias oblG_alloc_discharged]
theorem state_insert_discharged {S : OidMap Bool} {k : Oid} (hk : get? S k = none) :
    stateAuth S ⊢@{IProp GF} |==> (stateAuth (insert S k true) ∗ discharged k) := by
  unfold stateAuth discharged
  iintro Ha
  iapply ghost_map_insert_persist k true hk $$ Ha

/-- Discharge: the full assigned state becomes discharged (Rocq `oblG_assigned_to_discharged`,
here against the authoritative state map). -/
@[lantana_alias oblG_assigned_to_discharged]
theorem assigned_to_discharged (S : OidMap Bool) (k : Oid) :
    stateAuth S ∗ assigned k 1 ⊢@{IProp GF}
      |==> (stateAuth (insert S k true) ∗ discharged k) := by
  unfold stateAuth assigned discharged
  iintro ⟨Ha, H⟩
  imod ghost_map_update true $$ Ha H with ⟨Ha, H⟩
  imod ghost_map_elem_persist $$ H with H
  imodintro
  iframe

#lantana_ignore oblG_assigned_to_discharged_2 "the fractions combine by `assigned_fractional`"
#lantana_ignore oblG_assigned_to_true_2 "no boolean flag on the state"
#lantana_ignore oblG_assigned_to_true "no boolean flag on the state"

/-! ### Fuel (cash) -/

#lantana_ignore oblG_fuel_eq "Leibniz equality"
#lantana_ignore oblG_fuel_eq_list "Leibniz equality"
#lantana_ignore oblG_fuel_eq_set "Leibniz equality"

/-- Two pieces of the bank of `k` (fuel or supply) are under the same names. -/
private theorem bank_combine (k : Oid) (x y : Bank Fuel) :
    (∃ ns, names k ns ∗ bankOwn ns.bank x) ∗ (∃ ns, names k ns ∗ bankOwn ns.bank y) ⊢@{IProp GF}
      ∃ ns, names k ns ∗ bankOwn ns.bank (x • y) := by
  iintro ⟨⟨%ns₁, #Hn₁, H₁⟩, ⟨%ns₂, #Hn₂, H₂⟩⟩
  icases names_agree k ns₁ ns₂ $$ [$Hn₁ $Hn₂] with %h
  subst h
  iexists ns₁
  iframe Hn₁
  iapply (bankOwn_op _ x y).mpr
  isplitl [H₁]
  · iexact H₁
  · iexact H₂

private theorem bank_split (k : Oid) (x y : Bank Fuel) :
    (∃ ns, names k ns ∗ bankOwn ns.bank (x • y)) ⊢@{IProp GF}
      (∃ ns, names k ns ∗ bankOwn ns.bank x) ∗ (∃ ns, names k ns ∗ bankOwn ns.bank y) := by
  iintro ⟨%ns, #Hn, H⟩
  icases bankOwn_op _ x y $$ H with ⟨H₁, H₂⟩
  isplitl [H₁]
  · iexists ns
    iframe Hn
    iexact H₁
  · iexists ns
    iframe Hn
    iexact H₂

private theorem bank_update {k : Oid} {x y : Bank Fuel} (h : x ~~> y) :
    (∃ ns, names k ns ∗ bankOwn ns.bank x) ⊢@{IProp GF}
      |==> ∃ ns, names k ns ∗ bankOwn ns.bank y := by
  iintro ⟨%ns, #Hn, H⟩
  imod bankOwn_update h $$ H with H
  imodintro
  iexists ns
  iframe Hn
  iexact H

@[lantana_alias oblG_fuel_mon]
theorem fuel_mon {k : Oid} {a₀ a₁ : Fuel} (h : a₀ ≤ a₁) :
    fuel k a₁ ⊢@{IProp GF} |==> fuel k a₀ :=
  bank_update (Bank.cash_update h)

@[lantana_alias oblG_fuel_split]
theorem fuel_split (k : Oid) (a₀ a₁ : Fuel) :
    fuel k (a₀ +ₕ a₁) ⊣⊢@{IProp GF} fuel k a₀ ∗ fuel k a₁ :=
  ⟨bank_split k (Bank.cash a₀) (Bank.cash a₁), bank_combine k (Bank.cash a₀) (Bank.cash a₁)⟩

@[lantana_alias oblG_fuel_mon_split]
theorem fuel_mon_split {k : Oid} {a₀ a₁ a₂ : Fuel} (h : a₀ +ₕ a₁ ≤ a₂) :
    fuel k a₂ ⊢@{IProp GF} |==> (fuel k a₀ ∗ fuel k a₁) :=
  (fuel_mon h).trans (BIUpdate.mono (fuel_split k a₀ a₁).mp)

/-- Split off a positive unit of fuel. -/
@[lantana_alias oblG_fuel_lt]
theorem fuel_lt {k : Oid} {a₀ a₁ : Fuel} (h : a₀ < a₁) :
    fuel k a₁ ⊢@{IProp GF} |==> (fuel k a₀ ∗ ∃ c, ⌜0 < c⌝ ∗ fuel k c) := by
  obtain ⟨c, hc, hle⟩ := Ordinal.lt_exists_left.mpr h
  iintro H
  imod fuel_mon_split hle $$ H with ⟨H₀, Hc⟩
  imodintro
  iframe H₀
  iexists c
  iframe Hc
  ipureintro
  exact hc

instance fuel_intoSep (k : Oid) (a₀ a₁ : Fuel) :
    IntoSep (fuel (GF := GF) k (a₀ +ₕ a₁)) (fuel k a₀) (fuel k a₁) where
  into_sep := (fuel_split k a₀ a₁).mp

instance fuel_fromSep (k : Oid) (a₀ a₁ : Fuel) :
    FromSep (fuel (GF := GF) k (a₀ +ₕ a₁)) (fuel k a₀) (fuel k a₁) where
  from_sep := (fuel_split k a₀ a₁).mpr

instance fuel_combineSepAs (k : Oid) (a₀ a₁ : Fuel) :
    CombineSepAs (fuel (GF := GF) k a₀) (fuel k a₁) (fuel k (a₀ +ₕ a₁)) where
  combine_sep_as := (fuel_split k a₀ a₁).mpr

/-! Big-operator versions, over lists and sets of obligations. -/

@[lantana_alias oblG_fuel_mon_list]
theorem fuel_mon_list {L : List Oid} {a₀ a₁ : Fuel} (h : a₀ ≤ a₁) :
    ([∗list] k ∈ L, fuel k a₁) ⊢@{IProp GF} |==> [∗list] k ∈ L, fuel k a₀ :=
  (BigSepL.bigSepL_mono_of_forall (fuel_mon h)).trans (BigSepL.bigSepL_bupd _ L)

@[lantana_alias oblG_fuel_split_list]
theorem fuel_split_list (L : List Oid) (a₀ a₁ : Fuel) :
    ([∗list] k ∈ L, fuel k (a₀ +ₕ a₁)) ⊣⊢@{IProp GF}
      ([∗list] k ∈ L, fuel k a₀) ∗ [∗list] k ∈ L, fuel k a₁ :=
  ⟨(BigSepL.bigSepL_mono_of_forall (fuel_split _ a₀ a₁).mp).trans BigSepL.bigSepL_sep_eqv.mp,
    BigSepL.bigSepL_sep_eqv.mpr.trans (BigSepL.bigSepL_mono_of_forall (fuel_split _ a₀ a₁).mpr)⟩

@[lantana_alias oblG_fuel_mon_split_list]
theorem fuel_mon_split_list {L : List Oid} {a₀ a₁ a₂ : Fuel} (h : a₀ +ₕ a₁ ≤ a₂) :
    ([∗list] k ∈ L, fuel k a₂) ⊢@{IProp GF}
      |==> (([∗list] k ∈ L, fuel k a₀) ∗ [∗list] k ∈ L, fuel k a₁) :=
  (fuel_mon_list h).trans (BIUpdate.mono (fuel_split_list L a₀ a₁).mp)

@[lantana_alias oblG_fuel_lt_list]
theorem fuel_lt_list {L : List Oid} {a₀ a₁ : Fuel} (h : a₀ < a₁) :
    ([∗list] k ∈ L, fuel k a₁) ⊢@{IProp GF}
      |==> (([∗list] k ∈ L, fuel k a₀) ∗ [∗list] k ∈ L, ∃ c, ⌜0 < c⌝ ∗ fuel k c) :=
  (BigSepL.bigSepL_mono_of_forall (fuel_lt h)).trans <|
    (BigSepL.bigSepL_bupd _ L).trans (BIUpdate.mono BigSepL.bigSepL_sep_eqv.mp)

@[lantana_alias oblG_fuel_mon_set]
theorem fuel_mon_set {K : Oids} {a₀ a₁ : Fuel} (h : a₀ ≤ a₁) :
    ([∗set] k ∈ K, fuel k a₁) ⊢@{IProp GF} |==> [∗set] k ∈ K, fuel k a₀ :=
  (BigSepS.bigSepS_mono_of_forall fun _ => fuel_mon h).trans (BigSepS.bigSepS_bupd _ K)

@[lantana_alias oblG_fuel_split_set]
theorem fuel_split_set (K : Oids) (a₀ a₁ : Fuel) :
    ([∗set] k ∈ K, fuel k (a₀ +ₕ a₁)) ⊣⊢@{IProp GF}
      ([∗set] k ∈ K, fuel k a₀) ∗ [∗set] k ∈ K, fuel k a₁ :=
  ⟨(BigSepS.bigSepS_mono_of_forall fun _ => (fuel_split _ a₀ a₁).mp).trans BigSepS.bigSepS_sep.mp,
    BigSepS.bigSepS_sep.mpr.trans
      (BigSepS.bigSepS_mono_of_forall fun _ => (fuel_split _ a₀ a₁).mpr)⟩

@[lantana_alias oblG_fuel_mon_split_set]
theorem fuel_mon_split_set {K : Oids} {a₀ a₁ a₂ : Fuel} (h : a₀ +ₕ a₁ ≤ a₂) :
    ([∗set] k ∈ K, fuel k a₂) ⊢@{IProp GF}
      |==> (([∗set] k ∈ K, fuel k a₀) ∗ [∗set] k ∈ K, fuel k a₁) :=
  (fuel_mon_set h).trans (BIUpdate.mono (fuel_split_set K a₀ a₁).mp)

@[lantana_alias oblG_fuel_lt_set]
theorem fuel_lt_set {K : Oids} {a₀ a₁ : Fuel} (h : a₀ < a₁) :
    ([∗set] k ∈ K, fuel k a₁) ⊢@{IProp GF}
      |==> (([∗set] k ∈ K, fuel k a₀) ∗ [∗set] k ∈ K, ∃ c, ⌜0 < c⌝ ∗ fuel k c) :=
  (BigSepS.bigSepS_mono_of_forall fun _ => fuel_lt h).trans <|
    (BigSepS.bigSepS_bupd _ K).trans (BIUpdate.mono BigSepS.bigSepS_sep.mp)

/-! ### Fuel (supply) -/

@[lantana_alias oblG_fuel_supply_fractional]
instance supply_fractional (k : Oid) (a : Fuel) : Fractional (supply (GF := GF) k a) where
  fractional p q := by
    unfold supply
    rw [Bank.debt_split (add := nadd) a p q]
    exact ⟨bank_split k _ _, bank_combine k _ _⟩

@[lantana_alias oblG_fuel_supply_as_fractional]
instance supply_asFractional (k : Oid) (a : Fuel) (q : Qp) {ioΦ ioq : InOut} :
    AsFractional (supply (GF := GF) k a q) ioΦ (supply k a) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := supply_fractional k a

@[lantana_alias oblG_fuel_supply_mon]
theorem supply_mon {k : Oid} {a₀ a₁ : Fuel} (q : Qp) (h : a₀ ≤ a₁) :
    supply k a₀ q ⊢@{IProp GF} |==> supply k a₁ q :=
  bank_update (Bank.debtOf_update h)

@[lantana_alias oblG_fuel_supply_add]
theorem supply_add (k : Oid) (a₀ a₁ : Fuel) (q₀ q₁ : Qp) :
    supply k a₀ q₀ ∗ supply k a₁ q₁ ⊢@{IProp GF}
      ∃ b, supply k b (q₀ + q₁) ∗ ⌜b ≤ a₀ ∧ b ≤ a₁⌝ := by
  refine (bank_combine k _ _).trans ?_
  rw [Bank.debtOf_op (add := nadd)]
  unfold supply
  iintro H
  iexists min a₀ a₁
  iframe H
  ipureintro
  exact ⟨OCM.min_le_left a₀ a₁, OCM.min_le_right a₀ a₁⟩

@[lantana_alias oblG_fuel_supply_dfrac_valid]
theorem supply_frac_valid (k : Oid) (a : Fuel) (q : Qp) :
    supply k a q ⊢@{IProp GF} ⌜q ≤ 1⌝ := by
  unfold supply
  iintro ⟨%ns, -, H⟩
  icases bankOwn_valid _ _ $$ H with %h
  ipureintro
  exact (Bank.valid_debt.mp h).2

/-- The cash of an obligation is at most its supply. -/
theorem supply_fuel_le (k : Oid) (a c : Fuel) (q : Qp) :
    supply k a q ∗ fuel k c ⊢@{IProp GF} ⌜c ≤ a⌝ := by
  refine (bank_combine k _ _).trans ?_
  iintro ⟨%ns, -, H⟩
  icases bankOwn_valid _ _ $$ H with %hv
  ipureintro
  exact (Bank.valid_debtOf_cash.mp hv).1

/-- Issue cash `a₁`, raising the supply (the full fraction is needed). -/
@[lantana_alias oblG_fuel_supply_issue]
theorem supply_issue (k : Oid) (a₀ a₁ : Fuel) :
    supply k a₀ 1 ⊢@{IProp GF} |==> (supply k (a₀ +ₕ a₁) 1 ∗ fuel k a₁) :=
  (bank_update (Bank.debtOf_owe a₀ a₁)).trans (BIUpdate.mono (bank_split k _ _))

/-- Spend cash `a₁`, lowering the supply (any fraction). -/
@[lantana_alias oblG_fuel_spend]
theorem supply_spend (k : Oid) (a₀ a₁ : Fuel) (q : Qp) :
    supply k a₀ q ∗ fuel k a₁ ⊢@{IProp GF} |==> ∃ a₂, ⌜a₁ +ₕ a₂ ≤ a₀⌝ ∗ supply k a₂ q := by
  refine (bank_combine k _ _).trans ?_
  unfold supply
  iintro ⟨%ns, #Hn, H⟩
  imod bankOwn_updateP (Bank.debtOf_pay a₀ a₁ q) $$ H with ⟨%x, %⟨a₂, rfl, ha₂⟩, H⟩
  imodintro
  iexists a₂
  isplitr
  · ipureintro
    exact ha₂
  · iexists ns
    iframe Hn
    iexact H

@[lantana_alias oblG_fuel_supply_issue_2]
theorem supply_issue_2 {k : Oid} {q₀ q₁ : Qp} (hq : q₀ + q₁ = 1) (a₀ a₁ b : Fuel) :
    supply k a₀ q₀ ∗ supply k a₁ q₁ ⊢@{IProp GF}
      |==> (supply k (a₀ +ₕ b) q₀ ∗ supply k (a₀ +ₕ b) q₁ ∗ fuel k b) := by
  have e₁ : supply k a₀ (q₀ + q₁) ⊢@{IProp GF} supply k a₀ 1 := by
    rw [hq]
  have e₂ : supply k (a₀ +ₕ b) 1 ⊢@{IProp GF} supply k (a₀ +ₕ b) q₀ ∗ supply k (a₀ +ₕ b) q₁ := by
    rw [← hq]
    exact ((supply_fractional k _).fractional q₀ q₁).mp
  iintro H
  icases supply_add k a₀ a₁ q₀ q₁ $$ H with ⟨%c, H, %hc⟩
  imod supply_mon (q₀ + q₁) hc.1 $$ H with H
  ihave H := e₁ $$ H
  imod supply_issue k a₀ b $$ H with ⟨H, Hf⟩
  icases e₂ $$ H with ⟨H₀, H₁⟩
  imodintro
  iframe

@[lantana_alias oblG_fuel_spend_2]
theorem supply_spend_2 (k : Oid) (a₀ a₁ c : Fuel) (q₀ q₁ : Qp) :
    supply k a₀ q₀ ∗ supply k a₁ q₁ ∗ fuel k c ⊢@{IProp GF}
      |==> ∃ a₂, ⌜c +ₕ a₂ ≤ a₀ ∧ c +ₕ a₂ ≤ a₁⌝ ∗ supply k a₂ q₀ ∗ supply k a₂ q₁ := by
  iintro ⟨H₀, H₁, Hf⟩
  icases supply_add k a₀ a₁ q₀ q₁ $$ [$H₀ $H₁] with ⟨%b, H, %hb⟩
  imod supply_spend k b c (q₀ + q₁) $$ [$H $Hf] with ⟨%a₂, %ha₂, H⟩
  icases (supply_fractional k a₂).fractional q₀ q₁ $$ H with ⟨H₀, H₁⟩
  imodintro
  iexists a₂
  iframe H₀ H₁
  ipureintro
  exact ⟨Ordinal.le_trans ha₂ hb.1, Ordinal.le_trans ha₂ hb.2⟩

/-! ### The invariant of one obligation -/

/-- The invariant of obligation `k` in state `g`: a bound `β`, the whole supply `α ≤ β`, and `α`
at most the model fuel (assigned) or the persistent discharged state (Rocq: the body of the
big separating conjunction of `osat`, without the owner and the fractions of the state). -/
@[reducible] def oblInv (k : Oid) : Obl → IProp GF
  | .assigned a _ => iprop(∃ β, bound k β ∗ ∃ α, supply k α 1 ∗ ⌜α ≤ β ∧ α ≤ a⌝)
  | .discharged => iprop(∃ β, bound k β ∗ ∃ α, supply k α 1 ∗ ⌜α ≤ β⌝ ∗ discharged k)

instance oblInv_timeless (k : Oid) (g : Obl) : Timeless (oblInv (GF := GF) k g) := by
  cases g <;> unfold oblInv <;> infer_instance

end OSat

/-! ## The invariant `osat` -/

/-- The authoritative maps `S` (statuses) and `Ns` (names) of `osat Ω` have the domain of `Ω`,
and `S` records the statuses of `Ω`. -/
structure OSatWf (Ω : Obls) (S : OidMap Bool) (Ns : OidMap OblNames) : Prop where
  state : ∀ k, get? S k = (get? Ω k).map Obl.isDischarged
  names : ∀ k, (get? Ns k).isSome = (get? Ω k).isSome

namespace OSatWf

variable {Ω : Obls} {S : OidMap Bool} {Ns : OidMap OblNames}

theorem empty : OSatWf ∅ ∅ ∅ where
  state k := by simp [get?_empty]
  names k := by simp [get?_empty]

theorem state_none (h : OSatWf Ω S Ns) {k : Oid} (hk : get? Ω k = none) : get? S k = none := by
  simp [h.state k, hk]

theorem names_none (h : OSatWf Ω S Ns) {k : Oid} (hk : get? Ω k = none) : get? Ns k = none := by
  have := h.names k
  simp only [hk, Option.isSome_none, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at this
  exact this

theorem alloc (h : OSatWf Ω S Ns) (k : Oid) (g : Obl) (ns : OblNames) :
    OSatWf (insert Ω k g) (insert S k g.isDischarged) (insert Ns k ns) where
  state j := by
    rw [get?_insert, get?_insert]
    split
    · rfl
    · exact h.state j
  names j := by
    rw [get?_insert, get?_insert]
    split
    · rfl
    · exact h.names j

/-- A change of an obligation that keeps its status. -/
theorem insert_same (h : OSatWf Ω S Ns) {k : Oid} {g g' : Obl} (hk : get? Ω k = some g)
    (hg : g'.isDischarged = g.isDischarged) : OSatWf (insert Ω k g') S Ns where
  state j := by
    rw [get?_insert]
    split
    · next hkj => subst hkj; rw [h.state k, hk, Option.map_some, Option.map_some, hg]
    · exact h.state j
  names j := by
    rw [get?_insert]
    split
    · next hkj => subst hkj; rw [h.names k, hk]; rfl
    · exact h.names j

/-- The discharge of an obligation. -/
theorem discharge (h : OSatWf Ω S Ns) {k : Oid} {g : Obl} (hk : get? Ω k = some g) :
    OSatWf (insert Ω k .discharged) (insert S k true) Ns where
  state j := by
    rw [get?_insert, get?_insert]
    split
    · rfl
    · exact h.state j
  names j := by
    rw [get?_insert]
    split
    · next hkj => subst hkj; rw [h.names k, hk]; rfl
    · exact h.names j

theorem assigned_of_state (h : OSatWf Ω S Ns) {k : Oid} (hk : get? S k = some false) :
    ∃ a t, get? Ω k = some (.assigned a t) := by
  rw [h.state k] at hk
  cases e : get? Ω k with
  | none => simp [e] at hk
  | some g =>
    cases g with
    | assigned a t => exact ⟨a, t, rfl⟩
    | discharged => simp [e] at hk

theorem discharged_of_state (h : OSatWf Ω S Ns) {k : Oid} (hk : get? S k = some true) :
    get? Ω k = some .discharged := by
  rw [h.state k] at hk
  cases e : get? Ω k with
  | none => simp [e] at hk
  | some g =>
    cases g with
    | assigned a t => simp [e] at hk
    | discharged => rfl

end OSatWf

/-! ### Pure lemmas for `osat_progress`

`osat_progress` makes the obligations of a submap `D` of `Ω` progress one by one. The condition
of the round is `(get? D k).isSome ∧ C k g`, evaluated on the values of the initial map `Ω`. -/

namespace Obls

variable {C : Oid → Obl → Prop}

private theorem condProgress_empty (Ω : Obls) :
    condProgress (fun k g => (get? (∅ : Obls) k).isSome ∧ C k g) Ω Ω :=
  ⟨mapForall2_refl (fun _ _ => .inr ⟨by simp [get?_empty], rfl⟩) Ω, keep_refl Ω⟩

private theorem condProgress_get?_of_none {D Ω Ω₁ : Obls} {i : Oid} {x : Obl}
    (h₁ : condProgress (fun k g => (get? D k).isSome ∧ C k g) Ω Ω₁) (hi : get? D i = none)
    (hΩi : get? Ω i = some x) : get? Ω₁ i = some x := by
  obtain ⟨y, hy, hr⟩ := mapForall2.lookup_left h₁.1 hΩi
  rcases hr with ⟨⟨hc, -⟩, -⟩ | ⟨-, rfl⟩
  · simp [hi] at hc
  · exact hy

private theorem condProgress_insert_step {D Ω Ω₁ : Obls} {i : Oid} {a a' : Fuel}
    {o : ThreadId} (h₁ : condProgress (fun k g => (get? D k).isSome ∧ C k g) Ω Ω₁)
    (hΩi : get? Ω i = some (.assigned a o)) (hCi : C i (.assigned a o)) (hlt : a' < a) :
    condProgress (fun k g => (get? (insert D i (.assigned a o)) k).isSome ∧ C k g) Ω
      (insert Ω₁ i (.assigned a' o)) := by
  obtain ⟨hs, hkeep⟩ := h₁
  refine ⟨mapForall2_intro fun j => ?_, mapForall2_intro fun j => ?_⟩
  · by_cases hij : i = j
    · subst hij
      exact .inr ⟨_, _, hΩi, get?_insert_eq rfl,
        .inl ⟨⟨by simp [get?_insert_eq], hCi⟩, .inl hlt⟩⟩
    · rw [get?_insert_ne hij]
      rcases hs.inv j with ⟨e₁, e₂⟩ | ⟨g₁, g₂, e₁, e₂, hr⟩
      · exact .inl ⟨e₁, e₂⟩
      · refine .inr ⟨g₁, g₂, e₁, e₂, ?_⟩
        simpa only [get?_insert_ne hij] using hr
  · by_cases hij : i = j
    · subst hij
      exact .inr ⟨_, _, hΩi, get?_insert_eq rfl, trivial⟩
    · rw [get?_insert_ne hij]
      exact hkeep.inv j

private theorem condProgress_insert_skip {D Ω Ω₁ : Obls} {i : Oid} {x : Obl}
    (h₁ : condProgress (fun k g => (get? D k).isSome ∧ C k g) Ω Ω₁) (hi : get? D i = none)
    (hΩi : get? Ω i = some x) (hnC : ¬C i x) :
    condProgress (fun k g => (get? (insert D i x) k).isSome ∧ C k g) Ω Ω₁ := by
  refine ⟨condRel_iff_lookup h₁.1 fun j g hj => ?_, h₁.2⟩
  by_cases hij : i = j
  · subst hij
    rw [hΩi] at hj
    cases hj
    simp [hi, hnC]
  · simp [get?_insert_ne hij]

end Obls

section Osat

variable {GF : BundledGFunctors} [OSatGS GF]

/-- The invariant of the ghost state of obligations (Rocq `osat`): the authoritative state map
records the statuses of `Ω`, the authoritative name map has the domain of `Ω`, and every
obligation satisfies `OSat.oblInv`. -/
@[lantana_alias osat]
def osat (Ω : Obls) : IProp GF :=
  iprop(∃ S Ns, ⌜OSatWf Ω S Ns⌝ ∗ OSat.stateAuth S ∗ OSat.namesAuth Ns ∗
    [∗map] k ↦ g ∈ Ω, OSat.oblInv k g)

@[lantana_alias osat_timeless]
instance osat_timeless (Ω : Obls) : Timeless (osat (GF := GF) Ω) := by
  unfold osat; infer_instance

/-! ### Lookups -/

@[lantana_alias osat_elem]
theorem osat_elem (Ω : Obls) (k : Oid) :
    osat Ω ∗ OSat.elem k ⊢@{IProp GF} ⌜(get? Ω k).isSome⌝ := by
  unfold osat
  iintro ⟨⟨%S, %Ns, %hwf, -, HN, -⟩, He⟩
  icases OSat.elem_lookup Ns k $$ [$HN $He] with %h
  ipureintro
  rw [← hwf.names k]
  exact h

@[lantana_alias osat_elem_lookup]
theorem osat_elem_lookup (Ω : Obls) (k : Oid) :
    osat Ω ∗ OSat.elem k ⊢@{IProp GF} ⌜∃ a t, get? Ω k = some (.assigned a t)⌝ ∨
      (OSat.discharged k ∗ ⌜get? Ω k = some .discharged⌝) := by
  unfold osat
  iintro ⟨⟨%S, %Ns, %hwf, -, HN, HM⟩, He⟩
  icases OSat.elem_lookup Ns k $$ [$HN $He] with %h
  rw [hwf.names k] at h
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp h
  cases g with
  | assigned a t =>
    ileft
    ipureintro
    exact ⟨a, t, hg⟩
  | discharged =>
    iright
    icases BigSepM.bigSepM_lookup hg $$ HM with ⟨%β, -, %α, -, -, #Hd⟩
    iframe Hd
    ipureintro
    exact hg

/-- An assigned state is in `Ω` (Rocq `osat_lookup_assigned`, which also takes `oblG_elem k`). -/
@[lantana_alias osat_lookup_assigned]
theorem osat_lookup_assigned (Ω : Obls) (k : Oid) (q : Qp) :
    osat Ω ∗ OSat.assigned k q ⊢@{IProp GF} ⌜∃ a t, get? Ω k = some (.assigned a t)⌝ := by
  unfold osat
  iintro ⟨⟨%S, %Ns, %hwf, HS, -, -⟩, Ha⟩
  icases OSat.state_lookup_assigned S k q $$ [$HS $Ha] with %h
  ipureintro
  exact hwf.assigned_of_state h

/-- A discharged state is in `Ω` (Rocq `osat_lookup_discharged`, which also takes
`oblG_elem k`). -/
@[lantana_alias osat_lookup_discharged]
theorem osat_lookup_discharged (Ω : Obls) (k : Oid) :
    osat Ω ∗ OSat.discharged k ⊢@{IProp GF} ⌜get? Ω k = some .discharged⌝ := by
  unfold osat
  iintro ⟨⟨%S, %Ns, %hwf, HS, -, -⟩, Hd⟩
  icases OSat.state_lookup_discharged S k $$ [$HS $Hd] with %h
  ipureintro
  exact hwf.discharged_of_state h

#lantana_ignore osat_lookup_owner "no owner ghost state: the owner is read from `Ω`"
#lantana_ignore osat_open_owner "no owner ghost state: the owner is read from `Ω`"
#lantana_ignore osat_assigned_to_true "no boolean flag on the state"
#lantana_ignore Qp_add_help_1 "no fractions of the state in `osat`"

/-- The cash of an obligation is at most its model fuel (Rocq `osat_fuel_le`, in `oforest.v`). -/
@[lantana_alias osat_fuel_le]
theorem osat_fuel_le (Ω : Obls) (x : Oid) (a : Fuel) :
    osat Ω ∗ OSat.fuel x a ⊢@{IProp GF}
      ⌜∀ f t, get? Ω x = some (.assigned f t) → a ≤ f⌝ := by
  unfold osat
  iintro ⟨⟨%S, %Ns, %hwf, -, -, HM⟩, Hf⟩
  cases hx : get? Ω x with
  | none =>
    ipureintro
    intro f t h
    cases h
  | some g =>
    cases g with
    | discharged =>
      ipureintro
      intro f t h
      cases h
    | assigned f t =>
      icases BigSepM.bigSepM_lookup hx $$ HM with ⟨%β, -, %α, Hsup, %hα⟩
      icases OSat.supply_fuel_le x α a 1 $$ [$Hsup $Hf] with %h
      ipureintro
      intro f' t' h'
      cases h'
      exact Ordinal.le_trans h hα.2

/-! ### Allocation -/

@[lantana_alias osat_alloc_obl_assigned]
theorem osat_alloc_obl_assigned {Ω : Obls} {k : Oid} (hk : get? Ω k = none) (α : Fuel)
    (t : ThreadId) :
    osat Ω ⊢@{IProp GF} |==> (osat (insert Ω k (.assigned α t)) ∗ OSat.bound k α ∗ OSat.elem k ∗
      OSat.assigned k 1 ∗ OSat.fuel k α ∗ ⌜Obls.alloc Ω (insert Ω k (.assigned α t))⌝) := by
  unfold osat
  iintro ⟨%S, %Ns, %hwf, HS, HN, HM⟩
  imod OSat.names_alloc (hwf.names_none hk) α α $$ HN with ⟨%ns, HN, #Hb, Hsup, Hf⟩
  imod OSat.state_insert_assigned (hwf.state_none hk) $$ HS with ⟨HS, Ha⟩
  imodintro
  isplitl [HS HN HM Hsup]
  · iexists insert S k false, insert Ns k ns
    isplitr
    · ipureintro
      exact hwf.alloc k (.assigned α t) ns
    iframe HS HN
    iapply (BigSepM.bigSepM_insert hk).mpr
    iframe HM
    iexists α
    iframe Hb
    iexists α
    iframe Hsup
    ipureintro
    exact ⟨Ordinal.le_rfl, Ordinal.le_rfl⟩
  iframe Hb Ha Hf
  isplitr
  · iapply OSat.bound_elem $$ Hb
  · ipureintro
    exact ⟨k, hk, _, rfl⟩

@[lantana_alias osat_alloc_obl_discharged]
theorem osat_alloc_obl_discharged {Ω : Obls} {k : Oid} (hk : get? Ω k = none) (α : Fuel) :
    osat Ω ⊢@{IProp GF} |==> (osat (insert Ω k .discharged) ∗ OSat.bound k α ∗ OSat.elem k ∗
      OSat.discharged k ∗ OSat.fuel k α ∗ ⌜Obls.alloc Ω (insert Ω k .discharged)⌝) := by
  unfold osat
  iintro ⟨%S, %Ns, %hwf, HS, HN, HM⟩
  imod OSat.names_alloc (hwf.names_none hk) α α $$ HN with ⟨%ns, HN, #Hb, Hsup, Hf⟩
  imod OSat.state_insert_discharged (hwf.state_none hk) $$ HS with ⟨HS, #Hd⟩
  imodintro
  isplitl [HS HN HM Hsup]
  · iexists insert S k true, insert Ns k ns
    isplitr
    · ipureintro
      exact hwf.alloc k .discharged ns
    iframe HS HN
    iapply (BigSepM.bigSepM_insert hk).mpr
    iframe HM
    iexists α
    iframe Hb
    iexists α
    iframe Hsup Hd
    ipureintro
    exact Ordinal.le_rfl
  iframe Hb Hd Hf
  isplitr
  · iapply OSat.bound_elem $$ Hb
  · ipureintro
    exact ⟨k, hk, _, rfl⟩

/-! ### Progress, owner change and discharge -/

/-- Spending positive cash makes an assigned obligation progress; its owner may change at the
same time (Rocq `osat_progress_one_owner`: without owner ghost state, the owner is just part of
the new `Ω`). -/
@[lantana_alias osat_progress_one_owner]
theorem osat_progress_one_owner {Ω : Obls} {k : Oid} {a : Fuel} {t₁ : ThreadId} (t₂ : ThreadId)
    {c : Fuel} (hk : get? Ω k = some (.assigned a t₁)) (hc : 0 < c) :
    osat Ω ∗ OSat.fuel k c ⊢@{IProp GF} |==> ∃ a', osat (insert Ω k (.assigned a' t₂)) ∗
      ⌜Obl.progress (.assigned a t₁) (.assigned a' t₂)⌝ := by
  unfold osat
  iintro ⟨⟨%S, %Ns, %hwf, HS, HN, HM⟩, Hf⟩
  icases (BigSepM.bigSepM_delete hk).mp $$ HM with ⟨⟨%β, #Hb, %α, Hsup, %hα⟩, HM⟩
  imod OSat.supply_spend k α c 1 $$ [$Hsup $Hf] with ⟨%a₂, %ha₂, Hsup⟩
  have hlt : a₂ < α := by
    refine Ordinal.lt_of_lt_of_le (lt_nadd_of_pos_right a₂ hc) ?_
    rw [nadd_comm]
    exact ha₂
  imodintro
  iexists a₂
  isplitl
  · iexists S, Ns
    isplitr
    · ipureintro
      exact hwf.insert_same hk rfl
    iframe HS HN
    iapply BigSepM.bigSepM_insert_delete.mpr
    iframe HM
    iexists β
    iframe Hb
    iexists a₂
    iframe Hsup
    ipureintro
    exact ⟨Ordinal.le_trans (Ordinal.le_of_lt hlt) hα.1, Ordinal.le_rfl⟩
  · ipureintro
    exact Ordinal.lt_of_lt_of_le hlt hα.2

/-- Spending positive cash makes an assigned obligation progress. -/
@[lantana_alias osat_progress_one]
theorem osat_progress_one {Ω : Obls} {k : Oid} {a : Fuel} {t : ThreadId} {c : Fuel}
    (hk : get? Ω k = some (.assigned a t)) (hc : 0 < c) :
    osat Ω ∗ OSat.fuel k c ⊢@{IProp GF} |==> ∃ a', osat (insert Ω k (.assigned a' t)) ∗
      ⌜Obl.progress (.assigned a t) (.assigned a' t)⌝ :=
  osat_progress_one_owner t hk hc

/-- Discharge an obligation with its full assigned state (Rocq `osat_discharge`, which also takes
`oblG_elem k` and the owner). -/
@[lantana_alias osat_discharge]
theorem osat_discharge (Ω : Obls) (k : Oid) :
    osat Ω ∗ OSat.assigned k 1 ⊢@{IProp GF} |==> (osat (insert Ω k .discharged) ∗
      OSat.discharged k ∗ ⌜∃ a t, get? Ω k = some (.assigned a t)⌝) := by
  unfold osat
  iintro ⟨⟨%S, %Ns, %hwf, HS, HN, HM⟩, Ha⟩
  icases OSat.state_lookup_assigned S k 1 $$ [$HS $Ha] with %hS
  obtain ⟨a, t, hk⟩ := hwf.assigned_of_state hS
  imod OSat.assigned_to_discharged S k $$ [$HS $Ha] with ⟨HS, #Hd⟩
  icases (BigSepM.bigSepM_delete hk).mp $$ HM with ⟨⟨%β, #Hb, %α, Hsup, %hα⟩, HM⟩
  imodintro
  isplitl [HS HN HM Hsup]
  · iexists insert S k true, Ns
    isplitr
    · ipureintro
      exact hwf.discharge hk
    iframe HS HN
    iapply BigSepM.bigSepM_insert_delete.mpr
    iframe HM
    iexists β
    iframe Hb
    iexists α
    iframe Hsup Hd
    ipureintro
    exact hα.1
  iframe Hd
  ipureintro
  exact ⟨a, t, hk⟩

/-- The obligations of a submap `D` of `Ω` that satisfy `C`, each with positive cash, progress;
the others stay. By induction on `D`. -/
private theorem osat_progress_sub (C : Oid → Obl → Prop)
    (hC : ∀ k g, C k g → ∃ a o, g = .assigned a o) (D : Obls) :
    ∀ Ω : Obls, D ⊆ Ω →
      osat Ω ∗ ([∗map] k ↦ g ∈ D, (⌜C k g⌝ ∗ ∃ c, ⌜0 < c⌝ ∗ OSat.fuel k c) ∨ ⌜¬C k g⌝)
        ⊢@{IProp GF} |==> ∃ Ω', osat Ω' ∗
          ⌜Obls.condProgress (fun k g => (get? D k).isSome ∧ C k g) Ω Ω'⌝ := by
  induction D using LawfulFiniteMap.induction_on with
  | hemp =>
    intro Ω _
    iintro ⟨Hs, -⟩
    imodintro
    iexists Ω
    iframe Hs
    ipureintro
    exact Obls.condProgress_empty Ω
  | hins i x D hi ih =>
    intro Ω hsub
    have hD : D ⊆ Ω := PartialMap.subset_trans (subset_insert hi) hsub
    have hΩi : get? Ω i = some x := hsub i x (get?_insert_eq rfl)
    iintro ⟨Hs, HD⟩
    icases (BigSepM.bigSepM_insert hi).mp $$ HD with ⟨Hi, HD⟩
    imod ih Ω hD $$ [$Hs $HD] with ⟨%Ω₁, Hs, %h₁⟩
    have hΩ₁i := Obls.condProgress_get?_of_none h₁ hi hΩi
    icases Hi with (⟨%hCi, %c, %hc, Hf⟩ | %hnC)
    · obtain ⟨a, o, rfl⟩ := hC i x hCi
      imod osat_progress_one hΩ₁i hc $$ [$Hs $Hf] with ⟨%a', Hs, %hp⟩
      imodintro
      iexists insert Ω₁ i (.assigned a' o)
      iframe Hs
      ipureintro
      exact Obls.condProgress_insert_step h₁ hΩi hCi hp
    · imodintro
      iexists Ω₁
      iframe Hs
      ipureintro
      exact Obls.condProgress_insert_skip h₁ hi hΩi hnC

/-- The obligations that satisfy `C`, each with positive cash, progress; the others stay
(Rocq `osat_progress`). -/
@[lantana_alias osat_progress]
theorem osat_progress (Ω : Obls) (C : Oid → Obl → Prop)
    (hC : ∀ k g, C k g → ∃ a o, g = .assigned a o) :
    osat Ω ∗ ([∗map] k ↦ g ∈ Ω, (⌜C k g⌝ ∗ ∃ c, ⌜0 < c⌝ ∗ OSat.fuel k c) ∨ ⌜¬C k g⌝)
      ⊢@{IProp GF} |==> ∃ Ω', osat Ω' ∗ ⌜Obls.condProgress C Ω Ω'⌝ := by
  refine (osat_progress_sub C hC Ω Ω (PartialMap.subset_refl Ω)).trans (BIUpdate.mono ?_)
  iintro ⟨%Ω', Hs, %h⟩
  iexists Ω'
  iframe Hs
  ipureintro
  exact ⟨condRel_iff_lookup h.1 fun k g hk => by simp [hk], h.2⟩

end Osat

/-- Allocation of the ghost state of obligations, with no obligation (Rocq `osat_alloc`). -/
@[lantana_alias osat_alloc]
theorem osat_alloc {GF : BundledGFunctors} [OSatGpreS GF] :
    ⊢@{IProp GF} |==> ∃ _ : OSatGS GF, osat ∅ := by
  imod ghost_map_alloc_empty (GF := GF) (K := Oid) (V := Bool) with ⟨%γs, HS⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Oid) (V := OblNames) with ⟨%γn, HN⟩
  imodintro
  iexists { stateName := γs, namesName := γn }
  unfold osat OSat.stateAuth OSat.namesAuth
  iexists ∅, ∅
  iframe HS HN
  isplitr
  · ipureintro
    exact OSatWf.empty
  · iapply BigSepM.bigSepM_empty.mpr
    iempintro

end Lantana.Model
