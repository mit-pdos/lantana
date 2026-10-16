/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Algebra.BCred
public import Lantana.BaseLogic.Witness
public import Lantana.BaseLogic.ModelRel
public import Lantana.BaseLogic.Model.OSat
public import Lantana.BaseLogic.Model.MapBigOp

/-! # The ghost state of witnesses

Rocq `lantana/base_logic/owit.v`: every obligation has a witness with a persistent *bound*
and *credits* (the bounded-credit camera `BCred Fuel` of `Algebra/BCred.lean`, under a
per-obligation ghost name recorded in a persistent name map). The invariant `owit W` holds, for
every assigned witness `k` with bound `b`, credits `α ≥ b` (so credits can be split off whenever
a witness makes progress); for discharged witnesses it holds the persistent `OSat.discharged k`.
The pure relation between obligations and witnesses is `owitInv` (`ModelRel.lean`).
-/

@[expose] public noncomputable section

namespace Lantana.Model

open Iris Iris.BI Iris.ProofMode Iris.Std LawfulPartialMap
open Ordinals Ordinal

/-- The ghost state of witnesses that a world provides: the name map and the per-obligation
credit camera (in `Type 2`, through `constOFP`). -/
@[lantana_alias owitGpreS] -- Rocq `owitGS.owitGpreS`
class OWitGpreS (GF : BundledGFunctors) where
  [namesG : GhostMapG GF Oid GName OidMap]
  credG : ElemG GF (constOFP (BCred Fuel))

attribute [reducible, instance] OWitGpreS.namesG OWitGpreS.credG
attribute [lantana_alias owitGpreS_witness] OWitGpreS.credG

/-- The ghost state of witnesses: the name of the name map. -/
@[lantana_alias owitGS] -- Rocq `owitGS.owitGS`
class OWitGS (GF : BundledGFunctors) extends OWitGpreS GF where
  /-- The ghost name of the map of per-obligation credit names. -/
  namesName : GName

attribute [lantana_alias owit_inG] OWitGS.toOWitGpreS
attribute [lantana_alias witness_name] OWitGS.namesName

#lantana_ignore «owitΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#lantana_ignore «subG_owitΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#lantana_ignore witG_bound_token_id "no reservation maps: per-obligation ghost names"
#lantana_ignore witG_bound_token_id_timeless "no reservation maps"

namespace OWit

variable {GF : BundledGFunctors} [OWitGS GF]

/-- The ghost name of the credit camera of obligation `k` is `γ` (persistent). -/
def names (k : Oid) (γ : GName) : IProp GF :=
  OWitGS.namesName (GF := GF) ↪◯MAP[k]{DFrac.discard} γ

/-- The authoritative map of credit names. -/
def namesAuth (Ns : OidMap GName) : IProp GF :=
  OWitGS.namesName (GF := GF) ↪●MAP Ns

/-- Ownership of the credit camera at the name `γ`. -/
def credOwn (γ : GName) (x : BCred Fuel) : IProp GF :=
  iOwn (F := constOFP (BCred Fuel)) γ x

/-- The witness bound of obligation `k` is `ℵ` (persistent; Rocq `witG_bound`). -/
@[lantana_alias witG_bound]
def bound (k : Oid) (ℵ : Fuel) : IProp GF :=
  iprop(∃ γ, names k γ ∗ credOwn γ (BCred.creditBound ℵ))

/-- `a` credits of the witness of obligation `k` (Rocq `witG_witness`). -/
@[lantana_alias witG_witness]
def cred (k : Oid) (a : Fuel) : IProp GF :=
  iprop(∃ γ, names k γ ∗ credOwn γ (BCred.credit a))

instance names_persistent (k : Oid) (γ : GName) : Persistent (names (GF := GF) k γ) := by
  unfold names; infer_instance

instance names_timeless (k : Oid) (γ : GName) : Timeless (names (GF := GF) k γ) := by
  unfold names; infer_instance

instance namesAuth_timeless (Ns : OidMap GName) : Timeless (namesAuth (GF := GF) Ns) := by
  unfold namesAuth; infer_instance

instance credOwn_timeless (γ : GName) (x : BCred Fuel) : Timeless (credOwn (GF := GF) γ x) := by
  unfold credOwn; infer_instance

instance credOwn_bound_persistent (γ : GName) (ℵ : Fuel) :
    Persistent (credOwn (GF := GF) γ (BCred.creditBound ℵ)) := by
  unfold credOwn; infer_instance

@[lantana_alias witG_bound_persistent]
instance bound_persistent (k : Oid) (ℵ : Fuel) : Persistent (bound (GF := GF) k ℵ) := by
  unfold bound; infer_instance

@[lantana_alias witG_bound_timeless]
instance bound_timeless (k : Oid) (ℵ : Fuel) : Timeless (bound (GF := GF) k ℵ) := by
  unfold bound; infer_instance

@[lantana_alias witG_witness_timeless]
instance cred_timeless (k : Oid) (a : Fuel) : Timeless (cred (GF := GF) k a) := by
  unfold cred; infer_instance

/-! ### Ownership -/

theorem credOwn_op (γ : GName) (x y : BCred Fuel) :
    credOwn γ (x • y) ⊣⊢@{IProp GF} credOwn γ x ∗ credOwn γ y := by
  unfold credOwn; exact iOwn_op

theorem credOwn_valid (γ : GName) (x : BCred Fuel) : credOwn γ x ⊢@{IProp GF} ⌜✓ x⌝ := by
  unfold credOwn
  iintro H
  icases iOwn_cmraValid $$ H with %h
  ipureintro
  exact h

theorem credOwn_mono {γ : GName} {x y : BCred Fuel} (h : y ≼ x) :
    credOwn γ x ⊢@{IProp GF} credOwn γ y := by
  unfold credOwn; exact iOwn_mono h

theorem credOwn_update {γ : GName} {x y : BCred Fuel} (h : x ~~> y) :
    credOwn γ x ⊢@{IProp GF} |==> credOwn γ y := by
  unfold credOwn; exact iOwn_update h

theorem credOwn_updateP {γ : GName} {x : BCred Fuel} {P : BCred Fuel → Prop} (h : x ~~>: P) :
    credOwn γ x ⊢@{IProp GF} |==> ∃ y, ⌜P y⌝ ∗ credOwn γ y := by
  unfold credOwn; exact iOwn_updateP h

/-! ### Names -/

theorem names_agree (k : Oid) (γ₁ γ₂ : GName) :
    names k γ₁ ∗ names k γ₂ ⊢@{IProp GF} ⌜γ₁ = γ₂⌝ :=
  ghost_map_elem_agree _ _ _ _ _ _

theorem names_lookup (Ns : OidMap GName) (k : Oid) (γ : GName) :
    namesAuth Ns ∗ names k γ ⊢@{IProp GF} ⌜get? Ns k = some γ⌝ := by
  unfold namesAuth names
  iintro ⟨Ha, Hn⟩
  iapply ghost_map_lookup $$ Ha Hn

theorem names_insert {Ns : OidMap GName} {k : Oid} (hk : get? Ns k = none) (γ : GName) :
    namesAuth Ns ⊢@{IProp GF} |==> (namesAuth (insert Ns k γ) ∗ names k γ) := by
  unfold namesAuth names
  iintro Ha
  iapply ghost_map_insert_persist k γ hk $$ Ha

/-- Allocation of the credit camera of a new witness `k` with bound and credits `a`
(Rocq `witG_bound_id_alloc`). -/
@[lantana_alias witG_bound_id_alloc]
theorem names_alloc {Ns : OidMap GName} {k : Oid} (hk : get? Ns k = none) (a : Fuel) :
    namesAuth Ns ⊢@{IProp GF} |==> ∃ γ, namesAuth (insert Ns k γ) ∗ bound k a ∗ cred k a := by
  iintro Ha
  imod iOwn_alloc (F := constOFP (BCred Fuel)) (GF := GF)
    (BCred.creditBound a • BCred.credit a) (BCred.creditBound_credit_valid_eq a) with ⟨%γ, H⟩
  imod names_insert hk γ $$ Ha with ⟨Ha, #Hn⟩
  icases iOwn_op $$ H with ⟨Hb, Hc⟩
  imodintro
  iexists γ
  iframe Ha
  unfold bound cred credOwn
  isplitl [Hb]
  · iexists γ
    iframe Hn
    iexact Hb
  · iexists γ
    iframe Hn
    iexact Hc

/-! ### Credits -/

/-- Two pieces of the credit camera of `k` are under the same name. -/
private theorem cred_combine (k : Oid) (x y : BCred Fuel) :
    (∃ γ, names k γ ∗ credOwn γ x) ∗ (∃ γ, names k γ ∗ credOwn γ y) ⊢@{IProp GF}
      ∃ γ, names k γ ∗ credOwn γ (x • y) := by
  iintro ⟨⟨%γ₁, #Hn₁, H₁⟩, ⟨%γ₂, #Hn₂, H₂⟩⟩
  icases names_agree k γ₁ γ₂ $$ [$Hn₁ $Hn₂] with %h
  subst h
  iexists γ₁
  iframe Hn₁
  iapply (credOwn_op _ x y).mpr
  isplitl [H₁]
  · iexact H₁
  · iexact H₂

private theorem cred_split' (k : Oid) (x y : BCred Fuel) :
    (∃ γ, names k γ ∗ credOwn γ (x • y)) ⊢@{IProp GF}
      (∃ γ, names k γ ∗ credOwn γ x) ∗ (∃ γ, names k γ ∗ credOwn γ y) := by
  iintro ⟨%γ, #Hn, H⟩
  icases credOwn_op _ x y $$ H with ⟨H₁, H₂⟩
  isplitl [H₁]
  · iexists γ
    iframe Hn
    iexact H₁
  · iexists γ
    iframe Hn
    iexact H₂

private theorem cred_update' {k : Oid} {x y : BCred Fuel} (h : x ~~> y) :
    (∃ γ, names k γ ∗ credOwn γ x) ⊢@{IProp GF} |==> ∃ γ, names k γ ∗ credOwn γ y := by
  iintro ⟨%γ, #Hn, H⟩
  imod credOwn_update h $$ H with H
  imodintro
  iexists γ
  iframe Hn
  iexact H

#lantana_ignore witG_witness_eq "Leibniz equality"

@[lantana_alias witG_witness_mon]
theorem cred_mon {k : Oid} {a₀ a₁ : Fuel} (h : a₀ ≤ a₁) :
    cred k a₁ ⊢@{IProp GF} |==> cred k a₀ :=
  cred_update' (BCred.credit_update h)

@[lantana_alias witG_witness_split]
theorem cred_split (k : Oid) (a₀ a₁ : Fuel) :
    cred k (a₀ +ₕ a₁) ⊣⊢@{IProp GF} cred k a₀ ∗ cred k a₁ :=
  ⟨cred_split' k (BCred.credit a₀) (BCred.credit a₁),
    cred_combine k (BCred.credit a₀) (BCred.credit a₁)⟩

@[lantana_alias witG_witness_mon_split]
theorem cred_mon_split {k : Oid} {a₀ a₁ a₂ : Fuel} (h : a₀ +ₕ a₁ ≤ a₂) :
    cred k a₂ ⊢@{IProp GF} |==> (cred k a₀ ∗ cred k a₁) :=
  (cred_mon h).trans (BIUpdate.mono (cred_split k a₀ a₁).mp)

/-- Split off a positive credit. -/
@[lantana_alias witG_witness_lt]
theorem cred_lt {k : Oid} {a₀ a₁ : Fuel} (h : a₀ < a₁) :
    cred k a₁ ⊢@{IProp GF} |==> (cred k a₀ ∗ ∃ c, ⌜0 < c⌝ ∗ cred k c) := by
  obtain ⟨c, hc, hle⟩ := Ordinal.lt_exists_left.mpr h
  iintro H
  imod cred_mon_split hle $$ H with ⟨H₀, Hc⟩
  imodintro
  iframe H₀
  iexists c
  iframe Hc
  ipureintro
  exact hc

instance cred_intoSep (k : Oid) (a₀ a₁ : Fuel) :
    IntoSep (cred (GF := GF) k (a₀ +ₕ a₁)) (cred k a₀) (cred k a₁) where
  into_sep := (cred_split k a₀ a₁).mp

instance cred_fromSep (k : Oid) (a₀ a₁ : Fuel) :
    FromSep (cred (GF := GF) k (a₀ +ₕ a₁)) (cred k a₀) (cred k a₁) where
  from_sep := (cred_split k a₀ a₁).mpr

/-- Zero credits come for free from any credits (`a = a +ₕ 0`). -/
theorem cred_zero (k : Oid) (a : Fuel) : cred k a ⊢@{IProp GF} cred k a ∗ cred k 0 := by
  have h := (cred_split (GF := GF) k a 0).mp
  rwa [Ordinal.nadd_zero] at h

/-! ### Bounds -/

/-- A bound may be raised (`creditBound a₁ ≼ creditBound a₀` for `a₀ ≤ a₁`; Rocq
`witG_bound_mon`, there under an update). -/
@[lantana_alias witG_bound_mon]
theorem bound_mon {k : Oid} {a₀ a₁ : Fuel} (h : a₀ ≤ a₁) :
    bound k a₀ ⊢@{IProp GF} bound k a₁ := by
  unfold bound
  iintro ⟨%γ, #Hn, H⟩
  iexists γ
  iframe Hn
  iapply credOwn_mono (BCred.creditBound_included h) $$ H

/-- The credits are below the bound (Rocq `witG_compare`). -/
@[lantana_alias witG_compare]
theorem compare (k : Oid) (a₀ a₁ : Fuel) :
    bound k a₀ ∗ cred k a₁ ⊢@{IProp GF} ⌜a₁ ≤ a₀⌝ := by
  unfold bound cred
  iintro H
  icases cred_combine k (BCred.creditBound a₀) (BCred.credit a₁) $$ H with ⟨%γ, -, H⟩
  icases credOwn_valid _ _ $$ H with %hv
  ipureintro
  exact BCred.creditBound_credit_valid_compare.mp hv

/-- Spending credits lowers the bound (Rocq `witG_witness_spend_gen`). -/
@[lantana_alias witG_witness_spend_gen]
theorem cred_spend_gen (k : Oid) (a₀ a₁ : Fuel) :
    bound k a₀ ∗ cred k a₁ ⊢@{IProp GF} |==> ∃ a₂, ⌜a₁ +ₕ a₂ ≤ a₀⌝ ∗ bound k a₂ := by
  unfold bound cred
  iintro H
  icases cred_combine k (BCred.creditBound a₀) (BCred.credit a₁) $$ H with ⟨%γ, #Hn, H⟩
  imod credOwn_updateP (BCred.credit_spend a₀ a₁) $$ H with ⟨%y, %⟨a₂, rfl, hle⟩, H⟩
  imodintro
  iexists a₂
  isplitr
  · ipureintro
    exact hle
  · iexists γ
    iframe Hn
    iexact H

/-- Spending positive credits strictly lowers the bound (Rocq `witG_witness_spend`). -/
@[lantana_alias witG_witness_spend]
theorem cred_spend {k : Oid} {a₀ a₁ : Fuel} (h : 0 < a₁) :
    bound k a₀ ∗ cred k a₁ ⊢@{IProp GF} |==> ∃ a₂, ⌜a₂ < a₀⌝ ∗ bound k a₂ := by
  iintro H
  imod cred_spend_gen k a₀ a₁ $$ H with ⟨%a₂, %hle, Hb⟩
  imodintro
  iexists a₂
  iframe Hb
  ipureintro
  refine Ordinal.lt_of_lt_of_le ?_ hle
  rw [Ordinal.nadd_comm]
  exact Ordinal.lt_nadd_of_pos_right a₂ h

/-- The content of the invariant for one witness. -/
@[reducible] def witInv [OSatGS GF] (k : Oid) : Witness → IProp GF
  | .assigned b => iprop(∃ α, ⌜b ≤ α⌝ ∗ cred k α)
  | .discharged => OSat.discharged k

/-- A positive credit of an assigned witness (what a progress round yields). -/
@[reducible] def witCredit [OSatGS GF] (k : Oid) : Witness → IProp GF
  | .assigned _ => iprop(∃ c, ⌜0 < c⌝ ∗ cred k c)
  | .discharged => OSat.discharged k

/-- Zero credits of an assigned witness. -/
@[reducible] def witCreditZero [OSatGS GF] (k : Oid) : Witness → IProp GF
  | .assigned _ => cred k 0
  | .discharged => OSat.discharged k

instance witInv_timeless [OSatGS GF] (k : Oid) (w : Witness) :
    Timeless (witInv (GF := GF) k w) := by
  cases w <;> infer_instance

end OWit

/-! ## The invariant `owit` -/

section Owit

variable {GF : BundledGFunctors} [OSatGS GF] [OWitGS GF]

/-- The invariant of the ghost state of witnesses (Rocq `owit`): the name map has the domain of
`W`, every assigned witness has credits above its bound, and every discharged witness is a
discharged obligation. -/
@[lantana_alias owit]
def owit (W : Witnesses) : IProp GF :=
  iprop(∃ Ns : OidMap GName, ⌜∀ k, (get? W k).isSome ↔ (get? Ns k).isSome⌝ ∗
    OWit.namesAuth Ns ∗ [∗map] k ↦ w ∈ W, OWit.witInv k w)

@[lantana_alias owit_timeless]
instance owit_timeless (W : Witnesses) : Timeless (owit (GF := GF) W) := by
  unfold owit; infer_instance

/-! ### Allocation of witnesses -/

@[lantana_alias owit_alloc_witness_assigned]
theorem owit_alloc_witness_assigned {W : Witnesses} {k : Oid} (hk : get? W k = none)
    (a : Fuel) :
    owit W ⊢@{IProp GF} |==> (owit (insert W k (.assigned a)) ∗ OWit.bound k a) := by
  unfold owit
  iintro ⟨%Ns, %hdom, HN, HM⟩
  have hNs : get? Ns k = none := by
    have := hdom k
    rw [hk] at this
    simpa using this.symm
  imod OWit.names_alloc hNs a $$ HN with ⟨%γ, HN, #Hb, Hc⟩
  imodintro
  iframe Hb
  iexists insert Ns k γ
  iframe HN
  isplitr
  · ipureintro
    intro k'
    by_cases hkk : k = k'
    · subst hkk
      simp [get?_insert_eq rfl]
    · rw [get?_insert_ne hkk, get?_insert_ne hkk]
      exact hdom k'
  · iapply (BigSepM.bigSepM_insert hk).mpr
    iframe HM
    iexists a
    iframe Hc
    ipureintro
    exact Ordinal.le_rfl

@[lantana_alias owit_alloc_witness_discharged]
theorem owit_alloc_witness_discharged {W : Witnesses} {k : Oid} (hk : get? W k = none)
    (a : Fuel) :
    owit W ∗ OSat.discharged k ⊢@{IProp GF}
      |==> (owit (insert W k .discharged) ∗ OWit.bound k a) := by
  unfold owit
  iintro ⟨⟨%Ns, %hdom, HN, HM⟩, #Hd⟩
  have hNs : get? Ns k = none := by
    have := hdom k
    rw [hk] at this
    simpa using this.symm
  imod OWit.names_alloc hNs a $$ HN with ⟨%γ, HN, #Hb, -⟩
  imodintro
  iframe Hb
  iexists insert Ns k γ
  iframe HN
  isplitr
  · ipureintro
    intro k'
    by_cases hkk : k = k'
    · subst hkk
      simp [get?_insert_eq rfl]
    · rw [get?_insert_ne hkk, get?_insert_ne hkk]
      exact hdom k'
  · iapply (BigSepM.bigSepM_insert hk).mpr
    iframe HM
    iexact Hd

/-! ### Rounds -/

/-- Witnesses may decrease (Rocq `owit_mon`): the lemma every round uses to re-establish the
invariant for the environment's choice of witnesses. -/
@[lantana_alias owit_mon]
theorem owit_mon {W₁ W₂ : Witnesses} (h : Witnesses.mono W₁ W₂) :
    owit W₁ ⊢@{IProp GF} owit W₂ := by
  unfold owit
  iintro ⟨%Ns, %hdom, HN, HM⟩
  iexists Ns
  iframe HN
  isplitr
  · ipureintro
    intro k
    rw [← h.isSome_iff k]
    exact hdom k
  · have hpt : ∀ k w₁ w₂, Witness.ndLe w₁ w₂ →
        OWit.witInv (GF := GF) k w₁ ⊢ OWit.witInv k w₂ := by
      intro k w₁ w₂ hw
      cases w₁ <;> cases w₂ <;> simp only [Witness.ndLe] at hw
      · -- assigned → assigned, the bound decreased
        iintro ⟨%α, %hα, Hc⟩
        iexists α
        iframe Hc
        ipureintro
        exact Ordinal.le_trans hw hα
      · exact .rfl
    iapply bigSepM_mapForall2 h hpt $$ HM

/-- A progress round of the assigned witnesses yields a positive credit for each of them
(Rocq `owit_progress`). -/
@[lantana_alias owit_progress]
theorem owit_progress {W₁ W₂ : Witnesses}
    (h : Witnesses.condProgress Witness.condAssigned W₁ W₂) :
    owit W₁ ⊢@{IProp GF} |==> (owit W₂ ∗ [∗map] k ↦ w ∈ W₁, OWit.witCredit k w) := by
  unfold owit
  have hR : mapForall2 (fun k w₁ w₂ =>
      ((Witness.condAssigned k w₁ ∧ Witness.step w₁ w₂) ∨
        (¬Witness.condAssigned k w₁ ∧ w₁ = w₂)) ∧ Witness.keep w₁ w₂) W₁ W₂ :=
    h.1.and h.2
  have hpt : ∀ k w₁ w₂, (((Witness.condAssigned k w₁ ∧ Witness.step w₁ w₂) ∨
        (¬Witness.condAssigned k w₁ ∧ w₁ = w₂)) ∧ Witness.keep w₁ w₂) →
      OWit.witInv (GF := GF) k w₁ ⊢ |==> (OWit.witInv k w₂ ∗ OWit.witCredit k w₁) := by
    intro k w₁ w₂ ⟨hw, hkeep⟩
    rcases hw with ⟨hC, hs | hs⟩ | ⟨hC, rfl⟩
    · -- progress of an assigned witness
      cases w₁ with
      | discharged => exact hC.elim
      | assigned b₁ =>
        cases w₂ with
        | discharged => exact hs.elim
        | assigned b₂ =>
          change b₂ < b₁ at hs
          iintro ⟨%α, %hα, Hc⟩
          obtain ⟨c, hc, hle⟩ := Ordinal.lt_exists_left.mpr (Ordinal.lt_of_lt_of_le hs hα)
          imod OWit.cred_mon_split hle $$ Hc with ⟨Hα, Hc⟩
          imodintro
          isplitl [Hα]
          · iexists b₂
            iframe Hα
            ipureintro
            exact Ordinal.le_rfl
          · iexists c
            iframe Hc
            ipureintro
            exact hc
    · -- a discharge step is excluded by `keep`
      exact (by cases w₁ <;> cases w₂ <;> first | exact hs.elim | exact hkeep.elim : False).elim
    · -- an unchanged (discharged) witness
      cases w₁ with
      | assigned b => exact (hC trivial).elim
      | discharged =>
        iintro #Hd
        imodintro
        iframe Hd
  iintro ⟨%Ns, %hdom, HN, HM⟩
  imod bigSepM_mapForall2_bupd hR hpt $$ HM with ⟨HM, HC⟩
  imodintro
  iframe HC
  iexists Ns
  iframe HN HM
  ipureintro
  intro k
  rw [← h.1.isSome_iff k]
  exact hdom k

/-- Any progress round keeps the invariant (Rocq `owit_progress_any`). -/
@[lantana_alias owit_progress_any]
theorem owit_progress_any {C : Oid → Witness → Prop} {W₁ W₂ : Witnesses}
    (h : Witnesses.condProgress C W₁ W₂) : owit W₁ ⊢@{IProp GF} owit W₂ :=
  owit_mon (Witnesses.condProgress_mono h)

/-- Discharging a witness needs no update: the credits are dropped (Rocq `owit_discharge`). -/
@[lantana_alias owit_discharge]
theorem owit_discharge {W : Witnesses} {k : Oid} {a : Fuel} (hk : get? W k = some (.assigned a)) :
    owit W ∗ OSat.discharged k ⊢@{IProp GF} owit (insert W k .discharged) := by
  unfold owit
  iintro ⟨⟨%Ns, %hdom, HN, HM⟩, #Hd⟩
  iexists Ns
  iframe HN
  isplitr
  · ipureintro
    intro k'
    by_cases hkk : k = k'
    · subst hkk
      rw [get?_insert_eq rfl]
      have := hdom k
      rw [hk] at this
      simpa using this
    · rw [get?_insert_ne hkk]
      exact hdom k'
  · icases (BigSepM.bigSepM_delete hk).1 $$ HM with ⟨-, HM⟩
    iapply BigSepM.bigSepM_insert_delete.2
    iframe HM
    iexact Hd

/-- Every witness yields zero credits (Rocq `owit_get_credit_zero`). -/
@[lantana_alias owit_get_credit_zero]
theorem owit_get_credit_zero (W : Witnesses) :
    owit W ⊢@{IProp GF} owit W ∗ [∗map] k ↦ w ∈ W, OWit.witCreditZero k w := by
  unfold owit
  iintro ⟨%Ns, %hdom, HN, HM⟩
  have hsplit : ([∗map] k ↦ w ∈ W, OWit.witInv (GF := GF) k w) ⊢
      [∗map] k ↦ w ∈ W, iprop(OWit.witInv k w ∗ OWit.witCreditZero k w) := by
    refine BigSepM.bigSepM_mono fun {k w} _ => ?_
    cases w with
    | assigned b =>
      iintro ⟨%α, %hα, Hc⟩
      icases OWit.cred_zero k α $$ Hc with ⟨Hc, H0⟩
      iframe H0
      iexists α
      iframe Hc
      ipureintro
      exact hα
    | discharged =>
      iintro #Hd
      iframe Hd
  icases hsplit $$ HM with HM
  icases (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1 $$ HM with ⟨HM, HZ⟩
  iframe HZ
  iexists Ns
  iframe HN HM
  ipureintro
  exact hdom

end Owit

/-- Allocation of the ghost state of witnesses, with no witness (Rocq `owit_alloc`). -/
@[lantana_alias owit_alloc]
theorem owit_alloc {GF : BundledGFunctors} [OSatGS GF] [OWitGpreS GF] :
    ⊢@{IProp GF} |==> ∃ _ : OWitGS GF, owit ∅ := by
  imod ghost_map_alloc_empty (GF := GF) (K := Oid) (V := GName) with ⟨%γ, HN⟩
  imodintro
  iexists { namesName := γ }
  unfold owit OWit.namesAuth
  iexists ∅
  iframe HN
  isplitr
  · ipureintro
    intro k
    simp [get?_empty]
  · iapply BigSepM.bigSepM_empty.mpr
    iempintro


end Lantana.Model
