/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.BaseLogic.Model.OPredsBase
public import Lantana.BaseLogic.Model.OForest
public import Lantana.BaseLogic.Model.MUpd

/-! # The children predicates and the model updates of the forest

Rocq `lantana/base_logic/opreds.v` §14.3–14.4, the part that involves the forest: the children
predicate `parKids p K` (the children of `p` are exactly `K`: the exclusive children fragment of
the forest, the children share of `p` if it is an obligation, and the children share of every
child), the running handle `thActive i` (the user's half of the running status of a thread),
`thDone i`; the facts that need no invariant (`oblKids_discharged_false`, `parKids_discharged`);
the round templates `mupd_ghost_round` and `mupd_model_round` over `Model.mupd_nd_step`, at any
view of the pool; the forest operations as model updates (thread termination, creation of an
obligation, live or discharged, moves, checks of witnesses, discharge of a leaf, the only round
with `Obls.lef`, and the read of the fuel as a rank of the forest, `kids_rank_mupd`); the facts
about the bill `OForest.bill i B` of a thread, an upper bound of its children; and the physical
steps: `mprog_step_kids` (paid by the bill), `mprog_step_crashed` (a crashed thread pays for
nothing), and `mphys_step_kids` (the forked threads get their pieces, the nodes of the newly
crashed threads go in and those of the recovered ones come out), with its form for unchanged
bits `mphys_step_fork`. Adding a child under `p` adds it to the bill of `p`
(`OForest.parBill`, nothing for an obligation). The statements are those of the sealed interface
`Lantana.ProgramLogic.OblForest`, whose predicates are these definitions.

Fraction scheme (plan M4 §1.4): the user's `oblAssigned k q` is the ghost fraction `q / 2`, the
two children shares `oblShare k` (one held by the children predicate of `k`, one by the children
predicate of its parent) are quarters, so `oblAssigned k 1 ∗ oblShare k ∗ oblShare k` is the whole
ghost fraction (`oblAssigned_shares`).
-/

@[expose] public noncomputable section

namespace Lantana.Model.OPreds

open Iris Iris.BI Iris.ProofMode Iris.Std LawfulPartialMap
open Ordinals Ordinal
open scoped Lantana.Measure

/-! ## Sets of obligations -/

/-- `Std.ExtTreeSet.insert` as the union with a singleton. -/
theorem oids_insert_eq (K : Oids) (k : Oid) : K.insert k = {k} ∪ K :=
  insert_eq_singleton_union_extTreeSet

/-- `Std.ExtTreeSet.erase` as a set difference. -/
theorem oids_erase_eq (K : Oids) (k : Oid) : K.erase k = K \ {k} :=
  LawfulSet.ext fun x => by
    rw [Std.ExtTreeSet.mem_erase, LawfulSet.mem_diff, LawfulSet.mem_singleton, Ne,
      Std.LawfulEqCmp.compare_eq_iff_eq]
    grind

/-- `Std.ExtTreeMap.insert` is the partial-map insertion of Iris-Lean. -/
theorem oidMap_insert_eq {V : Type _} (F : OidMap V) (k : Oid) (v : V) :
    F.insert k v = PartialMap.insert F k v := by
  refine Std.ExtTreeMap.ext_getElem? fun k' => ?_
  change (F.insert k v)[k']? = (F.alter k fun _ => some v)[k']?
  rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_alter]

/-- `BigSepS.bigSepS_insert` for `Std.ExtTreeSet.insert`. -/
theorem bigSepS_oids_insert {PROP : Type _} [BI PROP] {Φ : Oid → PROP} {K : Oids} {k : Oid}
    (hk : k ∉ K) : ([∗set] x ∈ K.insert k, Φ x) ⊣⊢ Φ k ∗ [∗set] x ∈ K, Φ x := by
  rw [oids_insert_eq]
  exact BigSepS.bigSepS_insert hk

/-- `BigSepS.bigSepS_delete` for `Std.ExtTreeSet.erase`. -/
theorem bigSepS_oids_erase {PROP : Type _} [BI PROP] {Φ : Oid → PROP} {K : Oids} {k : Oid}
    (hk : k ∈ K) : ([∗set] x ∈ K, Φ x) ⊣⊢ Φ k ∗ [∗set] x ∈ K.erase k, Φ x := by
  rw [oids_erase_eq]
  exact BigSepS.bigSepS_delete hk

variable {GF : BundledGFunctors}

/-! ## Definitions -/

section Defs

variable [OSatGS GF] [OForestGS GF]

/-- What the children predicate of `p` holds of `p` itself: nothing for a thread, the children
share of an obligation. -/
@[reducible] def parSelf : Parent → IProp GF
  | .thread _ => iprop(emp)
  | .obl k => oblShare k

/-- The children of `p` are exactly `K` (Rocq `parP_kids`): the children fragment of the forest,
what `p` holds of itself (`parSelf`), and the children share of every child. -/
@[lantana_alias omodel.parP_kids]
def parKids (p : Parent) (K : Oids) : IProp GF :=
  iprop(parSelf p ∗ OForest.kids p K ∗ [∗set] x ∈ K, oblShare x)

/-- Thread `i` is running: the user's half of its running status. -/
def thActive (i : ThreadId) : IProp GF :=
  OForest.exec i (Qp.half 1)

/-- Thread `i` has terminated (Rocq `thP_done`). -/
@[lantana_alias omodel.thP_done]
def thDone (i : ThreadId) : IProp GF :=
  OForest.done i

instance parSelf_timeless (p : Parent) : Timeless (parSelf (GF := GF) p) := by
  cases p <;> unfold parSelf <;> infer_instance

instance parKids_timeless (p : Parent) (K : Oids) : Timeless (parKids (GF := GF) p K) := by
  unfold parKids; infer_instance

instance thActive_timeless (i : ThreadId) : Timeless (thActive (GF := GF) i) := by
  unfold thActive; infer_instance

instance thDone_timeless (i : ThreadId) : Timeless (thDone (GF := GF) i) := by
  unfold thDone; infer_instance

instance thDone_persistent (i : ThreadId) : Persistent (thDone (GF := GF) i) := by
  unfold thDone; infer_instance

/-- Rocq `parP_kids_frag`: the unfolded shape. -/
@[lantana_alias omodel.parP_kids_frag]
theorem parKids_unfold (p : Parent) (K : Oids) :
    parKids (GF := GF) p K ⊣⊢ parSelf p ∗ OForest.kids p K ∗ [∗set] x ∈ K, oblShare x :=
  .rfl

end Defs

section Layers

variable [OSatGS GF] [OWitGS GF]

/-- A new obligation at layer `ℓ` may be created below `p` (the interface's `parLe`). -/
@[reducible] def parLe : Parent → Layer → IProp GF
  | .thread _, _ => iprop(True)
  | .obl q, ℓ => iprop(∃ ℓq : Layer, ⌜ℓq ≤ ℓ⌝ ∗ witLayer q ℓq)

/-- One unit of fuel at layer `ℓ` is enough to hang below `p` (the interface's `parBelow`). -/
@[reducible] def parBelow : Parent → Layer → IProp GF
  | .thread _, _ => iprop(True)
  | .obl q, ℓ => iprop(∃ ℓq : Layer, ⌜ℓq < ℓ⌝ ∗ witLayer q ℓq)

end Layers

/-! ## Facts without the invariant -/

section Shares

variable [OSatGS GF]

/-- The fraction scheme: the user's full assignment and the two children shares. -/
theorem oblAssigned_shares (k : Oid) :
    OSat.elem k ∗ OSat.assigned k 1 ⊣⊢@{IProp GF} oblAssigned k 1 ∗ oblShare k ∗ oblShare k := by
  have e : OSat.assigned (GF := GF) k 1 =
      OSat.assigned k (Qp.half 1 + (Qp.half (Qp.half 1) + Qp.half (Qp.half 1))) := by
    rw [Qp.half_add_half, Qp.half_add_half]
  unfold oblAssigned oblShare
  rw [e, ((OSat.assigned_fractional k).fractional (Qp.half 1) _).to_eq,
    ((OSat.assigned_fractional k).fractional (Qp.half (Qp.half 1)) _).to_eq]
  constructor
  · iintro ⟨#He, Ha, Hb, Hc⟩
    isplitl [Ha]
    · iframe Ha
      iexact He
    isplitl [Hb]
    · iframe Hb
      iexact He
    · iframe Hc
      iexact He
  · iintro ⟨⟨#He, Ha⟩, ⟨-, Hb⟩, ⟨-, Hc⟩⟩
    iframe Ha Hb Hc
    iexact He

theorem oblShare_discharged_false (k : Oid) :
    oblShare (GF := GF) k ∗ oblDischarged k ⊢ False := by
  unfold oblShare oblDischarged
  iintro ⟨⟨-, Ha⟩, ⟨-, Hd⟩⟩
  iapply OSat.assigned_discharged_false k _ $$ [$Ha $Hd]

/-- Fuels at one layer with equal interpretations are equal (Rocq `oblP_fuel_proper`, which also
assumes `ℓ1 == ℓ2`: across layers, the model fuels differ by the `▽` of the encoding). -/
@[lantana_alias omodel.oblP_fuel_proper]
theorem oblFuel_eq_of_rep (k : Oid) (ℓ : Layer) {μ₁ μ₂ : Measure}
    (h : Measure.rep ℓ μ₁ = Measure.rep ℓ μ₂) :
    oblFuel (GF := GF) k ℓ μ₁ ⊣⊢ oblFuel k ℓ μ₂ := by
  unfold oblFuel modelFuel
  rw [Measure.rep_mul, Measure.rep_mul, h]
  exact .rfl

end Shares

section Facts

variable [OSatGS GF] [OForestGS GF]

@[lantana_alias omodel.oblP_kids_discharged_false]
theorem oblKids_discharged_false (k : Oid) (K : Oids) :
    parKids (GF := GF) (.obl k) K ⊢ oblDischarged k -∗ False := by
  unfold parKids
  iintro ⟨Hk, -, -⟩ Hd
  iapply oblShare_discharged_false k $$ [$Hk $Hd]

@[lantana_alias omodel.parP_kids_discharged]
theorem parKids_discharged (k : Oid) (p : Parent) (K : Oids) :
    parKids (GF := GF) p K ⊢ oblDischarged k -∗ ⌜k ∉ K⌝ := by
  unfold parKids
  iintro ⟨-, -, Hs⟩ Hd
  by_cases hk : k ∈ K
  · icases BigSepS.bigSepS_elem_of_acc hk $$ Hs with ⟨Hk, -⟩
    iexfalso
    iapply oblShare_discharged_false k $$ [$Hk $Hd]
  · ipureintro
    exact hk

omit [OSatGS GF] in
theorem thActive_done_false (i : ThreadId) : thActive (GF := GF) i ⊢ thDone i -∗ False := by
  unfold thActive thDone
  iintro He Hd
  iapply OForest.exec_done_false i _ $$ [$He $Hd]

end Facts

/-! ## Helpers for the rounds -/

/-- The part of a big separating conjunction over a map at the keys of `R`. -/
theorem bigSepM_restrict {V : Type _} (m : OidMap V) (R : Oids)
    (hR : ∀ r, r ∈ R → (get? m r).isSome) {Φ : Oid → V → IProp GF} {Ψ : Oid → IProp GF}
    (h : ∀ k v, get? m k = some v → k ∈ R → Φ k v ⊢ Ψ k) :
    ([∗map] k ↦ v ∈ m, Φ k v) ⊢ [∗set] r ∈ R, Ψ r := by
  have heq : (FiniteMap.dom_set (PartialMap.filter (fun x (_ : V) => decide (x ∈ R)) m) :
      Oids) = R := LawfulSet.ext fun x => by
    rw [LawfulFiniteMap.mem_dom_set, get?_filter]
    by_cases hx : x ∈ R
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hR x hx)
      simp [hv, hx]
    · cases get? m x <;> simp [hx]
  rw [← heq]
  refine (BigSepM.bigSepM_mono fun {k v} hkv => ?_).trans (bigSepS_dom_filter m _ Ψ).mpr
  by_cases hk : k ∈ R
  · simp only [hk, decide_true, ite_true]
    exact h k v hkv hk
  · simp only [hk, decide_false]
    exact Affine.affine

section Helpers

variable [OSatGS GF]

theorem witLayer_elem [OWitGS GF] (k : Oid) (ℓ : Layer) :
    witLayer (GF := GF) k ℓ ⊢ OSat.elem k := by
  unfold witLayer witBoundVal
  iintro ⟨⟨%μ, He, -⟩, -⟩
  iexact He

/-- The witnesses of `R` are obligations of the model. -/
theorem osat_elems [OWitGS GF] (Ω : Obls) (R : Oids) :
    osat Ω ∗ ([∗set] r ∈ R, ∃ ℓ, witLayer (GF := GF) r ℓ) ⊢
      ⌜∀ r, r ∈ R → (get? Ω r).isSome⌝ := by
  refine (BI.forall_intro fun r => ?_).trans BI.pure_forall.2
  by_cases hr : r ∈ R
  · refine (?_ : _ ⊢ ⌜(get? Ω r).isSome⌝).trans (BI.pure_mono fun h _ => h)
    iintro ⟨Hs, HR⟩
    icases BigSepS.bigSepS_elem_of_acc hr $$ HR with ⟨⟨%ℓ, Hw⟩, -⟩
    ihave He := witLayer_elem r ℓ $$ Hw
    iapply osat_elem Ω r $$ [$Hs $He]
  · exact BI.pure_intro fun h => (hr h).elim

/-- One unit of fuel at any layer is positive cash. -/
theorem oblFuel_pos (k : Oid) :
    (∃ ℓ, oblFuel (GF := GF) k ℓ 1) ⊢ ∃ c, ⌜0 < c⌝ ∗ OSat.fuel k c := by
  unfold oblFuel oblFuelVal
  iintro ⟨%ℓ, -, Hf⟩
  iexists modelFuel ℓ 1
  iframe Hf
  ipureintro
  rw [modelFuel_one, nadd_comm]
  exact Ordinal.lt_of_lt_of_le zero_lt_one (le_nadd_self _ _)

/-- The fuel `π` of `k` is a piece below `p` if it is above the fuel of the parent. -/
theorem fuel_forestPiece {Ω : Obls} {k : Oid} {p : Parent} {π : Fuel}
    (h : ∀ q, p = .obl q → Ω.fuelOf q < π) :
    OSat.fuel k π ⊢@{IProp GF} forestPiece Ω k p := by
  cases p with
  | thread j =>
    iintro -
    ipureintro
    trivial
  | obl q =>
    iintro Hf
    iexists π
    iframe Hf
    ipureintro
    exact h q rfl

end Helpers

/-! ## Round templates -/

section Rounds

variable [ModelGS GF]

/-- A round that may change the obligations without discharge, keeping their domain, on the
forest at any thread count (Rocq `mupd_model_round`): the witnesses chosen by the environment are
then below the old ones. -/
@[lantana_alias omodel.mupd_model_round]
theorem mupd_model_round (n : Nat) (P : IProp GF) :
    (∀ (Ω : Obls) (tc : Nat) (X : ThreadId → Prop), osat Ω ∗ oforest Ω tc X ==∗ ∃ Ω' : Obls,
        ⌜Obls.ndf Ω Ω' ∧ ∀ x, (get? Ω' x).isSome ↔ (get? Ω x).isSome⌝ ∗
        osat Ω' ∗ oforest Ω' tc X ∗ P) ⊢ mupd n P := by
  iintro H
  iapply mupd_nd_step
  iintro %h %i %Ω₁ %W₁ %tc %X HM
  unfold modelInterp
  icases HM with ⟨HH, Hs, Hf, Hw, %hI₁⟩
  imod H $$ %Ω₁ %tc %X [$Hs $Hf] with ⟨%Ω₂, %⟨hnd, hdom⟩, Hs, Hf, HP⟩
  imod modelHistoryInterp_step h i (Nat.le_refl n) hnd.lef.le $$ HH with HH
  imodintro
  iexists Ω₂
  isplitr
  · ipureintro
    exact hnd
  iintro %W₂ %⟨hW, hI₂⟩
  have hmono : W₁.mono W₂ := hW.mono fun k hk =>
    (hI₁.dom k).1 ((hdom k).1 ((hI₂.dom k).2 hk))
  imodintro
  iframe HH Hs Hf
  isplitl [Hw]
  · isplitl [Hw]
    · iapply owit_mon hmono $$ Hw
    · ipureintro
      exact hI₂
  · iapply mupd_intro
    iexact HP

/-- A round that changes only ghost state, on the forest at any thread count (Rocq
`mupd_ghost_round`). -/
@[lantana_alias omodel.mupd_ghost_round]
theorem mupd_ghost_round (n : Nat) (P : IProp GF) :
    (∀ (Ω : Obls) (tc : Nat) (X : ThreadId → Prop),
        osat Ω ∗ oforest Ω tc X ==∗ osat Ω ∗ oforest Ω tc X ∗ P) ⊢
      mupd n P := by
  iintro H
  iapply mupd_model_round
  iintro %Ω %tc %X HΩ
  imod H $$ %Ω %tc %X HΩ with ⟨Hs, Hf, HP⟩
  imodintro
  iexists Ω
  iframe Hs Hf HP
  ipureintro
  exact ⟨Obls.ndf_refl Ω, fun _ => Iff.rfl⟩

private theorem mupd_mono_of {n : Nat} {P Q : IProp GF} (h : P ⊢ Q) :
    mupd n P ⊢ mupd n Q := by
  iintro H
  iapply mupd_bind n P Q $$ [] H
  iintro HP
  iapply mupd_intro
  iapply h $$ HP

end Rounds

/-! ## The forest operations as model updates -/

section Operations

variable [ModelGS GF]

/-- A running thread without children terminates (Rocq `thread_terminate_mupd`). -/
@[lantana_alias omodel.thread_terminate_mupd]
theorem thread_terminate_mupd (n : Nat) (i : ThreadId) :
    thActive (GF := GF) i ⊢ parKids (.thread i) ∅ -∗ mupd n (thDone i) := by
  unfold thActive parKids thDone
  iintro He ⟨-, Hk, -⟩
  iapply mupd_ghost_round
  iintro %Ω %tc %X ⟨Hs, Hf⟩
  imod oforest_exec_to_done Ω tc i $$ [$Hf $He $Hk] with ⟨Hf, Hd⟩
  imodintro
  iframe Hs Hf Hd

/-- The owner `t` of a new obligation below `p`, and its piece `ν` at layer `ℓ`: below an
obligation `q` with a witness at layer `ℓq ≤ ℓ`, above the fuel of `q` (`layer_le_bound`). -/
theorem parLe_owner (Ω : Obls) (tc : Nat) (X : ThreadId → Prop) (p : Parent) (K : Oids)
    (ℓ : Layer) :
    oforest Ω tc X ∗ OForest.kids p K ∗ parLe p ℓ ⊢@{IProp GF}
      ⌜∃ (t : ThreadId) (ν : Measure), match p with
        | .thread j => j = t
        | .obl q => Ω.ownerOf q = some t ∧ Ω.fuelOf q < Measure.rep ℓ ν⌝ := by
  cases p with
  | thread j =>
    iintro -
    ipureintro
    exact ⟨j, ▽, rfl⟩
  | obl q =>
    iintro ⟨Hf, Hk, %ℓq, %hℓ, #Hw⟩
    icases witLayer_bound q ℓq $$ Hw with ⟨%μq, #Hb⟩
    icases oforest_obl_fuel_bound Ω tc q K _ $$ [$Hf $Hk $Hb] with %⟨hle, hlive⟩
    obtain ⟨t, ht⟩ := Obls.ownerOf_of_live hlive
    ipureintro
    exact ⟨t, μq + 1, ht, Ordinal.lt_of_le_of_lt hle (Measure.layer_le_bound μq hℓ)⟩

/-- The owner `j` of `p`: below an obligation `q` with a witness at a layer `ℓq < ℓ`, the fuel
of `q` is below `▽` at `ℓ` (`layer_dominates`). -/
theorem parBelow_owner (Ω : Obls) (tc : Nat) (X : ThreadId → Prop) (p : Parent) (K : Oids)
    (ℓ : Layer) :
    oforest Ω tc X ∗ OForest.kids p K ∗ parBelow p ℓ ⊢@{IProp GF}
      ⌜∃ j : ThreadId, match p with
        | .thread j' => j' = j
        | .obl q => Ω.ownerOf q = some j ∧ Ω.fuelOf q < Measure.rep ℓ ▽⌝ := by
  cases p with
  | thread j =>
    iintro -
    ipureintro
    exact ⟨j, rfl⟩
  | obl q =>
    iintro ⟨Hf, Hk, %ℓq, %hℓ, #Hw⟩
    icases witLayer_bound q ℓq $$ Hw with ⟨%μq, #Hb⟩
    icases oforest_obl_fuel_bound Ω tc q K _ $$ [$Hf $Hk $Hb] with %⟨hle, hlive⟩
    obtain ⟨t, ht⟩ := Obls.ownerOf_of_live hlive
    ipureintro
    exact ⟨t, ht, Ordinal.lt_of_le_of_lt hle (Measure.layer_dominates μq hℓ)⟩

/-- The witness bound of a new obligation keeps the witnesses chosen by the environment below the
old ones. -/
private theorem wits_mono_new {Ω₁ : Obls} {W₁ W₂ : Witnesses} {k : Oid} {g : Obl}
    (hI₁ : owitInvFair Ω₁ W₁) (hW : W₁.ndf W₂) (hI₂ : owitInvFair (insert Ω₁ k g) W₂) :
    Witnesses.mono (insert W₁ k (match g with
      | .assigned a _ => .assigned (fairMeasureUb a)
      | .discharged => .discharged)) W₂ :=
  wits_ndf_insert_mono hI₁ hW hI₂ fun w₂ hw₂ => by
    have hr := mapForall2.lookup hI₂ (get?_insert_eq rfl) hw₂
    cases g <;> cases w₂ <;> simp_all [owitRel, Witness.ndLe]

private theorem get?_none_wits {Ω : Obls} {W : Witnesses} {k : Oid} (hI : owitInvFair Ω W)
    (hk : get? Ω k = none) : get? W k = none := by
  have h := hI.dom k
  rw [hk] at h
  cases e : get? W k
  · rfl
  · simp [e] at h

/-- A new live obligation below `p`, added to the bill of `p` (Rocq `obl_new_mupd`): its owner is
the owner of `p`, its model fuel is the user's fuel, an extra `▽` and its piece above the fuel of
the parent. -/
@[lantana_alias omodel.obl_new_mupd]
theorem obl_new_mupd (n : Nat) (p : Parent) (K B : Oids) (ℓ : Layer) (μ : Measure) :
    parLe (GF := GF) p ℓ ⊢ parKids p K -∗ OForest.parBill p B -∗
      mupd n iprop(∃ k : Oid, ⌜k ∉ K⌝ ∗ parKids p (K.insert k) ∗
        OForest.parBill p (B.insert k) ∗ parKids (.obl k) ∅ ∗ oblAssigned k 1 ∗ oblFuel k ℓ μ ∗
        witLayer k ℓ) := by
  unfold parKids
  iintro Hb ⟨Hx, Hk, Hs⟩ HB
  iapply mupd_nd_step
  iintro %h %i %Ω₁ %W₁ %tc %X HM
  unfold modelInterp
  icases HM with ⟨HH, Hos, Hf, Hw, %hI₁⟩
  icases parLe_owner Ω₁ tc X p K ℓ $$ [$Hf $Hk $Hb] with %⟨t, ν, hpt⟩
  have hk := Obls.get?_fresh Ω₁
  have hkW := get?_none_wits hI₁ hk
  have hpiece : ∀ q, p = .obl q → Ω₁.fuelOf q < Measure.rep ℓ ν := by
    rintro q rfl
    exact hpt.2
  have hpa : match (generalizing := false) p with
      | .thread j => j = t
      | .obl q => Ω₁.ownerOf q = some t ∧
        Ω₁.fuelOf q < modelFuel ℓ μ +ₕ Measure.rep ℓ ▽ +ₕ Measure.rep ℓ ν := by
    cases p with
    | thread j => exact hpt
    | obl q => exact ⟨hpt.1, Ordinal.lt_of_lt_of_le hpt.2 (le_nadd_self _ _)⟩
  have hrep : Measure.rep ℓ ((1 + ▽) * μ + ▽ + ν) =
      modelFuel ℓ μ +ₕ Measure.rep ℓ ▽ +ₕ Measure.rep ℓ ν := by
    rw [Measure.rep_add, Measure.rep_add]
    rfl
  imod osat_alloc_obl_assigned hk (modelFuel ℓ μ +ₕ Measure.rep ℓ ▽ +ₕ Measure.rep ℓ ν) t
    $$ Hos with ⟨Hos, #Hβ, #He, Ha, Hfu, -⟩
  icases (OSat.fuel_split Ω₁.fresh _ _).mp $$ Hfu with ⟨Hfu, Hπ⟩
  icases (OSat.fuel_split Ω₁.fresh _ _).mp $$ Hfu with ⟨Hfu, -⟩
  ihave Hπ := fuel_forestPiece hpiece $$ Hπ
  imod oforest_alloc_obl hk hpa Ordinal.le_rfl B $$ [$Hf $Hk $HB $Hβ $Hπ]
    with ⟨Hf, %hkK, Hk, HB, Hkk⟩
  imod owit_alloc_witness_assigned hkW
    (fairMeasureUb (modelFuel ℓ μ +ₕ Measure.rep ℓ ▽ +ₕ Measure.rep ℓ ν)) $$ Hw with ⟨Hw, #Hwb⟩
  have hnd := Obls.ndf_insert_fresh (.assigned
    (modelFuel ℓ μ +ₕ Measure.rep ℓ ▽ +ₕ Measure.rep ℓ ν) t) hk
  imod modelHistoryInterp_step h i (Nat.le_refl n) hnd.lef.le $$ HH with HH
  icases (oblAssigned_shares Ω₁.fresh).mp $$ [$He $Ha] with ⟨Ha, Hsh₁, Hsh₂⟩
  imodintro
  iexists _
  isplitr
  · ipureintro
    exact hnd
  iintro %W₂ %⟨hW, hI₂⟩
  imodintro
  iframe HH Hos Hf
  isplitl [Hw]
  · isplitl [Hw]
    · iapply owit_mon (wits_mono_new hI₁ hW hI₂) $$ Hw
    · ipureintro
      exact hI₂
  iapply mupd_intro
  iexists Ω₁.fresh
  isplitr
  · ipureintro
    exact hkK
  isplitl [Hx Hk Hs Hsh₁]
  · iframe Hx
    isplitl [Hk]
    · rw [oids_insert_eq]
      iexact Hk
    · iapply (bigSepS_oids_insert hkK).mpr
      iframe Hsh₁ Hs
  isplitl [HB]
  · rw [oids_insert_eq]
    iexact HB
  isplitl [Hkk Hsh₂]
  · iframe Hsh₂ Hkk
    iapply BigSepS.bigSepS_empty.mpr
    iempintro
  iframe Ha
  unfold oblFuel oblFuelVal witLayer witBoundVal
  isplitl [Hfu]
  · iframe Hfu
    iexact He
  isplitl []
  · iexists (1 + ▽) * μ + ▽ + ν
    rw [hrep]
    isplitl []
    · iexact He
    · iexact Hwb
  · iexists (1 + ▽) * μ + ▽ + ν
    rw [hrep]
    iexact Hβ

/-- A new discharged obligation (Rocq `obl_new_discharged_mupd`): it is outside the forest. -/
@[lantana_alias omodel.obl_new_discharged_mupd]
theorem obl_new_discharged_mupd (n : Nat) (ℓ : Layer) :
    ⊢@{IProp GF} mupd n iprop(∃ k : Oid, oblDischarged k ∗ witLayer k ℓ) := by
  iapply mupd_nd_step
  iintro %h %i %Ω₁ %W₁ %tc %X HM
  unfold modelInterp
  icases HM with ⟨HH, Hos, Hf, Hw, %hI₁⟩
  have hk := Obls.get?_fresh Ω₁
  have hkW := get?_none_wits hI₁ hk
  imod osat_alloc_obl_discharged hk (Measure.rep ℓ 1) $$ Hos with ⟨Hos, #Hβ, #He, #Hd, -, -⟩
  imod owit_alloc_witness_discharged hkW (fairMeasureUb (Measure.rep ℓ 1)) $$ [$Hw $Hd]
    with ⟨Hw, #Hwb⟩
  ihave Hf := oforest_alloc_discharged hk $$ Hf
  have hnd := Obls.ndf_insert_fresh .discharged hk
  imod modelHistoryInterp_step h i (Nat.le_refl n) hnd.lef.le $$ HH with HH
  imodintro
  iexists _
  isplitr
  · ipureintro
    exact hnd
  iintro %W₂ %⟨hW, hI₂⟩
  imodintro
  iframe HH Hos Hf
  isplitl [Hw]
  · isplitl [Hw]
    · iapply owit_mon (wits_mono_new hI₁ hW hI₂) $$ Hw
    · ipureintro
      exact hI₂
  iapply mupd_intro
  iexists Ω₁.fresh
  unfold oblDischarged witLayer witBoundVal
  isplitl []
  · isplitl []
    · iexact He
    · iexact Hd
  isplitl []
  · iexists 1
    isplitl []
    · iexact He
    · iexact Hwb
  · iexists 1
    iexact Hβ

/-- A move of the node `k` from `p₁` to `p₂`, with the unit `u` that `k` burns if its owner
changes and the piece `π` above the fuel of `p₂` (Rocq: the two cases of `obl_move_mupd`, with
`oforest_move_same` and `oforest_move_cross`). -/
theorem oforest_move {Ω : Obls} {tc : Nat} {X : ThreadId → Prop} {p₁ p₂ : Parent}
    {K₁ K₂ B₂ : Oids} {k : Oid} {j : ThreadId} {u π : Fuel} (hk : k ∈ K₁) (hu : 0 < u)
    (hp₂ : match p₂ with
      | .thread j' => j' = j
      | .obl q => Ω.ownerOf q = some j ∧ Ω.fuelOf q < π) :
    osat Ω ∗ oforest Ω tc X ∗ OForest.kids p₁ K₁ ∗ OForest.kids p₂ K₂ ∗
        OForest.parBill p₂ B₂ ∗ OSat.fuel k u ∗ OSat.fuel k π
      ⊢@{IProp GF} |==> ∃ Ω', ⌜Obls.ndf Ω Ω' ∧ (∀ x, (get? Ω' x).isSome ↔ (get? Ω x).isSome) ∧
        k ∉ K₂⌝ ∗ osat Ω' ∗ oforest Ω' tc X ∗ OForest.kids p₁ (K₁ \ {k}) ∗
        OForest.kids p₂ ({k} ∪ K₂) ∗ OForest.parBill p₂ ({k} ∪ B₂) := by
  iintro ⟨Hs, Hf, H₁, H₂, HB, Hu, Hπ⟩
  icases oforest_kids_live Ω tc p₁ K₁ $$ [$Hf $H₁] with %⟨hlive, -⟩
  obtain ⟨t, ht⟩ := Obls.ownerOf_of_live (hlive k hk)
  obtain ⟨a, ha⟩ := Obls.ownerOf_eq_some.1 ht
  have hpiece : ∀ q, p₂ = .obl q → Ω.fuelOf q < π := by
    rintro q rfl
    exact hp₂.2
  by_cases htj : t = j
  · subst htj
    icases osat_fuel_le Ω k π $$ [$Hs $Hπ] with %hle
    have hπk : π ≤ Ω.fuelOf k := by
      rw [Obls.fuelOf_eq ha]
      exact hle a t ha
    have hp₂' : match (generalizing := false) p₂ with
        | .thread j => Ω.ownerOf k = some j
        | .obl q => Ω.ownerOf q = Ω.ownerOf k ∧ Ω.fuelOf q < Ω.fuelOf k := by
      cases p₂ with
      | thread j' => exact hp₂ ▸ ht
      | obl q => exact ⟨hp₂.1.trans ht.symm, Ordinal.lt_of_lt_of_le hp₂.2 hπk⟩
    ihave Hπ := fuel_forestPiece hpiece $$ Hπ
    imod oforest_move_same hk hp₂' B₂ $$ [$Hf $H₁ $H₂ $HB $Hπ] with ⟨%hkK, Hf, H₁, H₂, HB⟩
    imodintro
    iexists Ω
    iframe Hs Hf H₁ H₂ HB
    ipureintro
    exact ⟨Obls.ndf_refl Ω, fun _ => Iff.rfl, hkK⟩
  · have hp₂' : match (generalizing := false) p₂ with
        | .thread j' => j' = j
        | .obl q => Ω.ownerOf q = some j := by
      cases p₂ with
      | thread j' => exact hp₂
      | obl q => exact hp₂.1
    ihave Hπ := fuel_forestPiece hpiece $$ Hπ
    imod oforest_move_cross hk ht htj hu hp₂' B₂ $$ [$Hs $Hf $H₁ $H₂ $HB $Hu $Hπ]
      with ⟨%Ω', %hΩ', Hs, Hf, H₁, H₂, HB⟩
    imodintro
    iexists Ω'
    iframe Hs Hf H₁ H₂ HB
    ipureintro
    exact hΩ'

/-- The obligation `k` moves with its subtree from `p₁` to `p₂`, added to the bill of `p₂`,
burning one unit at a layer that dominates `p₂` (Rocq `obl_move_mupd`): the unit splits into `1`,
burnt by `k` if its owner changes, and `▽`, its new piece below an obligation. -/
@[lantana_alias omodel.obl_move_mupd]
theorem obl_move_mupd (n : Nat) (p₁ p₂ : Parent) (K₁ K₂ B₂ : Oids) (k : Oid) (ℓ : Layer)
    (hk : k ∈ K₁) :
    parBelow (GF := GF) p₂ ℓ ⊢ parKids p₁ K₁ -∗ parKids p₂ K₂ -∗ OForest.parBill p₂ B₂ -∗
      oblFuel k ℓ 1 -∗
      mupd n iprop(⌜k ∉ K₂⌝ ∗ parKids p₁ (K₁.erase k) ∗ parKids p₂ (K₂.insert k) ∗
        OForest.parBill p₂ (B₂.insert k)) := by
  unfold parKids oblFuel oblFuelVal
  rw [modelFuel_one]
  iintro Hb ⟨Hx₁, Hk₁, Hs₁⟩ ⟨Hx₂, Hk₂, Hs₂⟩ HB ⟨-, Hfk⟩
  icases (bigSepS_oids_erase hk).mp $$ Hs₁ with ⟨Hsk, Hs₁⟩
  icases (OSat.fuel_split k _ _).mp $$ Hfk with ⟨Hu, Hπ⟩
  iapply mupd_model_round
  iintro %Ω %tc %X ⟨Hs, Hf⟩
  icases parBelow_owner Ω tc X p₂ K₂ ℓ $$ [$Hf $Hk₂ $Hb] with %⟨j, hj⟩
  imod oforest_move hk zero_lt_one hj $$ [$Hs $Hf $Hk₁ $Hk₂ $HB $Hu $Hπ]
    with ⟨%Ω', %⟨hnd, hdom, hkK⟩, Hs, Hf, Hk₁, Hk₂, HB⟩
  imodintro
  iexists Ω'
  isplitr
  · ipureintro
    exact ⟨hnd, hdom⟩
  iframe Hs Hf
  isplitr
  · ipureintro
    exact hkK
  isplitl [Hx₁ Hk₁ Hs₁]
  · iframe Hx₁ Hs₁
    rw [oids_erase_eq]
    iexact Hk₁
  isplitl [Hx₂ Hk₂ Hs₂ Hsk]
  · iframe Hx₂
    isplitl [Hk₂]
    · rw [oids_insert_eq]
      iexact Hk₂
    · iapply (bigSepS_oids_insert hkK).mpr
      iframe Hsk Hs₂
  · rw [oids_insert_eq]
    iexact HB

/-- A grandchild `x`, child of `k`, moves up to the parent `p` of `k`, added to the bill of `p`
(Rocq `obl_move_up_mupd`): a ghost round. -/
@[lantana_alias omodel.obl_move_up_mupd]
theorem obl_move_up_mupd (n : Nat) (p : Parent) (K B : Oids) (k : Oid) (Kk : Oids) (x : Oid)
    (hk : k ∈ K) (hx : x ∈ Kk) :
    parKids (GF := GF) p K ⊢ OForest.parBill p B -∗ parKids (.obl k) Kk -∗
      mupd n iprop(⌜x ∉ K⌝ ∗ parKids p (K.insert x) ∗ OForest.parBill p (B.insert x) ∗
        parKids (.obl k) (Kk.erase x)) := by
  unfold parKids
  iintro ⟨Hx, Hp, Hs⟩ HB ⟨Hxk, Hk, Hsk⟩
  icases (bigSepS_oids_erase hx).mp $$ Hsk with ⟨Hsx, Hsk⟩
  iapply mupd_ghost_round
  iintro %Ω %tc %X ⟨Hos, Hf⟩
  imod oforest_move_up hk hx B $$ [$Hf $Hp $HB $Hk] with ⟨%hxK, Hf, Hp, HB, Hk⟩
  imodintro
  iframe Hos Hf
  isplitr
  · ipureintro
    exact hxK
  isplitl [Hx Hp Hs Hsx]
  · iframe Hx
    isplitl [Hp]
    · rw [oids_insert_eq]
      iexact Hp
    · iapply (bigSepS_oids_insert hxK).mpr
      iframe Hsx Hs
  isplitl [HB]
  · rw [oids_insert_eq]
    iexact HB
  · iframe Hxk Hsk
    rw [oids_erase_eq]
    iexact Hk

/-! ### Bills -/

/-- The bill of thread `i` contains its children. -/
theorem bill_kids_subset_mupd (n : Nat) (i : ThreadId) (B K : Oids) :
    OForest.bill (GF := GF) i B ⊢ parKids (.thread i) K -∗
      mupd n iprop(⌜K ⊆ B⌝ ∗ OForest.bill i B ∗ parKids (.thread i) K) := by
  unfold parKids
  iintro Hb ⟨Hx, Hk, Hs⟩
  iapply mupd_ghost_round
  iintro %Ω %tc %X ⟨Hos, Hf⟩
  icases oforest_bill_kids Ω tc i B K $$ [$Hf $Hb $Hk] with %h
  imodintro
  iframe Hos Hf Hb Hx Hk Hs
  ipureintro
  exact h

/-- The bill of thread `i` becomes its children. -/
theorem bill_resync_mupd (n : Nat) (i : ThreadId) (B K : Oids) :
    OForest.bill (GF := GF) i B ⊢ parKids (.thread i) K -∗
      mupd n iprop(OForest.bill i K ∗ parKids (.thread i) K) := by
  unfold parKids
  iintro Hb ⟨Hx, Hk, Hs⟩
  iapply mupd_ghost_round
  iintro %Ω %tc %X ⟨Hos, Hf⟩
  imod oforest_bill_resync Ω tc i B K $$ [$Hf $Hb $Hk] with ⟨Hf, Hb, Hk⟩
  imodintro
  iframe Hos Hf Hb Hx Hk Hs

/-- A discharged obligation leaves the bill of thread `i`. -/
theorem bill_erase_discharged_mupd (n : Nat) (i : ThreadId) (B : Oids) (k : Oid) :
    OForest.bill (GF := GF) i B ⊢ oblDischarged k -∗
      mupd n iprop(OForest.bill i (B.erase k)) := by
  unfold oblDischarged
  iintro Hb ⟨-, Hd⟩
  iapply mupd_ghost_round
  iintro %Ω %tc %X ⟨Hos, Hf⟩
  icases osat_lookup_discharged Ω k $$ [$Hos $Hd] with %hk
  have hlive : ¬Ω.live k := fun ⟨_, _, h⟩ => by
    rw [hk] at h
    cases h
  imod oforest_bill_erase hlive i B $$ [$Hf $Hb] with ⟨Hf, Hb⟩
  imodintro
  iframe Hos Hf
  rw [oids_erase_eq]
  iexact Hb


/-- An element of `R` with its witness credits or its discharge. -/
private theorem witLayer_cred_or (r : Oid) (a : Fuel) :
    (∃ ℓ, witLayer (GF := GF) r ℓ) ∗ (OWit.cred r a ∨ OSat.discharged r) ⊢
      witCred r a ∨ oblDischarged r := by
  unfold witCred oblDischarged
  iintro ⟨⟨%ℓ, Hw⟩, Hc⟩
  ihave #He := witLayer_elem r ℓ $$ Hw
  icases Hc with (Hc | Hd)
  · ileft
    iframe Hc
    iexact He
  · iright
    iframe Hd
    iexact He

private theorem witLayers_creds (R : Oids) (a : Fuel) :
    ([∗set] r ∈ R, ∃ ℓ, witLayer (GF := GF) r ℓ) ∗
        ([∗set] r ∈ R, OWit.cred r a ∨ OSat.discharged r) ⊢
      [∗set] r ∈ R, witCred r a ∨ oblDischarged r :=
  BigSepS.bigSepS_sep.mpr.trans (BigSepS.bigSepS_mono_of_forall fun r => witLayer_cred_or r a)

/-- The witnesses of `R` get zero credits or are discharged (Rocq `obl_check_witnesses_mupd`). -/
@[lantana_alias omodel.obl_check_witnesses_mupd]
theorem obl_check_witnesses_mupd (n : Nat) (R : Oids) :
    ([∗set] r ∈ R, ∃ ℓ, witLayer (GF := GF) r ℓ) ⊢
      mupd n iprop([∗set] r ∈ R, witCred r 0 ∨ oblDischarged r) := by
  iintro #HR
  iapply mupd_nd_step
  iintro %h %i %Ω₁ %W₁ %tc %X HM
  unfold modelInterp
  icases HM with ⟨HH, Hos, Hf, Hw, %hI₁⟩
  icases osat_elems Ω₁ R $$ [$Hos $HR] with %hR
  icases owit_get_credit_zero W₁ $$ Hw with ⟨Hw, Hc⟩
  have hpt : ∀ k w, get? W₁ k = some w → k ∈ R →
      OWit.witCreditZero k w ⊢@{IProp GF} OWit.cred k 0 ∨ OSat.discharged k := by
    intro k w _ _
    cases w with
    | assigned b => exact BI.or_intro_l
    | discharged => exact BI.or_intro_r
  ihave Hc := bigSepM_restrict W₁ R (fun r hr => (hI₁.dom r).1 (hR r hr)) hpt $$ Hc
  imod modelHistoryInterp_step h i (Nat.le_refl n) (Obls.le_refl Ω₁) $$ HH with HH
  imodintro
  iexists Ω₁
  isplitr
  · ipureintro
    exact Obls.ndf_refl Ω₁
  iintro %W₂ %⟨hW, hI₂⟩
  imodintro
  iframe HH Hos Hf
  isplitl [Hw]
  · isplitl [Hw]
    · iapply owit_mon (wits_lef_same_mono hI₁ hW.lef hI₂) $$ Hw
    · ipureintro
      exact hI₂
  iapply mupd_intro
  iapply witLayers_creds R 0
  isplitr [Hc]
  · iexact HR
  · iexact Hc

/-- The witness `r` gets zero credits or is discharged (Rocq `obl_check_witnesses_mupd` for one
witness). -/
theorem obl_check_witness_mupd (n : Nat) (r : Oid) (ℓ : Layer) :
    witLayer (GF := GF) r ℓ ⊢ mupd n iprop(witCred r 0 ∨ oblDischarged r) := by
  have h₁ : ([∗set] x ∈ ({r} : Oids), witCred (GF := GF) x 0 ∨ oblDischarged x) ⊢
      witCred r 0 ∨ oblDischarged r :=
    (BigSepS.bigSepS_singleton (Φ := fun x => iprop(witCred (GF := GF) x 0 ∨ oblDischarged x))).mp
  have h₂ : witLayer (GF := GF) r ℓ ⊢ [∗set] x ∈ ({r} : Oids), ∃ ℓ, witLayer x ℓ :=
    (BI.exists_intro (Ψ := fun ℓ => witLayer (GF := GF) r ℓ) ℓ).trans
      (BigSepS.bigSepS_singleton (Φ := fun x => iprop(∃ ℓ, witLayer (GF := GF) x ℓ))).mpr
  exact h₂.trans ((obl_check_witnesses_mupd n {r}).trans (mupd_mono_of h₁))

/-- Discharge of a leaf `k` below `p` (Rocq `obl_discharge_mupd`): the round with `Obls.lef`,
through `mupd_unfold`. The children predicates of `p` and `k` give the two children shares of
`k`, with the user's half the full assignment. -/
@[lantana_alias omodel.obl_discharge_mupd]
theorem obl_discharge_mupd (n : Nat) (p : Parent) (K : Oids) (k : Oid) (hk : k ∈ K) :
    parKids (GF := GF) p K ⊢ parKids (.obl k) ∅ -∗ oblAssigned k 1 -∗
      mupd n iprop(parKids p (K.erase k) ∗ oblDischarged k) := by
  unfold parKids
  iintro ⟨Hx, Hp, Hs⟩ ⟨Hsh₁, Hkk, -⟩ Ha
  icases (bigSepS_oids_erase hk).mp $$ Hs with ⟨Hsh₂, Hs⟩
  icases (oblAssigned_shares k).mpr $$ [$Ha $Hsh₁ $Hsh₂] with ⟨#He, Ha⟩
  iapply (mupd_unfold n _).2
  unfold mupdPre
  iright
  iintro %h %i %Ω₁ %W₁ %tc %X HM
  unfold modelInterp
  icases HM with ⟨HH, Hos, Hf, Hw, %hI₁⟩
  imod osat_discharge Ω₁ k $$ [$Hos $Ha] with ⟨Hos, #Hd, %⟨a, t, hk₁⟩⟩
  imod oforest_discharge_obl hk $$ [$Hf $Hp $Hkk] with ⟨Hf, Hp⟩
  obtain ⟨w, hw, hr⟩ := mapForall2.lookup_left hI₁ hk₁
  obtain ⟨b, rfl⟩ : ∃ b, w = .assigned b := by
    cases w with
    | assigned b => exact ⟨b, rfl⟩
    | discharged => simp [owitRel] at hr
  ihave Hw := owit_discharge hw $$ [$Hw $Hd]
  have hlef := Obls.lef_insert_step (g₂ := .discharged) hk₁ (.inr trivial)
  imod modelHistoryInterp_step h i (Nat.le_refl n) hlef.le $$ HH with HH
  imodintro
  iexists _
  isplitr
  · ipureintro
    exact hlef
  iintro %W₂ %⟨hW, hI₂⟩
  imodintro
  iframe HH Hos Hf
  isplitl [Hw]
  · isplitl [Hw]
    · iapply owit_mon (wits_lef_discharge_mono hI₁ hW hI₂) $$ Hw
    · ipureintro
      exact hI₂
  iapply mupd_intro
  isplitl [Hx Hp Hs]
  · iframe Hx Hs
    rw [oids_erase_eq]
    iexact Hp
  · unfold oblDischarged
    isplitl []
    · iexact He
    · iexact Hd

/-- The fuel ranks the obligations of `S` whose children predicates are at hand: each child has
more fuel than its parent (`oforest_kids_obl`). -/
theorem oforest_kids_rank (Ω : Obls) (tc : Nat) (X : ThreadId → Prop) (S : Oids)
    (kids : Oid → Oids) :
    oforest Ω tc X ∗ ([∗set] k ∈ S, parKids (GF := GF) (.obl k) (kids k)) ⊢
      ⌜∀ k, k ∈ S → ∀ x, x ∈ kids k → Ω.fuelOf k < Ω.fuelOf x⌝ := by
  refine (BI.forall_intro fun k => ?_).trans BI.pure_forall.2
  by_cases hk : k ∈ S
  · refine (?_ : _ ⊢ ⌜∀ x, x ∈ kids k → Ω.fuelOf k < Ω.fuelOf x⌝).trans
      (BI.pure_mono fun h _ => h)
    unfold parKids
    iintro ⟨Hf, HS⟩
    icases BigSepS.bigSepS_elem_of_acc hk $$ HS with ⟨⟨-, Hk, -⟩, -⟩
    icases oforest_kids_obl Ω tc k (kids k) $$ [$Hf $Hk] with %⟨-, h⟩
    ipureintro
    exact fun x hx => (h x hx).2
  · exact BI.pure_intro fun h => (hk h).elim

/-- A rank of the obligations of `S` whose children predicates are at hand, growing from parent
to child, read from the model by a ghost round: the fuel. -/
theorem kids_rank_mupd (n : Nat) (S : Oids) (kids : Oid → Oids) :
    ([∗set] k ∈ S, parKids (GF := GF) (.obl k) (kids k)) ⊢
      mupd n iprop(⌜∃ r : Oid → Fuel, ∀ k, k ∈ S → ∀ x, x ∈ kids k → r k < r x⌝ ∗
        [∗set] k ∈ S, parKids (.obl k) (kids k)) := by
  iintro HS
  iapply mupd_ghost_round
  iintro %Ω %tc %X ⟨Hos, Hf⟩
  icases oforest_kids_rank Ω tc X S kids $$ [$Hf $HS] with %h
  imodintro
  iframe Hos Hf HS
  ipureintro
  exact ⟨Ω.fuelOf, h⟩

/-- The node of a thread through the user's predicates: its running handle and its empty
children predicate. -/
theorem node_eq (j : ThreadId) :
    thActive (GF := GF) j ∗ parKids (.thread j) ∅ ⊣⊢ OForest.node j := by
  unfold thActive parKids
  constructor
  · iintro ⟨He, -, Hk, -⟩
    isplitl [He]
    · iexact He
    · iexact Hk
  · iintro ⟨He, Hk⟩
    iframe He Hk
    iapply BigSepS.bigSepS_empty.mpr
    iempintro

/-- New threads `tc, …, tc + m - 1`, running, with empty bills, and with their running handles
and children predicates if their bits are not set (Rocq `thP_kids_alloc_threads`). -/
@[lantana_alias omodel.thP_kids_alloc_threads]
theorem thKids_alloc_threads (Ω : Obls) (tc m : Nat) (X : ThreadId → Prop) :
    oforest Ω tc X ⊢@{IProp GF} |==> (oforest Ω (tc + m) X ∗
      [∗list] j ∈ List.range' tc m,
        (⌜¬X j⌝ -∗ thActive j ∗ parKids (.thread j) ∅) ∗ OForest.bill j ∅) := by
  iintro Hf
  imod oforest_alloc_threads Ω tc m $$ Hf with ⟨Hf, Hl⟩
  imodintro
  iframe Hf
  iapply BigSepL.bigSepL_mono_of_forall ?_ $$ Hl
  intro _ j
  exact sep_mono_left (wand_mono_right (node_eq j).2)

end Operations

/-! ## Physical steps -/

section Physical

variable [ModelGS GF]

/-- A step of thread `i` (Rocq `mprog_step_kids`): one unit of fuel of each obligation of the
bill of `i` makes every obligation of `i` progress (`oforest_osat_step`, keeping the owners),
every assigned witness gets a positive credit (`owit_progress`), weakened to one credit for the
witnesses of `R`. -/
@[lantana_alias omodel.mprog_step_kids]
theorem mprog_step_kids (n tc : Nat) (X : ThreadId → Prop) (i : ThreadId) (B R : Oids)
    (P : IProp GF) :
    OForest.bill i B ⊢ ([∗set] k ∈ B, ∃ ℓ, oblFuel k ℓ 1) -∗
      ([∗set] r ∈ R, ∃ ℓ, witLayer r ℓ) -∗
      (OForest.bill i B -∗ ([∗set] r ∈ R, witCred r 1 ∨ oblDischarged r) ={∅}=∗ P) -∗
      mprog n tc X i P := by
  unfold mprog
  iintro Hb HF #HR H %h %a %Ω₁ %W₁ HM
  unfold modelInterp
  icases HM with ⟨HH, Hos, Hf, Hw, %hI₁⟩
  icases osat_elems Ω₁ R $$ [$Hos $HR] with %hR
  ihave HF := BigSepS.bigSepS_mono_of_forall (fun k => oblFuel_pos (GF := GF) k) $$ HF
  imod oforest_osat_step Ω₁ tc i B $$ [$Hos $Hf $Hb $HF] with ⟨%Ω₂, %⟨hp, -⟩, Hos, Hf, Hb⟩
  imod modelHistoryInterp_step h a (Nat.le_refl n) (Obls.condProgress_le hp) $$ HH with HH
  imodintro
  iexists Ω₂
  isplitr
  · ipureintro
    exact hp
  iintro %W₂ %⟨hW, hI₂⟩
  imod owit_progress hW $$ Hw with ⟨Hw, Hc⟩
  have hpt : ∀ k w, get? W₁ k = some w → k ∈ R →
      OWit.witCredit k w ⊢@{IProp GF} |==> (OWit.cred k 1 ∨ OSat.discharged k) := by
    intro k w _ _
    cases w with
    | assigned b =>
      iintro ⟨%c, %hc, Hc⟩
      imod OWit.cred_mon (one_eq_succ_zero ▸ succ_le_of_lt hc) $$ Hc with Hc
      imodintro
      ileft
      iexact Hc
    | discharged =>
      iintro Hd
      imodintro
      iright
      iexact Hd
  ihave Hc := bigSepM_restrict W₁ R (fun r hr => (hI₁.dom r).1 (hR r hr)) hpt $$ Hc
  imod BigSepS.bigSepS_bupd _ R $$ Hc with Hc
  imod H $$ Hb [Hc] with HP
  · iapply witLayers_creds R 1
    isplitr [Hc]
    · iexact HR
    · iexact Hc
  imodintro
  iframe HH Hos Hf Hw HP
  ipureintro
  exact hI₂

/-- A step of a crashed thread `i` pays for nothing, whatever its bill: the bill is resynchronized
against the empty children that the invariant holds (`oforest_bill_crashed`), then the step is
`mprog_step_kids` with the empty bill. -/
theorem mprog_step_crashed (n tc : Nat) (X : ThreadId → Prop) {i : ThreadId} (hX : X i)
    (B R : Oids) (P : IProp GF) :
    OForest.bill i B ⊢ ([∗set] r ∈ R, ∃ ℓ, witLayer r ℓ) -∗
      (OForest.bill i ∅ -∗ ([∗set] r ∈ R, witCred r 1 ∨ oblDischarged r) ={∅}=∗ P) -∗
      mprog n tc X i P := by
  iintro Hb HR H
  unfold mprog
  iintro %h %a %Ω₁ %W₁ HM
  unfold modelInterp
  icases HM with ⟨HH, Hos, Hf, Hw, %hI₁⟩
  imod oforest_bill_crashed Ω₁ tc hX B $$ [$Hf $Hb] with ⟨Hf, Hb⟩
  ihave Hstep := mprog_step_kids n tc X i ∅ R P $$ Hb [] HR H
  · iapply BigSepS.bigSepS_empty.mpr
    iempintro
  unfold mprog modelInterp
  iapply Hstep $$ %h %a %Ω₁ %W₁ [HH Hos Hf Hw]
  iframe HH Hos Hf Hw
  ipureintro
  exact hI₁

/-- The forked threads, not crashed, get their nodes. -/
private theorem forked_pieces {tc₁ m : Nat} {X : ThreadId → Prop} (hX : ∀ j, tc₁ ≤ j → ¬X j) :
    ([∗list] j ∈ List.range' tc₁ m,
        (⌜¬X j⌝ -∗ thActive j ∗ parKids (.thread j) ∅) ∗ OForest.bill j ∅) ⊢@{IProp GF}
      [∗list] j ∈ List.range' tc₁ m, thActive j ∗ parKids (.thread j) ∅ ∗ OForest.bill j ∅ :=
  BigSepL.bigSepL_mono fun {_ j} hj => by
    have hle := (List.mem_range'_1.1 (List.mem_of_getElem? hj)).1
    iintro ⟨Hn, Hb⟩
    icases Hn $$ %(hX j hle) with ⟨He, Hk⟩
    iframe He Hk Hb

/-- The first stage of the physical round: the step index and the thread count change at the
bits `X₁`, and the forked threads `tc₁, …, tc₂ - 1`, not crashed, get their running handles,
empty children predicates and empty bills. -/
theorem mphys_forks {n₁ n₂ tc₁ tc₂ : Nat} {X₁ X₂ : ThreadId → Prop} {P : IProp GF}
    (hn : n₁ ≤ n₂) (htc : tc₁ ≤ tc₂) (hX₁ : ∀ j, tc₁ ≤ j → ¬X₁ j) :
    (([∗list] j ∈ List.range' tc₁ (tc₂ - tc₁),
        thActive j ∗ parKids (.thread j) ∅ ∗ OForest.bill j ∅) ={∅}=∗
      ALC (mupd n₂ (mbits n₂ tc₂ X₁ X₂ P))) ⊢ mphys n₁ n₂ tc₁ tc₂ X₁ X₂ P := by
  unfold mphys
  iintro H %h %a %Ω %W HM
  unfold modelInterp
  icases HM with ⟨HH, Hos, Hf, Hw, %hI⟩
  imod modelHistoryInterp_step h a hn (Obls.le_refl Ω) $$ HH with HH
  imod thKids_alloc_threads Ω tc₁ (tc₂ - tc₁) X₁ $$ Hf with ⟨Hf, Hl⟩
  rw [show tc₁ + (tc₂ - tc₁) = tc₂ by omega]
  ihave Hl := forked_pieces hX₁ $$ Hl
  imod H $$ Hl with HP
  imodintro
  iframe HH Hos Hf Hw HP
  ipureintro
  exact hI

/-- The last stage of the physical round: the nodes of the newly crashed threads go in, the nodes
of the recovered ones come out (`oforest_bits`). -/
theorem mbits_kids (n tc : Nat) (X₁ X₂ : ThreadId → Prop) (P : IProp GF) :
    ([∗list] j ∈ List.range tc, ⌜¬X₁ j ∧ X₂ j⌝ -∗ thActive j ∗ parKids (.thread j) ∅) ∗
        (([∗list] j ∈ List.range tc, ⌜X₁ j ∧ ¬X₂ j⌝ -∗ thActive j ∗ parKids (.thread j) ∅)
          -∗ P)
      ⊢@{IProp GF} mbits n tc X₁ X₂ P := by
  unfold mbits
  iintro ⟨Hin, HP⟩ %h %a %Ω %W HM
  unfold modelInterp
  icases HM with ⟨HH, Hos, Hf, Hw, %hI⟩
  ihave Hin := BigSepL.bigSepL_mono_of_forall
    (fun {_ j} => wand_mono_right (node_eq (GF := GF) j).1) $$ Hin
  icases oforest_bits Ω tc X₁ X₂ $$ [$Hf $Hin] with ⟨Hf, Hout⟩
  ihave Hout := BigSepL.bigSepL_mono_of_forall
    (fun {_ j} => wand_mono_right (node_eq (GF := GF) j).2) $$ Hout
  imodintro
  iframe HH Hos Hf Hw
  isplitr [HP Hout]
  · ipureintro
    exact hI
  · iapply HP $$ Hout

/-- A step that forks the threads `tc₁, …, tc₂ - 1` and changes the bits from `X₁` to `X₂`
(Rocq `mphys_step_kids`, with the bits): the forked threads get their pieces; after the model
update at `n₂`, the nodes of the newly crashed threads go in and the nodes of the recovered ones
come out. -/
@[lantana_alias omodel.mphys_step_kids]
theorem mphys_step_kids (n₁ n₂ tc₁ tc₂ : Nat) (X₁ X₂ : ThreadId → Prop) (P : IProp GF)
    (hn : n₁ ≤ n₂) (htc : tc₁ ≤ tc₂) (hX₁ : ∀ j, tc₁ ≤ j → ¬X₁ j) :
    (([∗list] j ∈ List.range' tc₁ (tc₂ - tc₁),
        thActive j ∗ parKids (.thread j) ∅ ∗ OForest.bill j ∅) ={∅}=∗
      ALC (mupd n₂ iprop(
        ([∗list] j ∈ List.range tc₂, ⌜¬X₁ j ∧ X₂ j⌝ -∗ thActive j ∗ parKids (.thread j) ∅) ∗
        (([∗list] j ∈ List.range tc₂, ⌜X₁ j ∧ ¬X₂ j⌝ -∗ thActive j ∗ parKids (.thread j) ∅)
          -∗ P)))) ⊢
      mphys n₁ n₂ tc₁ tc₂ X₁ X₂ P := by
  iintro H
  iapply mphys_forks hn htc hX₁
  iintro Hl
  imod H $$ Hl with H
  imodintro
  iapply ALC_mono (mupd_mono_of (mbits_kids n₂ tc₂ X₁ X₂ P)) $$ H

/-- A step that forks the threads `tc₁, …, tc₂ - 1` and keeps the bits. -/
theorem mphys_step_fork (n₁ n₂ tc₁ tc₂ : Nat) (X : ThreadId → Prop) (P : IProp GF)
    (hn : n₁ ≤ n₂) (htc : tc₁ ≤ tc₂) (hX : ∀ j, tc₁ ≤ j → ¬X j) :
    (([∗list] j ∈ List.range' tc₁ (tc₂ - tc₁),
        thActive j ∗ parKids (.thread j) ∅ ∗ OForest.bill j ∅) ={∅}=∗ ALC (mupd n₂ P)) ⊢
      mphys n₁ n₂ tc₁ tc₂ X X P := by
  iintro H
  iapply mphys_forks hn htc hX
  iintro Hl
  imod H $$ Hl with H
  imodintro
  iapply ALC_mono (mupd_mono_of (mbits_intro n₂ tc₂ X P)) $$ H

end Physical

end Lantana.Model.OPreds
