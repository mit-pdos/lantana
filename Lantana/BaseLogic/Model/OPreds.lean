/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.BaseLogic.Model.OPredsBase
public import Lantana.BaseLogic.Model.OForest
public import Lantana.BaseLogic.Model.MUpd

/-! # The children predicates and the model updates of the forest

Rocq `lantana/base_logic/opreds.v` §14.3–14.4, the part that involves the forest: the children
predicate `parKids p K` (the children of `p` are exactly `K`: the exclusive children fragment of
the forest, half of the running status of a thread or the children share of an obligation, and
the children share of every child), `thDone i`; the facts that need no invariant
(`oblKids_discharged_false`, `parKids_discharged`); the round templates `mupd_ghost_round` and
`mupd_model_round` over `Model.mupd_nd_step`; the forest operations as model updates (thread
termination, creation of an obligation, live or discharged, moves, checks of witnesses, discharge
of a leaf, the only round with `Obls.lef`); and the two physical steps `mprog_step_kids` and
`mphys_step_kids`. The statements are those of the sealed interface
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

variable {GF : BundledGFunctors}

/-! ## Definitions -/

section Defs

variable [OSatGS GF] [OForestGS GF]

/-- What the children predicate of `p` holds of `p` itself: half of the running status of a
thread, the children share of an obligation. -/
@[reducible] def parSelf : Parent → IProp GF
  | .thread i => OForest.exec i (Qp.half 1)
  | .obl k => oblShare k

/-- The children of `p` are exactly `K` (Rocq `parP_kids`): the children fragment of the forest,
what `p` holds of itself (`parSelf`), and the children share of every child. -/
@[lantana_alias omodel.parP_kids]
def parKids (p : Parent) (K : Oids) : IProp GF :=
  iprop(parSelf p ∗ OForest.kids p K ∗ [∗set] x ∈ K, oblShare x)

/-- Thread `i` has terminated (Rocq `thP_done`). -/
@[lantana_alias omodel.thP_done]
def thDone (i : ThreadId) : IProp GF :=
  OForest.done i

instance parSelf_timeless (p : Parent) : Timeless (parSelf (GF := GF) p) := by
  cases p <;> unfold parSelf <;> infer_instance

instance parKids_timeless (p : Parent) (K : Oids) : Timeless (parKids (GF := GF) p K) := by
  unfold parKids; infer_instance

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

/-- A round that may change the obligations without discharge, keeping their domain (Rocq
`mupd_model_round`): the witnesses chosen by the environment are then below the old ones. -/
@[lantana_alias omodel.mupd_model_round]
theorem mupd_model_round (n tc : Nat) (P : IProp GF) :
    (∀ Ω : Obls, osat Ω ∗ oforest Ω tc ==∗ ∃ Ω' : Obls,
        ⌜Obls.ndf Ω Ω' ∧ ∀ x, (get? Ω' x).isSome ↔ (get? Ω x).isSome⌝ ∗
        osat Ω' ∗ oforest Ω' tc ∗ P) ⊢ mupd n tc P := by
  iintro H
  iapply mupd_nd_step
  iintro %h %i %Ω₁ %W₁ HM
  unfold modelInterp
  icases HM with ⟨HH, Hs, Hf, Hw, %hI₁⟩
  imod H $$ %Ω₁ [$Hs $Hf] with ⟨%Ω₂, %⟨hnd, hdom⟩, Hs, Hf, HP⟩
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

/-- A round that changes only ghost state (Rocq `mupd_ghost_round`). -/
@[lantana_alias omodel.mupd_ghost_round]
theorem mupd_ghost_round (n tc : Nat) (P : IProp GF) :
    (∀ Ω : Obls, osat Ω ∗ oforest Ω tc ==∗ osat Ω ∗ oforest Ω tc ∗ P) ⊢ mupd n tc P := by
  iintro H
  iapply mupd_model_round
  iintro %Ω HΩ
  imod H $$ %Ω HΩ with ⟨Hs, Hf, HP⟩
  imodintro
  iexists Ω
  iframe Hs Hf HP
  ipureintro
  exact ⟨Obls.ndf_refl Ω, fun _ => Iff.rfl⟩

private theorem mupd_mono_of {n tc : Nat} {P Q : IProp GF} (h : P ⊢ Q) :
    mupd n tc P ⊢ mupd n tc Q := by
  iintro H
  iapply mupd_bind n tc P Q $$ [] H
  iintro HP
  iapply mupd_intro
  iapply h $$ HP

end Rounds

end Lantana.Model.OPreds
