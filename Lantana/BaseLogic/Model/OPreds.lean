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

/-! ## The forest operations as model updates -/

section Operations

variable [ModelGS GF]

/-- A running thread without children terminates (Rocq `thread_terminate_mupd`). -/
@[lantana_alias omodel.thread_terminate_mupd]
theorem thread_terminate_mupd (n tc : Nat) (i : ThreadId) :
    parKids (GF := GF) (.thread i) ∅ ⊢ mupd n tc (thDone i) := by
  unfold parKids thDone
  iintro ⟨He, Hk, -⟩
  iapply mupd_ghost_round
  iintro %Ω ⟨Hs, Hf⟩
  imod oforest_exec_to_done Ω tc i $$ [$Hf $He $Hk] with ⟨Hf, Hd⟩
  imodintro
  iframe Hs Hf Hd

/-- The owner `t` of a new obligation below `p`, and its piece `ν` at layer `ℓ`: below an
obligation `q` with a witness at layer `ℓq ≤ ℓ`, above the fuel of `q` (`layer_le_bound`). -/
theorem parLe_owner (Ω : Obls) (tc : Nat) (p : Parent) (K : Oids) (ℓ : Layer) :
    oforest Ω tc ∗ OForest.kids p K ∗ parLe p ℓ ⊢@{IProp GF}
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
theorem parBelow_owner (Ω : Obls) (tc : Nat) (p : Parent) (K : Oids) (ℓ : Layer) :
    oforest Ω tc ∗ OForest.kids p K ∗ parBelow p ℓ ⊢@{IProp GF}
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

/-- A new live obligation below `p` (Rocq `obl_new_mupd`): its owner is the owner of `p`, its
model fuel is the user's fuel, an extra `▽` and its piece above the fuel of the parent. -/
@[lantana_alias omodel.obl_new_mupd]
theorem obl_new_mupd (n tc : Nat) (p : Parent) (K : Oids) (ℓ : Layer) (μ : Measure) :
    parLe (GF := GF) p ℓ ⊢ parKids p K -∗
      mupd n tc iprop(∃ k : Oid, ⌜k ∉ K⌝ ∗ parKids p (K.insert k) ∗ parKids (.obl k) ∅ ∗
        oblAssigned k 1 ∗ oblFuel k ℓ μ ∗ witLayer k ℓ) := by
  unfold parKids
  iintro Hb ⟨Hx, Hk, Hs⟩
  iapply mupd_nd_step
  iintro %h %i %Ω₁ %W₁ HM
  unfold modelInterp
  icases HM with ⟨HH, Hos, Hf, Hw, %hI₁⟩
  icases parLe_owner Ω₁ tc p K ℓ $$ [$Hf $Hk $Hb] with %⟨t, ν, hpt⟩
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
  imod oforest_alloc_obl hk hpa Ordinal.le_rfl $$ [$Hf $Hk $Hβ $Hπ] with ⟨Hf, %hkK, Hk, Hkk⟩
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
theorem obl_new_discharged_mupd (n tc : Nat) (ℓ : Layer) :
    ⊢@{IProp GF} mupd n tc iprop(∃ k : Oid, oblDischarged k ∗ witLayer k ℓ) := by
  iapply mupd_nd_step
  iintro %h %i %Ω₁ %W₁ HM
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
theorem oforest_move {Ω : Obls} {tc : Nat} {p₁ p₂ : Parent} {K₁ K₂ : Oids} {k : Oid}
    {j : ThreadId} {u π : Fuel} (hk : k ∈ K₁) (hu : 0 < u)
    (hp₂ : match p₂ with
      | .thread j' => j' = j
      | .obl q => Ω.ownerOf q = some j ∧ Ω.fuelOf q < π) :
    osat Ω ∗ oforest Ω tc ∗ OForest.kids p₁ K₁ ∗ OForest.kids p₂ K₂ ∗ OSat.fuel k u ∗
        OSat.fuel k π
      ⊢@{IProp GF} |==> ∃ Ω', ⌜Obls.ndf Ω Ω' ∧ (∀ x, (get? Ω' x).isSome ↔ (get? Ω x).isSome) ∧
        k ∉ K₂⌝ ∗ osat Ω' ∗ oforest Ω' tc ∗ OForest.kids p₁ (K₁ \ {k}) ∗
        OForest.kids p₂ ({k} ∪ K₂) := by
  iintro ⟨Hs, Hf, H₁, H₂, Hu, Hπ⟩
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
    imod oforest_move_same hk hp₂' $$ [$Hf $H₁ $H₂ $Hπ] with ⟨%hkK, Hf, H₁, H₂⟩
    imodintro
    iexists Ω
    iframe Hs Hf H₁ H₂
    ipureintro
    exact ⟨Obls.ndf_refl Ω, fun _ => Iff.rfl, hkK⟩
  · have hp₂' : match (generalizing := false) p₂ with
        | .thread j' => j' = j
        | .obl q => Ω.ownerOf q = some j := by
      cases p₂ with
      | thread j' => exact hp₂
      | obl q => exact hp₂.1
    ihave Hπ := fuel_forestPiece hpiece $$ Hπ
    imod oforest_move_cross hk ht htj hu hp₂' $$ [$Hs $Hf $H₁ $H₂ $Hu $Hπ]
      with ⟨%Ω', %hΩ', Hs, Hf, H₁, H₂⟩
    imodintro
    iexists Ω'
    iframe Hs Hf H₁ H₂
    ipureintro
    exact hΩ'

/-- The obligation `k` moves with its subtree from `p₁` to `p₂`, burning one unit at a layer
that dominates `p₂` (Rocq `obl_move_mupd`): the unit splits into `1`, burnt by `k` if its owner
changes, and `▽`, its new piece below an obligation. -/
@[lantana_alias omodel.obl_move_mupd]
theorem obl_move_mupd (n tc : Nat) (p₁ p₂ : Parent) (K₁ K₂ : Oids) (k : Oid) (ℓ : Layer)
    (hk : k ∈ K₁) :
    parBelow (GF := GF) p₂ ℓ ⊢ parKids p₁ K₁ -∗ parKids p₂ K₂ -∗ oblFuel k ℓ 1 -∗
      mupd n tc iprop(⌜k ∉ K₂⌝ ∗ parKids p₁ (K₁.erase k) ∗ parKids p₂ (K₂.insert k)) := by
  unfold parKids oblFuel oblFuelVal
  rw [modelFuel_one]
  iintro Hb ⟨Hx₁, Hk₁, Hs₁⟩ ⟨Hx₂, Hk₂, Hs₂⟩ ⟨-, Hfk⟩
  icases (bigSepS_oids_erase hk).mp $$ Hs₁ with ⟨Hsk, Hs₁⟩
  icases (OSat.fuel_split k _ _).mp $$ Hfk with ⟨Hu, Hπ⟩
  iapply mupd_model_round
  iintro %Ω ⟨Hs, Hf⟩
  icases parBelow_owner Ω tc p₂ K₂ ℓ $$ [$Hf $Hk₂ $Hb] with %⟨j, hj⟩
  imod oforest_move hk zero_lt_one hj $$ [$Hs $Hf $Hk₁ $Hk₂ $Hu $Hπ]
    with ⟨%Ω', %⟨hnd, hdom, hkK⟩, Hs, Hf, Hk₁, Hk₂⟩
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
  · iframe Hx₂
    isplitl [Hk₂]
    · rw [oids_insert_eq]
      iexact Hk₂
    · iapply (bigSepS_oids_insert hkK).mpr
      iframe Hsk Hs₂

/-- A grandchild `x`, child of `k`, moves up to the parent `p` of `k` (Rocq
`obl_move_up_mupd`): a ghost round. -/
@[lantana_alias omodel.obl_move_up_mupd]
theorem obl_move_up_mupd (n tc : Nat) (p : Parent) (K : Oids) (k : Oid) (Kk : Oids) (x : Oid)
    (hk : k ∈ K) (hx : x ∈ Kk) :
    parKids (GF := GF) p K ⊢ parKids (.obl k) Kk -∗
      mupd n tc iprop(⌜x ∉ K⌝ ∗ parKids p (K.insert x) ∗ parKids (.obl k) (Kk.erase x)) := by
  unfold parKids
  iintro ⟨Hx, Hp, Hs⟩ ⟨Hxk, Hk, Hsk⟩
  icases (bigSepS_oids_erase hx).mp $$ Hsk with ⟨Hsx, Hsk⟩
  iapply mupd_ghost_round
  iintro %Ω ⟨Hos, Hf⟩
  imod oforest_move_up hk hx $$ [$Hf $Hp $Hk] with ⟨%hxK, Hf, Hp, Hk⟩
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
  · iframe Hxk Hsk
    rw [oids_erase_eq]
    iexact Hk


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
theorem obl_check_witnesses_mupd (n tc : Nat) (R : Oids) :
    ([∗set] r ∈ R, ∃ ℓ, witLayer (GF := GF) r ℓ) ⊢
      mupd n tc iprop([∗set] r ∈ R, witCred r 0 ∨ oblDischarged r) := by
  iintro #HR
  iapply mupd_nd_step
  iintro %h %i %Ω₁ %W₁ HM
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
theorem obl_check_witness_mupd (n tc : Nat) (r : Oid) (ℓ : Layer) :
    witLayer (GF := GF) r ℓ ⊢ mupd n tc iprop(witCred r 0 ∨ oblDischarged r) := by
  have h₁ : ([∗set] x ∈ ({r} : Oids), witCred (GF := GF) x 0 ∨ oblDischarged x) ⊢
      witCred r 0 ∨ oblDischarged r :=
    (BigSepS.bigSepS_singleton (Φ := fun x => iprop(witCred (GF := GF) x 0 ∨ oblDischarged x))).mp
  have h₂ : witLayer (GF := GF) r ℓ ⊢ [∗set] x ∈ ({r} : Oids), ∃ ℓ, witLayer x ℓ :=
    (BI.exists_intro (Ψ := fun ℓ => witLayer (GF := GF) r ℓ) ℓ).trans
      (BigSepS.bigSepS_singleton (Φ := fun x => iprop(∃ ℓ, witLayer (GF := GF) x ℓ))).mpr
  exact h₂.trans ((obl_check_witnesses_mupd n tc {r}).trans (mupd_mono_of h₁))

/-- Discharge of a leaf `k` below `p` (Rocq `obl_discharge_mupd`): the round with `Obls.lef`,
through `mupd_unfold`. The children predicates of `p` and `k` give the two children shares of
`k`, with the user's half the full assignment. -/
@[lantana_alias omodel.obl_discharge_mupd]
theorem obl_discharge_mupd (n tc : Nat) (p : Parent) (K : Oids) (k : Oid) (hk : k ∈ K) :
    parKids (GF := GF) p K ⊢ parKids (.obl k) ∅ -∗ oblAssigned k 1 -∗
      mupd n tc iprop(parKids p (K.erase k) ∗ oblDischarged k) := by
  unfold parKids
  iintro ⟨Hx, Hp, Hs⟩ ⟨Hsh₁, Hkk, -⟩ Ha
  icases (bigSepS_oids_erase hk).mp $$ Hs with ⟨Hsh₂, Hs⟩
  icases (oblAssigned_shares k).mpr $$ [$Ha $Hsh₁ $Hsh₂] with ⟨#He, Ha⟩
  iapply (mupd_unfold n tc _).2
  unfold mupdPre
  iright
  iintro %h %i %Ω₁ %W₁ HM
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

/-- New threads `tc, …, tc + m - 1` with their children predicates (Rocq
`thP_kids_alloc_threads`). -/
@[lantana_alias omodel.thP_kids_alloc_threads]
theorem thKids_alloc_threads (Ω : Obls) (tc m : Nat) :
    oforest Ω tc ⊢@{IProp GF} |==> (oforest Ω (tc + m) ∗
      [∗list] j ∈ List.range' tc m, parKids (.thread j) ∅) := by
  iintro Hf
  imod oforest_alloc_threads Ω tc m $$ Hf with ⟨Hf, Hl⟩
  imodintro
  iframe Hf
  iapply BigSepL.bigSepL_mono_of_forall ?_ $$ Hl
  intro _ j
  unfold parKids
  iintro ⟨Hk, He⟩
  iframe Hk He
  iapply BigSepS.bigSepS_empty.mpr
  iempintro

end Operations

/-! ## Physical steps -/

section Physical

variable [ModelGS GF]

/-- A step of thread `i` (Rocq `mprog_step_kids`): one unit of fuel of each child of `i` makes
every obligation of `i` progress (`oforest_osat_step`, keeping the owners), every assigned
witness gets a positive credit (`owit_progress`), weakened to one credit for the witnesses of
`R`. -/
@[lantana_alias omodel.mprog_step_kids]
theorem mprog_step_kids (n tc : Nat) (i : ThreadId) (K R : Oids) (P : IProp GF) :
    parKids (.thread i) K ⊢ ([∗set] k ∈ K, ∃ ℓ, oblFuel k ℓ 1) -∗
      ([∗set] r ∈ R, ∃ ℓ, witLayer r ℓ) -∗
      (parKids (.thread i) K -∗ ([∗set] r ∈ R, witCred r 1 ∨ oblDischarged r) ={∅}=∗ P) -∗
      mprog n tc i P := by
  unfold parKids mprog
  iintro ⟨Hx, Hk, Hs⟩ HF #HR H %h %a %Ω₁ %W₁ HM
  unfold modelInterp
  icases HM with ⟨HH, Hos, Hf, Hw, %hI₁⟩
  icases osat_elems Ω₁ R $$ [$Hos $HR] with %hR
  ihave HF := BigSepS.bigSepS_mono_of_forall (fun k => oblFuel_pos (GF := GF) k) $$ HF
  imod oforest_osat_step Ω₁ tc i K $$ [$Hos $Hf $Hk $HF] with ⟨%Ω₂, %⟨hp, -⟩, Hos, Hf, Hk⟩
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
  imod H $$ [Hx Hk Hs] [Hc] with HP
  · iframe Hx Hk Hs
  · iapply witLayers_creds R 1
    isplitr [Hc]
    · iexact HR
    · iexact Hc
  imodintro
  iframe HH Hos Hf Hw HP
  ipureintro
  exact hI₂

/-- A step that forks the threads `tc₁, …, tc₂ - 1` (Rocq `mphys_step_kids`): each of them gets
an empty set of children. -/
@[lantana_alias omodel.mphys_step_kids]
theorem mphys_step_kids (n₁ n₂ tc₁ tc₂ : Nat) (P : IProp GF) (hn : n₁ ≤ n₂) (htc : tc₁ ≤ tc₂) :
    (([∗list] j ∈ List.range' tc₁ (tc₂ - tc₁), parKids (.thread j) ∅) ={∅}=∗ P) ⊢
      mphys n₁ n₂ tc₁ tc₂ P := by
  unfold mphys
  iintro H %h %a %Ω %W HM
  unfold modelInterp
  icases HM with ⟨HH, Hos, Hf, Hw, %hI⟩
  imod modelHistoryInterp_step h a hn (Obls.le_refl Ω) $$ HH with HH
  imod thKids_alloc_threads Ω tc₁ (tc₂ - tc₁) $$ Hf with ⟨Hf, Hl⟩
  rw [show tc₁ + (tc₂ - tc₁) = tc₂ by omega]
  imod H $$ Hl with HP
  imodintro
  iframe HH Hos Hf Hw HP
  ipureintro
  exact hI

end Physical

end Lantana.Model.OPreds
