/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TrSpecFixpoint
public import Lantana.Trace.Adequacy.Temporal

/-! # The model of trace specifications

Rocq `lantana/trace/trspec_model.v`: under the ghost-state assumptions of the adequacy theorem
(`TemporalGpreS`), what is valid in the logic holds on the trace (`TrSpec.valid_ext`). Hence
in-logic entailment `⊑ₛ` is sound for the trace readings of complete specifications
(`TrSpec.le_sound`) and not complete for them (`TrSpec.always_elim_not_le`), and a guarded
fixpoint body has no fold (`TrSpec.mu_unfold_r_guarded`).

**The instances.** Rocq allocates the ghost state under the satisfiability of `|==>` and
extracts the instances with the existential property. Here the instance records
(`ModelGS GF`, `TemporalGS Expr State GF`) live in `Type 4` (their `ElemG` fields hold maps
on `IProp GF`), while the existential property `SIdxLarge SI X` holds for `X : Type ≤ 3` only
(`SI = Ordinal.{3} : Type 4`). So the allocation exposes the ghost *names*
(`invGS_alloc_names`, a copy of `invGS_alloc` and `wsat_alloc` with the names in the
existential), the names are extracted, and the instance is rebuilt from the world's `GpreS`
instances and the names (`InvGS.ofNames`). Only world satisfaction and the credit supply are
needed: the internal reading is valid for every instance, so the other components get
arbitrary names (`ModelGS.ofInvGS`, `TemporalGS.ofGpreS`).
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode Ordinals

/-! ## The instances, from the ghost names -/

section Alloc

variable {GF : BundledGFunctors} [InvGpreS GF]

/-- The ghost state of world satisfaction and of the credits at the names `γ` (invariants,
enabled, disabled, credits). -/
@[reducible] def InvGS.ofNames (γ : GName × GName × GName × GName) : InvGS GF where
  toWsatGS :=
    { inv := WsatGpreS.inv, enabled := WsatGpreS.enabled, disabled := WsatGpreS.disabled,
      invariant_name := γ.1, enabled_name := γ.2.1, disabled_name := γ.2.2.1 }
  toCreditGS := { elem := CreditGpreS.elem, name := γ.2.2.2 }

/-- The resources framed by the satisfiability predicate of adequacy (`iPropSatLcAt ⊤`): a
credit supply, world satisfaction and the full mask. -/
def invInitRes [InvGS GF] : IProp GF := iprop((∃ x : Ordinal.{1}, ●£ₒ x) ∗ wsat ∗ ownE ⊤)

/-- `invGS_alloc` with the ghost names in the existential: the names are small enough for the
existential property of satisfiability, the instance is not. -/
theorem invGS_alloc_names :
    ⊢@{IProp GF} |==> ∃ γ : GName × GName × GName × GName,
      @invInitRes GF (InvGS.ofNames γ) := by
  imod iOwn_alloc (E := (inferInstance : WsatGpreS GF).inv) (HeapView.Auth (.own 1) ∅)
    HeapView.auth_one_valid with ⟨%γi, Hi⟩
  imod iOwn_alloc (E := (inferInstance : WsatGpreS GF).enabled) (DisjointLeibnizSet.valid ⊤) ⟨⟩
    with ⟨%γe, He⟩
  imod iOwn_alloc (E := (inferInstance : WsatGpreS GF).disabled) (DisjointLeibnizSet.valid ∅) ⟨⟩
    with ⟨%γd, -⟩
  imod iOwn_alloc (E := (inferInstance : TlcGpreS GF).elem)
    ((Auth.auth (.own 1) (0 : Ordinal.{1})) • (Auth.frag (0 : Ordinal.{1})))
    (Auth.auth_both_valid_discrete.mpr ⟨CMRA.inc_refl _, CreditCamera.valid_trivial _⟩)
    with ⟨%γc, Hc⟩
  icases iOwn_op $$ Hc with ⟨Hc, -⟩
  imodintro
  iexists (γi, γe, γd, γc)
  unfold invInitRes
  isplitl [Hc]
  · iexists 0
    unfold supply
    iexact Hc
  isplitl [Hi]
  · unfold wsat
    iexists ∅
    isplitl
    · have H : liftInv (∅ : InvMap (IProp GF)) = ∅ := by
        simp only [liftInv, Iris.Std.LawfulPartialMap.map_empty]
      rw [invMap, H]
      iexact Hi
    · iapply BigSepM.bigSepM_empty
      itrivial
  · unfold ownE
    iexact He

end Alloc

section Instances

variable {GF : BundledGFunctors}

/-- The ghost state of the model with world satisfaction and credits `Gi`; the other names
are arbitrary. -/
@[reducible] def ModelGS.ofInvGS [ModelGpreS GF] (Gi : InvGS GF) : ModelGS GF where
  toInvGS := Gi
  toOSatGS := { stateName := 0, namesName := 0 }
  toOWitGS := { namesName := 0 }
  toOForestGS := { kidsName := 0, statusName := 0 }
  toMHistGS := { name := 0 }

/-- The ghost state of the temporal layer, at arbitrary names. -/
@[reducible] def TemporalGS.ofGpreS (Expr State : Type) [TemporalGpreS Expr State GF] :
    TemporalGS Expr State GF where
  name := 0
  regName := 0

end Instances

namespace TrSpec

variable {Expr State : Type} {GF : BundledGFunctors}

/-! ## Validity, soundness and incompleteness of `⊑ₛ` -/

/-- What is valid in the logic (for every instance of the ghost state) holds on the trace. -/
@[lantana_alias trSpec_valid_ext]
theorem valid_ext [TemporalGpreS Expr State GF] (G : TrSpec Expr State GF)
    (τ : Trace Expr State) (hG : ∀ [ModelGS GF] [TemporalGS Expr State GF], ⊢ G.internal τ) :
    G.external τ := by
  have h := iPropSat.mono (true_emp.mp.trans invGS_alloc_names) (iPropSat_intro (GF := GF))
  obtain ⟨γ, hγ⟩ := iPropSat.sat_exists (iPropSat.sat_bupd h)
  letI : ModelGS GF := ModelGS.ofInvGS (InvGS.ofNames γ)
  letI : TemporalGS Expr State GF := TemporalGS.ofGpreS Expr State
  refine G.adeq iprop(emp) τ (iPropSatLcAtFrame_sat.mpr (iPropSat.mono ?_ hγ))
  unfold invInitRes
  iintro ⟨Hc, Hw, HE⟩
  iframe Hc Hw HE
  isplitl []
  · itrivial
  · iapply hG

/-- Soundness: for a complete `G`, in-logic entailment implies trace inclusion. -/
@[lantana_alias trSpec_le_sound]
theorem le_sound [TemporalGpreS Expr State GF] (G G' : TrSpec Expr State GF) [Complete G]
    (hle : G ⊑ₛ G') : G.external ⊆ G'.external :=
  fun τ hτ => valid_ext G' τ ((Complete.complete τ hτ).trans (hle τ))

/-- Incompleteness: `□ ⊥ ⊆ ⊥` holds on traces, but `□ ⊥ ⊑ₛ ⊥` does not hold in the logic
(the reading of `□ ⊥` starts with a later, so it is proved by Löb induction). -/
@[lantana_alias trSpec_always_elim_not_le]
theorem always_elim_not_le [TemporalGpreS Expr State GF] (τ : Trace Expr State) :
    ¬ ((□ₛ ⌜False⌝ₛ) ⊑ₛ (⌜False⌝ₛ : TrSpec Expr State GF)) := by
  intro hle
  refine valid_ext (⌜False⌝ₛ : TrSpec Expr State GF) τ ?_
  intro _ _
  change ⊢ iprop(⌜False⌝)
  have hle' : (□ₛ (⌜False⌝ₛ : TrSpec Expr State GF)).internal τ ⊢ iprop(⌜False⌝) := hle τ
  iloeb as IH
  iapply hle'
  have h : TrIProp.defer iprop(TrIProp.pure False τ ∧ TrIProp.always (TrIProp.pure False) τ.next)
      ⊢ (□ₛ (⌜False⌝ₛ : TrSpec Expr State GF)).internal τ :=
    (TrIProp.always_unfold _ τ).mpr
  iapply h
  iapply TrIProp.defer_intro_later
  inext
  icases IH with %hF
  exact hF.elim

/-! ## No fold for a guarded body -/

/-- A pre-fixpoint of the guarded body `X ↦ ⊳ ⊚ (⊥ ∨ (⊤ ∧ shift X))` is valid, by Löb
induction. -/
@[lantana_alias trSpec_guarded_prefix_valid]
theorem guarded_prefix_valid (M : TrSpec Expr State GF)
    (hM : untilBody TrSpec.true ⌜False⌝ₛ M ⊑ₛ M) [ModelGS GF] [TemporalGS Expr State GF]
    (τ : Trace Expr State) : ⊢ M.internal τ := by
  suffices h : ⊢ ∀ τ, M.internal τ from h.trans (forall_elim τ)
  iloeb as IH
  iintro %τ
  have h : TrIProp.defer iprop(⌜False⌝ ∨ (⌜True⌝ ∧ M.internal τ.next)) ⊢
      (untilBody TrSpec.true ⌜False⌝ₛ M).internal τ := .rfl
  iapply hM τ
  iapply h
  iapply TrIProp.defer_intro_later
  inext
  iright
  isplit
  · ipureintro
    trivial
  · iapply IH

/-- The pre-fixpoint is true on every trace. -/
@[lantana_alias trSpec_guarded_prefix_ext]
theorem guarded_prefix_ext [TemporalGpreS Expr State GF] (M : TrSpec Expr State GF)
    (τ : Trace Expr State) (hM : untilBody TrSpec.true ⌜False⌝ₛ M ⊑ₛ M) : M.external τ :=
  valid_ext M τ (guarded_prefix_valid M hM τ)

/-- The guarded body has no fold: on traces its least fixpoint is `⊤ 𝒰 ⊥`, which is empty,
whereas a fold would make it a pre-fixpoint, true on every trace. -/
@[lantana_alias trSpec_mu_unfold_r_guarded]
theorem mu_unfold_r_guarded [TemporalGpreS Expr State GF] (τ : Trace Expr State) :
    ¬ (untilBody TrSpec.true ⌜False⌝ₛ (mu (untilBody TrSpec.true ⌜False⌝ₛ)) ⊑ₛ
      mu (untilBody (TrSpec.true : TrSpec Expr State GF) ⌜False⌝ₛ)) := by
  intro hfold
  obtain ⟨_, _, hF, _⟩ := mu_until_ext _ _ τ (guarded_prefix_ext _ τ hfold)
  exact hF

end TrSpec

end Lantana
