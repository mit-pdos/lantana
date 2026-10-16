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
(`SI = Ordinal.{3} : Type 4`). So, as in adequacy (D32), the allocation exposes the ghost
*names* (`adequacy_alloc_names`), the names are extracted (`iPropSat.sat_alloc`), and the
instances are rebuilt from the world's cameras and the names (`ModelGS.ofNames`,
`TemporalGS.ofNames`). Only world satisfaction and the credit supply are used.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode Ordinals

namespace TrSpec

variable {Expr State : Type} {GF : BundledGFunctors}

/-! ## Validity, soundness and incompleteness of `⊑ₛ` -/

/-- What is valid in the logic (for every instance of the ghost state) holds on the trace. -/
@[lantana_alias trSpec_valid_ext]
theorem valid_ext [TemporalGpreS Expr State GF] (G : TrSpec Expr State GF)
    (τ : Trace Expr State) (hG : ∀ [ModelGS GF] [TemporalGS Expr State GF], ⊢ G.internal τ) :
    G.external τ := by
  obtain ⟨γ, hγ⟩ := iPropSat.sat_alloc
    (adequacy_alloc_names (GF := GF) (τ.seq τ.pos).cfg.2 (τ.seq τ.pos).cfg.1)
  letI : ModelGS GF := ModelGS.ofNames γ.1
  letI : TemporalGS Expr State GF := TemporalGS.ofNames γ.2
  refine G.adeq iprop(emp) τ (iPropSatLcAtFrame_sat.mpr (iPropSat.mono ?_ hγ))
  iintro ⟨Hc, Hw, HE, -⟩
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
