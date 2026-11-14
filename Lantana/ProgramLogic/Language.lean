/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.EctxiLanguage
public import Lantana.Init

/-! # Lantana's additions to Iris-Lean's language interface

Lantana's languages are Iris-Lean's (`Iris.ProgramLogic.Language`, `EctxLanguage`,
`EctxItemLanguage`), used as they are.  This module adds what the program logic needs on top:
the class `Crash` by which a language declares its crashed threads (a crashed thread is not
finished, yet inactive), the reducibility a stuckness requires (`Stuckness.maybeReducible`), the
evaluation-context instances for composed functions and for the empty and composed contexts of an
`EvContext` (candidates for upstream, `docs/iris-lean-proposal.md`), and the uniqueness of the
context around a reducible expression of an `EctxItemLanguage`.
-/

@[expose] public section

namespace Lantana

open Iris.ProgramLogic Iris.ProgramLogic.Language.Notation

/-! ## The Rocq declarations that Iris-Lean provides -/

#lantana_ignore language "Iris-Lean's `Language`"
#lantana_ignore LanguageCtxMixin "contexts are Iris-Lean's `EvContext`, outside the language"
#lantana_ignore ctx "Iris-Lean's `EvContext` (its type of contexts)"
#lantana_ignore ctx_apply "Iris-Lean's `EvContext.fill`"
#lantana_ignore ctx_id "Iris-Lean's `EvContextOps.empty`"
#lantana_ignore ctx_comp "Iris-Lean's `EvContextOps.comp`"
#lantana_ignore ctx_id_apply "Iris-Lean's `EvContext.fill_empty`"
#lantana_ignore ctx_comp_apply "Iris-Lean's `EvContext.fill_comp`"
#lantana_ignore reducible "Iris-Lean's `PrimStep.Reducible`"
#lantana_ignore irreducible "Iris-Lean's `PrimStep.Irreducible`"
#lantana_ignore stuck "Iris-Lean's `PrimStep.Stuck`"
#lantana_ignore not_stuck "Iris-Lean's `PrimStep.NotStuck`"
#lantana_ignore not_reducible "Iris-Lean's `Language.not_reducible_iff_irreducible`"
#lantana_ignore reducible_not_val "Iris-Lean's `Language.toVal_none_of_reducible`"
#lantana_ignore val_irreducible "Iris-Lean's `Language.val_irreducible`"
#lantana_ignore not_not_stuck "Iris-Lean's `Language.not_not_suck`"
#lantana_ignore prim_step_not_stuck "Iris-Lean's `Language.notStuck_of_primStep`"
#lantana_ignore Atomic "Iris-Lean's `Language.Atomic`"
#lantana_ignore stuckness_to_atomicity "Iris-Lean's `Language.Atomicity.ofStuckness`"
#lantana_ignore strongly_atomic_atomic "Iris-Lean's `Language.stronglyAtomic_atomic`"
#lantana_ignore LanguageCtx "Iris-Lean's `Language.Context`"
#lantana_ignore language_ctx_id "Iris-Lean's `Language.instContext_id`"
#lantana_ignore reducible_fill "Iris-Lean's `Language.Context.reducible_fill`"
#lantana_ignore reducible_fill_inv "Iris-Lean's `Language.Context.reducible_fill_inv`"
#lantana_ignore irreducible_fill "Iris-Lean's `Language.Context.irreducible_fill`"
#lantana_ignore irreducible_fill_inv "Iris-Lean's `Language.Context.irreducible_fill_inv`"
#lantana_ignore not_stuck_fill_inv "Iris-Lean's `Language.Context.notStuck_fill_inv`"
#lantana_ignore stuck_fill "Iris-Lean's `Language.Context.stuck_fill`"
#lantana_ignore pure_step "Iris-Lean's `Language.PurePrimStep`"
#lantana_ignore PureExec "Iris-Lean's `Language.PureExec`"
#lantana_ignore pure_step_ctx "Iris-Lean's `Language.purePrimStep_fill`"
#lantana_ignore pure_step_nsteps_ctx "Iris-Lean's `Language.iterate_purePrimStep_fill`"
#lantana_ignore pure_exec_ctx "Iris-Lean's `Language.pureExec_fill`"
#lantana_ignore rtc_pure_step_val "Iris-Lean's `Language.ReflTransGen_purePrimStep_val`"
#lantana_ignore IntoVal "Iris-Lean's `Language.IntoVal`"
#lantana_ignore AsVal "Iris-Lean's `Language.AsVal`"
#lantana_ignore as_val_is_Some "Iris-Lean's `Language.as_val_isSome`"

#lantana_ignore fork_thread_ids
  "thread ids are positions in the pool and forked threads are appended, so there are no fresh ids"
#lantana_ignore empty_ectx "Iris-Lean's `EvContextOps.empty`"
#lantana_ignore comp_ectx "Iris-Lean's `EvContextOps.comp`"
#lantana_ignore fill "Iris-Lean's `EvContext.fill`"
#lantana_ignore fill_empty "Iris-Lean's `EvContext.fill_empty`"
#lantana_ignore fill_comp "Iris-Lean's `EvContext.fill_comp`"
#lantana_ignore fill_inj "Iris-Lean's `EvContext.fill_inj`"
#lantana_ignore ectxLanguage "Iris-Lean's `EctxLanguage`"
#lantana_ignore EctxLanguageMixin "Iris-Lean's `EctxLanguage`"
#lantana_ignore base_step "Iris-Lean's `BaseStep.baseStep`"
#lantana_ignore val_base_stuck "Iris-Lean's `EctxLanguage.val_stuck`"
#lantana_ignore fill_val "Iris-Lean's `EctxLanguage.fill_val`"
#lantana_ignore step_by_val "Iris-Lean's `EctxLanguage.step_by_val`"
#lantana_ignore ectx_language.base_ctx_step_val "Iris-Lean's `EctxLanguage.base_ctx_step_val`"
#lantana_ignore fill_not_val "Iris-Lean's `EctxLanguage.fill_not_val`"
#lantana_ignore ectx_lang "Iris-Lean's `EctxLanguage.instLanguage`"
#lantana_ignore ectx_lang_mixin "Iris-Lean's `EctxLanguage.instLanguage`"
#lantana_ignore LanguageOfEctx "Iris-Lean's `EctxLanguage.instLanguage`"
#lantana_ignore ectx_lang_ctx_mixin "Iris-Lean's `EctxLanguage.toEvContext`"
#lantana_ignore prim_step "Iris-Lean's `BaseStep.ContextStep`"
#lantana_ignore Ectx_step "Iris-Lean's `BaseStep.ContextStep.ofBaseStep'`"
#lantana_ignore Ectx_step' "Iris-Lean's `BaseStep.ContextStep.ofBaseStep`"
#lantana_ignore base_reducible "Iris-Lean's `BaseStep.Reducible`"
#lantana_ignore base_irreducible "Iris-Lean's `BaseStep.Irreducible`"
#lantana_ignore base_stuck "Iris-Lean's `BaseStep.Stuck`"
#lantana_ignore base_reducible_no_obs "Iris-Lean's `BaseStep.ReducibleNoObs`"
#lantana_ignore base_reducible_no_obs_reducible "Iris-Lean's `BaseStep.reducible_of_reducibleNoObs`"
#lantana_ignore not_base_reducible "Iris-Lean's `BaseStep.not_reducible_iff_irreducible`"
#lantana_ignore sub_redexes_are_values "Iris-Lean's `EctxLanguage.SubredexesAreValues`"
#lantana_ignore base_atomic "Iris-Lean's `EctxLanguage.BaseAtomic`"
#lantana_ignore base_redex_unique "Iris-Lean's `EctxLanguage.base_redex_unique`"
#lantana_ignore base_prim_step "Iris-Lean's `EctxLanguage.primStep_of_baseStep`"
#lantana_ignore base_step_not_stuck "Iris-Lean's `EctxLanguage.base_step_not_stuck`"
#lantana_ignore fill_prim_step "Iris-Lean's `EctxLanguage.fill_primStep`"
#lantana_ignore fill_reducible "Iris-Lean's `EctxLanguage.fill_reducible`"
#lantana_ignore fill_reducible_no_obs "Iris-Lean's `EctxLanguage.reducibleNoObs_fill`"
#lantana_ignore base_prim_reducible
  "Iris-Lean's `EctxLanguage.primStep_reducible_of_baseStep_reducible`"
#lantana_ignore base_prim_fill_reducible
  "Iris-Lean's `EctxLanguage.primStep_reducible_fill_of_baseStep_reducible`"
#lantana_ignore base_prim_reducible_no_obs
  "Iris-Lean's `EctxLanguage.primStep_reducibleNoObs_of_baseStep_reducibleNoObs`"
#lantana_ignore base_prim_fill_reducible_no_obs
  "Iris-Lean's `EctxLanguage.primStep_reducibleNoObs_fill_of_baseStep_reducibleNoObs`"
#lantana_ignore base_prim_irreducible
  "Iris-Lean's `EctxLanguage.baseStep_irreducible_of_primStep_irreducible`"
#lantana_ignore prim_base_reducible
  "Iris-Lean's `EctxLanguage.baseStep_reducible_of_primStep_reducible`"
#lantana_ignore prim_base_irreducible
  "Iris-Lean's `EctxLanguage.primStep_irreducible_of_baseStep_irreducible`"
#lantana_ignore base_stuck_stuck "Iris-Lean's `EctxLanguage.primStep_stuck_of_baseStep_stuck`"
#lantana_ignore ectx_language_atomic "Iris-Lean's `EctxLanguage.Atomic.ofBaseAtomic`"
#lantana_ignore base_reducible_prim_step_ctx
  "Iris-Lean's `EctxLanguage.exists_baseStep_of_primStep_fill_of_redex_baseStep_reducible`"
#lantana_ignore base_reducible_prim_step
  "Iris-Lean's `EctxLanguage.baseStep_of_primStep_of_baseStep_reducible`"
#lantana_ignore ectx_lang_ctx "Iris-Lean's `EctxLanguage.instContextFill`"
#lantana_ignore pure_base_step "Iris-Lean's `EctxLanguage.PureBaseStep`"
#lantana_ignore pure_base_step_pure_step "Iris-Lean's `EctxLanguage.purePrimStep_of_pureBaseStep`"
#lantana_ignore pure_exec_fill "Iris-Lean's `EctxLanguage.pureExec_fill`"

#lantana_ignore ectxiLanguage "Iris-Lean's `EctxItemLanguage`"
#lantana_ignore EctxiLanguageMixin "Iris-Lean's `EctxItemLanguage`"
#lantana_ignore fill_item "Iris-Lean's `EctxItemLanguage.fillItem`"
#lantana_ignore ectxi_language.base_step "Iris-Lean's `BaseStep.baseStep`"
#lantana_ignore fill_item_val "Iris-Lean's `EctxItemLanguage.fillItem_val`"
#lantana_ignore fill_item_inj "Iris-Lean's `EctxItemLanguage.fillItem_inj`"
#lantana_ignore fill_item_no_val_inj "Iris-Lean's `EctxItemLanguage.fillItem_no_val_inj`"
#lantana_ignore ectxi_language.base_ctx_step_val "Iris-Lean's `EctxItemLanguage.base_ctx_step_val`"
#lantana_ignore ectxi_language.fill "Iris-Lean's `EctxItemLanguage.instEvContext`"
#lantana_ignore fill_app "Iris-Lean's `EctxItemLanguage.fill_append`"
#lantana_ignore ectxi_language.fill_not_val "Iris-Lean's `EctxItemLanguage.fill_not_val`"
#lantana_ignore ectxi_lang_ectx "Iris-Lean's `EctxItemLanguage.instEctxLanguage`"
#lantana_ignore ectxi_lang_ectx_mixin "Iris-Lean's `EctxItemLanguage.instEctxLanguage`"
#lantana_ignore EctxLanguageOfEctxi "Iris-Lean's `EctxItemLanguage.instEctxLanguage`"
#lantana_ignore ectxi_lang "Iris-Lean's `EctxLanguage.instLanguage`"
#lantana_ignore ectxi_language_sub_redexes_are_values
  "Iris-Lean's `EctxItemLanguage.subredexes_are_values`"
#lantana_ignore ectxi_lang_ctx_item "Iris-Lean's `EctxLanguage.instContextFill [Ki]`"

variable {Expr State Obs Val Ectx : Type}

/-! ## Crashed threads -/

/-- The crashed threads of a language: whether the thread running an expression is crashed in a
state. -/
class Crash (Expr State : Type) (Obs Val : outParam Type) [Language Expr State Obs Val] where
  /-- The thread running `e` is crashed in the state `σ`. -/
  crashed : Expr → State → Prop
  /-- A finished thread is not crashed. -/
  crashed_not_val {e : Expr} {σ : State} : crashed e σ → toVal e = none

/-! ## Reducibility required by a stuckness -/

section Stuckness
variable [Language Expr State Obs Val]

/-- Reducibility required by the stuckness `s`: `NotStuck` requires a step, `MaybeStuck`
nothing. -/
def _root_.Iris.Stuckness.maybeReducible : Iris.Stuckness → Expr → State → Prop
  | .NotStuck, e, σ => PrimStep.Reducible (e, σ)
  | .MaybeStuck, _, _ => True

theorem _root_.Iris.Stuckness.maybeReducible_mono {s₁ s₂ : Iris.Stuckness} (hs : s₁ ≤ s₂)
    {e : Expr} {σ : State} (h : s₁.maybeReducible e σ) : s₂.maybeReducible e σ := by
  cases s₁ <;> cases s₂ <;> simp_all [Iris.Stuckness.maybeReducible, LE.le]

end Stuckness

/-! ## Evaluation contexts -/

namespace Language.Context

variable [Language Expr State Obs Val]

/-- Evaluation contexts compose (Iris-Lean has only the identity, `instContext_id`). -/
@[lantana_alias language_ctx_compose]
instance comp (K₁ K₂ : Expr → Expr) [Language.Context K₁] [Language.Context K₂] :
    Language.Context (K₁ ∘ K₂) where
  toVal_eq_none_fill h := Language.Context.toVal_eq_none_fill (K := K₁)
    (Language.Context.toVal_eq_none_fill (K := K₂) h)
  primStep_fill h :=
    Language.Context.primStep_fill (K := K₁) (Language.Context.primStep_fill (K := K₂) h)
  primStep_fill_inv hv h := by
    obtain ⟨e₁, rfl, h₁⟩ := Language.Context.primStep_fill_inv (K := K₁)
      (Language.Context.toVal_eq_none_fill (K := K₂) hv) h
    obtain ⟨e₂, rfl, h₂⟩ := Language.Context.primStep_fill_inv (K := K₂) hv h₁
    exact ⟨e₂, rfl, h₂⟩

variable [EvContext Expr Ectx]

/-- The empty context is an evaluation context. -/
instance fillEmpty : Language.Context (fill (Expr := Expr) (empty : Ectx)) :=
  (funext (EvContext.fill_empty (Ectx := Ectx)) : fill (Expr := Expr) (empty : Ectx) = id) ▸
    Language.instContext_id

/-- The composition of two evaluation contexts is an evaluation context. -/
instance fillComp (K₁ K₂ : Ectx) [Language.Context (fill (Expr := Expr) K₁)]
    [Language.Context (fill (Expr := Expr) K₂)] :
    Language.Context (fill (Expr := Expr) (EvContextOps.comp K₁ K₂)) :=
  (funext fun e => (EvContext.fill_comp K₁ K₂ e).symm :
      fill (Expr := Expr) (EvContextOps.comp K₁ K₂) = fill K₁ ∘ fill K₂) ▸ comp _ _

end Language.Context

/-! ## Contexts of a reducible expression -/

namespace EctxItemLanguage

variable {EctxItem : Type} [Iris.ProgramLogic.EctxItemLanguage Expr EctxItem State Obs Val]

/-- A reducible expression determines its context. -/
@[lantana_alias fill_ctx_step_inj]
theorem fill_ctx_step_inj {K₁ K₂ : List EctxItem} {e : Expr} {σ : State} {obs : List Obs}
    {e' : Expr} {σ' : State} {efs : List Expr} (h : (e, σ) -<obs>-> (e', σ', efs))
    (heq : fill K₁ e = fill K₂ e) : K₁ = K₂ := by
  obtain ⟨hs⟩ := h
  rw [← Iris.ProgramLogic.EctxItemLanguage.fill_append,
    ← Iris.ProgramLogic.EctxItemLanguage.fill_append] at heq
  have hK := (EctxLanguage.base_redex_unique heq ⟨_, _, _, _, hs⟩ ⟨_, _, _, _, hs⟩).1
  exact List.append_cancel_left (hK.trans (List.nil_append _))

end EctxItemLanguage

end Lantana
