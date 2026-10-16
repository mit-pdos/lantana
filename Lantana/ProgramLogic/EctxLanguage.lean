/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.ProgramLogic.Language

/-! # Languages with evaluation contexts

Rocq `lantana/program_logic/ectx_language.v`, adapted from Iris-Lean's
`Iris.ProgramLogic.EctxLanguage`. A language is given by a base step on redexes and evaluation
contexts `Ectx` with `fill`; the primitive step of the derived `Language` is a base step under
a context. As in `Lantana.Language`, the base step knows nothing about thread ids (forked
threads are appended to the pool, D14) and has no observations (D15).

As in Iris-Lean, the empty context and composition (`EvContextOps`) and `fill` with its laws
(`EvContext`) are classes of their own, so that `emptyEctx` is determined by the type of
contexts alone; `EctxLanguage` extends both.
-/

@[expose] public section

namespace Lantana

open Iris.ProgramLogic (ToVal toVal)
open Iris.ProgramLogic.Language (Atomicity)


#lantana_ignore fork_thread_ids
  "positional thread ids (D14): forked threads are appended to the pool, so there are no fresh ids"
#lantana_ignore base_reducible_no_obs "observations dropped (D15): this is `BaseReducible`"
#lantana_ignore base_reducible_no_obs_reducible "observations dropped (D15)"
#lantana_ignore fill_reducible_no_obs "observations dropped (D15): this is `reducible_fill`"
#lantana_ignore base_prim_reducible_no_obs
  "observations dropped (D15): this is `reducible_of_baseReducible`"
#lantana_ignore base_prim_fill_reducible_no_obs
  "observations dropped (D15): this is `reducible_fill_of_baseReducible`"

/-- The empty context and the composition of contexts. -/
class EvContextOps (Ectx : Type) where
  /-- The empty context. -/
  emptyEctx : Ectx
  /-- `compEctx K₁ K₂` is `K₂` plugged into `K₁` (`EvContext.fill_comp`). -/
  compEctx : Ectx → Ectx → Ectx

export EvContextOps (emptyEctx compEctx)

attribute [lantana_alias empty_ectx] EvContextOps.emptyEctx
attribute [lantana_alias comp_ectx] EvContextOps.compEctx

/-- Evaluation contexts `Ectx` of the expressions `Expr`: expressions with a hole, which `fill`
plugs. -/
class EvContext (Expr : Type) (Ectx : outParam (Type)) extends EvContextOps Ectx where
  /-- Plug an expression into the hole of a context. -/
  fill : Ectx → Expr → Expr
  fill_empty (e : Expr) : fill emptyEctx e = e
  fill_comp (K₁ K₂ : Ectx) (e : Expr) : fill K₁ (fill K₂ e) = fill (compEctx K₁ K₂) e
  fill_inj {K : Ectx} : Function.Injective (fill K)

export EvContext (fill)

attribute [lantana_alias fill] EvContext.fill
attribute [lantana_alias fill_empty] EvContext.fill_empty
attribute [lantana_alias fill_comp] EvContext.fill_comp
attribute [lantana_alias fill_inj] EvContext.fill_inj

attribute [simp] EvContext.fill_empty

/-- A language with evaluation contexts: the base step `baseStep e σ e' σ' efs` of a redex `e`
(forking the threads `efs`), evaluation contexts `Ectx`, and the laws relating them. -/
@[lantana_alias ectxLanguage, lantana_alias EctxLanguageMixin]
class EctxLanguage (Expr : Type) (State : outParam (Type)) (Val : outParam (Type))
    (Ectx : outParam (Type)) extends ToVal Expr Val, EvContext Expr Ectx where
  /-- The base step: one step of a redex, forking the threads `efs`. -/
  baseStep : Expr → State → Expr → State → List Expr → Prop
  /-- Values are not redexes. -/
  val_base_stuck {e₁ : Expr} {σ₁ : State} {e₂ σ₂ efs} :
    baseStep e₁ σ₁ e₂ σ₂ efs → toVal e₁ = none
  /-- Removing a context from a value gives a value. -/
  fill_val (K : Ectx) (e : Expr) : (toVal (fill K e)).isSome → (toVal e).isSome
  /-- A base redex in `fill K' e₁'`, with `e₁'` not a value, lies inside `e₁'`. Hence there is
  at most one base redex (`base_redex_unique`). -/
  step_by_val {K' K_redex : Ectx} {e₁' e₁_redex : Expr} {σ₁ : State} {e₂ σ₂ efs} :
    fill K' e₁' = fill K_redex e₁_redex → toVal e₁' = none →
    baseStep e₁_redex σ₁ e₂ σ₂ efs → ∃ K'', K_redex = compEctx K' K''
  /-- Wrapping a non-value in a context adds no base redex positions. -/
  base_ctx_step_val {K : Ectx} {e : Expr} {σ₁ : State} {e₂ σ₂ efs} :
    baseStep (fill K e) σ₁ e₂ σ₂ efs → (toVal e).isSome ∨ K = emptyEctx

export EctxLanguage (baseStep)

attribute [lantana_alias base_step] EctxLanguage.baseStep
attribute [lantana_alias val_base_stuck] EctxLanguage.val_base_stuck
attribute [lantana_alias fill_val] EctxLanguage.fill_val
attribute [lantana_alias step_by_val] EctxLanguage.step_by_val
attribute [lantana_alias ectx_language.base_ctx_step_val] EctxLanguage.base_ctx_step_val

namespace EctxLanguage

open EvContext (fill_empty fill_comp fill_inj)

variable {Expr : Type} {State : Type} {Val : Type} {Ectx : Type}
  [Λ : EctxLanguage Expr State Val Ectx]

@[lantana_alias fill_not_val]
theorem fill_not_val (K : Ectx) {e : Expr} (h : toVal e = none) : toVal (fill K e) = none := by
  cases hK : toVal (fill K e) with
  | none => rfl
  | some _ => simpa [h] using fill_val K e (by simp [hK])

/-- The language of an `EctxLanguage`: a primitive step is a base step under a context, and the
contexts of the language are the evaluation contexts `Ectx` (Rocq `ectx_lang_ctx_mixin`). -/
@[lantana_alias ectx_lang, lantana_alias ectx_lang_mixin, lantana_alias LanguageOfEctx,
  lantana_alias ectx_lang_ctx_mixin]
instance instLanguage : Language Expr State Val where
  primStep e σ e' σ' efs := ∃ K e₁ e₂, e = fill K e₁ ∧ e' = fill K e₂ ∧ baseStep e₁ σ e₂ σ' efs
  val_stuck := fun ⟨K, _, _, he, _, h⟩ => he ▸ fill_not_val K (val_base_stuck h)
  Ctx := Ectx
  ctxApply := fill
  ctxId := emptyEctx
  ctxComp := compEctx
  ctxApply_id := fill_empty
  ctxApply_comp K₁ K₂ e := (fill_comp K₁ K₂ e).symm

/-- The contexts of the language are the evaluation contexts. -/
@[simp]
theorem ctxApply_eq_fill (K : Ectx) (e : Expr) : ctxApply (Expr := Expr) K e = fill K e := rfl

/-- The primitive step, unfolded. -/
@[lantana_alias prim_step]
theorem primStep_iff {e : Expr} {σ : State} {e' σ' efs} :
    primStep e σ e' σ' efs ↔
      ∃ K e₁ e₂, e = fill K e₁ ∧ e' = fill K e₂ ∧ baseStep e₁ σ e₂ σ' efs :=
  .rfl

@[lantana_alias Ectx_step]
theorem primStep_of_eq_fill (K : Ectx) {e e₁ e' e₂ : Expr} {σ σ' : State} {efs}
    (he : e = fill K e₁) (he' : e' = fill K e₂) (h : baseStep e₁ σ e₂ σ' efs) :
    primStep e σ e' σ' efs :=
  ⟨K, e₁, e₂, he, he', h⟩

@[lantana_alias Ectx_step']
theorem primStep_fill_of_baseStep (K : Ectx) {e₁ : Expr} {σ₁ : State} {e₂ σ₂ efs}
    (h : baseStep e₁ σ₁ e₂ σ₂ efs) : primStep (fill K e₁) σ₁ (fill K e₂) σ₂ efs :=
  ⟨K, e₁, e₂, rfl, rfl, h⟩

/-! ## Base reducibility -/

@[lantana_alias base_reducible]
def BaseReducible (e : Expr) (σ : State) : Prop := ∃ e' σ' efs, baseStep e σ e' σ' efs

@[lantana_alias base_irreducible]
def BaseIrreducible (e : Expr) (σ : State) : Prop := ∀ e' σ' efs, ¬ baseStep e σ e' σ' efs

@[lantana_alias base_stuck]
def BaseStuck (e : Expr) (σ : State) : Prop := toVal e = none ∧ BaseIrreducible e σ

/-- All redexes of `e` that are not values are at the root. -/
@[lantana_alias sub_redexes_are_values]
def SubredexesAreValues (e : Expr) : Prop :=
  ∀ (K : Ectx) e', e = fill K e' → toVal e' = none → K = emptyEctx

/-- Every base step of `e` ends in an irreducible expression (`WeaklyAtomic`) or a value
(`StronglyAtomic`). -/
@[lantana_alias base_atomic]
def BaseAtomic (a : Atomicity) (e : Expr) : Prop :=
  ∀ (σ : State) e' σ' efs, baseStep e σ e' σ' efs →
    match a with
    | .WeaklyAtomic => Language.Irreducible e' σ'
    | .StronglyAtomic => (toVal e').isSome

/-- An expression with a base step has no other redex. -/
theorem subredexesAreValues_of_baseStep {e : Expr} {σ : State} {e' σ' efs}
    (h : baseStep e σ e' σ' efs) : SubredexesAreValues e := by
  rintro K e₁ rfl hv
  rcases base_ctx_step_val h with h' | h'
  · simp [hv] at h'
  · exact h'

@[lantana_alias not_base_reducible]
theorem not_baseReducible_iff {e : Expr} {σ : State} :
    ¬ BaseReducible e σ ↔ BaseIrreducible e σ := by
  simp [BaseReducible, BaseIrreducible]

/-- The decomposition of an expression into a context and a base redex is unique. No law
equates `compEctx K' emptyEctx` with `K'`. -/
@[lantana_alias base_redex_unique]
theorem base_redex_unique {K K' : Ectx} {e e' : Expr} {σ σ' : State}
    (heq : fill K e = fill K' e') (h : BaseReducible e σ) (h' : BaseReducible e' σ') :
    K = compEctx K' emptyEctx ∧ e = e' := by
  obtain ⟨_, _, _, hs⟩ := h
  obtain ⟨_, _, _, hs'⟩ := h'
  obtain ⟨K'', rfl⟩ := step_by_val heq.symm (val_base_stuck hs') hs
  rw [← fill_comp] at heq
  obtain rfl := fill_inj heq.symm
  rcases base_ctx_step_val hs' with hv | rfl
  · simp [val_base_stuck hs] at hv
  · exact ⟨rfl, (fill_empty e).symm⟩

@[lantana_alias base_prim_step]
theorem primStep_of_baseStep {e₁ : Expr} {σ₁ : State} {e₂ σ₂ efs}
    (h : baseStep e₁ σ₁ e₂ σ₂ efs) : primStep e₁ σ₁ e₂ σ₂ efs :=
  ⟨emptyEctx, e₁, e₂, (fill_empty e₁).symm, (fill_empty e₂).symm, h⟩

@[lantana_alias base_step_not_stuck]
theorem notStuck_of_baseStep {e : Expr} {σ : State} {e' σ' efs}
    (h : baseStep e σ e' σ' efs) : Language.NotStuck e σ :=
  Language.notStuck_of_primStep (primStep_of_baseStep h)

@[lantana_alias fill_prim_step]
theorem primStep_fill (K : Ectx) {e₁ : Expr} {σ₁ : State} {e₂ σ₂ efs}
    (h : primStep e₁ σ₁ e₂ σ₂ efs) : primStep (fill K e₁) σ₁ (fill K e₂) σ₂ efs := by
  obtain ⟨K', e₁', e₂', rfl, rfl, h⟩ := h
  exact ⟨compEctx K K', e₁', e₂', fill_comp .., fill_comp .., h⟩

@[lantana_alias fill_reducible]
theorem reducible_fill (K : Ectx) {e : Expr} {σ : State} (h : Language.Reducible e σ) :
    Language.Reducible (fill K e) σ :=
  let ⟨_, _, _, h⟩ := h; ⟨_, _, _, primStep_fill K h⟩

@[lantana_alias base_prim_reducible]
theorem reducible_of_baseReducible {e : Expr} {σ : State} (h : BaseReducible e σ) :
    Language.Reducible e σ :=
  let ⟨_, _, _, h⟩ := h; ⟨_, _, _, primStep_of_baseStep h⟩

@[lantana_alias base_prim_fill_reducible]
theorem reducible_fill_of_baseReducible (K : Ectx) {e : Expr} {σ : State}
    (h : BaseReducible e σ) : Language.Reducible (fill K e) σ :=
  reducible_fill K (reducible_of_baseReducible h)

@[lantana_alias base_prim_irreducible]
theorem baseIrreducible_of_irreducible {e : Expr} {σ : State} (h : Language.Irreducible e σ) :
    BaseIrreducible e σ :=
  fun _ _ _ hs => h _ _ _ (primStep_of_baseStep hs)

theorem baseStep_of_primStep {e₁ : Expr} {σ₁ : State} {e₂ σ₂ efs}
    (h : primStep e₁ σ₁ e₂ σ₂ efs) (hsub : SubredexesAreValues e₁) :
    baseStep e₁ σ₁ e₂ σ₂ efs := by
  obtain ⟨K, e₁', e₂', rfl, rfl, h⟩ := h
  obtain rfl := hsub K e₁' rfl (val_base_stuck h)
  rwa [fill_empty, fill_empty]

theorem primStep_iff_baseStep {e₁ : Expr} {σ₁ : State} {e₂ σ₂ efs}
    (hsub : SubredexesAreValues e₁) : primStep e₁ σ₁ e₂ σ₂ efs ↔ baseStep e₁ σ₁ e₂ σ₂ efs :=
  ⟨(baseStep_of_primStep · hsub), primStep_of_baseStep⟩

@[lantana_alias prim_base_reducible]
theorem baseReducible_of_reducible {e : Expr} {σ : State} (h : Language.Reducible e σ)
    (hsub : SubredexesAreValues e) : BaseReducible e σ :=
  let ⟨_, _, _, h⟩ := h; ⟨_, _, _, baseStep_of_primStep h hsub⟩

@[lantana_alias prim_base_irreducible]
theorem irreducible_of_baseIrreducible {e : Expr} {σ : State} (h : BaseIrreducible e σ)
    (hsub : SubredexesAreValues e) : Language.Irreducible e σ :=
  fun _ _ _ hs => h _ _ _ (baseStep_of_primStep hs hsub)

@[lantana_alias base_stuck_stuck]
theorem stuck_of_baseStuck {e : Expr} {σ : State} (h : BaseStuck e σ)
    (hsub : SubredexesAreValues e) : Language.Stuck e σ :=
  ⟨h.1, irreducible_of_baseIrreducible h.2 hsub⟩

@[lantana_alias ectx_language_atomic]
theorem atomic_of_baseAtomic {a : Atomicity} {e : Expr} (h : BaseAtomic a e)
    (hsub : SubredexesAreValues e) : Language.Atomic a e where
  atomic hs := h _ _ _ _ (baseStep_of_primStep hs hsub)

@[lantana_alias base_reducible_prim_step_ctx]
theorem exists_baseStep_of_primStep_fill {K : Ectx} {e₁ : Expr} {σ₁ : State} {e₂ σ₂ efs}
    (hred : BaseReducible e₁ σ₁) (h : primStep (fill K e₁) σ₁ e₂ σ₂ efs) :
    ∃ e₂', e₂ = fill K e₂' ∧ baseStep e₁ σ₁ e₂' σ₂ efs := by
  obtain ⟨_, _, _, hs⟩ := hred
  obtain ⟨K', e₁', e₂', heq, rfl, h⟩ := h
  obtain ⟨K'', rfl⟩ := step_by_val heq (val_base_stuck hs) h
  rw [← fill_comp] at heq
  obtain rfl := fill_inj heq
  rcases base_ctx_step_val hs with hv | rfl
  · simp [val_base_stuck h] at hv
  · exact ⟨e₂', by rw [← fill_comp, fill_empty], by rwa [fill_empty]⟩

@[lantana_alias base_reducible_prim_step]
theorem baseStep_of_primStep_of_baseReducible {e₁ : Expr} {σ₁ : State} {e₂ σ₂ efs}
    (hred : BaseReducible e₁ σ₁) (h : primStep e₁ σ₁ e₂ σ₂ efs) :
    baseStep e₁ σ₁ e₂ σ₂ efs := by
  have h' : primStep (fill emptyEctx e₁) σ₁ e₂ σ₂ efs := by rwa [fill_empty]
  obtain ⟨e₂', rfl, hs⟩ := exists_baseStep_of_primStep_fill hred h'
  rwa [fill_empty]

/-- Every evaluation context is a context of the language. -/
@[lantana_alias ectx_lang_ctx]
instance instContextFill (K : Ectx) : Language.Context (Expr := Expr) K where
  toVal_eq_none_fill := fill_not_val K
  primStep_fill := EctxLanguage.primStep_fill K
  primStep_fill_inv {e _ _ _ _} hv h := by
    obtain ⟨K', e₁, e₂, heq, rfl, hs⟩ := h
    obtain ⟨K'', rfl⟩ := step_by_val heq hv hs
    rw [← fill_comp] at heq
    obtain rfl := fill_inj heq
    exact ⟨fill K'' e₂, (fill_comp ..).symm, primStep_fill_of_baseStep K'' hs⟩

/-! ## Pure steps -/

/-- A pure base step: always possible, deterministic, changes neither the state nor the
pool. -/
@[lantana_alias pure_base_step]
structure PureBaseStep (e₁ e₂ : Expr) : Prop where
  safe (σ : State) : BaseReducible e₁ σ
  det {σ : State} {e₂' σ' efs} : baseStep e₁ σ e₂' σ' efs → σ' = σ ∧ e₂' = e₂ ∧ efs = []

@[lantana_alias pure_base_step_pure_step]
theorem PureBaseStep.pureStep {e₁ e₂ : Expr} (h : PureBaseStep e₁ e₂) :
    Language.PureStep e₁ e₂ where
  safe σ := reducible_of_baseReducible (h.safe σ)
  det hs := h.det (baseStep_of_primStep_of_baseReducible (h.safe _) hs)

/-- Not an instance: the tactics of the program logic handle evaluation contexts themselves. -/
@[lantana_alias pure_exec_fill]
theorem pureExec_fill (K : Ectx) {φ : Prop} {n : Nat} {e₁ e₂ : Expr}
    (h : Language.PureExec φ n e₁ e₂) : Language.PureExec φ n (fill K e₁) (fill K e₂) :=
  Language.PureExec.fill (Expr := Expr) K h

end EctxLanguage
end Lantana
