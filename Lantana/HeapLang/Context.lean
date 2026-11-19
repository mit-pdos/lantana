/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.HeapLang.Instances

/-! # The evaluation contexts of HeapLang

`lWP` quantifies over every evaluation context `K : Exp → Exp` (`Language.Context K`), and the laws
of HeapLang hold a thread's expression under a list `C` of context items.
`context_eq_fill_of_primStep` relates the two: a context that agrees with `fill C` before a step
agrees with it after the step.  See `docs/program-logic.md`, §4.
-/

@[expose] public section

namespace Lantana.HeapLang

open Iris.ProgramLogic
open Iris.ProgramLogic.PrimStep (primStep)

/-- An evaluation context that agrees with the items `C` on `e₁` agrees with them on the result of
a step of `e₁`. -/
theorem context_eq_fill_of_primStep {K : Exp → Exp} [Language.Context K] {C : List ECtxItem}
    {e₁ e₂ : Exp} {σ₁ σ₂ : State} {obs : List Empty} {efs : List Exp}
    (heq : K e₁ = fill C e₁) (hs : primStep (e₁, σ₁) obs (e₂, σ₂, efs)) :
    K e₂ = fill C e₂ := by
  sorry

end Lantana.HeapLang
