/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for the liveness weakest precondition `lWP` (M5): the proof-mode instances, the
structural rules and the pure-step lifting lemmas, over an arbitrary language. -/

namespace LantanaTest.WeakestPre

open Iris Iris.BI Iris.ProofMode Lantana Ordinals Ordinal
open Iris.ProgramLogic (toVal Language EvContext EvContextOps)
open Iris.ProgramLogic.EvContext (fill)

section

variable {Expr State Obs Val Ectx : Type} {GF : BundledGFunctors}
variable [Λ : Language Expr State Obs Val] [EvContext Expr Ectx] [ModelGS GF]
variable [LantanaGS Expr State Obs Val GF] [TemporalInterp Expr State GF]
variable {s : Stuckness} {i : ThreadId} {E E₂ : CoPset} {e : Expr} {Φ : Val → IProp GF}
  {P Q : IProp GF}

/-! Updates in front of `lWP` at the same mask. -/

example : (|={E}=> P) ∗ (P -∗ lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }} := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

example : (|==> P) ∗ (P -∗ lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }} := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

example : (|={E}=>m P) ∗ (P -∗ lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }} := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

example : ◇ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ Φ }} := by
  iintro H
  imod H
  iexact H

/-! Mask-changing updates in front of an atomic expression. -/

example [Language.Atomic ↑s e] :
    (|={E,E₂}=> P) ∗ (P -∗ lWP e @ s; i; E₂ {{ v, |={E₂,E}=> Φ v }}) ⊢
      lWP e @ s; i; E {{ Φ }} := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

example [Language.Atomic ↑s e] :
    (|={E,E₂}=>m P) ∗ (P -∗ lWP e @ s; i; E₂ {{ v, |={E₂,E}=>m Φ v }}) ⊢
      lWP e @ s; i; E {{ Φ }} := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

/-! Opening an invariant around an atomic expression. -/

example (N : Namespace) [Language.Atomic ↑s e] (hN : ↑N ⊆ E) :
    inv N P ∗ (▷ P -∗ lWP e @ s; i; (E \ ↑N) {{ v, |={E \ ↑N}=> ▷ P ∗ Φ v }}) ⊢
      lWP e @ s; i; E {{ Φ }} := by
  iintro ⟨#Hinv, H⟩
  iinv Hinv with HP
  iapply H $$ HP

/-! Framing, wands, values. -/

example : P ∗ lWP e @ s; i; E {{ _v, Q }} ⊢ lWP e @ s; i; E {{ _v, P ∗ Q }} := by
  iintro ⟨HP, H⟩
  iframe HP
  iexact H

example : lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ i; E ?{{ Φ }} := lwp_stuck_weaken

example (v : Val) : Φ v ⊢ lWP (v : Expr) @ s; i; E {{ Φ }} := lwp_value'

example (h : E ⊆ E₂) : lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E₂ {{ Φ }} := lwp_mask_mono h

/-! Bind: a context around an expression. -/

example (K₁ K₂ : Ectx) [Language.Context (fill (Expr := Expr) K₁)]
    [Language.Context (fill (Expr := Expr) K₂)] :
    lWP e @ s; i; E {{ fun v : Val =>
        lWP (fill K₁ (fill K₂ (v : Expr))) @ s; i; E {{ Φ }} }} ⊢
      lWP (fill K₁ (fill K₂ e)) @ s; i; E {{ Φ }} := by
  iintro H
  rw [EvContext.fill_comp]
  iapply lwp_bind (EvContextOps.comp K₁ K₂)
  isimp only [← EvContext.fill_comp]
  iexact H

/-! The empty context. -/

example : lWP e @ s; i; E {{ Φ }} ⊢ lWP (fill (EvContextOps.empty : Ectx) e) @ s; i; E {{ Φ }} := by
  rw [EvContext.fill_empty]

/-! Two pure steps paid at once. -/

example [Inhabited State] (ς : ThreadId → Expr → IProp GF) [PureExecSI ς i] {e₁ e₂ : Expr}
    [Language.PureExec True 2 e₁ e₂] (G R : Oids) (o : Fuel) :
    ς i e₁ ∗ thCarriers i G ∗ oblFuels G ((2 : Nat) : Measure) ∗ witLayers R ∗
      (ς i e₂ -∗ thCarriers i G -∗
        ([∗set] r ∈ R, Wit.cred r ((2 : Nat) : Fuel) ∨ Obl.discharged r) -∗
        £ₒ (o ×ⱼ ((2 : Nat) : Fuel)) -∗ |={E}=>m lWP e₂ @ s; i; E {{ Φ }})
      ⊢ lWP e₁ @ s; i; E {{ Φ }} :=
  lwp_pure_step_simple 2 (by omega) G R o trivial

end

end LantanaTest.WeakestPre
