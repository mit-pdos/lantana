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
open Iris.ProgramLogic (toVal Language)

section

variable {Expr State Obs Val : Type} {GF : BundledGFunctors}
variable [Λ : Language Expr State Obs Val] [Crash Expr State Obs Val]
variable [ModelGS GF] [LantanaGS Expr State Obs Val GF] [TemporalInterp Expr State GF]
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

/-! Bind: a context around an expression; contexts are functions and compose. -/

example (K₁ K₂ : Expr → Expr) [Language.Context K₁] [Language.Context K₂] :
    lWP e @ s; i; E {{ fun v : Val => lWP (K₁ (K₂ (v : Expr))) @ s; i; E {{ Φ }} }} ⊢
      lWP (K₁ (K₂ e)) @ s; i; E {{ Φ }} :=
  lwp_bind (K₁ ∘ K₂)

/-! The identity context. -/

example : lWP e @ s; i; E {{ fun v : Val => lWP (v : Expr) @ s; i; E {{ Φ }} }} ⊢
    lWP e @ s; i; E {{ Φ }} :=
  lwp_bind id

/-! Two pure steps paid at once, each keeping the crashed threads. -/

example [Inhabited State] (ς : ThreadId → Expr → IProp GF) [PureExecSI ς i] {e₁ e₂ : Expr}
    [Language.PureExec True 2 e₁ e₂] (G R : Oids) (o : Fuel)
    (hkeep : ∀ e e' : Expr, Language.PurePrimStep e e' → KeepsCrashed i e) :
    ς i e₁ ∗ thCarriers i G ∗ Obl.fuels G ((2 : Nat) : Measure) ∗ Wit.layers R ∗
      (ς i e₂ -∗ thCarriers i G -∗
        ([∗set] r ∈ R, Wit.cred r ((2 : Nat) : Fuel) ∨ Obl.discharged r) -∗
        £ₒ (o ×ⱼ ((2 : Nat) : Fuel)) -∗ |={E}=>m lWP e₂ @ s; i; E {{ Φ }})
      ⊢ lWP e₁ @ s; i; E {{ Φ }} :=
  lwp_pure_step_simple 2 (by omega) G R o trivial hkeep

end

end LantanaTest.WeakestPre
