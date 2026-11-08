/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for the language-independent trace layer (`Lantana.Temporal`): the connectives and
their notations at any configuration type, the thread systems and their behaviors, and Lantana's
language as an instance. -/

namespace LantanaTest.Temporal

open Lantana
open scoped Lantana.TrProp

section Generic

variable {C : Type}

/-- The notations parse at any configuration type, with negation and the two-position atom. -/
example (R : C → C → Prop) (φ : TsProp C) :
    (□ₜ ◇ₜ TrProp.step R ∧ₜ ¬ₜ TrProp.now φ) ⊆ (□ₜ ◇ₜ TrProp.step R) :=
  TrProp.and_elim_l

/-- Infinitely often is the same at every position of a run. -/
example (P : TrProp C) (τ : Trace C) (m : Nat) :
    (□ₜ ◇ₜ P) τ ↔ (□ₜ ◇ₜ P) { τ with pos := m } :=
  TrProp.absolute_always_eventually τ m

/-- Weak fairness is weaker than strong fairness, for any enabling condition and grant. -/
example (A G : TrProp C) : (□ₜ ◇ₜ A →ₜ □ₜ ◇ₜ G) ⊆ (◇ₜ □ₜ A →ₜ □ₜ ◇ₜ G) :=
  TrProp.imp_mono TrProp.eventually_always_le (TrProp.le_refl _)

end Generic

section ThreadSystem

variable {C : Type} [ThreadSystem C]

/-- A behavior is a run of the thread system from the current position on. -/
example (τ : Trace C) :
    IsBehavior τ ↔
      ∀ m, τ.pos ≤ m → ∃ i, ThreadSystem.Step i (τ.seq m) (τ.seq (m + 1)) :=
  isBehavior_iff

example (τ : Trace C) (h : IsBehavior τ) : IsBehavior τ.next.next := h.next.next

end ThreadSystem

section Lantana

variable {Expr State Val : Type} [Language Expr State Val]

example : ThreadSystem (Cfg Expr State) := inferInstance

/-- At Lantana's instance, a behavior is a sequence of trace steps from the current position. -/
example (τ : Trace (Cfg Expr State)) :
    IsBehavior τ ↔ ∀ m, τ.pos ≤ m → ∃ i, TraceStep i (τ.seq m) (τ.seq (m + 1)) :=
  Iff.rfl

/-- At Lantana's instance, a thread is inactive exactly when it is not active. -/
example (i : ThreadId) (τ : Trace (Cfg Expr State)) : inactive i τ ↔ τ.now.inactive i :=
  inactive_iff.trans Cfg.inactive_iff_not_active.symm

end Lantana

/-- info: 'Lantana.TrProp.absolute_always_eventually' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrProp.absolute_always_eventually

/--
info: 'Lantana.TrProp.not_always_eventually_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TrProp.not_always_eventually_le

end LantanaTest.Temporal
