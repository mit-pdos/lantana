/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for trace specifications: instance resolution of `Complete`, `Instant`, `Ext` and
`Mono`, existentials, and the fixpoint characterizations of always and until. -/

namespace LantanaTest.Trace

open Iris Lantana
open scoped Lantana.TrProp Lantana.TrSpec

variable {Expr State : Type} {GF : BundledGFunctors}

example (p : Prop) (φ : State → ThreadPool Expr → Prop) :
    TrSpec.Complete (□ₛ (⌜p⌝ₛ ∧ₛ TrSpec.state (GF := GF) φ)) := inferInstance

example (p : Prop) (φ : State → ThreadPool Expr → Prop) :
    TrSpec.Instant (⌜p⌝ₛ ∨ₛ TrSpec.state (GF := GF) φ) := inferInstance

example (G H : TrSpec Expr State GF) [TrSpec.Complete G] [TrSpec.Complete H] :
    TrSpec.Complete (G 𝒰ₛ H) := inferInstance

example (G : TrSpec Expr State GF) [TrSpec.Complete G] : TrSpec.Complete (◇ₛ G) :=
  inferInstance

/-- `Ext` computes the trace reading from the shape. -/
example (G : TrSpec Expr State GF) (p : Prop) :
    TrSpec.Ext (□ₛ (G ∧ₛ ⌜p⌝ₛ)) (□ₜ (G.external ∧ₜ ⌜p⌝ₜ)) := inferInstance

/-- Existentials over small types elaborate directly. -/
noncomputable example (G : Nat → TrSpec Expr State GF) : TrSpec Expr State GF := ∃ₛ n, G n

/-- Over a larger universe (`Fuel : Type 2`) the index type must be given: the `SIdxLarge`
instance would otherwise be synthesized at `Type 0` before the index type is known. -/
noncomputable example (G : Fuel → TrSpec Expr State GF) : TrSpec Expr State GF :=
  TrSpec.ex (X := Fuel) G

/-- Monotone and continuous bodies, by instance resolution (including eta-reducible bodies). -/
example (G : TrSpec Expr State GF) :
    TrSpec.Mono fun X : TrSpec Expr State GF => TrSpec.later (TrSpec.step (G ∧ₛ TrSpec.shift X)) :=
  inferInstance

example (G : TrSpec Expr State GF) :
    TrSpec.Mono fun X : TrSpec Expr State GF => G 𝒰ₛ (□ₛ (X ∨ₛ G)) :=
  inferInstance

example (A G : TrSpec Expr State GF) :
    TrSpec.Cont fun X : TrSpec Expr State GF => G ∨ₛ (A →ₛ (G ∧ₛ TrSpec.shift X)) :=
  inferInstance

example (G : TrSpec Expr State GF) : (□ₛ G) ⊑ₛ TrSpec.nu (TrSpec.alwaysBody G) :=
  TrSpec.always_le_nu G

example (G : TrSpec Expr State GF) : TrSpec.nu (TrSpec.alwaysBody G) ⊑ₛ (□ₛ G) :=
  TrSpec.nu_le_always G

example (G₁ G₂ : TrSpec Expr State GF) (τ : Trace Expr State) :
    (TrSpec.mu (TrSpec.untilBody G₁ G₂)).external τ ↔ (G₁.external 𝒰ₜ G₂.external) τ :=
  TrSpec.mu_until_ext_iff G₁ G₂ τ

end LantanaTest.Trace
