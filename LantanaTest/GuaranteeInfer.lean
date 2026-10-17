/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for guarantee inference: ghost and trace-visible existentials (over `Nat`, over
`Fuel : Type 2`, over `IProp`, over a `Prop`), checking mode, the inferred trace property, and
the axioms of the guarantees of the recursive structures. -/

namespace LantanaTest.GuaranteeInfer

open Iris Iris.BI Lantana
open scoped Lantana.TrProp Lantana.TrSpec

variable {Expr State Val : Type} {GF : BundledGFunctors} [Language Expr State Val]
  [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF]

/-- An existential over `Fuel : Type 2` whose body depends on the witness is trace-visible. -/
example (N : Namespace) (f : Fuel → Prop) :
    trSpecOf (Expr := Expr) (State := State)
      iprop(∃ a : Fuel, alwaysI (Expr := Expr) (State := State) N (iprop(⌜f a⌝) : IProp GF)) =
      TrSpec.ex (X := Fuel) fun a => □ₛ ⌜f a⌝ₛ :=
  rfl

/-- An existential over `IProp GF : Type 4` is ghost, whatever its body. -/
example (N : Namespace) :
    trSpecOf (Expr := Expr) (State := State)
      iprop(∃ P : IProp GF, alwaysI (Expr := Expr) (State := State) N P) = □ₛ TrSpec.true :=
  rfl

/-- An existential over a proposition is ghost. -/
example (φ ψ : Prop) :
    trSpecOf (Expr := Expr) (State := State) (GF := GF) iprop(∃ _ : φ, ⌜ψ⌝) = ⌜ψ⌝ₛ :=
  rfl

/-- Checking mode: an existential is trace-visible against an existential target over the
same type, ghost otherwise. -/
example (N : Namespace) (f : Nat → Prop) :
    ⊢@{IProp GF} iprop(∃ n : Nat, alwaysI (Expr := Expr) (State := State) N iprop(⌜f n⌝)) ⊨ₜ
      TrSpec.ex fun n : Nat => □ₛ ⌜f n⌝ₛ :=
  IntoGuar.into_guar

example (N : Namespace) :
    ⊢@{IProp GF} iprop(∃ n : Nat, alwaysI (Expr := Expr) (State := State) N iprop(⌜n = n⌝)) ⊨ₜ
      (□ₛ TrSpec.true : TrSpec Expr State GF) :=
  IntoGuar.into_guar

/-- A big separating conjunction over a list: the guarded family of the elements'
guarantees. -/
example (l : List Nat) (f : Nat → Prop) :
    trSpecOf (Expr := Expr) (State := State) (GF := GF) iprop([∗list] x ∈ l, ⌜f x⌝) =
      ∀ₛ (k : Nat), ∀ₛ (x : Nat), (⌜l[k]? = some x⌝ₛ →ₛ ⌜f x⌝ₛ) :=
  rfl

/-- The trace property of a guarded state fact. -/
example (φ : Prop) (Q : IProp GF) (ψ : State → ThreadPool Expr → Prop) [StateFact Q ψ] :
    trOf (Expr := Expr) (State := State) iprop(⌜φ⌝ → Q) = (⌜φ⌝ₜ →ₜ TrProp.state ψ) :=
  rfl

/-- The trace reading of a canonical specification goes through inference. -/
example (φ : Prop) :
    TrSpec.Ext (TrSpec.canon (Expr := Expr) (State := State) (GF := GF) iprop(⌜φ⌝)) ⌜φ⌝ₜ :=
  inferInstance

/-- info: 'Lantana.nest_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nest_alloc

/-- info: 'Lantana.guar_renew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guar_renew

/--
info: 'Lantana.guar_requestMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms guar_requestMap

end LantanaTest.GuaranteeInfer
