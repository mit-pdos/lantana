/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for the temporal formulas: `iinv` opens an `alwaysI`, fractions of an until, the
guarantees inferred from the shape of a formula, and the axioms of the guarantees. -/

namespace LantanaTest.TemporalFormula

open Iris Iris.BI Lantana
open scoped Lantana.TrProp Lantana.TrSpec

variable {Expr State Val : Type} {GF : BundledGFunctors} [Language Expr State Val]
  [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF]

/-- `iinv` opens an `alwaysI` like an invariant. -/
example (N : Namespace) (P : IProp GF) [Persistent P] : alwaysI N P ⊢ |={⊤}=> ▷ P := by
  iintro #H
  iinv H with #HP Hclose
  imod Hclose $$ [] with -
  · iexact HP
  imodintro
  iexact HP

/-- An until splits into halves. -/
example (N : Namespace) (k : Oid) (P Q : IProp GF) :
    untilI N k 1 P Q ⊢ untilI N k (Qp.half 1) P Q ∗ untilI N k (Qp.half 1) P Q :=
  untilI_frac_split (Qp.half_add_half 1).symm

/-- The guarantee of a formula is inferred through `alwaysI` and `untilI`. -/
example (N : Namespace) (k : Oid) (q : Qp) (φ ψ : Prop) :
    ⊢@{IProp GF} iprop(alwaysI N iprop(⌜φ⌝) ∗ untilI N k q iprop(⌜φ⌝) iprop(⌜ψ⌝)) ⊨ₜ
      ((□ₛ ⌜φ⌝ₛ) ∧ₛ (⌜φ⌝ₛ 𝒰ₛ ⌜ψ⌝ₛ) : TrSpec Expr State GF) :=
  IntoGuar.into_guar

/-- A done until guarantees a finally. -/
example (k : Oid) (ψ : Prop) :
    ⊢@{IProp GF} untilIDone k iprop(⌜ψ⌝) ⊨ₜ (◇ₛ ⌜ψ⌝ₛ : TrSpec Expr State GF) :=
  IntoGuar.into_guar

/-- info: 'Lantana.guar_alwaysI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guar_alwaysI

/-- info: 'Lantana.guar_untilI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guar_untilI

end LantanaTest.TemporalFormula
