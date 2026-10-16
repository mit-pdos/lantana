module

public import Lantana

/-! Tests of the measure notation and of `Measure.rep`. -/

open Ordinals Ordinal Lantana Measure

/-! Notation: numerals, `+`, `*`, `^`, `▽`, `ℵ`, `⟪hwf, a⟫`. -/

example : Measure := 5 * ▽ + 5
example (μ : Measure) : Measure := μ * ▽ + 1
-- The exponent is a measure: in `▽ ^ 2` Lean would read `2` as a `Nat`.
example : Measure := ▽ ^ (2 : Measure) * ℵ
example : Measure := ⟪Nat.lt_wfRel.wf, 3⟫
example (n : Nat) : Measure := n + 1

/-! Interpretation of numerals. -/

example (ℓ : Layer) : rep ℓ (3 : Measure) = (3 : Fuel) := rep_ofNat ℓ 3

example (ℓ : Layer) (n : Nat) : rep ℓ (n : Measure) = (n : Fuel) := rep_nat ℓ n

example (ℓ : Layer) : rep ℓ (2 + 3 : Measure) = (5 : Fuel) := by
  rw [rep_add, rep_ofNat, rep_ofNat]
  exact nadd_ofNat 2 3

/-! Layers: `▽` at a higher layer dominates everything below. -/

example (μ : Measure) : rep 0 μ < rep 1 ▽ :=
  layer_dominates μ zero_lt_one

example (ℓ : Layer) (μ : Measure) : rep ℓ μ < rep ℓ (μ + 1) :=
  layer_le_bound μ Ordinal.le_rfl

example (ℓ : Layer) : rep ℓ (5 : Measure) < rep ℓ ℵ :=
  rep_large_lt ℓ _ 5
