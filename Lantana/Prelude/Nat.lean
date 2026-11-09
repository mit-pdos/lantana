/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Init

/-! # Least witnesses on `Nat`

The least witness of a satisfiable predicate on `Nat` (classical), used by the fairness
theory: the next hit and the budget of refusals before the next grant
(`Lantana.Temporal.Fairness.AttemptGrant`), and a thread's next step
(`Lantana.Temporal.Fairness.OwnView`).
-/

@[expose] public section

namespace Lantana

/-- A minimal witness of a satisfiable predicate on `Nat` (classical). -/
theorem Nat.exists_min {p : Nat → Prop} : ∀ n, p n → ∃ m, p m ∧ ∀ k, k < m → ¬ p k
  | n, hn => by
    classical
    by_cases h : ∃ k, k < n ∧ p k
    · obtain ⟨k, hk, hpk⟩ := h
      exact Nat.exists_min k hpk
    · exact ⟨n, hn, fun k hk hpk => h ⟨k, hk, hpk⟩⟩
termination_by n => n

/-- The least witness of a satisfiable predicate on `Nat`. -/
noncomputable def Nat.minWitness {p : Nat → Prop} (h : ∃ n, p n) : Nat :=
  Classical.choose (Nat.exists_min h.choose h.choose_spec)

/-- The least witness satisfies the predicate. -/
theorem Nat.minWitness_spec {p : Nat → Prop} (h : ∃ n, p n) : p (Nat.minWitness h) :=
  (Classical.choose_spec (Nat.exists_min h.choose h.choose_spec)).1

/-- Nothing below the least witness satisfies the predicate. -/
theorem Nat.minWitness_min {p : Nat → Prop} (h : ∃ n, p n) {k : Nat}
    (hk : k < Nat.minWitness h) : ¬ p k :=
  (Classical.choose_spec (Nat.exists_min h.choose h.choose_spec)).2 k hk

end Lantana
