/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Fairness.AttemptGrant

/-! # Fairness assumptions

An `Assumption` is an attempt–grant pair whose attempts and grants are decided by the transition
at each position: the notion a language instance declares.  `a.holds` is the core's fairness of
the pair, read through `attempted` and `granted`; because the pair is step-local, what a
transition does to the counter is a function of the transition alone (`move`), and the counter's
rules read by the move (`counter_reset`, `counter_drop`, `counter_stay`, `isCounter_iff_move`).
See `docs/temporal.md`.
-/

@[expose] public section

namespace Lantana.Fairness

open scoped Lantana.TrProp

/-- A fairness assumption: an attempt–grant pair of relations on the step, the notion a language
instance declares. -/
structure Assumption (C : Type) where
  /-- The transitions that are attempts. -/
  attempt : C → C → Prop
  /-- The transitions that are grants. -/
  grant : C → C → Prop

namespace Assumption

variable {C : Type}

/-! ### Definitions -/

/-- The transition at the current position is an attempt. -/
abbrev attempted (a : Assumption C) : TrProp C := TrProp.step a.attempt

/-- The transition at the current position is a grant. -/
abbrev granted (a : Assumption C) : TrProp C := TrProp.step a.grant

/-- The transition at the current position is a granted attempt. -/
abbrev hit (a : Assumption C) : TrProp C := AttemptGrant.hit a.attempted a.granted

/-- The transition at the current position is a refused attempt. -/
abbrev miss (a : Assumption C) : TrProp C := AttemptGrant.miss a.attempted a.granted

/-- The assumption holds of the run: the core's fairness of its pair. -/
def holds (a : Assumption C) : TrProp C := AttemptGrant.Fair a.attempted a.granted

/-- The counter of the assumption: zero at a granted attempt, one more at a refused attempt than
at the next position, unchanged where there is no attempt. -/
abbrev IsCounter (a : Assumption C) (δ : Nat → Nat) : TrProp C :=
  AttemptGrant.IsCounter a.attempted a.granted δ

/-- The grant is certain: every attempt is granted, from the current position on. -/
abbrev Certain (a : Assumption C) : TrProp C := AttemptGrant.Certain a.attempted a.granted

/-- What a transition does to the counter: a granted attempt resets it, a refused attempt drops
it, no attempt leaves it. -/
inductive Move
  /-- A granted attempt: the counter resets. -/
  | reset
  /-- A refused attempt: the counter drops by one. -/
  | drop
  /-- No attempt: the counter stays. -/
  | stay
  deriving DecidableEq

open Classical in
/-- The move of the counter at the transition from `c` to `c'`. -/
noncomputable def move (a : Assumption C) (c c' : C) : Move :=
  if a.attempt c c' then (if a.grant c c' then .reset else .drop) else .stay

variable {a : Assumption C} {c c' : C} {δ : Nat → Nat} {τ : Trace C}

/-! ### The move of a transition -/

/-- The counter resets exactly at a granted attempt. -/
theorem move_eq_reset_iff : a.move c c' = .reset ↔ a.attempt c c' ∧ a.grant c c' := by
  unfold move
  by_cases ha : a.attempt c c' <;> by_cases hg : a.grant c c' <;> simp [ha, hg]

/-- The counter drops exactly at a refused attempt. -/
theorem move_eq_drop_iff : a.move c c' = .drop ↔ a.attempt c c' ∧ ¬ a.grant c c' := by
  unfold move
  by_cases ha : a.attempt c c' <;> by_cases hg : a.grant c c' <;> simp [ha, hg]

/-- The counter stays exactly where there is no attempt. -/
theorem move_eq_stay_iff : a.move c c' = .stay ↔ ¬ a.attempt c c' := by
  unfold move
  by_cases ha : a.attempt c c' <;> by_cases hg : a.grant c c' <;> simp [ha, hg]

/-! ### The meaning of the assumption, and the existence of a counter -/

/-- The assumption is the same at every position of the run. -/
theorem holds_absolute : TrProp.Absolute a.holds := AttemptGrant.fair_absolute

/-- The meaning: infinitely many attempts force infinitely many granted ones. -/
theorem holds_iff_attempted : a.holds τ ↔ ((□ₜ ◇ₜ a.attempted) τ → (□ₜ ◇ₜ a.hit) τ) :=
  AttemptGrant.fair_iff_attempt

/-- The assumption holds exactly when it has a counter. -/
theorem holds_iff_counter : a.holds τ ↔ ∃ δ, a.IsCounter δ τ := AttemptGrant.fair_iff_counter

/-- The assumption gives a counter. -/
theorem counter_of_holds (hag : a.holds τ) : ∃ δ, a.IsCounter δ τ := holds_iff_counter.1 hag

/-- A counter gives the assumption. -/
theorem holds_of_counter (hδ : a.IsCounter δ τ) : a.holds τ := holds_iff_counter.2 ⟨δ, hδ⟩

/-! ### The counter's rules, in terms of the move -/

/-- A counter from `τ` is a counter from every later position. -/
theorem IsCounter.mono (hδ : a.IsCounter δ τ) {m : Nat} (hm : τ.pos ≤ m) :
    a.IsCounter δ { τ with pos := m } :=
  AttemptGrant.IsCounter.mono hδ hm

/-- Reset: the counter is zero where the transition resets it. -/
theorem counter_reset (hδ : a.IsCounter δ τ) (h : a.move τ.now τ.next.now = .reset) :
    δ τ.pos = 0 :=
  have ⟨ha, hg⟩ := move_eq_reset_iff.1 h
  AttemptGrant.counter_reset hδ ha hg

/-- Drop: where the transition drops the counter, it is one more than at the next position. -/
theorem counter_drop (hδ : a.IsCounter δ τ) (h : a.move τ.now τ.next.now = .drop) :
    δ τ.pos = δ (τ.pos + 1) + 1 :=
  have ⟨ha, hg⟩ := move_eq_drop_iff.1 h
  AttemptGrant.counter_drop hδ ha hg

/-- Stay: where the transition leaves the counter, it is unchanged. -/
theorem counter_stay (hδ : a.IsCounter δ τ) (h : a.move τ.now τ.next.now = .stay) :
    δ τ.pos = δ (τ.pos + 1) :=
  AttemptGrant.counter_stay hδ (move_eq_stay_iff.1 h)

/-- The counter, by the move of the transition at every position from the current one on. -/
theorem isCounter_iff_move : a.IsCounter δ τ ↔
    ∀ m, τ.pos ≤ m →
      (a.move (τ.seq m) (τ.seq (m + 1)) = .reset → δ m = 0) ∧
      (a.move (τ.seq m) (τ.seq (m + 1)) = .drop → δ m = δ (m + 1) + 1) ∧
      (a.move (τ.seq m) (τ.seq (m + 1)) = .stay → δ m = δ (m + 1)) :=
  AttemptGrant.isCounter_iff.trans
    ⟨fun h m hm =>
      ⟨fun hmv => (move_eq_reset_iff.1 hmv).elim (h m hm).1,
        fun hmv => (move_eq_drop_iff.1 hmv).elim (h m hm).2.1,
        fun hmv => (h m hm).2.2 (move_eq_stay_iff.1 hmv)⟩,
      fun h m hm =>
      ⟨fun ha hg => (h m hm).1 (move_eq_reset_iff.2 ⟨ha, hg⟩),
        fun ha hg => (h m hm).2.1 (move_eq_drop_iff.2 ⟨ha, hg⟩),
        fun ha => (h m hm).2.2 (move_eq_stay_iff.2 ha)⟩⟩

/-! ### A certain grant -/

/-- A certain grant gives the assumption outright. -/
theorem holds_of_certain : a.Certain ⊆ a.holds := AttemptGrant.fair_of_certain

/-- With a certain grant the zero function is a counter. -/
theorem counter_zero_of_certain (hc : a.Certain τ) : a.IsCounter (fun _ => 0) τ :=
  AttemptGrant.counter_zero_of_certain hc

end Assumption

end Lantana.Fairness
