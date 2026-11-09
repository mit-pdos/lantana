/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Fairness.OwnView

/-! # Fairness assumptions

A fairness assumption (`Assumption`) is an attempt–grant pair whose attempts and grants are decided
by the transition at each position: two relations on steps, read on a trace through the step
atoms `attempted` and `granted`.  It is the step-local instance of layer 0, so layer 0's theorems
apply to it as they stand; the module restates by the assumption's name the ones a language
instance reads (`holds_iff_counter`, the counter's rules).  It is the notion a language instance
declares: what the instance's trace side updates is the counter of each declared assumption, and
what a transition does to that counter is decided by the transition alone (`move`: a granted
attempt resets it, a refused attempt drops it, no attempt leaves it; `counter_reset`,
`counter_drop`, `counter_stay`, `isCounter_iff_move`).

Every fairness notion of the theory is one: strong fairness of an action (`Action.strong`, the
general path, `Action.holds_strong`), weak fairness of an action (`Action.weak`,
`Action.holds_weak`), a thread's own view of an action (`Action.own`, the cheap path,
`Action.holds_own`), and fair scheduling (`Sched.assumption`, `Sched.holds_assumption`).
-/

@[expose] public section

namespace Lantana.Fairness

open scoped Lantana.TrProp

/-! ## 7. Fairness assumptions (`Assumption`) -/

/-- A fairness assumption on a thread system: an attempt–grant pair whose attempts and grants are
decided by the transition at each position.  The step-local instance of layer 0, and the notion a
language instance declares.  Strong fairness, weak fairness, fair scheduling and a thread's own
view of an action are the four ways to build one (`Action.strong`, `Action.weak`, `Action.own`,
`Sched.assumption`). -/
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

/-- The assumption holds of the run: layer 0's fairness of its pair. -/
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

/-! ### The four ways to build an assumption -/

namespace Action

variable {C : Type}

/-- Strong fairness of the action: attempts are the positions where it is enabled, whoever steps
(the general path). -/
def strong (a : Action C) : Assumption C := ⟨fun c _ => a.enabled c, a.grant⟩

/-- Weak fairness of the action: every position attempts, and a position is granted when the
action is disabled or its step is a grant. -/
def weak (a : Action C) : Assumption C :=
  ⟨fun _ _ => True, fun c c' => ¬ a.enabled c ∨ a.grant c c'⟩

/-- The thread's own view of the action: attempts are its steps from an enabled configuration (the
cheap path). -/
def own [ThreadSystem C] (i : ThreadId) (a : Action C) : Assumption C :=
  ⟨fun c c' => ThreadSystem.step i c c' ∧ a.enabled c, a.grant⟩

variable {a : Action C} {δ : Nat → Nat} {τ : Trace C}

/-- The strong assumption of an action holds exactly when the action is strongly fair. -/
theorem holds_strong : a.strong.holds τ ↔ a.SF τ := sf_iff_fair.symm

/-- The counters of the strong assumption of an action are the action's counters. -/
theorem isCounter_strong : a.strong.IsCounter δ τ ↔ a.IsCounter δ τ := Iff.rfl

/-- The weak assumption of an action holds exactly when the action is weakly fair.  Its misses
are the positions where the action is enabled and the step is not a grant, its hits the positions
where the action is disabled or the step is a grant. -/
theorem holds_weak : a.weak.holds τ ↔ a.WF τ := by
  constructor
  · intro hag hev
    refine Classical.byContradiction fun hno => ?_
    obtain ⟨N, hN, hen⟩ := TrProp.eventually_always_iff.mp hev
    obtain ⟨N', -, hnh⟩ :=
      TrProp.eventually_always_iff.mp (TrProp.not_always_eventually_le τ hno)
    have hle : ∀ m, max N N' ≤ m → N ≤ m ∧ N' ≤ m := fun m hm =>
      ⟨Nat.le_trans (Nat.le_max_left _ _) hm, Nat.le_trans (Nat.le_max_right _ _) hm⟩
    have hmiss : (□ₜ ◇ₜ a.weak.miss) τ := TrProp.always_eventually_iff.mpr fun n _ =>
      ⟨max n (max N N'), Nat.le_max_left _ _, trivial, fun hg =>
        have h := hle _ (Nat.le_max_right _ _)
        hg.elim (fun hA => hA (hen _ h.1)) fun hg => hnh _ h.2 ⟨hen _ h.1, hg⟩⟩
    obtain ⟨m, hm, -, hg⟩ := TrProp.always_eventually_iff.mp (hag hmiss) (max N N')
      (Nat.le_trans hN (Nat.le_max_left _ _))
    have hAm := hen m (hle m hm).1
    exact hnh m (hle m hm).2 ⟨hAm, hg.resolve_left (absurd hAm)⟩
  · intro hwf _
    refine TrProp.always_eventually_iff.mpr fun n hn => Classical.byContradiction fun hno => ?_
    have hen : ∀ m, n ≤ m → a.enabledNow { τ with pos := m } := fun m hm =>
      Classical.byContradiction fun hA => hno ⟨m, hm, trivial, Or.inl hA⟩
    obtain ⟨m, hm, -, hg⟩ :=
      TrProp.always_eventually_iff.mp (hwf (TrProp.eventually_always_iff.mpr ⟨n, hn, hen⟩)) n hn
    exact hno ⟨m, hm, trivial, Or.inr hg⟩

/-- The thread's own assumption of an action holds exactly when the thread's view of the action
does. -/
theorem holds_own [ThreadSystem C] {i : ThreadId} :
    (a.own i).holds τ ↔ Thread.AttemptGrant i a τ :=
  Iff.rfl

/-- The counters of the thread's own assumption of an action are the counters of the thread's
view. -/
theorem isCounter_own [ThreadSystem C] {i : ThreadId} :
    (a.own i).IsCounter δ τ ↔ Thread.IsCounter i a δ τ :=
  Iff.rfl

end Action

namespace Sched

variable {C : Type} [ThreadSystem C]

/-- Fair scheduling of the thread at `i` as an assumption. -/
def assumption (i : ThreadId) : Assumption C := (action i).strong

/-- The scheduling assumption of a thread holds exactly when the thread is fairly scheduled. -/
theorem holds_assumption {i : ThreadId} {τ : Trace C} :
    (assumption i).holds τ ↔ SF i τ :=
  Action.holds_strong

end Sched

end Lantana.Fairness
