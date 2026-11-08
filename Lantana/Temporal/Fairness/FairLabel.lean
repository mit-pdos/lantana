/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Fairness.Sched

/-! # Fair labelling

Every behavior on which each thread is fairly scheduled admits a schedule that is fair as well
(`exists_fair_schedule`): a schedule names one stepping thread at each position from the current
one on, and it is fair when every thread active infinitely often is named infinitely often while
active.  No behavior and no assumption names the thread that takes a step, but the adequacy proof
needs one owner per step; the theorem says that the owner can be chosen fairly.

A *claim* of thread `i` is a position at or after the current one where `i` is active and the
step taken is one of `i`'s steps.  The construction is diagonal: stage `s` visits the threads
`0, …, s`; a frontier only moves forward; a visited thread with a claim at or beyond the frontier
takes the least such claim and the frontier moves just past it.  Two visits never take the same
position (`takes_unique`), and a thread with infinitely many claims takes positions as far out as
wanted (`exists_takes_ge`).  The schedule names at a taken position the thread that took it, at
any other position at or after the current one some thread that steps there, and `0` before the
current position, where a schedule is unconstrained.  Classical; the names in `FairLabel` are
auxiliary.
-/

@[expose] public section

namespace Lantana.Fairness

open scoped Lantana.TrProp

/-! ## 6. The schedule as a proof instrument: fair labelling -/

namespace FairLabel

/-! ### The diagonal visit order -/

/-- The visit order, as pairs (stage, thread).  Stage `s` visits the threads `0, 1, …, s` in order,
and stage `s + 1` follows. -/
def visit : Nat → Nat × Nat
  | 0 => (0, 0)
  | k + 1 =>
    if (visit k).2 < (visit k).1 then ((visit k).1, (visit k).2 + 1) else ((visit k).1 + 1, 0)

/-- Within a stage, the visits run through the threads in order. -/
theorem visit_add {k s : Nat} (hk : visit k = (s, 0)) : ∀ j, j ≤ s → visit (k + j) = (s, j) := by
  sorry

/-- Every stage `s` begins, at a visit numbered at least `s`. -/
theorem exists_visit_stage : ∀ s, ∃ k, s ≤ k ∧ visit k = (s, 0) := by
  sorry

/-- Every thread is visited infinitely often: thread `i` at every stage from `i` on. -/
theorem visit_infOften (i : Nat) : MissHit.InfOften (fun k => (visit k).2 = i) := by
  sorry

/-! ### The frontier and the positions taken -/

variable {C : Type} [Pool C] (τ : Trace C)

/-- Position `n` is a claim of thread `i`: `n` is at or after the current position, the thread is
active at `n`, and the step taken at `n` is one of its steps. -/
def claim (i n : Nat) : Prop :=
  τ.pos ≤ n ∧ Pool.active i (τ.seq n) ∧ Pool.Step i (τ.seq n) (τ.seq (n + 1))

open Classical in
/-- The frontier before visit `k`.  The thread visited at `k` takes its least claim at or beyond
the frontier, if it has one, and the frontier moves just past that claim.  Otherwise the frontier
stays. -/
noncomputable def front : Nat → Nat
  | 0 => 0
  | k + 1 =>
    if h : ∃ p, front k ≤ p ∧ claim τ (visit k).2 p then Nat.minWitness h + 1 else front k

/-- Visit `k` takes position `n`: `n` is a claim of the visited thread at or beyond the frontier,
and the frontier moves just past `n`. -/
def takes (k n : Nat) : Prop :=
  front τ k ≤ n ∧ claim τ (visit k).2 n ∧ front τ (k + 1) = n + 1

variable {τ}

/-- The frontier never moves back at a visit. -/
theorem front_le_succ (k : Nat) : front τ k ≤ front τ (k + 1) := by
  sorry

/-- The frontier never moves back. -/
theorem front_mono {k k' : Nat} (h : k ≤ k') : front τ k ≤ front τ k' := by
  sorry

/-- A visited thread with a claim at or beyond the frontier takes the least such claim. -/
theorem takes_of_exists {k : Nat} (h : ∃ p, front τ k ≤ p ∧ claim τ (visit k).2 p) :
    takes τ k (Nat.minWitness h) := by
  sorry

/-- Two visits never take the same position. -/
theorem takes_unique {k k' n : Nat} (h : takes τ k n) (h' : takes τ k' n) : k = k' := by
  sorry

/-- A thread with infinitely many claims takes positions as far out as wanted. -/
theorem exists_takes_ge {i : Nat} (hcl : MissHit.InfOften (claim τ i)) (N : Nat) :
    ∃ k n, (visit k).2 = i ∧ N ≤ n ∧ takes τ k n := by
  sorry

/-! ### The schedule -/

open Classical in
/-- The schedule: at a taken position, the thread that took it; at any other position at or after
the current one, some thread that steps there; before the current position, `0`. -/
noncomputable def sched (hrun : IsBehavior τ) (n : Nat) : ThreadId :=
  if h : ∃ k, takes τ k n then (visit h.choose).2
  else if hn : τ.pos ≤ n then Classical.choose (isBehavior_iff.mp hrun n hn) else 0

/-- The schedule names a stepping thread at every position from the current one on. -/
theorem sched_step (hrun : IsBehavior τ) {n : Nat} (hn : τ.pos ≤ n) :
    Pool.Step (sched hrun n) (τ.seq n) (τ.seq (n + 1)) := by
  sorry

/-- At a taken position, the schedule names the thread that took it. -/
theorem sched_of_takes (hrun : IsBehavior τ) {k n : Nat} (h : takes τ k n) :
    sched hrun n = (visit k).2 := by
  sorry

end FairLabel

variable {C : Type} [Pool C] {τ : Trace C}

/-- **Fair labelling.**  A behavior on which every thread is fairly scheduled (`Sched.SF`: a thread
active infinitely often steps infinitely often) admits a schedule under which every thread active
infinitely often is named infinitely often while active.  The adequacy proof uses the schedule
for its per-thread bookkeeping; no assumption mentions it. -/
theorem exists_fair_schedule (hrun : IsBehavior τ) (hsf : ∀ i, Sched.SF i τ) :
    ∃ sched : Nat → ThreadId, Schedule sched τ ∧
      ∀ i, (□ₜ ◇ₜ active i) τ →
        (□ₜ ◇ₜ (active i ∧ₜ TrProp.atPos fun n => sched n = i)) τ := by
  sorry

/-- Under a fair schedule the thread's scheduling counter exists: it resets where the schedule
names the thread, drops where the thread is active and not named, and stays where it is inactive.
Normalised, this is `BehFscnt` (`Lantana.Temporal.FairScheduling`). -/
theorem Sched.exists_counter_of_fair_schedule {sched : Nat → ThreadId} {i : ThreadId}
    (hfair : (□ₜ ◇ₜ active i) τ → (□ₜ ◇ₜ (active i ∧ₜ TrProp.atPos fun n => sched n = i)) τ) :
    ∃ δ, AttemptGrant.IsCounter (active i) (TrProp.atPos fun n => sched n = i) δ τ := by
  sorry

end Lantana.Fairness
