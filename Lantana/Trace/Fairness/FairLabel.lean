/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Trace.Fairness.Pool

/-! # Fair labelling

Section 6 of the attempt–grant model of fairness (`Lantana.Trace.Fairness`): every run of the pool
on which each thread is fairly scheduled admits a fair schedule (`exists_fair_schedule`). -/

@[expose] public section

namespace Lantana.Fairness

/-! ## 6. The schedule as a proof instrument: fair labelling

Every run on which each thread is fairly scheduled admits a schedule that is fair as well
(`exists_fair_schedule`).  A *schedule* names one stepping thread at each position of the run.  A
schedule is fair when every thread active infinitely often is named infinitely often at positions
where it is active.  Fair scheduling is the relational assumption `Action.SF` of the thread step:
a thread active infinitely often steps infinitely often.

No run and no assumption names the thread that takes a step, but the adequacy proof needs one.
Each step must have an owner whose fuel pays for it while the other threads' scheduling counters
drop.  A step that changes the configuration has a forced owner.  A no-op step can be a step of
several threads at once, and the schedule chooses its owner.  The theorem says that the choice can
be made fairly, so the adequacy proof may assume a fair schedule although no hypothesis mentions
one.

Position `n` is a *claim* of thread `i` when `i` is active at `n` and the step taken at `n` is one
of `i`'s steps (`FairLabel.claim`).  Fair scheduling says that a thread active infinitely often has
infinitely many claims, and the schedule must give each such thread infinitely many of them.  A
position may be claimed by several threads, and infinitely many threads may appear over time.  A
priority by index or by count would therefore let fresh threads starve an old one.

The construction is diagonal.  Stage `s` visits the threads `0, 1, …, s` in order
(`FairLabel.visit`).  A frontier starts at 0 and only moves forward (`FairLabel.front`).  A visited
thread with a claim at or beyond the frontier takes the least such claim, and the frontier moves
just past it.  A visited thread with no such claim is skipped.  Two visits never take the same
position, because each taken position lies between the frontier before its visit and the frontier
after it (`FairLabel.takes_unique`).  A thread with infinitely many claims is visited at every stage
from its index on, and at each visit it finds a claim beyond the frontier.  It therefore takes
positions as far out as wanted (`FairLabel.exists_takes_ge`).  The schedule names at a taken
position the thread that took it, and at any other position some thread that steps there, which
exists because the run is a run of the pool (`FairLabel.sched`).

The construction is classical.  The names in `FairLabel` are auxiliary, and only the theorem is
meant for use. -/

namespace FairLabel

/-! ### The diagonal visit order -/

/-- The visit order, as pairs (stage, thread).  Stage `s` visits the threads `0, 1, …, s` in order,
and stage `s + 1` follows. -/
def visit : Nat → Nat × Nat
  | 0 => (0, 0)
  | k + 1 =>
    if (visit k).2 < (visit k).1 then ((visit k).1, (visit k).2 + 1) else ((visit k).1 + 1, 0)

/-- Within a stage, the visits run through the threads in order. -/
theorem visit_add {k s : Nat} (hk : visit k = (s, 0)) : ∀ j, j ≤ s → visit (k + j) = (s, j)
  | 0, _ => hk
  | j + 1, hj => by
    rw [← Nat.add_assoc, visit, visit_add hk j (Nat.le_of_succ_le hj)]
    exact ite_eq_left hj

/-- Every stage `s` begins, at a visit numbered at least `s`. -/
theorem exists_visit_stage : ∀ s, ∃ k, s ≤ k ∧ visit k = (s, 0)
  | 0 => ⟨0, Nat.le_refl 0, rfl⟩
  | s + 1 => by
    obtain ⟨k, hsk, hk⟩ := exists_visit_stage s
    refine ⟨k + s + 1, Nat.succ_le_succ (Nat.le_trans hsk (Nat.le_add_right k s)), ?_⟩
    rw [visit, visit_add hk s (Nat.le_refl s)]
    exact ite_eq_right (Nat.lt_irrefl s)

/-- Every thread is visited infinitely often: thread `i` at every stage from `i` on. -/
theorem visit_infOften (i : Nat) : MissHit.InfOften (fun k => (visit k).2 = i) := by
  intro n
  obtain ⟨k, hk, hv⟩ := exists_visit_stage (i + n)
  refine ⟨k + i, by omega, ?_⟩
  change (visit (k + i)).2 = i
  rw [visit_add hv i (Nat.le_add_right i n)]

/-! ### The frontier and the positions taken -/

variable {Cfg : Type} [Pool Cfg] (active : Nat → Cfg → Prop) (σ : Nat → Cfg)

/-- Position `n` is a claim of thread `i`: the thread is active at `n`, and the step taken at `n`
is one of its steps. -/
def claim (i n : Nat) : Prop := active i (σ n) ∧ Pool.Step i (σ n) (σ (n + 1))

open Classical in
/-- The frontier before visit `k`.  The thread visited at `k` takes its least claim at or beyond
the frontier, if it has one, and the frontier moves just past that claim.  Otherwise the frontier
stays. -/
noncomputable def front : Nat → Nat
  | 0 => 0
  | k + 1 =>
    if h : ∃ p, front k ≤ p ∧ claim active σ (visit k).2 p then Nat.minWitness h + 1
    else front k

/-- Visit `k` takes position `n`: `n` is a claim of the visited thread at or beyond the frontier,
and the frontier moves just past `n`. -/
def takes (k n : Nat) : Prop :=
  front active σ k ≤ n ∧ claim active σ (visit k).2 n ∧ front active σ (k + 1) = n + 1

variable {active σ}

/-- The frontier never moves back at a visit. -/
theorem front_le_succ (k : Nat) : front active σ k ≤ front active σ (k + 1) := by
  rw [front]
  split
  · next h => exact Nat.le_succ_of_le (Nat.minWitness_spec h).1
  · exact Nat.le_refl _

/-- The frontier never moves back. -/
theorem front_mono {k k' : Nat} (h : k ≤ k') : front active σ k ≤ front active σ k' := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (front_le_succ _)

/-- A visited thread with a claim at or beyond the frontier takes the least such claim. -/
theorem takes_of_exists {k : Nat}
    (h : ∃ p, front active σ k ≤ p ∧ claim active σ (visit k).2 p) :
    takes active σ k (Nat.minWitness h) :=
  ⟨(Nat.minWitness_spec h).1, (Nat.minWitness_spec h).2, by rw [front, dite_eq_left h]⟩

/-- Two visits never take the same position.  A taken position lies between the frontier before
its visit and the frontier after it, and the frontier never moves back. -/
theorem takes_unique {k k' n : Nat} (h : takes active σ k n) (h' : takes active σ k' n) :
    k = k' := by
  obtain ⟨hle, -, hsucc⟩ := h
  obtain ⟨hle', -, hsucc'⟩ := h'
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · have := front_mono (active := active) (σ := σ) (k := k + 1) hlt
    omega
  · exact heq
  · have := front_mono (active := active) (σ := σ) (k := k' + 1) hgt
    omega

/-- A thread with infinitely many claims takes positions as far out as wanted.  The frontier at
its visits grows without bound: at each visit the thread finds a claim beyond the frontier, takes
it and moves the frontier past it, and its next visit comes later. -/
theorem exists_takes_ge {i : Nat} (hcl : MissHit.InfOften (claim active σ i)) (N : Nat) :
    ∃ k n, (visit k).2 = i ∧ N ≤ n ∧ takes active σ k n := by
  have hfront : ∀ N, ∃ k, (visit k).2 = i ∧ N ≤ front active σ k := by
    intro N
    induction N with
    | zero =>
      obtain ⟨k, _, hk⟩ := visit_infOften i 0
      exact ⟨k, hk, Nat.zero_le _⟩
    | succ N ih =>
      obtain ⟨k, hk, hN⟩ := ih
      obtain ⟨p, hp, hcp⟩ := hcl (front active σ k)
      obtain ⟨hle, -, hsucc⟩ := takes_of_exists (k := k) ⟨p, hp, hk ▸ hcp⟩
      obtain ⟨k', hk', hv⟩ := visit_infOften i (k + 1)
      have := front_mono (active := active) (σ := σ) hk'
      exact ⟨k', hv, by omega⟩
  obtain ⟨k, hk, hN⟩ := hfront N
  obtain ⟨p, hp, hcp⟩ := hcl (front active σ k)
  have ht := takes_of_exists (k := k) ⟨p, hp, hk ▸ hcp⟩
  exact ⟨k, _, hk, Nat.le_trans hN ht.1, ht⟩

/-! ### The schedule -/

open Classical in
/-- The schedule: at a taken position, the thread that took it; at any other position, some thread
that steps there. -/
noncomputable def sched (hrun : PoolRun σ) (n : Nat) : Nat :=
  if h : ∃ k, takes active σ k n then (visit h.choose).2 else (hrun n).choose

/-- The schedule names a stepping thread at every position. -/
theorem sched_step (hrun : PoolRun σ) (n : Nat) :
    Pool.Step (sched (active := active) hrun n) (σ n) (σ (n + 1)) := by
  rw [sched]
  split
  · next h => exact h.choose_spec.2.1.2
  · exact (hrun n).choose_spec

/-- At a taken position, the schedule names the thread that took it. -/
theorem sched_of_takes (hrun : PoolRun σ) {k n : Nat} (h : takes active σ k n) :
    sched (active := active) hrun n = (visit k).2 := by
  have hex : ∃ k, takes active σ k n := ⟨k, h⟩
  rw [sched, dite_eq_left hex, takes_unique hex.choose_spec h]

end FairLabel

/-- **Fair labelling.**  A run of the pool on which every thread is fairly scheduled in the
relational sense (`Action.SF` of the thread step: a thread active infinitely often steps infinitely
often) admits a schedule, one stepping thread per position, under which every thread active
infinitely often is named infinitely often while active.  The adequacy proof uses the schedule for
its per-thread bookkeeping; no assumption mentions it. -/
theorem exists_fair_schedule {Cfg : Type} [Pool Cfg] {active : Nat → Cfg → Prop} {σ : Nat → Cfg}
    (hrun : PoolRun σ) (hsf : ∀ i, Sched.SF active i σ) :
    ∃ sched : Nat → Nat, Schedule σ sched ∧
      ∀ i, MissHit.InfOften (fun n => active i (σ n)) →
        MissHit.InfOften (fun n => active i (σ n) ∧ sched n = i) := by
  refine ⟨FairLabel.sched (active := active) hrun, FairLabel.sched_step hrun, ?_⟩
  intro i hA N
  obtain ⟨k, n, hk, hN, ht⟩ := FairLabel.exists_takes_ge (hsf i hA) N
  exact ⟨n, hN, hk ▸ ht.2.1.1, (FairLabel.sched_of_takes hrun ht).trans hk⟩

/-- Under a fair schedule the thread's scheduling counter exists: it resets where the schedule
names the thread, drops where the thread is active and not named, and stays where it is inactive.
Normalised, this is Lantana's `BehFscnt`. -/
theorem Sched.exists_counter_of_fair_schedule {Cfg : Type} {active : Nat → Cfg → Prop}
    {σ : Nat → Cfg} {sched : Nat → Nat} {i : Nat}
    (hfair : MissHit.InfOften (fun n => active i (σ n)) →
      MissHit.InfOften (fun n => active i (σ n) ∧ sched n = i)) :
    ∃ δ, AttemptGrant.IsCounter (fun n => active i (σ n)) (fun n => sched n = i) δ :=
  AttemptGrant.fair_iff_counter.1 (AttemptGrant.fair_iff_attempt.2 hfair)

end Lantana.Fairness
