/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Fairness.Scheduling

/-! # Fair labelling

A behavior on which every thread is fairly scheduled has a schedule that names every thread active
infinitely often infinitely often while active (`exists_fair_schedule`), by a diagonal
construction in `FairLabel`: stage `s` visits the threads `0, …, s`, and a visited thread takes
its least claim beyond a frontier that only moves forward.  Under such a schedule the fairness
counters exist (`exists_fair_schedule_behFscnt`).
See `docs/temporal.md`.
-/

@[expose] public section

namespace Lantana.Fairness

open scoped Lantana.TrProp

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

variable {C : Type} [ThreadSystem C] (τ : Trace C)

/-- Position `n` is a claim of thread `i`: `n` is at or after the current position, the thread is
active at `n`, and the step taken at `n` is one of its steps. -/
def claim (i n : Nat) : Prop :=
  τ.pos ≤ n ∧ ThreadSystem.active i (τ.seq n) ∧
    ThreadSystem.step i (τ.seq n) (τ.seq (n + 1))

open Classical in
/-- The frontier before visit `k`: the thread visited at `k` takes its least claim at or beyond
the frontier, if it has one, and the frontier moves just past that claim. -/
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
  rw [front]
  split
  · next h => exact Nat.le_succ_of_le (Nat.minWitness_spec h).1
  · exact Nat.le_refl _

/-- The frontier never moves back. -/
theorem front_mono {k k' : Nat} (h : k ≤ k') : front τ k ≤ front τ k' := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (front_le_succ _)

/-- A visited thread with a claim at or beyond the frontier takes the least such claim. -/
theorem takes_of_exists {k : Nat} (h : ∃ p, front τ k ≤ p ∧ claim τ (visit k).2 p) :
    takes τ k (Nat.minWitness h) :=
  ⟨(Nat.minWitness_spec h).1, (Nat.minWitness_spec h).2, by rw [front, dite_eq_left h]⟩

/-- Two visits never take the same position. -/
theorem takes_unique {k k' n : Nat} (h : takes τ k n) (h' : takes τ k' n) : k = k' := by
  obtain ⟨hle, -, hsucc⟩ := h
  obtain ⟨hle', -, hsucc'⟩ := h'
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · have := front_mono (τ := τ) (k := k + 1) hlt
    omega
  · exact heq
  · have := front_mono (τ := τ) (k := k' + 1) hgt
    omega

/-- A thread with infinitely many claims takes positions as far out as wanted. -/
theorem exists_takes_ge {i : Nat} (hcl : MissHit.InfOften (claim τ i)) (N : Nat) :
    ∃ k n, (visit k).2 = i ∧ N ≤ n ∧ takes τ k n := by
  have hfront : ∀ N, ∃ k, (visit k).2 = i ∧ N ≤ front τ k := by
    intro N
    induction N with
    | zero =>
      obtain ⟨k, _, hk⟩ := visit_infOften i 0
      exact ⟨k, hk, Nat.zero_le _⟩
    | succ N ih =>
      obtain ⟨k, hk, hN⟩ := ih
      obtain ⟨p, hp, hcp⟩ := hcl (front τ k)
      obtain ⟨hle, -, hsucc⟩ := takes_of_exists (k := k) ⟨p, hp, hk ▸ hcp⟩
      obtain ⟨k', hk', hv⟩ := visit_infOften i (k + 1)
      have := front_mono (τ := τ) hk'
      exact ⟨k', hv, by omega⟩
  obtain ⟨k, hk, hN⟩ := hfront N
  obtain ⟨p, hp, hcp⟩ := hcl (front τ k)
  have ht := takes_of_exists (k := k) ⟨p, hp, hk ▸ hcp⟩
  exact ⟨k, _, hk, Nat.le_trans hN ht.1, ht⟩

/-! ### The schedule -/

open Classical in
/-- The schedule: at a taken position, the thread that took it; at any other position at or after
the current one, some thread that steps there; before the current position, `0`. -/
noncomputable def sched (hrun : IsBehavior τ) (n : Nat) : ThreadId :=
  if h : ∃ k, takes τ k n then (visit h.choose).2
  else if hn : τ.pos ≤ n then Classical.choose (isBehavior_iff.mp hrun n hn) else 0

/-- The schedule names a stepping thread at every position from the current one on. -/
theorem sched_step (hrun : IsBehavior τ) {n : Nat} (hn : τ.pos ≤ n) :
    ThreadSystem.step (sched hrun n) (τ.seq n) (τ.seq (n + 1)) := by
  rw [sched]
  split
  · next h => exact h.choose_spec.2.1.2.2
  · exact Classical.choose_spec (isBehavior_iff.mp hrun n hn)

/-- At a taken position, the schedule names the thread that took it. -/
theorem sched_of_takes (hrun : IsBehavior τ) {k n : Nat} (h : takes τ k n) :
    sched hrun n = (visit k).2 := by
  have hex : ∃ k, takes τ k n := ⟨k, h⟩
  rw [sched, dite_eq_left hex, takes_unique hex.choose_spec h]

end FairLabel

variable {C : Type} [ThreadSystem C] {τ : Trace C}

/-- **Fair labelling.**  A behavior on which every thread is fairly scheduled admits a schedule
under which every thread active infinitely often is named infinitely often while active. -/
theorem exists_fair_schedule (hrun : IsBehavior τ) (hsf : ∀ i, Sched.SF i τ) :
    ∃ sched : Nat → ThreadId, Schedule sched τ ∧
      ∀ i, (□ₜ ◇ₜ active i) τ → (□ₜ ◇ₜ (active i ∧ₜ scheduled sched i)) τ := by
  refine ⟨FairLabel.sched hrun, schedule_iff.mpr fun _ hn => FairLabel.sched_step hrun hn, ?_⟩
  intro i hA
  have hcl : MissHit.InfOften (FairLabel.claim τ i) := by
    intro N
    obtain ⟨m, hm, hAm, hsm⟩ :=
      TrProp.always_eventually_iff.mp (hsf i hA) (max N τ.pos) (Nat.le_max_right _ _)
    exact ⟨m, Nat.le_trans (Nat.le_max_left _ _) hm,
      Nat.le_trans (Nat.le_max_right _ _) hm, hAm, hsm⟩
  refine TrProp.always_eventually_iff.mpr fun N _ => ?_
  obtain ⟨k, n, hk, hN, ht⟩ := FairLabel.exists_takes_ge hcl N
  exact ⟨n, hN, hk ▸ ht.2.1.2.1, (FairLabel.sched_of_takes hrun ht).trans hk⟩

/-- Under a fair schedule the thread's counter exists: it resets where the schedule names the
thread, drops where the thread is active and not named, and stays where it is inactive. -/
theorem Sched.exists_counter_of_fair_schedule {sched : Nat → ThreadId} {i : ThreadId}
    (hfair : (□ₜ ◇ₜ active i) τ → (□ₜ ◇ₜ (active i ∧ₜ scheduled sched i)) τ) :
    ∃ δ, AttemptGrant.IsCounter (active i) (scheduled sched i) δ τ :=
  AttemptGrant.fair_iff_counter.1 (AttemptGrant.fair_iff_attempt.2 hfair)

end Lantana.Fairness

namespace Lantana

open scoped Lantana.TrProp

variable {C : Type} [ThreadSystem C] {τ : Trace C}

/-- Under a schedule that names every thread active infinitely often infinitely often while it is
active, the run has fairness counters. -/
theorem exists_behFscnt_of_fair_schedule {sched : Nat → ThreadId}
    (hfair : ∀ i, (□ₜ ◇ₜ active i) τ → (□ₜ ◇ₜ (active i ∧ₜ scheduled sched i)) τ) :
    ∃ γ, BehFscnt sched γ τ :=
  ⟨fun m i => Classical.choose (Fairness.Sched.exists_counter_of_fair_schedule (hfair i)) m,
    behFscnt_of_counters fun i =>
      Classical.choose_spec (Fairness.Sched.exists_counter_of_fair_schedule (hfair i))⟩

/-- A behavior on which every thread is fairly scheduled admits a schedule and fairness counters
under it. -/
@[lantana_alias fair_scheduling_fscnt]
theorem exists_fair_schedule_behFscnt (hrun : IsBehavior τ) (hsf : fairScheduling τ) :
    ∃ (sched : Nat → ThreadId) (γ : Nat → ThreadId → Nat),
      Schedule sched τ ∧ BehFscnt sched γ τ := by
  obtain ⟨sched, hsch, hfair⟩ := Fairness.exists_fair_schedule hrun hsf
  obtain ⟨γ, hγ⟩ := exists_behFscnt_of_fair_schedule hfair
  exact ⟨sched, γ, hsch, hγ⟩

end Lantana
