/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Fairness

/-! # Fair scheduling and the fairness counters

Fair scheduling of a thread system (Rocq `fair_scheduling.v`): the strong fairness of every
thread's scheduling action, enabled where the thread is active and granted at its trace step
(`fairScheduling := ∀ₜ i, Sched.SF i`).  A trace property that names no scheduled thread; where
activity is convex it is the usual justice requirement, weak fairness (`fairScheduling_sf_iff_wf`).

The schedule is the adequacy proof's internal instrument.  The fair-labelling theorem
(`Fairness.exists_fair_schedule`) chooses a schedule of a behavior that names every thread active
infinitely often infinitely often while it is active.  The fairness counters that the adequacy
proof threads (Rocq `beh_fscnt`, a coinductive predicate on the counters of one position, obtained
by choice) are an explicit sequence of counters along the run under that schedule (D18):
`BehFscnt sched γ` says that while a thread is active and not named by the schedule its counter
strictly decreases.  A fair behavior has a schedule with such counters
(`exists_fair_schedule_behFscnt`), each thread's layer-0 counter of its scheduling pair.
-/

@[expose] public section

namespace Lantana

open scoped Lantana.TrProp

variable {C : Type} [ThreadSystem C]

/-- Fair scheduling: the strong fairness of the scheduling action of every thread, enabled where
the thread is active and granted at its trace step (`Fairness.Sched.SF`).  A statement about the
run that names no scheduled thread. -/
@[lantana_alias fair_scheduling]
def fairScheduling : TrProp C := ∀ₜ i : ThreadId, Fairness.Sched.SF i

/-- Fair scheduling is the same at every position of the run. -/
theorem fairScheduling_absolute : TrProp.Absolute (fairScheduling (C := C)) :=
  TrProp.absolute_all fun _ => Fairness.Action.sf_absolute

@[lantana_alias fair_scheduling_next]
theorem fairScheduling_next {τ : Trace C} (h : fairScheduling τ) : fairScheduling τ.next :=
  fairScheduling_absolute.next.mp h

/-- Fairness counters of a run under a schedule (Rocq `beh_fscnt`): from the current position on,
every thread is inactive, or active and either named by the schedule or with a strictly
decreasing counter. -/
@[lantana_alias beh_fscnt]
def BehFscnt (sched : Nat → ThreadId) (γ : Nat → ThreadId → Nat) : TrProp C :=
  □ₜ ∀ₜ i : ThreadId, inactive i ∨ₜ
    (active i ∧ₜ (TrProp.atPos (fun n => sched n = i) ∨ₜ TrProp.atPos fun n => γ (n + 1) i < γ n i))

#lantana_ignore fscnt_next_rel_th
  "the counters are global along the run under the schedule; the next-position relation is `BehFscnt` at one position"
#lantana_ignore fscnt_next_rel
  "the counters are global along the run under the schedule; the next-position relation is `BehFscnt` at one position"
#lantana_ignore exists_fscnt_next
  "the counters are global along the run under the schedule; the next-position relation is `BehFscnt` at one position"

variable {τ : Trace C} {sched : Nat → ThreadId} {γ : Nat → ThreadId → Nat}

/-- The counters, unfolded at a position: the form the adequacy proof reads. -/
theorem behFscnt_iff : BehFscnt sched γ τ ↔
    ∀ m, τ.pos ≤ m → ∀ i, ¬ ThreadSystem.active i (τ.seq m) ∨
      (ThreadSystem.active i (τ.seq m) ∧ (sched m = i ∨ γ (m + 1) i < γ m i)) :=
  Iff.rfl

/-- Layer 0's counters of the threads' scheduling pairs under a schedule are fairness counters:
at a position where the thread is active and not named the counter drops by one. -/
theorem behFscnt_of_counters {δ : ThreadId → Nat → Nat}
    (hδ : ∀ i, Fairness.AttemptGrant.IsCounter (active i) (TrProp.atPos fun n => sched n = i)
      (δ i) τ) :
    BehFscnt sched (fun m i => δ i m) τ := by
  refine behFscnt_iff.mpr fun m hm i => ?_
  by_cases hA : ThreadSystem.active i (τ.seq m)
  · refine .inr ⟨hA, ?_⟩
    by_cases hs : sched m = i
    · exact .inl hs
    · have hdrop := Fairness.AttemptGrant.counter_drop (τ := { τ with pos := m })
        ((hδ i).mono hm) hA hs
      right
      dsimp only at hdrop ⊢
      omega
  · exact .inl hA

/-- Under a schedule that names every thread active infinitely often infinitely often while it is
active, the run has fairness counters: for each thread, the counter of its scheduling pair. -/
theorem exists_behFscnt_of_fair_schedule
    (hfair : ∀ i, (□ₜ ◇ₜ active i) τ →
      (□ₜ ◇ₜ (active i ∧ₜ TrProp.atPos fun n => sched n = i)) τ) :
    ∃ γ, BehFscnt sched γ τ :=
  ⟨fun m i => Classical.choose (Fairness.Sched.exists_counter_of_fair_schedule (hfair i)) m,
    behFscnt_of_counters fun i =>
      Classical.choose_spec (Fairness.Sched.exists_counter_of_fair_schedule (hfair i))⟩

/-- A behavior on which every thread is fairly scheduled admits a fair schedule and fairness
counters under it (Rocq `fair_scheduling_fscnt`; classical): the schedule from the fair-labelling
theorem, the counters from layer 0's counter of the scheduling pair read under the schedule. -/
@[lantana_alias fair_scheduling_fscnt]
theorem exists_fair_schedule_behFscnt (hrun : IsBehavior τ) (hsf : fairScheduling τ) :
    ∃ (sched : Nat → ThreadId) (γ : Nat → ThreadId → Nat),
      Schedule sched τ ∧ BehFscnt sched γ τ := by
  obtain ⟨sched, hsch, hfair⟩ := Fairness.exists_fair_schedule hrun hsf
  obtain ⟨γ, hγ⟩ := exists_behFscnt_of_fair_schedule hfair
  exact ⟨sched, γ, hsch, hγ⟩

/-- Where a thread's activity is convex, its fair scheduling is weak fairness, the usual justice
requirement. -/
theorem fairScheduling_sf_iff_wf {i : ThreadId}
    (hconv : Fairness.Action.Convex (ThreadSystem.active i) τ) :
    Fairness.Sched.SF i τ ↔
      Fairness.Action.WF (ThreadSystem.active i) (ThreadSystem.Step i) τ :=
  Fairness.Action.sf_iff_wf_of_convex hconv

end Lantana
