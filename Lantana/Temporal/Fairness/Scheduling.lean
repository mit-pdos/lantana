/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.ThreadSystem
public import Lantana.Temporal.Fairness.Action

/-! # Fair scheduling

Fair scheduling is one more action, `Sched.action i`, enabled where the thread is active and
granted at its trace step; `Sched.SF i` is its strong fairness and `Sched.assumption i` its
strong recipe.  `fairScheduling := ∀ₜ i, Sched.SF i` is the hypothesis of the adequacy theorems
and names no scheduled thread.  Under a schedule, the fairness counters of the run are
`SchedCounters`.  The Rocq counterpart is `fair_scheduling.v`.
See `docs/temporal.md`.
-/

@[expose] public section

namespace Lantana

open scoped Lantana.TrProp

variable {C : Type} [ThreadSystem C]

namespace Fairness.Sched

/-- The scheduling action of the thread at `i`: enabled where the thread is active, granted at its
trace step. -/
def action (i : ThreadId) : Action C := ⟨ThreadSystem.active i, ThreadSystem.step i⟩

/-- Fair scheduling of the thread at `i`: the strong fairness of its scheduling action. -/
abbrev SF (i : ThreadId) : TrProp C := (action i).SF

/-- Fair scheduling of the thread at `i` as an assumption: the strong recipe of its scheduling
action. -/
def assumption (i : ThreadId) : Assumption C := (action i).strong

variable {i : ThreadId} {τ : Trace C}

/-- The scheduling assumption of a thread holds exactly when the thread is fairly scheduled. -/
theorem holds_assumption : (assumption i).holds τ ↔ SF i τ := Action.holds_strong

/-- A thread active infinitely often and fairly scheduled steps infinitely often. -/
theorem stepOfInfOften_of_sf : (SF i ∧ₜ □ₜ ◇ₜ active i : TrProp C) ⊆ StepOfInfOften i :=
  fun τ ⟨hsf, hinf⟩ => TrProp.always_eventually_mono (fun _ h => h.2) τ (hsf hinf)

end Fairness.Sched

/-! ### Fair scheduling of the thread system -/

/-- Fair scheduling: the strong fairness of the scheduling action of every thread.  A statement
about the run that names no scheduled thread. -/
@[lantana_alias fair_scheduling]
def fairScheduling : TrProp C := ∀ₜ i : ThreadId, Fairness.Sched.SF i

/-- Fair scheduling is the same at every position of the run. -/
theorem fairScheduling_absolute : TrProp.Absolute (fairScheduling (C := C)) :=
  TrProp.absolute_all fun _ => Fairness.Action.sf_absolute

@[lantana_alias fair_scheduling_next]
theorem fairScheduling_next {τ : Trace C} (h : fairScheduling τ) : fairScheduling τ.next :=
  fairScheduling_absolute.next.mp h

/-! ### The fairness counters under a schedule -/

/-- Fairness counters of a run under a schedule: from the current position on, every thread is
inactive, or active and either named by the schedule or with a strictly decreasing counter. -/
@[lantana_alias beh_fscnt]
def SchedCounters (sched : Nat → ThreadId) (γ : Nat → ThreadId → Nat) : TrProp C :=
  □ₜ ∀ₜ i : ThreadId, inactive i ∨ₜ
    (active i ∧ₜ (scheduled sched i ∨ₜ TrProp.atPos fun n => γ (n + 1) i < γ n i))

#lantana_ignore fscnt_next_rel_th
  "the counters are an explicit sequence along the run under the schedule"
#lantana_ignore fscnt_next_rel
  "the counters are an explicit sequence along the run under the schedule"
#lantana_ignore exists_fscnt_next
  "the counters are an explicit sequence along the run under the schedule"

variable {τ : Trace C} {sched : Nat → ThreadId} {γ : Nat → ThreadId → Nat}

/-- The counters, unfolded at a position: the form the adequacy proof reads. -/
theorem schedCounters_iff : SchedCounters sched γ τ ↔
    ∀ m, τ.pos ≤ m → ∀ i, ¬ ThreadSystem.active i (τ.seq m) ∨
      (ThreadSystem.active i (τ.seq m) ∧ (sched m = i ∨ γ (m + 1) i < γ m i)) :=
  Iff.rfl

/-- The core's counters of the pairs (active, scheduled) of the threads are fairness counters: where
a thread is active and not named, its counter drops by one. -/
theorem schedCounters_of_counters {δ : ThreadId → Nat → Nat}
    (hδ : ∀ i, Fairness.AttemptGrant.IsCounter (active i) (scheduled sched i) (δ i) τ) :
    SchedCounters sched (fun m i => δ i m) τ := by
  refine schedCounters_iff.mpr fun m hm i => ?_
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

end Lantana
