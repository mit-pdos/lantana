/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TracePropRules
public import Lantana.Trace.Fairness

/-! # Fair scheduling

Every thread active infinitely often steps infinitely often (Rocq `fair_scheduling.v`), stated
as an action of the attempt–grant model (`Lantana.Trace.Fairness`).  Lantana's configurations
are a pool whose step for the thread at `i` is its trace step `TraceStep i`: a primitive step, or
a stutter as a value or when stuck.  Fair scheduling of a thread is the strong fairness of its
scheduling action, enabled where the thread is active (`Cfg.active`) and granted at its trace
step (`Fairness.Sched.SF`), and `fairScheduling` asks it of every thread.  It is a statement about
the run that names no scheduled thread: traces carry no thread label.  Activity is convex along a
run, so it is the usual justice requirement, weak fairness (`fairScheduling_sf_iff_wf`).

The schedule is the adequacy proof's internal instrument.  The fair-labelling theorem
(`Fairness.exists_fair_schedule`) chooses a schedule of a run, the stepping thread at each
position, that names every thread active infinitely often infinitely often while it is active.
The fairness counters that the adequacy proof threads (Rocq `beh_fscnt`, a coinductive predicate
on the counters of one position, obtained by choice) are an explicit sequence of counters along
the run under that schedule (D18): `BehFscnt σ sched γ` says that while a thread is active and
not named by the schedule its counter strictly decreases.  A fair run has a schedule with such
counters (`exists_fair_schedule_behFscnt`), each thread's layer 0 counter of its scheduling pair.
-/

@[expose] public section

namespace Lantana


variable {Expr : Type} {State : Type} {Val : Type} [Λ : Language Expr State Val]

open scoped TrProp

/-! ## Lantana's traces as a pool of the attempt–grant model

Lantana's configurations form a pool (`Fairness.Pool`) whose step for the thread at `i` is its
trace step `TraceStep i`.  A run of the pool is a sequence of configurations each followed by
some thread's trace step: the configurations of a behavior (`IsBehavior.poolRun`).  The
scheduling action's enabling condition is `Cfg.active`, which is convex along a run
(`Cfg.active_convex'`), so fair scheduling is weak fairness (`fairScheduling_sf_iff_wf`). -/

/-- Lantana's configurations are a pool of the attempt–grant model: the step of the thread at `i`
is its trace step (a primitive step, or a stutter as a value or when stuck). -/
instance : Fairness.Pool (Cfg Expr State) := ⟨TraceStep⟩

/-- The pool's step on Lantana's configurations is the trace step. -/
@[simp] theorem Fairness.Pool.step_def {i : ThreadId} {ρ₁ ρ₂ : Cfg Expr State} :
    Fairness.Pool.Step i ρ₁ ρ₂ = TraceStep i ρ₁ ρ₂ := rfl

/-- The configurations of a behavior from position `0` are a run of the pool. -/
theorem IsBehavior.poolRun {τ : Trace Expr State} (h : IsBehavior τ) (hpos : τ.pos = 0) :
    Fairness.PoolRun τ.seq :=
  fun n => h n (hpos ▸ Nat.zero_le n)

/-- Activity is convex along a run of the pool: a thread is active from its fork until it becomes
a value, and never again. -/
theorem Cfg.active_convex' {σ : Nat → Cfg Expr State} (hrun : Fairness.PoolRun σ)
    (i : ThreadId) : Fairness.Action.Convex (Cfg.active i) σ :=
  Cfg.active_convex hrun

/-- Fair scheduling of Lantana's threads is the usual justice requirement, weak fairness, since
activity is convex (a thread is active from its fork until it becomes a value). -/
theorem fairScheduling_sf_iff_wf {σ : Nat → Cfg Expr State} (hrun : Fairness.PoolRun σ)
    (i : ThreadId) :
    Fairness.Sched.SF Cfg.active i σ ↔
      Fairness.Action.WF (Cfg.active i) (Fairness.Sched.grant i) σ :=
  Fairness.Action.sf_iff_wf_of_convex (Cfg.active_convex' hrun i)

/-! ## Fair scheduling and the fairness counters (D18) -/

/-- Fair scheduling: the strong fairness of the scheduling action of every thread, enabled where
the thread is active and granted at its trace step (`Fairness.Sched.SF`).  A statement about the
run that names no scheduled thread; since activity is convex, it is the usual justice requirement
(`fairScheduling_sf_iff_wf`). -/
@[lantana_alias fair_scheduling]
def fairScheduling : TrProp Expr State := fun τ => ∀ i, Fairness.Sched.SF Cfg.active i τ.seq

@[lantana_alias fair_scheduling_next]
theorem fairScheduling_next {τ : Trace Expr State} (h : fairScheduling τ) :
    fairScheduling τ.next :=
  h

/-- Fairness counters of a run under a schedule (Rocq `beh_fscnt`): at every position, every thread
is inactive, or active and either named by the schedule or with a strictly decreasing counter. -/
@[lantana_alias beh_fscnt]
def BehFscnt (σ : Nat → Cfg Expr State) (sched : Nat → ThreadId) (γ : Nat → ThreadId → Nat) :
    Prop :=
  ∀ m i, (σ m).inactive i ∨ ((σ m).active i ∧ (sched m = i ∨ γ (m + 1) i < γ m i))

#lantana_ignore fscnt_next_rel_th
  "the counters are global along the run under the schedule; the next-position relation is `BehFscnt` at one position"
#lantana_ignore fscnt_next_rel
  "the counters are global along the run under the schedule; the next-position relation is `BehFscnt` at one position"
#lantana_ignore exists_fscnt_next
  "the counters are global along the run under the schedule; the next-position relation is `BehFscnt` at one position"

/-- Layer 0's counters of the threads' scheduling pairs under a schedule are fairness counters:
at a position where the thread is active and not named the counter drops by one. -/
theorem behFscnt_of_counters {σ : Nat → Cfg Expr State} {sched : Nat → ThreadId}
    {δ : ThreadId → Nat → Nat}
    (hδ : ∀ i, Fairness.AttemptGrant.IsCounter (fun n => (σ n).active i) (fun n => sched n = i)
      (δ i)) :
    BehFscnt σ sched (fun m i => δ i m) := by
  intro m i
  rcases Cfg.active_or_inactive i (σ m) with hA | hna
  · refine .inr ⟨hA, ?_⟩
    by_cases hs : sched m = i
    · exact .inl hs
    · have hdrop := Fairness.AttemptGrant.counter_drop (n := m) (hδ i) hA hs
      right
      dsimp only
      omega
  · exact .inl hna

/-- Under a schedule that names every thread active infinitely often infinitely often while it is
active, the run has fairness counters: for each thread, the counter of its scheduling pair. -/
theorem exists_behFscnt_of_fair_schedule {σ : Nat → Cfg Expr State}
    {sched : Nat → ThreadId}
    (hfair : ∀ i, Fairness.MissHit.InfOften (fun n => (σ n).active i) →
      Fairness.MissHit.InfOften (fun n => (σ n).active i ∧ sched n = i)) :
    ∃ γ, BehFscnt σ sched γ :=
  ⟨fun m i => Classical.choose
      (Fairness.Sched.exists_counter_of_fair_schedule (active := Cfg.active) (hfair i)) m,
    behFscnt_of_counters fun i => Classical.choose_spec
      (Fairness.Sched.exists_counter_of_fair_schedule (active := Cfg.active) (hfair i))⟩

/-- A run of the pool on which every thread is fairly scheduled admits a fair schedule and
fairness counters under it (Rocq `fair_scheduling_fscnt`; classical): the schedule from the
fair-labelling theorem, the counters from layer 0's counter of the scheduling pair read under the
schedule. -/
@[lantana_alias fair_scheduling_fscnt]
theorem exists_fair_schedule_behFscnt {σ : Nat → Cfg Expr State} (hrun : Fairness.PoolRun σ)
    (hsf : ∀ i, Fairness.Sched.SF Cfg.active i σ) :
    ∃ (sched : Nat → ThreadId) (γ : Nat → ThreadId → Nat),
      Fairness.Schedule σ sched ∧ BehFscnt σ sched γ := by
  obtain ⟨sched, hsch, hfair⟩ := Fairness.exists_fair_schedule hrun hsf
  obtain ⟨γ, hγ⟩ := exists_behFscnt_of_fair_schedule hfair
  exact ⟨sched, γ, hsch, hγ⟩

end Lantana
