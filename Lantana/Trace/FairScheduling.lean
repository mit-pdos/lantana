/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Prelude.Nat
public import Lantana.Trace.TracePropRules
public import Lantana.Trace.Fairness

/-! # Fair scheduling

Every active thread is eventually scheduled (Rocq `fair_scheduling.v`). The fairness counter
that the adequacy proof threads (Rocq `beh_fscnt`, a coinductive predicate on the counters of
one position, obtained by choice) is an explicit sequence of counters along the trace (D18):
`BehFscnt τ γ` says that while a thread is active and not scheduled its counter strictly
decreases. A fair trace has one (`fairScheduling_behFscnt`, classical: the distance to the next
turn), and the counters of consecutive positions are related by `fscntNextRel`.

The last section makes Lantana's configurations a pool of the attempt–grant model
(`Lantana.Trace.Fairness`), the pool's step being the trace step `TraceStepOf`.  There fair
scheduling of a thread is the scheduling action's strong fairness `Fairness.Sched.SF Cfg.active`,
which a thread's convex activity turns into weak fairness (`fairScheduling_sf_iff_wf`).  A run on
which every thread is fairly scheduled admits a fair schedule and fairness counters under it
(`exists_fair_schedule_behFscnt`), which are `BehFscnt` of the trace the schedule labels
(`behFscnt_of_behFscntSched`).
-/

@[expose] public section

namespace Lantana


variable {Expr : Type} {State : Type} {Val : Type} [Λ : Language Expr State Val]

open scoped TrProp

/-- Fair scheduling: at every position, every thread is inactive or active and eventually
scheduled. -/
@[lantana_alias fair_scheduling]
def fairScheduling : TrProp Expr State :=
  □ₜ (∀ₜ i : ThreadId, TrProp.now (TraceState.inactive i) ∨ₜ
    (TrProp.now (TraceState.active i) ∧ₜ ◇ₜ TrProp.now (TraceState.turn i)))

@[lantana_alias fair_scheduling_next]
theorem fairScheduling_next {τ : Trace Expr State} (h : fairScheduling τ) :
    fairScheduling τ.next :=
  fun m hm => h m (Nat.le_of_succ_le hm)

/-! ## The fairness counter (D18)

The least witnesses `Nat.minWitness` are in `Lantana.Prelude.Nat`. -/

/-- Fairness counters along a trace (Rocq `beh_fscnt`): from the current position on, every
thread is inactive, or active and either scheduled or with a strictly decreasing counter. -/
@[lantana_alias beh_fscnt]
def BehFscnt (τ : Trace Expr State) (γ : Nat → ThreadId → Nat) : Prop :=
  ∀ m, τ.pos ≤ m → ∀ i, (τ.seq m).inactive i ∨
    ((τ.seq m).active i ∧ ((τ.seq m).turn i ∨ γ (m + 1) i < γ m i))

theorem BehFscnt.next {τ : Trace Expr State} {γ : Nat → ThreadId → Nat} (h : BehFscnt τ γ) :
    BehFscnt τ.next γ :=
  fun m hm => h m (Nat.le_of_succ_le hm)

/-- The counters of a thread at a position and at the next one (Rocq `fscnt_next_rel_th`):
unconstrained if the thread is scheduled or inactive, otherwise strictly decreasing. -/
@[lantana_alias fscnt_next_rel_th]
def fscntNextRelTh (τ : Trace Expr State) (i : ThreadId) (c₁ c₂ : Nat) : Prop :=
  τ.now.turn i ∨ τ.now.inactive i ∨ c₂ < c₁

@[lantana_alias fscnt_next_rel]
def fscntNextRel (τ : Trace Expr State) (γ₁ γ₂ : ThreadId → Nat) : Prop :=
  ∀ i, fscntNextRelTh τ i (γ₁ i) (γ₂ i)

/-- The counters of the next position are related to the current ones
(Rocq `exists_fscnt_next`, without choice: the sequence is given). -/
@[lantana_alias exists_fscnt_next]
theorem BehFscnt.nextRel {τ : Trace Expr State} {γ : Nat → ThreadId → Nat} (h : BehFscnt τ γ) :
    fscntNextRel τ (γ τ.pos) (γ (τ.pos + 1)) := by
  intro i
  rcases h τ.pos (Nat.le_refl _) i with hna | ⟨-, hturn | hlt⟩
  · exact .inr (.inl hna)
  · exact .inl hturn
  · exact .inr (.inr hlt)

open Classical in
/-- The distance from position `m` to the next turn of the thread `i` if it is active there,
`0` otherwise, given that active threads are eventually scheduled. -/
noncomputable def turnDist (τ : Trace Expr State)
    (hex : ∀ m, τ.pos ≤ m → ∀ i, (τ.seq m).active i → ∃ s, (τ.seq (m + s)).turn i)
    (m : Nat) (i : ThreadId) : Nat :=
  if hmi : τ.pos ≤ m ∧ (τ.seq m).active i then Nat.minWitness (hex m hmi.1 i hmi.2) else 0

theorem turnDist_eq (τ : Trace Expr State)
    (hex : ∀ m, τ.pos ≤ m → ∀ i, (τ.seq m).active i → ∃ s, (τ.seq (m + s)).turn i)
    {m : Nat} {i : ThreadId} (hm : τ.pos ≤ m) (hact : (τ.seq m).active i) :
    turnDist τ hex m i = Nat.minWitness (hex m hm i hact) := by
  simp only [turnDist, hm, hact, and_self, dite_true]

theorem turnDist_eq_zero (τ : Trace Expr State)
    (hex : ∀ m, τ.pos ≤ m → ∀ i, (τ.seq m).active i → ∃ s, (τ.seq (m + s)).turn i)
    {m : Nat} {i : ThreadId} (hna : (τ.seq m).inactive i) : turnDist τ hex m i = 0 := by
  have hn : ¬ (τ.pos ≤ m ∧ (τ.seq m).active i) := fun hmi =>
    TraceState.not_active_and_inactive i _ ⟨hmi.2, hna⟩
  simp only [turnDist, hn, dite_false]

/-- A fair trace has fairness counters: the distance of each active thread to its next turn
(Rocq `fair_scheduling_fscnt`; classical). -/
@[lantana_alias fair_scheduling_fscnt]
theorem fairScheduling_behFscnt {τ : Trace Expr State} (h : fairScheduling τ) :
    ∃ γ : Nat → ThreadId → Nat, BehFscnt τ γ := by
  classical
  have hex : ∀ m, τ.pos ≤ m → ∀ i, (τ.seq m).active i → ∃ s, (τ.seq (m + s)).turn i := by
    intro m hm i hact
    rcases h m hm i with hna | ⟨-, k, hmk, hturn, -⟩
    · exact absurd ⟨hact, hna⟩ (TraceState.not_active_and_inactive i _)
    · exact ⟨k - m, by rw [Nat.add_sub_cancel' hmk]; exact hturn⟩
  refine ⟨turnDist τ hex, ?_⟩
  intro m hm i
  rcases TraceState.active_or_inactive i (τ.seq m) with hact | hna
  · refine .inr ⟨hact, ?_⟩
    by_cases hturn : (τ.seq m).turn i
    · exact .inl hturn
    · right
      rw [turnDist_eq τ hex hm hact]
      have hs₀ := Nat.minWitness_spec (hex m hm i hact)
      have hpos : 0 < Nat.minWitness (hex m hm i hact) := by
        rcases Nat.eq_zero_or_pos (Nat.minWitness (hex m hm i hact)) with h0 | h0
        · rw [h0] at hs₀
          exact absurd hs₀ hturn
        · exact h0
      rcases TraceState.active_or_inactive i (τ.seq (m + 1)) with hact' | hna'
      · rw [turnDist_eq τ hex (Nat.le_succ_of_le hm) hact']
        have hle : Nat.minWitness (hex (m + 1) (Nat.le_succ_of_le hm) i hact') ≤
            Nat.minWitness (hex m hm i hact) - 1 := by
          apply Nat.le_of_not_lt
          intro hlt
          apply Nat.minWitness_min _ hlt
          have heq : m + 1 + (Nat.minWitness (hex m hm i hact) - 1) =
              m + Nat.minWitness (hex m hm i hact) := by omega
          rw [heq]
          exact hs₀
        omega
      · rw [turnDist_eq_zero τ hex hna']
        exact hpos
  · exact .inl hna

/-! ## Lantana's traces as a pool of the attempt–grant model

Lantana's configurations form a pool (`Fairness.Pool`) whose step for the thread at `i` is its
trace step `TraceStepOf i`: a primitive step, or a stutter as a value or when stuck.  A run of the
pool is a sequence of configurations each followed by some thread's trace step, the configurations
of a behavior (`IsBehavior.poolRun`), and a schedule of a run labels it into a behavior
(`isBehavior_of_schedule`).  The scheduling action's enabling condition is `Cfg.active`, which is
convex along a run (`Cfg.active_convex'`), so fair scheduling is weak fairness
(`fairScheduling_sf_iff_wf`).  A fair schedule, chosen by the fair-labelling theorem
(`Fairness.exists_fair_schedule`), gives each thread layer 0's counter of its scheduling pair, and
these counters are fairness counters under the schedule (`BehFscntSched`,
`exists_fair_schedule_behFscnt`), Lantana's `BehFscnt` of the labelled trace
(`behFscnt_of_behFscntSched`). -/

/-- Lantana's configurations are a pool of the attempt–grant model: the step of the thread at `i`
is its trace step (a primitive step, or a stutter as a value or when stuck). -/
instance : Fairness.Pool (Cfg Expr State) := ⟨TraceStepOf⟩

/-- The pool's step on Lantana's configurations is the trace step. -/
@[simp] theorem Fairness.Pool.step_def {i : ThreadId} {ρ₁ ρ₂ : Cfg Expr State} :
    Fairness.Pool.Step i ρ₁ ρ₂ = TraceStepOf i ρ₁ ρ₂ := rfl

/-- The configurations of a behavior from position `0` are a run of the pool. -/
theorem IsBehavior.poolRun {τ : Trace Expr State} (h : IsBehavior τ) (hpos : τ.pos = 0) :
    Fairness.PoolRun (fun n => (τ.seq n).cfg) :=
  fun n => ⟨_, h n (hpos ▸ Nat.zero_le n)⟩

/-- A run of the pool labelled by a schedule, the stepping thread at each position, is a
behavior. -/
theorem isBehavior_of_schedule {σ : Nat → Cfg Expr State} {sched : Nat → ThreadId}
    (hsch : Fairness.Schedule σ sched) :
    IsBehavior (⟨0, fun n => ⟨σ n, sched n⟩⟩ : Trace Expr State) :=
  fun m _ => hsch m

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

/-- Fairness counters of a configuration run under a schedule: at every position, every thread is
inactive, or active and either named by the schedule or with a strictly decreasing counter.
`BehFscnt` of the trace labelled by the schedule. -/
def BehFscntSched (σ : Nat → Cfg Expr State) (sched : Nat → ThreadId)
    (γ : Nat → ThreadId → Nat) : Prop :=
  ∀ m i, (σ m).inactive i ∨ ((σ m).active i ∧ (sched m = i ∨ γ (m + 1) i < γ m i))

/-- Layer 0's counters of the threads' scheduling pairs under a schedule are fairness counters:
at a position where the thread is active and not named the counter drops by one. -/
theorem behFscntSched_of_counters {σ : Nat → Cfg Expr State} {sched : Nat → ThreadId}
    {δ : ThreadId → Nat → Nat}
    (hδ : ∀ i, Fairness.AttemptGrant.IsCounter (fun n => (σ n).active i) (fun n => sched n = i)
      (δ i)) :
    BehFscntSched σ sched (fun m i => δ i m) := by
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
theorem exists_behFscntSched_of_fair_schedule {σ : Nat → Cfg Expr State}
    {sched : Nat → ThreadId}
    (hfair : ∀ i, Fairness.MissHit.InfOften (fun n => (σ n).active i) →
      Fairness.MissHit.InfOften (fun n => (σ n).active i ∧ sched n = i)) :
    ∃ γ, BehFscntSched σ sched γ :=
  ⟨fun m i => Classical.choose
      (Fairness.Sched.exists_counter_of_fair_schedule (active := Cfg.active) (hfair i)) m,
    behFscntSched_of_counters fun i => Classical.choose_spec
      (Fairness.Sched.exists_counter_of_fair_schedule (active := Cfg.active) (hfair i))⟩

/-- A run of the pool on which every thread is fairly scheduled admits a fair schedule and
fairness counters under it: the schedule from the fair-labelling theorem, the counters from
layer 0's counter of the scheduling pair read under the schedule. -/
theorem exists_fair_schedule_behFscnt {σ : Nat → Cfg Expr State} (hrun : Fairness.PoolRun σ)
    (hsf : ∀ i, Fairness.Sched.SF Cfg.active i σ) :
    ∃ (sched : Nat → ThreadId) (γ : Nat → ThreadId → Nat),
      Fairness.Schedule σ sched ∧ BehFscntSched σ sched γ := by
  obtain ⟨sched, hsch, hfair⟩ := Fairness.exists_fair_schedule hrun hsf
  obtain ⟨γ, hγ⟩ := exists_behFscntSched_of_fair_schedule hfair
  exact ⟨sched, γ, hsch, hγ⟩

/-- Fairness counters under a schedule are `BehFscnt` of the trace that the schedule labels. -/
theorem behFscnt_of_behFscntSched {σ : Nat → Cfg Expr State} {sched : Nat → ThreadId}
    {γ : Nat → ThreadId → Nat} (h : BehFscntSched σ sched γ) :
    BehFscnt (⟨0, fun n => ⟨σ n, sched n⟩⟩ : Trace Expr State) γ :=
  fun m _ i => h m i

/-- A behavior from position `0` on which every thread is fairly scheduled can be relabelled, its
configurations kept, into a behavior with fairness counters. -/
theorem IsBehavior.exists_relabel_behFscnt {τ : Trace Expr State} (h : IsBehavior τ)
    (hpos : τ.pos = 0) (hsf : ∀ i, Fairness.Sched.SF Cfg.active i (fun n => (τ.seq n).cfg)) :
    ∃ τ' : Trace Expr State, τ'.pos = 0 ∧ (∀ n, (τ'.seq n).cfg = (τ.seq n).cfg) ∧
      IsBehavior τ' ∧ ∃ γ, BehFscnt τ' γ := by
  obtain ⟨sched, γ, hsch, hγ⟩ := exists_fair_schedule_behFscnt (h.poolRun hpos) hsf
  exact ⟨⟨0, fun n => ⟨(τ.seq n).cfg, sched n⟩⟩, rfl, fun _ => rfl, isBehavior_of_schedule hsch,
    γ, behFscnt_of_behFscntSched hγ⟩

end Lantana
