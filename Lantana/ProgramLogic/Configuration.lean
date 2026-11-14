/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Prelude.Ids
public import Lantana.Temporal
public import Lantana.ProgramLogic.Language

/-! # Configurations, thread steps, and Lantana's language as a thread system

The trace part of Rocq `lantana/program_logic/language.v`.  A configuration is a thread pool
and a state; a thread id is a position in the pool, and a step of thread `i` (`ThreadStep i`,
Iris-Lean's `primStep` with its observation existential) replaces its expression and appends
the forked threads, which so get fresh ids.  A trace step (`TraceStep i`) is a step, or a
stutter when the thread is a value or stuck.  The configurations are a thread system: the step
of the thread at `i` is `TraceStep i`, its activity `Cfg.active i` (in the pool and not a value),
which is convex along a behavior, so fair scheduling is weak fairness (`Cfg.sched_sf_iff_wf`).
The crashed threads of a configuration (`Cfg.crashed`) are those of its pool that the language
declares crashed in its state (`Crash`); they are the model's view of the crashed threads, and a
step keeps the statuses when `Cfg.crashed ρ₂ = Cfg.crashed ρ₁`.
-/

@[expose] public section

namespace Lantana

open Iris.ProgramLogic (toVal Language PrimStep)
open Iris.ProgramLogic.PrimStep (primStep)


/-- The thread pool: the expression of every thread, by id. -/
@[lantana_alias thread_pool]
abbrev ThreadPool (Expr : Type) := List Expr

/-- A configuration: the thread pool and the state. -/
@[lantana_alias cfg]
abbrev Cfg (Expr : Type) (State : Type) := ThreadPool Expr × State

section
variable {Expr State Obs Val : Type} [Λ : Language Expr State Obs Val]

/-- A step of thread `i`: its expression steps, the forked threads are appended to the pool
(and are never removed). -/
@[lantana_alias thread_step]
inductive ThreadStep (i : ThreadId) : Cfg Expr State → Cfg Expr State → Prop where
  | step {tp : ThreadPool Expr} {σ : State} {e₁ : Expr} {obs : List Obs} {e₂ : Expr}
      {σ₂ : State} {efs : List Expr} :
    tp[i]? = some e₁ → primStep (e₁, σ) obs (e₂, σ₂, efs) →
    ThreadStep i (tp, σ) (tp.set i e₂ ++ efs, σ₂)

/-- Thread `i` is a value: the configuration stutters. -/
@[lantana_alias thread_done]
def ThreadDone (i : ThreadId) (ρ₁ ρ₂ : Cfg Expr State) : Prop :=
  ∃ e, ρ₁.1[i]? = some e ∧ (toVal e).isSome ∧ ρ₂ = ρ₁

/-- Thread `i` is stuck: the configuration stutters. Stuck executions are behaviors too;
adequacy shows that verified programs never take a stuck step. -/
@[lantana_alias thread_stuck]
def ThreadStuck (i : ThreadId) (ρ₁ ρ₂ : Cfg Expr State) : Prop :=
  ∃ e, ρ₁.1[i]? = some e ∧ PrimStep.Stuck (e, ρ₁.2) ∧ ρ₂ = ρ₁

/-- A trace step of thread `i`: its primitive step, or its stutter as a value or when stuck. -/
def TraceStep (i : ThreadId) (ρ₁ ρ₂ : Cfg Expr State) : Prop :=
  ThreadStep i ρ₁ ρ₂ ∨ ThreadDone i ρ₁ ρ₂ ∨ ThreadStuck i ρ₁ ρ₂

/-! ## Threads at a configuration -/

/-- Thread `i` is active at `ρ`: in the pool and not a value. -/
@[lantana_alias thread_active]
def Cfg.active (i : ThreadId) (ρ : Cfg Expr State) : Prop :=
  ∃ e, ρ.1[i]? = some e ∧ toVal e = none

/-- Thread `i` is not active at `ρ`: not in the pool, or a value. -/
@[lantana_alias thread_na]
def Cfg.inactive (i : ThreadId) (ρ : Cfg Expr State) : Prop :=
  ρ.1[i]? = none ∨ ∃ e, ρ.1[i]? = some e ∧ (toVal e).isSome

#lantana_ignore thread_turn
  "traces carry no thread label; the schedule is a proof instrument"

@[lantana_alias thread_active_or_not]
theorem Cfg.active_or_inactive (i : ThreadId) (ρ : Cfg Expr State) :
    ρ.active i ∨ ρ.inactive i := by
  rcases h : ρ.1[i]? with _ | e
  · exact .inr (.inl h)
  · rcases hv : toVal e with _ | v
    · exact .inl ⟨e, h, hv⟩
    · exact .inr (.inr ⟨e, h, by simp [hv]⟩)

@[lantana_alias thread_active_and_not_false]
theorem Cfg.not_active_and_inactive (i : ThreadId) (ρ : Cfg Expr State) :
    ¬ (ρ.active i ∧ ρ.inactive i) := by
  rintro ⟨⟨e, he, hv⟩, h | ⟨e', he', hv'⟩⟩
  · simp [he] at h
  · simp [he] at he'
    subst he'
    simp [hv] at hv'

/-- Inactivity is the negation of activity. -/
theorem Cfg.inactive_iff_not_active {i : ThreadId} {ρ : Cfg Expr State} :
    ρ.inactive i ↔ ¬ ρ.active i :=
  ⟨fun h ha => Cfg.not_active_and_inactive i ρ ⟨ha, h⟩,
    fun h => (Cfg.active_or_inactive i ρ).resolve_left h⟩

/-! ## Crashed threads -/

section Crashed
variable [Crash Expr State Obs Val]

/-- Thread `i` is crashed at `ρ`: in the pool, and crashed in the state by the language
(`Crash.crashed`). The configuration comes first, so that `ρ.crashed` is the model's view of the
crashed threads. -/
def Cfg.crashed (ρ : Cfg Expr State) (i : ThreadId) : Prop :=
  ∃ e, ρ.1[i]? = some e ∧ Crash.crashed e ρ.2

/-- A crashed thread is a thread of the pool. -/
theorem Cfg.crashed.lt_length {ρ : Cfg Expr State} {i : ThreadId} (h : ρ.crashed i) :
    i < ρ.1.length := by
  obtain ⟨e, he, -⟩ := h
  exact (List.getElem?_eq_some_iff.mp he).1

/-- No thread beyond the pool is crashed. -/
theorem Cfg.not_crashed_of_le {ρ : Cfg Expr State} {i : ThreadId} (h : ρ.1.length ≤ i) :
    ¬ ρ.crashed i :=
  fun hc => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hc.lt_length h)

/-- A crashed thread is not finished. -/
theorem Cfg.crashed.not_val {ρ : Cfg Expr State} {i : ThreadId} {e : Expr} (h : ρ.crashed i)
    (he : ρ.1[i]? = some e) : toVal e = none := by
  obtain ⟨e', he', hc⟩ := h
  rw [he] at he'
  cases he'
  exact Crash.crashed_not_val hc

/-- Two configurations have the same crashed threads when they agree on each: how a step that
keeps the statuses is stated (`Cfg.crashed ρ₂ = Cfg.crashed ρ₁`). -/
theorem Cfg.crashed_eq_of_iff {ρ₁ ρ₂ : Cfg Expr State} (h : ∀ j, ρ₂.crashed j ↔ ρ₁.crashed j) :
    Cfg.crashed ρ₂ = Cfg.crashed ρ₁ :=
  funext fun j => propext (h j)

/-- In a language that never crashes, all configurations have the same crashed threads (none),
so every step keeps the statuses. -/
theorem Cfg.crashed_eq_of_never (hnc : ∀ (e : Expr) (σ : State), ¬ Crash.crashed e σ)
    (ρ₁ ρ₂ : Cfg Expr State) : Cfg.crashed ρ₂ = Cfg.crashed ρ₁ :=
  Cfg.crashed_eq_of_iff fun _ =>
    ⟨fun ⟨e, _, hc⟩ => (hnc e _ hc).elim, fun ⟨e, _, hc⟩ => (hnc e _ hc).elim⟩

end Crashed

/-! ## Lantana's thread system -/

/-- Lantana's configurations are a thread system: the trace step of the thread at `i` is its
`TraceStep i` (a primitive step, or a stutter as a value or when stuck), its activity
`Cfg.active i`. -/
instance : ThreadSystem (Cfg Expr State) := ⟨TraceStep, Cfg.active⟩

/-- The thread system's step on Lantana's configurations is the trace step. -/
@[simp] theorem ThreadSystem.step_def {i : ThreadId} {ρ₁ ρ₂ : Cfg Expr State} :
    ThreadSystem.step i ρ₁ ρ₂ = TraceStep i ρ₁ ρ₂ := rfl

/-- The thread system's activity on Lantana's configurations is `Cfg.active`. -/
@[simp] theorem ThreadSystem.active_def {i : ThreadId} {ρ : Cfg Expr State} :
    ThreadSystem.active i ρ = ρ.active i := rfl

#lantana_ignore behavior_tp "adequacy fixes the initial configuration by `τ.seq 0 = ρ`"

/-! ## Facts about trace steps -/

section Facts
variable {i j : ThreadId} {ρ₁ ρ₂ : Cfg Expr State} {e : Expr}

/-- A step never shrinks the pool. -/
theorem ThreadStep.length_le (hs : ThreadStep i ρ₁ ρ₂) : ρ₁.1.length ≤ ρ₂.1.length := by
  cases hs with
  | step _ _ => simp

/-- A trace step never shrinks the pool (the stutters keep it). -/
theorem TraceStep.length_le (hs : TraceStep j ρ₁ ρ₂) : ρ₁.1.length ≤ ρ₂.1.length := by
  rcases hs with hs | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
  · exact hs.length_le
  · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- A step of thread `j` leaves the existing entry of another thread `i` in place. -/
theorem ThreadStep.get?_ne (hs : ThreadStep j ρ₁ ρ₂) (hji : j ≠ i) (he : ρ₁.1[i]? = some e) :
    ρ₂.1[i]? = some e := by
  cases hs with
  | step _ _ =>
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp he
    dsimp only at he ⊢
    rw [List.getElem?_append_left (by simpa using hi), List.getElem?_set_ne hji, he]

/-- A trace step of thread `j` leaves the existing entry of another thread `i` in place. -/
theorem TraceStep.get?_ne (hs : TraceStep j ρ₁ ρ₂) (hji : j ≠ i) (he : ρ₁.1[i]? = some e) :
    ρ₂.1[i]? = some e := by
  rcases hs with hs | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
  · exact hs.get?_ne hji he
  · exact he
  · exact he

/-- A value entry is never rewritten, by any thread's trace step: a value does not step. -/
theorem TraceStep.get?_of_val (hs : TraceStep j ρ₁ ρ₂) (he : ρ₁.1[i]? = some e)
    (hv : (toVal e).isSome) : ρ₂.1[i]? = some e := by
  by_cases hji : j = i
  · subst hji
    rcases hs with hs | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · cases hs with
      | step hj hprim =>
        dsimp only at he
        rw [hj] at he
        cases he
        simp [Language.val_stuck hprim] at hv
    · exact he
    · exact he
  · exact hs.get?_ne hji he

/-- Entries are never removed by a trace step. -/
theorem TraceStep.isSome_of_isSome (hs : TraceStep j ρ₁ ρ₂) (h : (ρ₁.1[i]?).isSome) :
    (ρ₂.1[i]?).isSome := by
  simp only [isSome_getElem?] at h ⊢
  exact Nat.lt_of_lt_of_le h hs.length_le

/-- A trace step of another thread keeps thread `i` active. -/
theorem Cfg.active_of_step_ne (hs : TraceStep j ρ₁ ρ₂) (hji : j ≠ i) (h : ρ₁.active i) :
    ρ₂.active i :=
  let ⟨e, he, hv⟩ := h
  ⟨e, hs.get?_ne hji he, hv⟩

/-- A thread in the pool that is inactive (so a value) stays inactive after any trace step. A
missing entry may be filled by a fork, hence the `isSome` hypothesis. -/
theorem Cfg.inactive_of_step_of_isSome (hs : TraceStep j ρ₁ ρ₂) (hsome : (ρ₁.1[i]?).isSome)
    (h : ρ₁.inactive i) : ρ₂.inactive i := by
  rcases h with h | ⟨e, he, hv⟩
  · simp [h] at hsome
  · exact .inr ⟨e, hs.get?_of_val he hv, hv⟩

end Facts

/-! ## Threads along a run -/

section Run
variable {σ : Nat → Cfg Expr State} {i : ThreadId}

/-- Along a run of trace steps, an entry, once in the pool, stays in it. -/
theorem Cfg.isSome_mono (hrun : ∀ n, ∃ j, TraceStep j (σ n) (σ (n + 1))) {n k : Nat}
    (hnk : n ≤ k) : ((σ n).1[i]?).isSome → ((σ k).1[i]?).isSome := by
  intro h
  induction hnk with
  | refl => exact h
  | step _ ih =>
    obtain ⟨_, hs⟩ := hrun _
    exact hs.isSome_of_isSome ih

/-- Along a run of trace steps, a thread in the pool that is inactive stays inactive. -/
theorem Cfg.inactive_mono_of_isSome (hrun : ∀ n, ∃ j, TraceStep j (σ n) (σ (n + 1)))
    {n k : Nat} (hnk : n ≤ k) :
    ((σ n).1[i]?).isSome → (σ n).inactive i → (σ k).inactive i := by
  intro hsome h
  induction hnk with
  | refl => exact h
  | step hle ih =>
    obtain ⟨_, hs⟩ := hrun _
    exact Cfg.inactive_of_step_of_isSome hs (Cfg.isSome_mono hrun hle hsome) ih

/-- **Convexity of activity**: along a run of trace steps, a thread active at two positions is
active at every position between them (once it stops, it never resumes). -/
theorem Cfg.active_convex (hrun : ∀ n, ∃ j, TraceStep j (σ n) (σ (n + 1))) :
    ∀ n m k, n ≤ m → m ≤ k → (σ n).active i → (σ k).active i → (σ m).active i := by
  intro n m k hnm hmk hn hk
  rcases Cfg.active_or_inactive i (σ m) with hm | hm
  · exact hm
  · obtain ⟨e, he, -⟩ := hn
    have hsome := Cfg.isSome_mono (i := i) hrun hnm (by simp [he])
    exact absurd ⟨hk, Cfg.inactive_mono_of_isSome hrun hmk hsome hm⟩
      (Cfg.not_active_and_inactive i (σ k))

end Run

/-! ## Fair scheduling of Lantana's threads

Fair scheduling (`fairScheduling`, `Lantana.Temporal.Fairness.Scheduling`) at Lantana's thread
system: the strong fairness of every thread's scheduling action, enabled where the thread is
active (`Cfg.active`) and granted at its trace step (`TraceStep`). Activity is convex along a
behavior, a thread being active from its fork until it becomes a value
(`Cfg.convex_of_isBehavior`), so fair scheduling of Lantana's threads is weak fairness
(`Cfg.sched_sf_iff_wf`).
-/

section Scheduling

open scoped TrProp

/-- Activity is convex along a behavior: a thread is active from its fork until it becomes a
value, and never again. -/
theorem Cfg.convex_of_isBehavior {i : ThreadId} :
    (IsBehavior : TrProp (Cfg Expr State)) ⊆
      Fairness.Action.Convex (Fairness.Sched.action i) := by
  intro τ hbeh m hm hA k hmk hev
  obtain ⟨k', hkk', hA'⟩ := TrProp.eventually_iff.mp hev
  have hrun : ∀ n, ∃ j, TraceStep j (τ.seq (m + n)) (τ.seq (m + n + 1)) :=
    fun n => isBehavior_iff.mp hbeh (m + n) (Nat.le_trans hm (Nat.le_add_right m n))
  have h := Cfg.active_convex (σ := fun n => τ.seq (m + n)) (i := i) hrun 0 (k - m) (k' - m)
    (Nat.zero_le _) (Nat.sub_le_sub_right hkk' m) (by simp only [Nat.add_zero]; exact hA)
    (by simp only [Nat.add_sub_cancel' (Nat.le_trans hmk hkk')]; exact hA')
  simp only [Nat.add_sub_cancel' hmk] at h
  exact h

/-- Fair scheduling of a thread of Lantana is weak fairness along a behavior, since activity is
convex. -/
theorem Cfg.sched_sf_iff_wf {τ : Trace (Cfg Expr State)} (hrun : IsBehavior τ)
    (i : ThreadId) :
    Fairness.Sched.SF i τ ↔ Fairness.Action.WF (Fairness.Sched.action i) τ :=
  Fairness.Action.sf_iff_wf_of_convex (Cfg.convex_of_isBehavior τ hrun)

end Scheduling

end

end Lantana
