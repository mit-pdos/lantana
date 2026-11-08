/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Prelude.Ids
public import Lantana.ProgramLogic.Language

/-! # Configurations, traces and behaviors

The trace part of Rocq `lantana/program_logic/language.v`. A thread pool is a list of
expressions and a thread id is a position in it (D14); a step of thread `i` replaces its
expression and appends the forked threads, so forked threads get fresh ids. A trace is a
position in an infinite sequence of trace states (a configuration and the thread scheduled
there); a behavior is a trace along which the scheduled thread steps, or stutters if it is a
value or stuck. Both are plain `∀`-statements over positions: no coinduction (D18). A trace
step is a step of the scheduled thread (`TraceStepOf`), and activity is a property of the
configuration (`Cfg.active`).
-/

@[expose] public section

namespace Lantana

open Iris.ProgramLogic (toVal)


/-- The thread pool: the expression of every thread, by id. -/
@[lantana_alias thread_pool]
abbrev ThreadPool (Expr : Type) := List Expr

/-- A configuration: the thread pool and the state. -/
@[lantana_alias cfg]
abbrev Cfg (Expr : Type) (State : Type) := ThreadPool Expr × State

section
variable {Expr : Type} {State : Type} {Val : Type} [Λ : Language Expr State Val]

/-- A step of thread `i`: its expression steps, the forked threads are appended to the pool
(and are never removed). -/
@[lantana_alias thread_step]
inductive ThreadStep (i : ThreadId) : Cfg Expr State → Cfg Expr State → Prop where
  | step {tp : ThreadPool Expr} {σ : State} {e₁ e₂ : Expr} {σ₂ : State} {efs : List Expr} :
    tp[i]? = some e₁ → primStep e₁ σ e₂ σ₂ efs →
    ThreadStep i (tp, σ) (tp.set i e₂ ++ efs, σ₂)

/-- The scheduled thread `i` is a value: the configuration stutters. -/
@[lantana_alias thread_done]
def ThreadDone (i : ThreadId) (ρ₁ ρ₂ : Cfg Expr State) : Prop :=
  ∃ e, ρ₁.1[i]? = some e ∧ (toVal e).isSome ∧ ρ₂ = ρ₁

/-- The scheduled thread `i` is stuck: the configuration stutters. Stuck executions are
behaviors too; adequacy shows that verified programs never take a stuck step. -/
@[lantana_alias thread_stuck]
def ThreadStuck (i : ThreadId) (ρ₁ ρ₂ : Cfg Expr State) : Prop :=
  ∃ e, ρ₁.1[i]? = some e ∧ Language.Stuck e ρ₁.2 ∧ ρ₂ = ρ₁

/-- A trace step of thread `i`: its primitive step, or its stutter as a value or when stuck. -/
def TraceStepOf (i : ThreadId) (ρ₁ ρ₂ : Cfg Expr State) : Prop :=
  ThreadStep i ρ₁ ρ₂ ∨ ThreadDone i ρ₁ ρ₂ ∨ ThreadStuck i ρ₁ ρ₂

end

/-- A trace state: a configuration and the thread scheduled at it. -/
@[lantana_alias trace_state]
structure TraceState (Expr : Type) (State : Type) where
  cfg : Cfg Expr State
  thread : ThreadId

/-- A trace: a position in an infinite sequence of trace states. -/
@[lantana_alias trace]
structure Trace (Expr : Type) (State : Type) where
  pos : Nat
  seq : Nat → TraceState Expr State

namespace Trace

variable {Expr : Type} {State : Type}

/-- The trace one position later. -/
@[lantana_alias trace_next]
def next (τ : Trace Expr State) : Trace Expr State := { τ with pos := τ.pos + 1 }

/-- The current trace state. -/
@[lantana_alias trace_now]
def now (τ : Trace Expr State) : TraceState Expr State := τ.seq τ.pos

/-- The thread scheduled at the current position. -/
@[lantana_alias trace_thread]
def thread (τ : Trace Expr State) : ThreadId := τ.now.thread

/-- The current configuration. -/
def cfg (τ : Trace Expr State) : Cfg Expr State := τ.now.cfg

@[simp] theorem next_pos (τ : Trace Expr State) : τ.next.pos = τ.pos + 1 := rfl
@[simp] theorem next_seq (τ : Trace Expr State) : τ.next.seq = τ.seq := rfl
@[simp] theorem now_next (τ : Trace Expr State) : τ.next.now = τ.seq (τ.pos + 1) := rfl

end Trace

section
variable {Expr : Type} {State : Type} {Val : Type} [Λ : Language Expr State Val]

/-- One step of a behavior: a trace step of the scheduled thread (it steps, or stutters because
it is a value or stuck); the next scheduled thread is arbitrary. -/
def TraceStep (s₁ s₂ : TraceState Expr State) : Prop :=
  TraceStepOf s₁.thread s₁.cfg s₂.cfg

/-- A trace step is the trace step of the scheduled thread. -/
theorem TraceStep_iff {s₁ s₂ : TraceState Expr State} :
    TraceStep s₁ s₂ ↔ TraceStepOf s₁.thread s₁.cfg s₂.cfg := Iff.rfl

/-- A behavior: from the current position on, every position is followed by a `TraceStep`. -/
@[lantana_alias behavior]
def IsBehavior (τ : Trace Expr State) : Prop :=
  ∀ m, τ.pos ≤ m → TraceStep (τ.seq m) (τ.seq (m + 1))

@[lantana_alias behavior_S]
theorem IsBehavior.next {τ : Trace Expr State} (h : IsBehavior τ) : IsBehavior τ.next :=
  fun m hm => h m (Nat.le_of_succ_le hm)

/-- Along a behavior, every configuration from the current position on is followed by a trace
step of some thread. -/
theorem IsBehavior.exists_traceStepOf {τ : Trace Expr State} (h : IsBehavior τ) {m : Nat}
    (hm : τ.pos ≤ m) : ∃ j, TraceStepOf j (τ.seq m).cfg (τ.seq (m + 1)).cfg :=
  ⟨_, h m hm⟩

/-- The behaviors starting from the configuration `ρ`. -/
@[lantana_alias behavior_cfg]
def IsBehaviorOf (ρ : Cfg Expr State) (τ : Trace Expr State) : Prop :=
  (τ.seq 0).cfg = ρ ∧ IsBehavior τ

/-- The behaviors starting from the thread pool `tp` (in any state). -/
@[lantana_alias behavior_tp]
def IsBehaviorOfPool (tp : ThreadPool Expr) (τ : Trace Expr State) : Prop :=
  ∃ σ, IsBehaviorOf (tp, σ) τ

/-! ## Threads at a configuration or a trace state -/

/-- Thread `i` is active at `ρ`: in the pool and not a value. -/
def Cfg.active (i : ThreadId) (ρ : Cfg Expr State) : Prop :=
  ∃ e, ρ.1[i]? = some e ∧ toVal e = none

/-- Thread `i` is not active at `ρ`: not in the pool, or a value. -/
def Cfg.inactive (i : ThreadId) (ρ : Cfg Expr State) : Prop :=
  ρ.1[i]? = none ∨ ∃ e, ρ.1[i]? = some e ∧ (toVal e).isSome

theorem Cfg.active_or_inactive (i : ThreadId) (ρ : Cfg Expr State) :
    ρ.active i ∨ ρ.inactive i := by
  rcases h : ρ.1[i]? with _ | e
  · exact .inr (.inl h)
  · rcases hv : toVal e with _ | v
    · exact .inl ⟨e, h, hv⟩
    · exact .inr (.inr ⟨e, h, by simp [hv]⟩)

theorem Cfg.not_active_and_inactive (i : ThreadId) (ρ : Cfg Expr State) :
    ¬ (ρ.active i ∧ ρ.inactive i) := by
  rintro ⟨⟨e, he, hv⟩, h | ⟨e', he', hv'⟩⟩
  · simp [he] at h
  · simp [he] at he'
    subst he'
    simp [hv] at hv'

/-- Thread `i` is active at `s`: in the pool and not a value. -/
@[lantana_alias thread_active]
def TraceState.active (i : ThreadId) (s : TraceState Expr State) : Prop :=
  ∃ e, s.cfg.1[i]? = some e ∧ toVal e = none

/-- Thread `i` is not active at `s`: not in the pool, or a value. -/
@[lantana_alias thread_na]
def TraceState.inactive (i : ThreadId) (s : TraceState Expr State) : Prop :=
  s.cfg.1[i]? = none ∨ ∃ e, s.cfg.1[i]? = some e ∧ (toVal e).isSome

/-- Thread `i` is scheduled at `s`. -/
@[lantana_alias thread_turn]
def TraceState.turn (i : ThreadId) (s : TraceState Expr State) : Prop := s.thread = i

@[lantana_alias thread_active_or_not]
theorem TraceState.active_or_inactive (i : ThreadId) (s : TraceState Expr State) :
    s.active i ∨ s.inactive i := by
  rcases h : s.cfg.1[i]? with _ | e
  · exact .inr (.inl h)
  · rcases hv : toVal e with _ | v
    · exact .inl ⟨e, h, hv⟩
    · exact .inr (.inr ⟨e, h, by simp [hv]⟩)

@[lantana_alias thread_active_and_not_false]
theorem TraceState.not_active_and_inactive (i : ThreadId) (s : TraceState Expr State) :
    ¬ (s.active i ∧ s.inactive i) := by
  rintro ⟨⟨e, he, hv⟩, h | ⟨e', he', hv'⟩⟩
  · simp [he] at h
  · simp [he] at he'
    subst he'
    simp [hv] at hv'

/-- Activity at a trace state is activity at its configuration. -/
theorem TraceState.active_iff {i : ThreadId} {s : TraceState Expr State} :
    s.active i ↔ s.cfg.active i := Iff.rfl

/-- Inactivity at a trace state is inactivity at its configuration. -/
theorem TraceState.inactive_iff {i : ThreadId} {s : TraceState Expr State} :
    s.inactive i ↔ s.cfg.inactive i := Iff.rfl

/-! ## Facts about trace steps -/

section Facts
variable {i j : ThreadId} {ρ₁ ρ₂ : Cfg Expr State} {e : Expr}

/-- A step never shrinks the pool. -/
theorem ThreadStep.length_le (hs : ThreadStep i ρ₁ ρ₂) : ρ₁.1.length ≤ ρ₂.1.length := by
  cases hs with
  | step _ _ => simp

/-- A trace step never shrinks the pool (the stutters keep it). -/
theorem TraceStepOf.length_le (hs : TraceStepOf j ρ₁ ρ₂) : ρ₁.1.length ≤ ρ₂.1.length := by
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
theorem TraceStepOf.get?_ne (hs : TraceStepOf j ρ₁ ρ₂) (hji : j ≠ i) (he : ρ₁.1[i]? = some e) :
    ρ₂.1[i]? = some e := by
  rcases hs with hs | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
  · exact hs.get?_ne hji he
  · exact he
  · exact he

/-- A value entry is never rewritten, by any thread's trace step: a value does not step. -/
theorem TraceStepOf.get?_of_val (hs : TraceStepOf j ρ₁ ρ₂) (he : ρ₁.1[i]? = some e)
    (hv : (toVal e).isSome) : ρ₂.1[i]? = some e := by
  by_cases hji : j = i
  · subst hji
    rcases hs with hs | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
    · cases hs with
      | step hj hprim =>
        dsimp only at he
        rw [hj] at he
        cases he
        simp [val_stuck hprim] at hv
    · exact he
    · exact he
  · exact hs.get?_ne hji he

/-- Entries are never removed by a trace step. -/
theorem TraceStepOf.isSome_of_isSome (hs : TraceStepOf j ρ₁ ρ₂) (h : (ρ₁.1[i]?).isSome) :
    (ρ₂.1[i]?).isSome := by
  simp only [isSome_getElem?] at h ⊢
  exact Nat.lt_of_lt_of_le h hs.length_le

/-- A trace step of another thread keeps thread `i` active. -/
theorem Cfg.active_of_step_ne (hs : TraceStepOf j ρ₁ ρ₂) (hji : j ≠ i) (h : ρ₁.active i) :
    ρ₂.active i :=
  let ⟨e, he, hv⟩ := h
  ⟨e, hs.get?_ne hji he, hv⟩

/-- A thread in the pool that is inactive (so a value) stays inactive after any trace step. A
missing entry may be filled by a fork, hence the `isSome` hypothesis. -/
theorem Cfg.inactive_of_step_of_isSome (hs : TraceStepOf j ρ₁ ρ₂) (hsome : (ρ₁.1[i]?).isSome)
    (h : ρ₁.inactive i) : ρ₂.inactive i := by
  rcases h with h | ⟨e, he, hv⟩
  · simp [h] at hsome
  · exact .inr ⟨e, hs.get?_of_val he hv, hv⟩

end Facts

/-! ## Threads along a run -/

section Run
variable {σ : Nat → Cfg Expr State} {i : ThreadId}

/-- Along a run of trace steps, an entry, once in the pool, stays in it. -/
theorem Cfg.isSome_mono (hrun : ∀ n, ∃ j, TraceStepOf j (σ n) (σ (n + 1))) {n k : Nat}
    (hnk : n ≤ k) : ((σ n).1[i]?).isSome → ((σ k).1[i]?).isSome := by
  intro h
  induction hnk with
  | refl => exact h
  | step _ ih =>
    obtain ⟨_, hs⟩ := hrun _
    exact hs.isSome_of_isSome ih

/-- Along a run of trace steps, a thread in the pool that is inactive stays inactive. -/
theorem Cfg.inactive_mono_of_isSome (hrun : ∀ n, ∃ j, TraceStepOf j (σ n) (σ (n + 1)))
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
theorem Cfg.active_convex (hrun : ∀ n, ∃ j, TraceStepOf j (σ n) (σ (n + 1))) :
    ∀ n m k, n ≤ m → m ≤ k → (σ n).active i → (σ k).active i → (σ m).active i := by
  intro n m k hnm hmk hn hk
  rcases Cfg.active_or_inactive i (σ m) with hm | hm
  · exact hm
  · obtain ⟨e, he, -⟩ := hn
    have hsome := Cfg.isSome_mono (i := i) hrun hnm (by simp [he])
    exact absurd ⟨hk, Cfg.inactive_mono_of_isSome hrun hmk hsome hm⟩
      (Cfg.not_active_and_inactive i (σ k))

end Run

end

end Lantana
