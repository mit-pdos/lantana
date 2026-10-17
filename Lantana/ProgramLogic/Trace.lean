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
value or stuck. Both are plain `∀`-statements over positions: no coinduction (D18).
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

/-- One step of a behavior: the scheduled thread steps, or stutters because it is a value or
stuck; the next scheduled thread is arbitrary. -/
def TraceStep (s₁ s₂ : TraceState Expr State) : Prop :=
  ThreadStep s₁.thread s₁.cfg s₂.cfg ∨ ThreadDone s₁.thread s₁.cfg s₂.cfg ∨
    ThreadStuck s₁.thread s₁.cfg s₂.cfg

/-- A behavior: from the current position on, every position is followed by a `TraceStep`. -/
@[lantana_alias behavior]
def IsBehavior (τ : Trace Expr State) : Prop :=
  ∀ m, τ.pos ≤ m → TraceStep (τ.seq m) (τ.seq (m + 1))

@[lantana_alias behavior_S]
theorem IsBehavior.next {τ : Trace Expr State} (h : IsBehavior τ) : IsBehavior τ.next :=
  fun m hm => h m (Nat.le_of_succ_le hm)

/-- The behaviors starting from the configuration `ρ`. -/
@[lantana_alias behavior_cfg]
def IsBehaviorOf (ρ : Cfg Expr State) (τ : Trace Expr State) : Prop :=
  (τ.seq 0).cfg = ρ ∧ IsBehavior τ

/-- The behaviors starting from the thread pool `tp` (in any state). -/
@[lantana_alias behavior_tp]
def IsBehaviorOfPool (tp : ThreadPool Expr) (τ : Trace Expr State) : Prop :=
  ∃ σ, IsBehaviorOf (tp, σ) τ

/-! ## Threads at a trace state -/

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

end

end Lantana
