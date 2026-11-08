/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.TracePropRules

/-! # Thread systems and their behaviors

A thread system (`ThreadSystem C`) is a type of configurations with, for the thread at each
position, its trace step (its step, or its stutter) and its activity, both supplied by the
language. Over a thread system: the trace properties that the thread at `i` takes a trace step
(`Steps i`), is active (`active i`) or inactive (`inactive i`); a behavior of the thread system
(`IsBehavior`), along which some thread takes a trace step at every position from the current
one on; a schedule (`Schedule sched`), naming the stepping thread at each position.
Traces carry no thread label: the schedule is a proof instrument. The class has no laws; what a
proof needs of an instance is a hypothesis. Lantana's language is an instance
(`Lantana.ProgramLogic.Configuration`).
-/

@[expose] public section

namespace Lantana

/-- A thread system: configurations with the trace step of the thread at each position (its
step, or its stutter) and the activity predicate the language supplies. -/
class ThreadSystem (C : Type) where
  /-- The trace step of the thread at position `i`, from one configuration to the next. -/
  Step : ThreadId → C → C → Prop
  /-- The thread at position `i` is active at a configuration. -/
  active : ThreadId → C → Prop

section

variable {C : Type} [ThreadSystem C]

open scoped TrProp

/-- The thread at `i` takes a trace step at the current position. -/
def Steps (i : ThreadId) : TrProp C := TrProp.step (ThreadSystem.Step i)

/-- The thread at `i` is active at the current configuration. -/
def active (i : ThreadId) : TrProp C := TrProp.now (ThreadSystem.active i)

/-- The thread at `i` is inactive at the current configuration. -/
def inactive (i : ThreadId) : TrProp C := ¬ₜ active i

/-- A behavior of the thread system: from the current position on, some thread takes a trace
step at every position. -/
@[lantana_alias behavior]
def IsBehavior : TrProp C := □ₜ ∃ₜ i, Steps i

/-- The behaviors starting from the configuration `ρ`. -/
@[lantana_alias behavior_cfg]
def IsBehaviorOf (ρ : C) : TrProp C := fun τ => τ.seq 0 = ρ ∧ IsBehavior τ

/-- The schedule `sched` names the stepping thread at every position from the current one on. -/
def Schedule (sched : Nat → ThreadId) : TrProp C :=
  □ₜ (fun τ => ThreadSystem.Step (sched τ.pos) τ.now τ.next.now)

/-- The thread at `i` takes a trace step infinitely often. -/
def StepsInfOften (i : ThreadId) : TrProp C := □ₜ ◇ₜ Steps i

variable {i : ThreadId} {τ : Trace C}

theorem steps_iff : Steps i τ ↔ ThreadSystem.Step i τ.now τ.next.now := Iff.rfl

theorem active_iff : active i τ ↔ ThreadSystem.active i τ.now := Iff.rfl

theorem inactive_iff : inactive i τ ↔ ¬ ThreadSystem.active i τ.now := Iff.rfl

theorem isBehavior_iff :
    IsBehavior τ ↔
      ∀ m, τ.pos ≤ m → ∃ i, ThreadSystem.Step i (τ.seq m) (τ.seq (m + 1)) :=
  Iff.rfl

theorem schedule_iff {sched : Nat → ThreadId} :
    Schedule sched τ ↔
      ∀ m, τ.pos ≤ m → ThreadSystem.Step (sched m) (τ.seq m) (τ.seq (m + 1)) :=
  Iff.rfl

theorem stepsInfOften_iff :
    StepsInfOften i τ ↔
      ∀ n, τ.pos ≤ n → ∃ m, n ≤ m ∧ ThreadSystem.Step i (τ.seq m) (τ.seq (m + 1)) :=
  TrProp.always_eventually_iff

@[lantana_alias behavior_S]
theorem IsBehavior.next (h : IsBehavior τ) : IsBehavior τ.next := TrProp.always_next τ h

/-- A behavior is a behavior from every later position. -/
theorem IsBehavior.always (h : IsBehavior τ) : (□ₜ IsBehavior) τ := TrProp.always_idemp τ h

end

end Lantana
