/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.TracePropRules

/-! # Thread systems

The class `ThreadSystem C`: configurations with, for each thread id, the thread's trace step (its
step, or its stutter) and its activity.  Over it, the trace properties `stepOf i`, `active i`,
`inactive i` and `StepOfInfOften i`, the behaviors (`IsBehavior`), and the schedules
(`scheduled sched i`, `Schedule sched`): traces carry no thread label, and a schedule is a proof
instrument.
See `docs/temporal.md`.
-/

@[expose] public section

namespace Lantana

/-- A thread system: for each thread id, the thread's trace step (its step, or its stutter) and
its activity.  The class has no laws. -/
class ThreadSystem (C : Type) where
  /-- The trace step of the thread at `i`, from one configuration to the next. -/
  step : ThreadId → C → C → Prop
  /-- The thread at `i` is active at a configuration. -/
  active : ThreadId → C → Prop

section

variable {C : Type} [ThreadSystem C]

open scoped TrProp

/-- The thread at `i` takes a trace step at the current position. -/
def stepOf (i : ThreadId) : TrProp C := TrProp.step (ThreadSystem.step i)

/-- The thread at `i` is active at the current configuration. -/
def active (i : ThreadId) : TrProp C := TrProp.atomic (ThreadSystem.active i)

/-- The thread at `i` is inactive at the current configuration. -/
def inactive (i : ThreadId) : TrProp C := ¬ₜ active i

/-- A behavior of the thread system: some thread takes a trace step at every position from the
current one on. -/
@[lantana_alias behavior]
def IsBehavior : TrProp C := □ₜ ∃ₜ i, stepOf i

#lantana_ignore behavior_cfg "adequacy fixes the initial configuration by `τ.seq 0 = ρ`"

/-- The thread at `i` takes a trace step infinitely often. -/
def StepOfInfOften (i : ThreadId) : TrProp C := □ₜ ◇ₜ stepOf i

/-- The schedule `sched` names the thread at `i` at the current position. -/
def scheduled (sched : Nat → ThreadId) (i : ThreadId) : TrProp C :=
  TrProp.atPos fun n => sched n = i

/-- The thread the schedule `sched` names takes a trace step at every position from the current
one on. -/
def Schedule (sched : Nat → ThreadId) : TrProp C := □ₜ ∃ₜ i, scheduled sched i ∧ₜ stepOf i

variable {i : ThreadId} {τ : Trace C}

theorem stepOf_iff : stepOf i τ ↔ ThreadSystem.step i τ.now τ.next.now := Iff.rfl

theorem active_iff : active i τ ↔ ThreadSystem.active i τ.now := Iff.rfl

theorem inactive_iff : inactive i τ ↔ ¬ ThreadSystem.active i τ.now := Iff.rfl

theorem isBehavior_iff :
    IsBehavior τ ↔
      ∀ m, τ.pos ≤ m → ∃ i, ThreadSystem.step i (τ.seq m) (τ.seq (m + 1)) :=
  Iff.rfl

theorem stepOfInfOften_iff :
    StepOfInfOften i τ ↔
      ∀ n, τ.pos ≤ n → ∃ m, n ≤ m ∧ ThreadSystem.step i (τ.seq m) (τ.seq (m + 1)) :=
  TrProp.always_eventually_iff

theorem schedule_iff {sched : Nat → ThreadId} :
    Schedule sched τ ↔
      ∀ m, τ.pos ≤ m → ThreadSystem.step (sched m) (τ.seq m) (τ.seq (m + 1)) :=
  forall_congr' fun _ => imp_congr_right fun _ =>
    ⟨fun ⟨_, (hi : sched _ = _), hs⟩ => hi ▸ hs, fun hs => ⟨_, rfl, hs⟩⟩

@[lantana_alias behavior_S]
theorem IsBehavior.next (h : IsBehavior τ) : IsBehavior τ.next := TrProp.always_next τ h

/-- A behavior is a behavior from every later position. -/
theorem IsBehavior.always (h : IsBehavior τ) : (□ₜ IsBehavior) τ := TrProp.always_idemp τ h

end

end Lantana
