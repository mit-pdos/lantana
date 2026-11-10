/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for the attempt–grant theory of fairness (`Lantana.Temporal.Fairness`): the main
theorems depend only on the standard axioms, the convex case on `propext` alone; the recipes and
fair scheduling as assumptions. -/

namespace LantanaTest.Fairness

/--
info: 'Lantana.Fairness.AttemptGrant.fair_iff_counter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.Fairness.AttemptGrant.fair_iff_counter

/--
info: 'Lantana.Fairness.FairnessAssumption.counter_of_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.Fairness.FairnessAssumption.counter_of_holds

/--
info: 'Lantana.Fairness.Action.sf_iff_counter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.Fairness.Action.sf_iff_counter

/--
info: 'Lantana.Fairness.Action.holds_weak' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.Fairness.Action.holds_weak

/-- info: 'Lantana.Fairness.Action.sf_iff_wf_of_convex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lantana.Fairness.Action.sf_iff_wf_of_convex

/--
info: 'Lantana.Fairness.Action.sf_iff_own_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.Fairness.Action.sf_iff_own_holds

/--
info: 'Lantana.Fairness.exists_fair_schedule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.Fairness.exists_fair_schedule

/--
info: 'Lantana.Fairness.Sched.exists_counter_of_fair_schedule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.Fairness.Sched.exists_counter_of_fair_schedule

/--
info: 'Lantana.exists_fair_schedule_schedCounters' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.exists_fair_schedule_schedCounters

/-- info: 'Lantana.Cfg.sched_sf_iff_wf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lantana.Cfg.sched_sf_iff_wf

open Lantana

/-- Fair scheduling is the strong fairness of every thread's scheduling action; it names no
scheduled thread. -/
example {C : Type} [ThreadSystem C] (τ : Trace C) :
    fairScheduling τ ↔ ∀ i, Fairness.Sched.SF i τ :=
  Iff.rfl

/-- Fair scheduling of a thread is a fairness assumption, the strong recipe of its scheduling
action. -/
example {C : Type} [ThreadSystem C] (τ : Trace C) (i : ThreadId) :
    (Fairness.Sched.assumption i).holds τ ↔ Fairness.Sched.SF i τ :=
  Fairness.Sched.holds_assumption

/-- The thread's own view of an action is an assumption, read by dot notation. -/
example {C : Type} [ThreadSystem C] (a : Fairness.Action C) (i : ThreadId) (τ : Trace C)
    (hown : a.OwnGrant i) (hsf : a.SF τ) : (a.own i).holds τ :=
  Fairness.Action.own_holds_of_sf hown τ hsf

/-! Lantana's configurations are a thread system, and fair scheduling of its threads is weak
fairness along a behavior. -/

section ThreadSystem

variable {Expr State Val : Type} [Language Expr State Val]

example : ThreadSystem (Cfg Expr State) := inferInstance

example (τ : Trace (Cfg Expr State)) (h : IsBehavior τ) (i : ThreadId) :
    Fairness.Sched.SF i τ ↔ Fairness.Action.WF (Fairness.Sched.action i) τ :=
  Cfg.sched_sf_iff_wf h i

end ThreadSystem

end LantanaTest.Fairness
