/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for the attempt–grant model of fairness over trace properties
(`Lantana.Temporal.Fairness`) and fair scheduling (`Lantana.Temporal.FairScheduling`): the main
theorems depend only on the standard axioms, some on fewer (`labelledView_of_sf` on none, the
convex case on `propext`); fairness assumptions (`Lantana.Temporal.Fairness.Assumption`). -/

namespace LantanaTest.Fairness

/--
info: 'Lantana.Fairness.AttemptGrant.fair_iff_counter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.Fairness.AttemptGrant.fair_iff_counter

/--
info: 'Lantana.Fairness.Action.sf_iff_counter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.Fairness.Action.sf_iff_counter

/--
info: 'Lantana.Fairness.Thread.sf_iff_attemptGrant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.Fairness.Thread.sf_iff_attemptGrant

/-- info: 'Lantana.Fairness.Action.sf_iff_wf_of_convex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lantana.Fairness.Action.sf_iff_wf_of_convex

/-- info: 'Lantana.Fairness.labelledView_of_sf' does not depend on any axioms -/
#guard_msgs in
#print axioms Lantana.Fairness.labelledView_of_sf

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
info: 'Lantana.exists_fair_schedule_behFscnt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.exists_fair_schedule_behFscnt

/-- info: 'Lantana.fairScheduling_sf_iff_wf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lantana.fairScheduling_sf_iff_wf

/-- info: 'Lantana.fairScheduling_sf_iff_wf'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lantana.fairScheduling_sf_iff_wf'

/--
info: 'Lantana.Fairness.Action.holds_weak' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.Fairness.Action.holds_weak

/--
info: 'Lantana.Fairness.Assumption.counter_of_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.Fairness.Assumption.counter_of_holds

open Lantana

/-- Fair scheduling is the strong fairness of every thread's scheduling action; it names no
scheduled thread. -/
example {C : Type} [ThreadSystem C] (τ : Trace C) :
    fairScheduling τ ↔ ∀ i, Fairness.Sched.SF i τ :=
  Iff.rfl

/-- Fair scheduling of a thread is a fairness assumption, the strong one of its scheduling
action. -/
example {C : Type} [ThreadSystem C] (τ : Trace C) (i : ThreadId) :
    (Fairness.Sched.assumption i).holds τ ↔ Fairness.Sched.SF i τ :=
  Fairness.Sched.holds_assumption

/-! Lantana's configurations are a thread system, and fair scheduling of its threads is weak
fairness along a behavior. -/

section ThreadSystem

variable {Expr State Val : Type} [Language Expr State Val]

example : ThreadSystem (Cfg Expr State) := inferInstance

example (τ : Trace (Cfg Expr State)) (h : IsBehavior τ) (i : ThreadId) :
    Fairness.Sched.SF i τ ↔ Fairness.Action.WF (Fairness.Sched.action i) τ :=
  fairScheduling_sf_iff_wf' h i

end ThreadSystem

end LantanaTest.Fairness
