/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for the attempt–grant model of fairness: its main theorems depend only on the standard
axioms (`Action.sf_iff_wf_of_convex` on none). -/

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

/-- info: 'Lantana.Fairness.Action.sf_iff_wf_of_convex' does not depend on any axioms -/
#guard_msgs in
#print axioms Lantana.Fairness.Action.sf_iff_wf_of_convex

/--
info: 'Lantana.Fairness.labelledView_of_sf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
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

/-! Lantana's traces are a pool of the attempt–grant model, and the scheduling counters under a
fair schedule depend only on the standard axioms. -/

section Pool

variable {Expr State Val : Type} [Lantana.Language Expr State Val]

example : Lantana.Fairness.Pool (Lantana.Cfg Expr State) := inferInstance

/-- Fair scheduling is the strong fairness of every thread's scheduling action on the run; it
names no scheduled thread. -/
example (τ : Lantana.Trace Expr State) :
    Lantana.fairScheduling τ ↔ ∀ i, Lantana.Fairness.Sched.SF Lantana.Cfg.active i τ.seq :=
  Iff.rfl

/-- A behavior from position `0` is a run of the pool. -/
example (τ : Lantana.Trace Expr State) (h : Lantana.IsBehavior τ) (hpos : τ.pos = 0) :
    Lantana.Fairness.PoolRun τ.seq :=
  h.poolRun hpos

end Pool

/--
info: 'Lantana.exists_fair_schedule_behFscnt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lantana.exists_fair_schedule_behFscnt

/-- info: 'Lantana.fairScheduling_sf_iff_wf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lantana.fairScheduling_sf_iff_wf

end LantanaTest.Fairness
