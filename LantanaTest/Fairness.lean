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

end LantanaTest.Fairness
