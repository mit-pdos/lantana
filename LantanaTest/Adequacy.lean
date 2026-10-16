module

public import Lantana

/-! Tests for adequacy: the two adequacy theorems and the single-step simulation depend only on
the standard axioms. -/

namespace LantanaTest.Adequacy

open Lantana

/-- info: 'Lantana.run_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_step

/--
info: 'Lantana.lwp_adequacy_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lwp_adequacy_safety

/--
info: 'Lantana.lwp_adequacy_temporal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lwp_adequacy_temporal

end LantanaTest.Adequacy
