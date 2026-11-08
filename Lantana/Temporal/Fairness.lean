/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Fairness.AttemptGrant
public import Lantana.Temporal.Fairness.Action
public import Lantana.Temporal.Fairness.Sched
public import Lantana.Temporal.Fairness.Thread
public import Lantana.Temporal.Fairness.FairLabel

/-! # The attempt–grant model of fairness: the general theory

The general theory of the attempt–grant model, layers 0 to 2, over trace properties
(`Lantana.Temporal.Trace`) and generic over a thread system (`Lantana.Temporal.Pool`): a type of
configurations with the trace step of the thread at each position and the activity predicate the
language supplies.  Everything is in the namespace `Lantana.Fairness`.  The theory was first
ported from xv6iris-lean's `MachCSL/Liveness/FairnessTheory.lean` (positions `Nat → Prop`, branch
`lean-lantana` at `050cf0808`) and then restated over trace properties with the temporal operators;
the names are the ported file's where the formula is the same, which is nearly all of them.

**The idea.**  Fairness is about two trace properties, the *attempts* and the *grants*.  A hit is a
granted attempt, and a miss is a refused one.  Attempt–grant fairness says that infinitely many
misses force infinitely many hits, `□ₜ ◇ₜ miss →ₜ □ₜ ◇ₜ hit`, or equivalently that infinitely
many attempts force infinitely many hits.  It is the existence of a counter, the budget of refusals
before the next grant: zero at a hit, one more at a miss than at the next position, unchanged
where there is no attempt.  That is layer 0, and the two layers above are instances of it.

A fairness assumption is an *action*: an *enabling condition* `A` on configurations and a *grant*
relation `G` on steps.  Its trusted form is the textbook strong fairness
`SF A G := □ₜ ◇ₜ now A →ₜ □ₜ ◇ₜ (now A ∧ₜ step G)`, a statement about the run that names no
thread.  `SF` is layer 0 with the positions where `A` holds as the attempts and the steps in `G` as
the grants.  Its counter moves at any step, whoever takes it.  Telling a thread about an update of
the counter at another thread's step is the program logic's job.

A thread's view of the action is layer 0 with the thread's own steps from a configuration where `A`
holds as the attempts.  The restriction is sound when every grant is one of the thread's
transitions (*own grant*).  It loses nothing when `A` persists and the thread is scheduled fairly.
The thread's counter stays at every other thread's step, because its attempts are the thread's
steps.  That makes the thread's view the cheap path for the logic.

Fair scheduling is one more action: its enabling condition is that the thread is active, and its
grant is the thread's step.  Labels are proof instruments: no behavior and no assumption names the
stepping thread, and the adequacy proof chooses a schedule that does.

**Map of the modules.**

1. `Lantana.Temporal.Fairness.AttemptGrant`, section 1: `AttemptGrant`, layer 0, the attempt–grant
   pair over two trace properties (`hit`, `miss`, `Fair`, `IsCounter`, `Certain`); its meaning
   (`fair_iff_attempt`), its counter (`fair_iff_counter`) and the counter's rules, stated once for
   every layer; restriction (`fair_mono`); a certain grant (`fair_of_certain`).  The engine
   underneath, `MissHit`, is arithmetic on positions.
2. `Lantana.Temporal.Fairness.Action`, section 2: `Action`, layer 1, the state form of an action
   `(A, G)`: `enabled A := now A`, `grant G := step G`, `SF`, `Response`, `WF`, `Convex`;
   `sf_iff_fair`, `sf_iff_counter`, `sf_of_response`, `wf_of_sf`, `sf_of_certain`,
   `sf_iff_wf_of_convex`.
3. `Lantana.Temporal.Fairness.Sched`, sections 3 and 4: a pair that is one thread's
   (`AttemptGrant.OwnStep`, `AttemptGrant.counter_stay_of_other`); the scheduling action `Sched`
   (`SF`, `attempt`, `AG`, `ownGrant`, `stepsInfOften_of_sf`, `certain`, `ag`, `counter_zero`); the
   schedule as a proof instrument (`SoleOwner`, `labelledView`, `labelledView_of_sf`).
4. `Lantana.Temporal.Fairness.Thread`, section 5: `Thread`, layer 2, the thread's view (`attempt`,
   `hit`, `miss`, `AttemptGrant`, `IsCounter`, `Certain`, `OwnGrant`, `Stable`, `Persists`);
   soundness (`attemptGrant_of_sf`, `counter_of_sf`), completeness (`persists_of_stable`,
   `attempt_pending`, `sf_of_attemptGrant`, `sf_iff_attemptGrant`), a certain grant
   (`attemptGrant_of_certain`, `counter_zero_of_certain`, `wf_of_certain`, `sf_of_certain`).
5. `Lantana.Temporal.Fairness.FairLabel`, section 6: `exists_fair_schedule`, a behavior with fair
   scheduling of every thread admits a fair schedule, by the diagonal construction of `FairLabel`;
   `Sched.exists_counter_of_fair_schedule`.

Fair scheduling of the whole system and the fairness counters under a schedule are in
`Lantana.Temporal.FairScheduling`.  Lantana takes one thing from each layer.  Its witness kind is
stated against layer 0.  Its trace side implements layer 1, one counter per declared action
updated at every step (the owner's decision of 2026-11-06).  Layer 2 is its cheap path, available
when the declared action has own grant.

**Naming policy.**  Namespaces are the layers.  Capitalised names are propositions about a whole
run or a relation (`Fair`, `SF`, `Response`, `WF`, `Certain`, `AttemptGrant`, `IsCounter`,
`OwnStep`, `OwnGrant`, `Stable`, `Persists`, `Convex`); lower-case names are position or
configuration predicates (`attempt`, `grant`, `hit`, `miss`, `enabled`).  The layers above layer 0
state their pair as abbreviations of layer 0's, so layer 0's theorems apply to them as they
stand; the layers copy none of the rules, and restate by the thread's name only the three facts
the documents cite (`Thread.attemptGrant_iff_attempt`, `attemptGrant_of_certain`,
`counter_zero_of_certain`).  Theorems read `conclusion_of_hypothesis` (`attemptGrant_of_sf`,
`counter_of_sf`, `sf_of_attemptGrant`) or `subject_property` (`counter_reset`,
`hit_miss_exclusive`), and equivalences read `x_iff_y` (`sf_iff_fair`, `sf_iff_attemptGrant`).
A theorem whose hypotheses and conclusion are all trace properties is an entailment `⊆`; one with
a pure hypothesis (own grant, stability, a sole owner) is stated at a trace `τ`.  A hypothesis has
the same name everywhere: `hsf` for `Action.SF`, `hag` for an attempt–grant form, `hown` for
`OwnGrant`, `hos` for `OwnStep`, `hso` for `SoleOwner`, `hconv` for `Convex`, `hsched` for fair
scheduling, `hsch` for a `Schedule`, `hper` for `Persists`, `hstab` for stability, `hrun` for a
behavior, `hδ` for a counter, `hc` for `Certain`, and `ha`, `hg`, `hA`, `hs` for the facts at a
position (an attempt, a grant, `A` holds, the thread steps).
-/
