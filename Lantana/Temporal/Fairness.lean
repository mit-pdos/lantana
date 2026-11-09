/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Fairness.MissHit
public import Lantana.Temporal.Fairness.AttemptGrant
public import Lantana.Temporal.Fairness.Action
public import Lantana.Temporal.Fairness.Scheduling
public import Lantana.Temporal.Fairness.Thread
public import Lantana.Temporal.Fairness.FairLabel
public import Lantana.Temporal.Fairness.Assumption

/-! # The attempt–grant model of fairness: the general theory

The general theory of the attempt–grant model, layers 0 to 2, over trace properties
(`Lantana.Temporal.Trace`) and generic over a thread system (`Lantana.Temporal.ThreadSystem`): a
type of configurations with the trace step of the thread at each position and the activity
predicate the language supplies.  Everything is in the namespace `Lantana.Fairness`.  The theory
was first ported from xv6iris-lean's `MachCSL/Liveness/FairnessTheory.lean` (positions
`Nat → Prop`, branch `lean-lantana` at `050cf0808`) and then restated over trace properties with
the temporal operators; the names are the ported file's where the formula is the same, which is
nearly all of them.

**The idea.**  Fairness is about two trace properties, the *attempts* and the *grants*.  A hit is a
granted attempt, and a miss is a refused one.  Attempt–grant fairness says that infinitely many
misses force infinitely many hits, `□ₜ ◇ₜ miss →ₜ □ₜ ◇ₜ hit`, or equivalently that infinitely
many attempts force infinitely many hits.  It is the existence of a counter, the budget of refusals
before the next grant: zero at a hit, one more at a miss than at the next position, unchanged
where there is no attempt.  That is layer 0, and the two layers above are instances of it.

Layer 1's object is an *action*, a structure `Action` with an *enabling condition* `enabled` on
configurations and a *grant* relation `grant` on steps, read on a trace through the atoms
`enabledNow` (`now a.enabled`) and `granted` (`step a.grant`).  Its trusted form is the textbook
strong fairness `a.SF := □ₜ ◇ₜ a.enabledNow →ₜ □ₜ ◇ₜ (a.enabledNow ∧ₜ a.granted)`, a statement
about the run that names no thread.  `SF` is layer 0 with the positions where the action is
enabled as the attempts and the steps in its grant as the grants.  Its counter moves at any step,
whoever takes it.  Telling a thread about an update of the counter at another thread's step is the
program logic's job.

A thread's view of the action is layer 0 with the thread's own steps from a configuration where
the action is enabled as the attempts.  The restriction is sound when every grant is one of the
thread's transitions (*own grant*).  It loses nothing when the enabling condition persists and the
thread is scheduled fairly.  The thread's counter stays at every other thread's step, because its
attempts are the thread's steps.  That makes the thread's view the cheap path for the logic.

Fair scheduling is one more action: its enabling condition is that the thread is active, and its
grant is the thread's step.  Labels are proof instruments: no behavior and no assumption names the
stepping thread, and the adequacy proof chooses a schedule that does.

A language instance declares its fairness assumptions as `Assumption`s: attempt–grant pairs whose
attempts and grants are relations on the step, so that what a transition does to the counter
(reset, drop, stay) is decided by the transition alone.  Strong and weak fairness of an action,
the thread's own view of an action and fair scheduling are the four ways to build one.

**Map of the modules.**

0. `Lantana.Temporal.Fairness.MissHit`, section 0: the engine `MissHit`, arithmetic on positions
   and not part of the theory's interface: miss–hit fairness over two position predicates and its
   counter, the oracle budget (`MissHit.fair_iff_counter`); and the bridge from trace properties
   to position predicates (`always_eventually_iff_infOften`).
1. `Lantana.Temporal.Fairness.AttemptGrant`, section 1: `AttemptGrant`, layer 0, the attempt–grant
   pair over two trace properties (`hit`, `miss`, `Fair`, `IsCounter`, `Certain`); its meaning
   (`fair_iff_attempt`), its counter (`fair_iff_counter`) and the counter's rules, stated once for
   every layer; restriction (`fair_mono`, `fair_mono_of_le`); a certain grant (`fair_of_certain`).
2. `Lantana.Temporal.Fairness.Action`, section 2: `Action`, layer 1, the state form of an action,
   a structure with the fields `enabled` and `grant`: `enabledNow a := now a.enabled`,
   `granted a := step a.grant`, `SF`, `Response`, `WF`, `Convex`; `sf_iff_fair`, `sf_iff_counter`,
   `sf_of_response`, `wf_of_sf`, `sf_of_certain`, `sf_iff_wf_of_convex`.
3. `Lantana.Temporal.Fairness.Scheduling`, sections 3 and 4: a pair that is one thread's
   (`AttemptGrant.OwnStep`, `AttemptGrant.counter_stay_of_other`); the scheduling action `Sched`
   (`action`, `SF`, `attempt`, `AG`, `ownGrant`, `stepsInfOften_of_sf`, `certain`, `ag`,
   `counter_zero`); the schedule as a proof instrument (`SoleOwner`, `labelledView`,
   `labelledView_of_sf`).
4. `Lantana.Temporal.Fairness.Thread`, section 5: `Thread`, layer 2, the thread's view (`attempt`,
   `hit`, `miss`, `AttemptGrant`, `IsCounter`, `Certain`, `OwnGrant`, `Stable`, `Persists`);
   soundness (`attemptGrant_of_sf`, `counter_of_sf`), completeness (`persists_of_stable`,
   `attempt_pending`, `sf_of_attemptGrant`, `sf_iff_attemptGrant`), a certain grant
   (`attemptGrant_of_certain`, `counter_zero_of_certain`, `wf_of_certain`, `sf_of_certain`).
5. `Lantana.Temporal.Fairness.FairLabel`, section 6: `exists_fair_schedule`, a behavior with fair
   scheduling of every thread admits a fair schedule, by the diagonal construction of `FairLabel`;
   `Sched.exists_counter_of_fair_schedule`.
6. `Lantana.Temporal.Fairness.Assumption`, section 7: `Assumption`, a fairness assumption, the
   notion a language instance declares: an attempt–grant pair of relations on the step (`attempted`,
   `granted`, `holds`, `IsCounter`, `Certain`); the counter's move at a transition (`move`,
   `counter_reset`, `counter_drop`, `counter_stay`, `isCounter_iff_move`), its existence
   (`holds_iff_counter`); the four constructors `Action.strong` (`holds_strong`), `Action.weak`
   (`holds_weak`), `Action.own` (`holds_own`) and `Sched.assumption` (`holds_assumption`).

Fair scheduling of the whole system and the fairness counters under a schedule are in
`Lantana.Temporal.FairScheduling`.  Lantana takes one thing from each layer.  Its witness kind is
stated against layer 0.  Its trace side implements layer 1, one counter per declared action
updated at every step (the owner's decision of 2026-11-06), the action declared as an assumption
(`Action.strong`).  Layer 2 is its cheap path (`Action.own`), available when the declared action
has own grant.

**Naming policy.**  Namespaces are the layers.  Capitalised names are propositions about a whole
run or a relation (`Fair`, `SF`, `Response`, `WF`, `Certain`, `AttemptGrant`, `IsCounter`,
`OwnStep`, `OwnGrant`, `Stable`, `Persists`, `Convex`); lower-case names are position or
configuration predicates (`attempt`, `hit`, `miss`), the fields of an action or an assumption
(`enabled`, `grant`, `attempt`) and the atoms that read them on a trace (`enabledNow`, `granted`,
`attempted`); `Assumption.holds`, the assumption holds of the run, reads as a verb.  A theorem
over an action or an assumption takes it as one argument `a` (`a.SF`, `a.holds`).  The layers
above layer 0 state their pair as abbreviations of layer 0's, so layer 0's theorems apply to them
as they stand; the layers copy none of the rules, and restate by the thread's name only the three
facts the documents cite (`Thread.attemptGrant_iff_attempt`, `attemptGrant_of_certain`,
`counter_zero_of_certain`).  `Assumption` restates by its name the facts a language instance
reads, the counter's rules in terms of the move.  Theorems read `conclusion_of_hypothesis`
(`attemptGrant_of_sf`, `counter_of_sf`, `sf_of_attemptGrant`) or `subject_property`
(`counter_reset`, `hit_miss_exclusive`), and equivalences read `x_iff_y` (`sf_iff_fair`,
`sf_iff_attemptGrant`).  A theorem whose hypotheses and conclusion are all trace properties is an
entailment `⊆`; one with a pure hypothesis (own grant, stability, a sole owner) is stated at a
trace `τ`.  A hypothesis has the same name everywhere: `hsf` for `Action.SF`, `hag` for an
attempt–grant form (`Assumption.holds` among them), `hown` for `OwnGrant`, `hos` for `OwnStep`,
`hso` for `SoleOwner`, `hconv` for `Convex`, `hsched` for fair scheduling, `hsch` for a
`Schedule`, `hper` for `Persists`, `hstab` for stability, `hrun` for a behavior, `hδ` for a
counter, `hc` for `Certain`, and `ha`, `hg`, `hA`, `hs` for the facts at a position (an attempt, a
grant, the action is enabled, the thread steps).
-/
