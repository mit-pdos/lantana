/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Trace.Fairness.AttemptGrant
public import Lantana.Trace.Fairness.Action
public import Lantana.Trace.Fairness.Pool
public import Lantana.Trace.Fairness.Thread
public import Lantana.Trace.Fairness.FairLabel

/-! # The attempt–grant model of fairness: the general theory

The general theory of the attempt–grant model, layers 0 to 2, generic over a thread pool.  A pool
(section 3) is a type of configurations with a step relation for the thread at each position, and
the theory takes nothing else from a language.  It is ported from xv6iris-lean's
`MachCSL/Liveness/FairnessTheory.lean` (branch `lean-lantana` at `050cf0808`), every name,
statement and docstring kept; the modules below keep that file's section numbers, which the
docstrings cite.  Everything is in the namespace `Lantana.Fairness`.

**The idea.**  Fairness is about two predicates on positions, the *attempts* and the *grants*.  A
hit is a granted attempt, and a miss is a refused one.  Attempt–grant fairness says that infinitely
many misses force infinitely many hits, or equivalently that infinitely many attempts force
infinitely many hits.  It is the existence of a counter, the budget of refusals before the next
grant: zero at a hit, one more at a miss than at the next position, unchanged where there is no
attempt.  That is layer 0, and the two layers above are instances of it.

A fairness assumption is an *action*: an *enabling condition* `A` on configurations and a *grant*
relation `G` on steps.  Its trusted form is the textbook strong fairness
`SF := □◇ A → □◇ (A ∧ G)`, a statement about the run that names no thread.  `SF` is layer 0 with
the positions where `A` holds as the attempts and the steps in `G` as the grants.  Its counter
moves at any step, whoever takes it.  Telling a thread about an update of the counter at another
thread's step is the program logic's job.

A thread's view of the action is layer 0 with the thread's own steps from a configuration where `A`
holds as the attempts.  The restriction is sound when every grant is one of the thread's
transitions (*own grant*).  It loses nothing when `A` persists and the thread is scheduled fairly.
The thread's counter stays at every other thread's step, because its attempts are the thread's
steps.  That makes the thread's view the cheap path for the logic.

Fair scheduling is one more action: its enabling condition is that the thread is active, and its
grant is the thread's step.  Labels are proof instruments: no run and no assumption names the
stepping thread, and the adequacy proof chooses a schedule that does.

**Map of the modules.**

1. `Lantana.Trace.Fairness.AttemptGrant`, section 1. `AttemptGrant`, layer 0: the attempt–grant
   pair over two position predicates (`hit`, `miss`, `Fair`, `IsCounter`, `Certain`).  Its meaning
   (`fair_iff_attempt`), its counter (`fair_iff_counter`) and the counter's rules, stated once for
   every layer; restriction (`fair_mono`); a certain grant (`fair_of_certain`).  The engine
   underneath, `MissHit`, is copied from Lantana's ghost toy.  Pure arithmetic of positions.
2. `Lantana.Trace.Fairness.Action`, section 2. `Action`, layer 1: the state form of an action
   `(A, G)`, with no thread and no pool.  Its `grant` is a position predicate, and its `hit`,
   `miss`, `IsCounter` and `Certain` are layer 0's at the positions where `A` holds.  `SF`,
   `Response` and `WF` are stated directly.  `SF` is layer 0's fairness (`sf_iff_fair`), hence the
   existence of a counter (`sf_iff_counter`).  A certain grant gives `SF` outright
   (`sf_of_certain`).
3. `Lantana.Trace.Fairness.Pool`, section 3. The pool, abstractly: a class of configurations with
   a thread's step (`Pool`, `Pool.Step`), and a thread's step on a run, a run, fair scheduling
   (`Steps`, `PoolRun`, `StepsInfOften`).  A pair of layer 0 is one thread's when its attempts are
   that thread's steps (`AttemptGrant.OwnStep`), and its counter then stays at the other threads'
   steps (`AttemptGrant.counter_stay_of_other`).
4. `Lantana.Trace.Fairness.Pool`, section 4. `Sched`, the scheduling action: enabled where the
   thread is active, a predicate the language supplies, and granted at the thread's step (`grant`,
   `SF`).  A thread active infinitely often steps infinitely often (`stepsInfOften_of_sf`), and the
   thread's view of its scheduling (`attempt`, `AG`) is certain, with counter zero (`certain`,
   `ag`, `counter_zero`).  For a convex condition `SF` and `WF` coincide
   (`Action.sf_iff_wf_of_convex`).  The schedule names the stepping thread at each position, a
   proof instrument (`Schedule`).  Under it a grant that only its thread can take (`SoleOwner`)
   turns `SF` into the thread's labelled view (`labelledView_of_sf`).
5. `Lantana.Trace.Fairness.Thread`, section 5. `Thread`, layer 2: the thread's view of an action,
   layer 0 at the thread's attempts (`attempt`, `hit`, `miss`, `AttemptGrant`, `IsCounter`,
   `Certain`), a pair that is the thread's by construction (`ownStep`), and own grant
   (`OwnGrant`).
   * Soundness: under own grant, `SF` gives the attempt–grant form (`attemptGrant_of_sf`, a
     restriction) and the counter (`counter_of_sf`).
   * Completeness: under persistence of `A` (`Persists`, from stability `Stable`) and fair
     scheduling, the attempt–grant form gives `SF` back (`sf_of_attemptGrant`), hence
     `sf_iff_attemptGrant`.
   * A grant certain at the thread's attempts (`Certain`): no misses, counter zero, `WF` from fair
     scheduling alone (`wf_of_certain`), `SF` with persistence as well (`sf_of_certain`).
6. `Lantana.Trace.Fairness.FairLabel`, section 6. `exists_fair_schedule`: a run with fair
   scheduling of every thread admits a fair schedule.

Lantana takes one thing from each layer.  Its witness kind is stated against layer 0.  Its trace
side implements layer 1, one counter per declared action updated at every step (the owner's
decision of 2026-11-06).  Layer 2 is its cheap path, available when the declared action has own
grant.

**Naming policy.**  Namespaces are the layers.  Capitalised names are propositions about a whole
run or a relation (`Fair`, `SF`, `Response`, `WF`, `Certain`, `AttemptGrant`, `IsCounter`,
`OwnStep`, `OwnGrant`, `Stable`, `Persists`); lower-case names are position or configuration
predicates (`attempt`, `grant`, `hit`, `miss`, `enabled`).  The layers above layer 0 state their
pair as abbreviations of layer 0's, so layer 0's theorems apply to them as they stand; the layers
copy none of the rules, and restate by the thread's name only the three facts the documents cite
(`Thread.attemptGrant_iff_attempt`, `attemptGrant_of_certain`, `counter_zero_of_certain`).
Theorems read `conclusion_of_hypothesis` (`attemptGrant_of_sf`, `counter_of_sf`,
`sf_of_attemptGrant`) or `subject_property` (`counter_reset`, `hit_miss_exclusive`), and
equivalences read `x_iff_y` (`sf_iff_fair`, `sf_iff_attemptGrant`).  A hypothesis has the same name
everywhere: `hsf` for `Action.SF`, `hag` for an attempt–grant form (layer 0's `Fair` or the
thread's `AttemptGrant`), `hown` for `OwnGrant`, `hos` for `OwnStep`, `hso` for `SoleOwner`,
`hconv` for `Convex`, `hsched` for fair scheduling (`StepsInfOften`, or `∀ i, Sched.SF`), `hsch`
for a `Schedule`, `hper` for `Persists`, `hstab` for stability, `hrun` for `PoolRun`, `hδ` for a
counter, `hc` for `Certain`,
and `ha`, `hg`, `hA`, `hs` for the facts at a position (an attempt, a grant, `A` holds, the thread
steps).  The names every action of `Fairness.lean` has are in that file's header.
-/
