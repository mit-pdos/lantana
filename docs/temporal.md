# The temporal layer: traces, thread systems, and fairness

`Lantana/Temporal` is the part of Lantana that knows nothing about Lantana's language or about
Iris: traces of an arbitrary configuration type, trace properties with the operators of linear
temporal logic, thread systems, and the attempt–grant theory of fairness.  Lantana's language is
an instance (`Lantana/ProgramLogic/Configuration.lean`), its traces are `Trace (Cfg Expr State)`,
and its only language-specific atom is the state atom (`Lantana/Trace/StateAtom.lean`).  The
layering is `Prelude < Temporal < Algebra < BaseLogic < ProgramLogic < Trace`.

| module | what it defines |
|---|---|
| `Temporal/Trace.lean` | `Trace C`, `AProp C`, `TrProp C`, the atoms, the connectives and their notations, entailment `⊆`, the fixpoints |
| `Temporal/TracePropRules.lean` | the rules of entailment, duality, infinitely often, `Absolute` |
| `Temporal/ThreadSystem.lean` | the class `ThreadSystem C`, behaviors, schedules |
| `Temporal/Fairness/MissHit.lean` | the engine: counters on positions (not an interface) |
| `Temporal/Fairness/AttemptGrant.lean` | the core: attempt–grant fairness over trace properties and its counter |
| `Temporal/Fairness/Assumption.lean` | `Assumption`, the step-local pair a language instance declares, and its counter's moves |
| `Temporal/Fairness/Action.lean` | `Action`, strong and weak fairness, the recipes `strong` and `weak` |
| `Temporal/Fairness/OwnView.lean` | the recipe `own`: a thread's view of an action, its soundness and completeness |
| `Temporal/Fairness/Scheduling.lean` | fair scheduling as an action; `fairScheduling`; the counters under a schedule |
| `Temporal/Fairness/FairLabel.lean` | fair labelling: a fair behavior has a fair schedule, with counters |

## 1. Traces and trace properties

A trace `τ : Trace C` is a position `τ.pos` in an infinite sequence `τ.seq : Nat → C` of
configurations; `τ.now` is the current configuration and `τ.next` the trace one position later.
There is no coinduction: a trace property `TrProp C := Trace C → Prop` is a predicate on traces
read at the current position, so temporal reasoning is ordinary classical reasoning about
positions.  `AProp C := C → Prop` are the atomic propositions, predicates on one configuration.

Three atoms read the trace: `TrProp.atomic P` (the atomic proposition `P` at the current
configuration), `TrProp.step R` (the relation `R` between the current configuration and the next
one), and `TrProp.atPos f` (a fact about the current position).  The connectives are `⌜p⌝ₜ`,
`∧ₜ`, `∨ₜ`, `→ₜ`, `¬ₜ`, `∀ₜ`, `∃ₜ`, `□ₜ` (always), `◇ₜ` (eventually), `○ₜ` (next) and `Uₜ`
(strong until), scoped in `Lantana.TrProp`.  The subscript keeps them apart from Iris's `□`
(persistently) and `◇` (except-0), which Lantana's `iProp`s use, and from Lean's own
connectives.  Entailment `R ⊆ S` is validity of `R →ₜ S`.

`Lantana.Temporal.TracePropRules` has the rules of entailment for every connective, coinduction
for `□ₜ` and induction for `Uₜ`, the classical dualities, the position-level readings
(`always_eventually_iff`, `eventually_always_iff`) and the *absolute* properties, those the same
at every position of a run (`TrProp.Absolute`): every `□ₜ ◇ₜ`, `◇ₜ □ₜ` and implication between
such is absolute, and so is every fairness property below.  `TrProp.along P τ` reads a trace
property along the run of `τ` as a predicate on positions; it is how the fairness theory talks to
its engine.

## 2. Thread systems

A thread system is a type of configurations with, for each thread id, the *trace step* of the
thread (its step, or its stutter) and its *activity*:

```lean
class ThreadSystem (C : Type) where
  step   : ThreadId → C → C → Prop
  active : ThreadId → C → Prop
```

The class has no laws; whatever a proof needs of an instance is a hypothesis.  Over it:
`threadStep i` (the thread at `i` takes a trace step at the current position), `active i`,
`inactive i`, and `IsBehavior := □ₜ ∃ₜ i, threadStep i` (some thread steps at every position from
the current one on).  `ThreadStepInfOften i := □ₜ ◇ₜ threadStep i`.

Traces carry no thread label.  A *schedule* `sched : Nat → ThreadId` names a thread at each
position; `scheduled sched i` says the schedule names `i` at the current position, and
`Schedule sched := □ₜ ∃ₜ i, scheduled sched i ∧ₜ threadStep i` says the named thread steps at
every position.  Schedules are proof instruments: no behavior and no assumption mentions one,
and the adequacy proof chooses one (section 3.6).

Lantana's instance is `⟨TraceStep, Cfg.active⟩`: the trace step of a thread is its primitive
step or its stutter as a value or when stuck, and a thread is active when it is in the pool and
not a value.

## 3. Fairness

### 3.1 The idea

Fairness is about two kinds of positions of a run, the *attempts* and the *grants*.  A *hit* is a
granted attempt and a *miss* a refused one.  Attempt–grant fairness says that infinitely many
misses force infinitely many hits, `□ₜ ◇ₜ miss →ₜ □ₜ ◇ₜ hit`, equivalently that infinitely many
attempts force infinitely many hits.  It is the same as the existence of a *counter*
`δ : Nat → Nat`, the budget of refusals before the next grant: zero at a hit, one more at a miss
than at the next position, unchanged where there is no attempt.  Everything else in the theory
is an instance of this one equivalence, and the counter is what the program logic turns into
fairness credits.

### 3.2 The engine and the core

`MissHit` (`Fairness/MissHit.lean`) proves the equivalence by arithmetic on positions, for two
position predicates: the counter is the number of misses before the next hit
(`MissHit.fair_iff_counter`).  It is not part of the theory's interface.

`AttemptGrant` (`Fairness/AttemptGrant.lean`) is the core, over two trace properties `attempt`
and `grant`: `hit`, `miss`, `Fair attempt grant`, `IsCounter attempt grant δ`, and
`Certain attempt grant` (every attempt is granted).  Its theorems are stated once, for every
instance below: the meaning (`fair_iff_attempt`), the counter (`fair_iff_counter`) and its three
rules (`counter_reset`, `counter_drop`, `counter_stay`), what the counter bounds
(`counter_bounds_misses`), restriction to fewer attempts (`fair_mono`, `fair_mono_of_le`) and a
certain grant (`fair_of_certain`, `counter_zero_of_certain`).

### 3.3 The declared notion: `Assumption`

A language instance declares its fairness assumptions as values of

```lean
structure Assumption (C : Type) where
  attempt : C → C → Prop
  grant   : C → C → Prop
```

an attempt–grant pair whose attempts and grants are decided by the transition at each position.
`a.attempted := step a.attempt`, `a.granted := step a.grant`, and `a.holds` is the core's
fairness of that pair.  Because the pair is step-local, what a transition does to the counter is
a function of the transition alone, `a.move c c' : Move` (`reset` at a granted attempt, `drop`
at a refused one, `stay` where there is no attempt), and the counter's rules read by the move
(`counter_reset`, `counter_drop`, `counter_stay`, `isCounter_iff_move`).  This is the interface
the program logic will consume: one counter per declared assumption, updated at every step by
the move of that step.

### 3.4 Actions, and the recipes for assumptions

An action is the usual state form of a fairness assumption, an enabling condition on the
configuration and a grant relation on the step:

```lean
structure Action (C : Type) where
  enabled : C → Prop
  grant   : C → C → Prop
```

Its strong fairness is the textbook `a.SF := □ₜ ◇ₜ a.enabledNow →ₜ □ₜ ◇ₜ (a.enabledNow ∧ₜ
a.granted)` and its weak fairness `a.WF` has `◇ₜ □ₜ a.enabledNow` as premise.  Both are
assumptions by a recipe: `a.strong := ⟨fun c _ => a.enabled c, a.grant⟩` with
`a.strong.holds ↔ a.SF` and `a.weak := ⟨fun _ _ => True, fun c c' => ¬ a.enabled c ∨ a.grant c c'⟩`
with `a.weak.holds ↔ a.WF`.  Where the enabling condition is *convex* along the run (true in
between any two positions where it is true, `a.Convex`) the two coincide (`sf_iff_wf_of_convex`).

The third recipe is a thread's *own view* of an action, `a.own i := ⟨fun c c' => step i c c' ∧
a.enabled c, a.grant⟩`: the attempts are the thread's own steps from a configuration where the
action is enabled (`Fairness/OwnView.lean`).  Its counter moves only at the thread's own steps
(`own_move_stay_of_other`), which makes it the cheap path for the program logic.  The view is
sound when every grant is one of the thread's transitions (`a.OwnGrant i`;
`own_holds_of_sf : a.SF ⊆ (a.own i).holds`), and it loses nothing when the thread is scheduled
infinitely often and the enabling condition persists (`a.Persists i`, which follows from
stability under the other threads' steps, `a.Stable i`; `sf_of_own_holds`, `sf_iff_own_holds`).

### 3.5 Fair scheduling

Fair scheduling is one more action: `Sched.action i := ⟨ThreadSystem.active i,
ThreadSystem.step i⟩`, enabled where the thread is active and granted at its trace step.
`Sched.SF i` is its strong fairness, `Sched.assumption i := (Sched.action i).strong` the
assumption, and `fairScheduling := ∀ₜ i, Sched.SF i` is the hypothesis of Lantana's adequacy
theorems: a thread active infinitely often steps infinitely often.  It names no scheduled
thread.  For a thread system whose activity is convex, as Lantana's is (a thread is active from
its fork until it becomes a value), this is the usual weak fairness (`Cfg.sched_sf_iff_wf`).

A thread's own view of its scheduling is trivial: its attempts are its own steps, so every
attempt is a grant and the counter is zero.  The scheduling counter that adequacy uses is the
one of the strong form, read under a schedule.

### 3.6 The schedule and the counters adequacy uses

Adequacy needs one owner per step and a decreasing measure for every waiting thread.  Fair
labelling (`Fairness/FairLabel.lean`, `exists_fair_schedule`) shows that a behavior on which
every thread is fairly scheduled has a schedule that names every thread active infinitely often
infinitely often while active, by a diagonal construction.  Under such a schedule the
*fairness counters* exist: `BehFscnt sched γ` says that at every position each thread is
inactive, or active and either named by the schedule or with a strictly decreasing counter
`γ n i`, and `exists_fair_schedule_behFscnt` produces both the schedule and the counters from
`IsBehavior τ` and `fairScheduling τ`.  The adequacy proofs thread `Schedule sched ⟨0, τf⟩` and
`BehFscnt sched γ ⟨0, τf⟩` along the run and bound the fair-scheduler witnesses by
`fairMeasure (γ n)`.

## 4. Naming

Namespaces follow the structure: `Lantana.TrProp` for trace properties, `Lantana` for thread
systems, behaviors and fair scheduling, `Lantana.Fairness` for the theory with the namespaces
`MissHit`, `AttemptGrant`, `Assumption`, `Action` and `Sched`.  Upper-case names are
propositions about a run or about a relation (`Fair`, `IsCounter`, `Certain`, `SF`, `WF`,
`Convex`, `OwnGrant`, `Stable`, `Persists`); lower-case names are trace properties at one
position (`hit`, `miss`, `attempted`, `granted`, `enabledNow`, `threadStep`, `active`) and the
fields of structures.  A theorem over an action or an assumption takes it as its argument `a`.
Theorems read `conclusion_of_hypothesis` (`own_holds_of_sf`) or `subject_property`
(`counter_reset`), equivalences `x_iff_y` (`sf_iff_wf_of_convex`).  A statement whose hypotheses
and conclusion are trace properties is an entailment `⊆`; one with a pure hypothesis is stated at
a trace `τ`.
