# Temporal formulas and adequacy

Temporal formulas are `iProp`s whose truth shows on the trace: an invariant that always holds,
an obligation that holds `P` until `Q`.  This note describes how they are registered, what a
guarantee `P ⊨ₜ G` is, how the adequacy proof reads the formulas off a run, the rules that
discharge untils, the structure of the adequacy proof, and the crash test.  Configurations, the
step of `lWP` and the lifting lemmas are described in `docs/program-logic.md`; the obligation
model, the nodes of crashed threads and the rounds of a step in `docs/model.md`; traces,
schedules and fairness counters in `docs/temporal.md`.

| module | contents |
|---|---|
| `Trace/TemporalFormula.lean` | the registry state, the temporal formulas, `mupd_read` (§1) |
| `Trace/Guarantee.lean` | guarantees, records, bundles, the one-step property (§2) |
| `Trace/TemporalFormulaRun.lean` | the check `reg_check`, the loops `always_run`, `until_run` (§3) |
| `Trace/TemporalFormulaRules.lean` | the rules and guarantees of the formulas (§3, §4) |
| `Trace/Adequacy/Temporal.lean`, `Safety.lean` | the adequacy theorems (§5.1, §5.5) |
| `Trace/Adequacy/Alloc.lean` | the ghost state that adequacy allocates (§5.2) |
| `Trace/Adequacy/RunStep.lean` | one step of the run, `run_step` (§5.3) |
| `Trace/Adequacy/Step.lean` | the witnesses of a step, the measures, active owners (§5.4) |
| `LantanaTest/Crash/` | a language whose threads crash, verified end to end (§7) |

## 1. The registry and the temporal formulas

The registry (`ProgramLogic/TemporalRegistry.lean`) is an append-only list of entries, each
tagged with a position of the history: a marker for each check of the adequacy proof
(`RegEntry.mark`), a registered `alwaysI` (`.always N γ`) or a registered `untilI`
(`.until N k γP γQ`).  The names `γ` are saved readings (`savedTrI`), which fix the step-indexed
reading of a content's specification so that every use of the entry agrees on it.  The temporal
layer is interpreted by the registry state (`regTemporalInterp`, `regState`), which interprets
each entry by `regEntryInterp`: its saved readings, the invariant of the formula and a
later-guarded guarantee of its content.  The program logic threads this state, so registering a
formula is a ghost update.

The formulas:

- `alwaysI N P` is the invariant `inv N P`, registered with the guarantee of its content, and
  the record of the content at the registration position.
- `untilI N k q P Q`, "`P` until `Q` on `k`", is an obligation invariant over the obligation
  `k`, `Obl.inv N k P (untilDischarged k G₂)`.  It holds `P` and half of the assignment of `k`
  while `k` is live and, once `k` is discharged, the record of the reading of `Q` at the
  discharge (`untilDischarged`).  The formula owns the fraction `q` of the other half, the
  user's.  Its persistent part (`untilIPers`) also holds the state of `k` and the record of the
  left reading at the registration.
- `finallyI N k q Q` is `untilI N k q True Q`.
- `untilIDone k Q` is a fulfilled until: `Q`, the discharge of `k` and the guarantee of `Q`.
  Nothing is registered.

Each formula comes in two forms.  The `guar` forms (`alwaysIGuar N P G`,
`untilIGuar N k q P Q G₁ G₂`, `untilIDoneGuar k Q G₂`) carry the readings of their contents
explicitly; the plain forms read their contents by the canonical specification `TrSpec.canon`
(§2), and `alwaysIAs N P V` reads `P` as `TrSpec.canon V`.  The `guar` forms are contractive in
their contents for fixed readings (`alwaysIGuar_contractive`, `untilIGuar_contractive_left`,
`untilIGuar_contractive_right`), so that formulas can be defined by guarded recursion (`renew`
in `Trace/GuaranteeRec.lean`); the plain forms are not, since `TrSpec.canon P` is not a
non-expansive function of `P`.  The forms are irreducible, with unfolding lemmas
(`alwaysIGuar_unfold`, `untilI_eq`, …).

Allocation records the content at the current position, so it reads the history and the model:
`mupd_read` is a model update that reads both, at any view, and updates the registry state
(`mupd_read_fupd` has fancy updates around the reading).

## 2. Guarantees and records

A guarantee `P ⊨ₜ G` (`guar P G`) says that whenever `P` holds, the rest of the execution
satisfies the trace specification `G`; adequacy concludes `G.external`.  (A trace specification,
`Trace/TrSpec.lean`, is a step-indexed reading `G.internal` with the trace property
`G.external` it is adequate for.)  The guarantee is persistent: at a position `n`, `P` with the
history and the model gives the persistent record `record G n`.  It takes the model at any view,
since guarantees are used inside model updates, which see the model at any view; between steps
the adequacy proof keeps the model at the view of the configuration, its thread count and its
crashed threads.

A record `record G n` is `recordTrI G.internal n`: for any running system `Sys : SysT` (a
resource indexed by the position and the configuration) with the one-step property
`sysStep Sys`, given the bundle of the check at `n` and the system at `n + 1`, the reading
`G.internal` holds at `n`.  A record is eliminated after the step from `n`, not before, because
it may be written during step `n`, in the model update before the step (when an until is
discharged, for example), too late for the check at `n` to certify it.

The check at `n` (§3) gives the bundle `bundle l n`: a prefix `l` of the registry that ends with
the marker of `n`, with the certificate of each entry (`cert`, `certPre`), a later-guarded
record of its content at `n`.  For an until, the certificate is the record of its left or right
formula at `n` or, if it was discharged at a position `n' ≤ n`, the record of its right formula
at `n'`.  A registered formula is so certified at every position after its registration, while
its content stays in its invariant.

The one-step property `sysStep Sys` (`sysStepPre`) says: from the system at `n`, with the history
and the model at the view of the configuration, the bundle for `n`, then, after the step, the
system at `n + 1`, the facts about the step and `c` later credits, under the modalities of
`TrIProp.defer`, `|={⊤,∅}=> ▷ |={∅,⊤}=> |={⊤,∅}=> alc (|={∅,⊤}=> …)`.  The facts are pure facts
about the run `τf : Nat → Cfg Expr State`, which the adequacy proof threads along it:

- `schedule sched ⟨0, τf⟩` and `schedCounters sched γ ⟨0, τf⟩`: the schedule and the fairness
  counters that the proof chooses (`docs/temporal.md`, §3.6).  They are trace properties of the
  run from position `0`, read at `n` through `schedule_iff` and `schedCounters_iff`.
- `OWitInvLb (fairMeasure (γ n)) Ω W`: the witnesses are bounded below by the fair-scheduler
  measures of the current counters.
- `HistTrace h τf`: the ghost history is a prefix of the run.
- Across a step, `ObligationsDrop`: the measure of every assigned obligation drops (§5.4).

Records are a guarded fixpoint, `recordTrI := fixpoint recordPre`: a record quantifies over
bundles, whose certificates hold records under a later, so `recordPre` is contractive
(`certPre_contractive`, `bundlePre_contractive`, `sysStepPre_contractive`).  `bundle`, `cert`
and `sysStep` are irreducible so that `inext` does not strip the laters of the certificates.

`TrSpec.canon Q` is the canonical specification guaranteed by `Q`, the strongest: the meet of
all the specifications that `Q` validly guarantees.  The class `StateFact P φ` says that the
state interpretation and `P` determine the state predicate `φ`.  It gives the atoms of trace
specifications, by the rule `guar_stateFact` of `Trace/GuaranteeRules.lean`, and it is defined
with the guarantees so that a language can give its instances without the rules.

## 3. Certification, and reading the formulas off a run

At every position `n`, the adequacy proof runs the check `reg_check`: it appends the marker of
`n` to the registry (`reg_mark`) and certifies every entry (`certify_entries`).  `cert_of_entry`
opens the invariant of an entry, takes a later-guarded record of its content, by the guarantee
stored with the entry or, for a discharged until, the record that its invariant keeps, and
closes the invariant.  The check gives the bundle for `n` and the registry state back.

A registered formula is read off a run by a loop, a Löb induction, for any system with the
one-step property.  An iteration (`sysStep_iter`) takes the certificate of the entry from the
bundle of the position (`bundle_always_cert`, `bundle_until_cert`), whose later the later of the
deferred shape strips; an entry registered during step `n`, after the check at `n`, has instead
the record taken at its allocation.  After the step, the iteration eliminates the record against
the system at `n + 1`.

- `always_run`: a registered `alwaysI` gives `TrIProp.always` of its reading at every position
  after its registration.
- `until_run`: a registered `untilI` whose obligation `k` is assigned at `n`, with fuel `fu` and
  owner `o`, gives the strong until of its readings at `n`, with the rank
  `succ (fairMeasure (γ n) o fu)`.  The certificate tells which formula holds at `n`.  If it is
  the left one, a later credit of the step opens the obligation invariant at `n + 1`.  If `k` is
  still assigned, the loop goes on at a lower rank, since the measure of every assigned
  obligation drops across a step (`ObligationsDrop`); if `k` was discharged during the step,
  the record of the right formula at the discharge, at `n` or at `n + 1`, ends the until
  (`until_run_discharged`).

The guarantees of the formulas, in `TemporalFormulaRules.lean`, start these loops:

- `guar_alwaysIGuar`, `alwaysIGuar N P G ⊨ₜ □ₛ G`: the certificate at `n`, then `always_run` from
  `n + 1`.
- `guar_untilIGuar`, `untilIGuar N k q P Q G₁ G₂ ⊨ₜ (G₁ Uₛ G₂)`, with the rank
  `succ (succ (fairMeasureUb fu))` for the fuel `fu` of `k` where the guarantee is used.  After
  the step, the obligation, read with a credit of the step (`alc_credits`), has a fuel
  `fu' ≤ fu`, whose measure is below `fairMeasureUb fu`, and `until_run` goes on from there.
- `guar_untilIDoneGuar`: a done until guarantees the until of any left reading, by its right
  formula, without a run.

Their canonical forms follow (`guar_alwaysI`, `guar_untilI`, `guar_untilIDone`, and the `_valid`
forms from a valid guarantee of the contents), and the `GuarOf` instances infer the guarantee of
a formula from its shape.

## 4. The rules of the formulas, and discharging untils

The rules are those of the paper (`docs/paper-correspondence.md`, §4), each for given and for
canonical readings.  Access: `alwaysI_acc` and `untilI_acc`, with instances so that `iinv` opens
an `alwaysI` like an invariant.  Allocation: `alwaysI_alloc`; `alwaysI_register` for an
existing invariant; `untilI_init` on an obligation held in full; `untilI_alloc`, which creates
the obligation below a parent, adds it to the parent's bill and lets the formulas be chosen once
`k` is known; `untilIDone_init` for an until fulfilled at once.  Discharge: `untilI_discharge`,
`untilI_discharge_done`, `finallyI_discharge` (with a later credit).  Then
`untilI_discharged_false` and the fractions, `untilI_frac_split` and `untilI_frac_add`.

### 4.1 Discharging an until with its invariant open

The rules above discharge an until inside its own invariant.  A thread whose step crashes
another must discharge the other's obligations in the model update inside the physical round,
which runs at the empty mask against the new configuration (`docs/program-logic.md`, §3;
`docs/activity.md`, §3).  The invariants are then opened before the step and closed after it:

- `untilIGuar_acc_assigned` opens the invariant of an until held in full (`q = 1`).  It gives the
  content with the whole assignment of `k`, the guarantee of the right formula under a later,
  and a closing that takes the content back, discharged or not, after which the half of the
  assignment kept rebuilds the until.
- `untilIGuar_record_discharged` writes the record of the right formula of a discharged
  obligation at the current position, from a resource `X` that implies `Q`, which is given back.
- `untilIGuar_discharge_opened` discharges `k`, a childless child of a parent `p`, at any mask,
  with such an `X`, and gives the content that closes the invariant.

### 4.2 Sets and forests of untils

The number of obligations to discharge need not be known.

- `untilIGuar_acc_assigned_set` opens the invariants of a finite set `S` of untils held in full,
  whose namespaces may depend on the obligation, are pairwise disjoint and avoid a mask `E'`, to
  which it opens.  One closing takes all the contents back.
  `untilIGuar_acc_assigned_set_ndot` is the case of the namespaces `N₀.@k`, opened to
  `E \ ↑N₀`.
- `untilIGuar_record_discharged_set` writes the records of a set of discharged obligations from
  one resource that implies all their right formulas: at a crash, the fact that the thread is
  crashed.
- `untilIGuar_discharge_opened_forest` discharges a forest in one model update: every obligation
  of `S`, with its whole assignment, where `S` is closed under children (`kids`) and hangs below
  the roots `ps`.  It rests on `Obl.discharge_forest` (`docs/model.md`, §6) and leaves each
  root with its children outside `S`.  `…_all` is the case where the roots end without
  children, and `…_threads` the case of thread roots, which end at `thKids j ∅`.

The `untilI` and `finallyI` forms of these rules take no guarantee, since a formula guarantees
its canonical reading (`guar_canon`).  The `untilIGuar` forms get the guarantee `▷ (Q ⊨ₜ G₂)`
from the opening, under a later, so they need a later credit, as does a left formula that is not
timeless; one credit serves a whole set.  The contents of `finallyI`s are timeless, so
`finallyI_acc_assigned_set` gives the assignments without a later.

### 4.3 A note on the proofs

In `TemporalFormulaRules.lean`, a premise `⊑ₛ` built with `TrSpec.canon_le` is written
`@TrSpec.canon_le _ _ _ _ _ _ _ instM instT _ _ _ hG`, with the ambient instances named
(`instM`, `instT`) and explicit.  Elaborated against the expected `⊑ₛ`, the application would
take the instances bound by `⊑ₛ` for its own instance arguments, and holes do not suffice under a
`⊑ₛ` rule such as `TrSpec.always_mono` (`LantanaTest/Guarantee.lean` shows the issue).

## 5. The adequacy proof

### 5.1 The theorems

`lwp_adequacy_temporal`, Theorem 1: let `G` be a trace specification and `R` a trace property
with `G.external ⊆ R`.  Suppose that, for every allocation of the temporal ghost state, the user
can give, from later credits `£ₒ c` and the pieces of the initial threads, under a model update,
a resource `P` with `P ⊨ₜ G` and the `lWP`s of the initial threads.  Then every behavior from
the initial configuration on which the threads are fairly scheduled (`fairScheduling`) satisfies
`R`.

The ghost state is allocated inside the proof, so the premise quantifies over its instances; the
user then chooses the state interpretation (after allocating the language's ghost state), the
postcondition of the forked threads and the postconditions of the initial threads.  The pieces
of an initial thread `j` are its empty bill `thCarriers j ∅` and, if it is not crashed, its
running handle and empty children `thActive j ∗ thKids j ∅`; the model holds the node of a
crashed one (`docs/model.md`, §4).  `init_threads_of_not_crashed` gives the plain list when no
initial thread is crashed.

`lwp_adequacy_safety` assumes the same, with a postcondition of an initial thread `j` that
implies `Φ j`, and concludes Iris-style safety on the same behaviors: no thread of the pool is
ever stuck, and `j`, once a value `v`, satisfies `Φ j v`.

The proof of Theorem 1:

1. The behavior carries no thread label.  The proof chooses a schedule of it and fairness
   counters under that schedule (`exists_fair_schedule_schedCounters`).
2. It allocates the ghost state (§5.2), with the model at the view of the initial configuration.
3. `lWP` is a running system with the one-step property: `sysLwp` is the registry state and the
   running threads of the pool, and `sysStep_lwp` is the check of the registry (`reg_check`, §3)
   followed by one step of the run (`run_step`, §5.3).
4. `lwp_adequacy_internal` runs the program logic from a position `n`: the user's model update
   gives `P`, its guarantee and the `lWP`s; `P` gives the record of `G` at `n`, which is
   eliminated after the first step, against the bundle of the check at `n` and `sysStep_lwp`.
5. Satisfiability reads `G.internal` off at position `0` (`TrSpec.adeq`), which gives
   `G.external`.

### 5.2 Allocation

`adequacy_alloc_names` allocates, before the user's resources: the credit supply, world
satisfaction and the full mask; the model at step `0`, with no obligation and no witness, at the
view of the initial configuration; the pieces of the initial threads (§5.1); the history with
its first entry, for any state interpretation, which is chosen after the allocation; and the
empty registry.  The existential is over the ghost *names* (`ModelNames × TemporalNames`), and
the instances are rebuilt from the names and the cameras of the world (`ModelGS.ofNames`,
`TemporalGS.ofNames`): the instance records are in `Type 4`, too large for the existential
property of satisfiability (`sat_exists`), while the names are small enough.
`iPropSat.sat_alloc` extracts the names from an allocation lemma.

### 5.3 One step of the run

The threads are a pool `tp` with a postcondition function `Ψ`.  In `threadsRun tp Ψ`, each thread
`j` has its postcondition `lwp.liftTerm j Ψ v` if it is a value `v`, and its
`lWP e @ j; ⊤ {{ lwp.liftTerm j Ψ }}` otherwise (`threadRun`).  After a step, the forked threads
`tp.length + k` get the postcondition `forkPost` (`postFork Ψ forkPost tp.length`).

`run_step` simulates the step of the run at position `n` by the `lWP`s of the threads.  From the
history and temporal interpretation, the model at the view of `τf n` and the running threads, it
gives, in the deferred shape, the same at `n + 1` with the facts about the step and `c` later
credits (`runStepPost`).  It is generic in the interpretation of the temporal layer.  First, no
thread of the pool is stuck at `n`: the `lWP` of a stuck thread, at `NotStuck`, proves that it
can step (`run_step_stuck`), whichever thread it is.  Then the proof inverts the trace step of
the thread that the schedule names at `n`:

- It steps, crashed or not (a crashed thread is not a value), and its `lWP` takes the step
  (`run_step_step`): the model update before the step, the progress round with the witnesses of
  `mprog_exists_step` (§5.4), the physical round with its later credits, and the model update
  after the step.  The forked threads start running, and the threads that became values run the
  model updates of their postconditions.
- It is a value: the configuration stutters (`run_step_done`), the model moves to the next step
  index (`modelInterp_step_idx`), and the measures drop through the counters (§5.4).
- It is stuck: impossible, as above.

The physical round moves the model to the view of the new configuration, and a stutter keeps it.
Besides the facts of the one-step property, `runStepPost` gives those that safety needs: no
thread of the pool is stuck at `n`, the pool only grows, and the old threads keep their
postconditions.

### 5.4 The measures, and why the owners of obligations are active

The witness of an assigned obligation with fuel `a` and owner `o` is its fair-scheduler measure
at the next position, `fairMeasure (γ (n + 1)) o a`.  After the progress round of the thread
`i` that the schedule names, these witnesses decrease strictly and keep the witness invariant
and its lower bound (`mprog_exists_step`).  The measure drops from `n` to `n + 1`
(`fairMeasure_next_lt`) for an obligation of `i`, whose fuel dropped in the progress round, and
for an obligation of another active owner, whose counter dropped: by `schedCounters`, an active
thread that the schedule does not name has a smaller counter at the next position.  So every
measure drops across a step of `i` (`obligationsDrop_step`, through the model updates and the
progress round) and across a stutter, where the thread the schedule names is inactive
(`obligationsDrop_inactive`, `owitInvLb_step_inactive_turn`).

Both need every owner of an obligation to be active (`ObligationsThreadActive`).
`get_obligationsThreadActive` proves it at a configuration whose crashed threads the model
sees, from the `Th.done` tokens of the finished threads (`doneTokens`, which `threadsRun`
provides through `lwp.liftTerm`).  An owner is a thread of the pool (`modelInterp_owner_lt`).
It is not a value, whose `Th.done` token contradicts the ownership
(`Th.done_modelInterp_not_owner`).  It is not crashed, since the model holds the node of a
crashed thread, which therefore owns nothing
(`Th.crashed_modelInterp_not_owner`).  `run_step` uses it before and after the progress round
(`obligationsThreadActive_keep`).

### 5.5 Safety

Safety is derived from `run_step` rather than proved by a second simulation.  The step-indexed
reading `safetyIrisTrI j Φ` is `TrIProp.always` of the pure safety facts at the current position
(`safeNow`: no thread of the pool is stuck, and a terminated `j` satisfies `Φ j`).
`threadsRun_safety` proves it by Löb induction, each position being one `run_step`: the step
gives that no thread is stuck at `n`; the postcondition of `j` gives `Φ j v` whenever `j` is a
value `v` (`threadsRun_ifTermVal`), and it does not change across steps.  Satisfiability turns
the reading into the trace property `safetyIris j Φ` (`safetyIrisTrI_trProp`).
`lwp_adequacy_safety` allocates and starts the run as Theorem 1 does, with the registry state as
the interpretation of the temporal layer, initialized from the empty registry of the allocation
(`regStateWith_init`).

## 6. Differences with the Rocq development

- Traces carry no thread label: the adequacy proof chooses the schedule, and the fairness
  counters are an explicit sequence read under it.  So `Cfg.NotStuck` is about every thread of
  the pool, where Rocq's `not_stuck` is about the scheduled thread, and safety holds for every
  thread of the pool, which is stronger.
- `run_step` also gives the pure facts of the step that safety needs, so safety is a Löb
  induction over it, not a second copy of the simulation.
- `safetyIrisTrI` uses the one-formula `TrIProp.always`: Rocq's second formula is only used with
  `True`.
- The postconditions are a function of the thread id.  Where Rocq requires the postcondition of
  `j` to be given (`Ψs !! j = Some Q`), `lwp_adequacy_safety` takes `j < tp.length`; a thread
  forked later gets `forkPost`, about which nothing is assumed.
- Allocation returns ghost names, from which the instances are rebuilt (§5.2).

## 7. The crash test

`LantanaTest/Crash/` verifies end to end a small language whose threads crash (the idea is in
`docs/activity.md`, §3).

- `Lang.lean`: the language, a worker `work n`, a killer and a reviver over a boolean state,
  "the worker is alive"; the worker is crashed while the state is `false` (`instCrash`).  The
  closed world `CrashGF` holds the temporal layer and a ghost variable of the state and of "the
  worker has finished"; the state interpretation `crashInterp` holds half of it, and
  `doneOrCrashed`, a fraction of it, has the state fact `σ = false ∨ fin tp`.
- `Step.lean`: the step rule `lwp_step`, which is `lwp_lift_step_gen_si` for this language, and
  which threads a step crashes or recovers.
- `Kill.lean`: the worker's forest of obligations (`HangsBelow {k} S kids`), each a `finallyI`
  of `doneOrCrashed` in the namespace `oblN.@j` of its obligation `j`; the shared invariant
  `crashInv`, which holds, by the state, the worker's node with its obligations (or, after a
  revival, its empty node), the discharges once it is crashed, and nothing once it has finished;
  and `killer_spec`.  The killer's step that crashes the worker opens the invariants of the
  whole forest before the step (`finallyI_acc_assigned_set_ndot`), discharges the forest with the
  crash disjunct inside the physical round (`finallyI_discharge_opened_forest_threads`), hands
  the emptied node in, and closes the invariants after the round.
- `Worker.lean`: `worker_spec`, by Löb induction.  Alive, the worker pays its bill; at `work 0`
  it discharges the forest in the same way, with the first disjunct, and ends its thread;
  crashed, it steps for free and gets its bill back empty.
- `Reviver.lean`: `reviver_spec`.  Reviving a crashed worker receives its node from the physical
  round and puts it back in the shared invariant; the worker goes on with no obligation.
- `Adequacy.lean`: the worker's obligations, `k` with a chain of any length below it
  (`worker_obligations_alloc`, `chain_alloc`), and `Crash.adequacy` and `Crash.revive_adequacy`: on
  every fairly scheduled behavior of `[work N, kill]` and of `[work N, kill, revive]`, started
  alive, eventually the worker has finished or is crashed.  The killer may give up, so the
  worker's obligation is needed; with the reviver, a crashed worker may recover and finish later.
