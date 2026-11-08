# Lane `lantana-fairness`: log (times UTC)

Worktree `/work/wt/lantana-fairness`, branch `agent/fairness` from `main` @ `effc218`.  The plan is
`/work/xv6iris-lean/local-plan/lantana-fairness/PLAN.md`; the file ported is
`/work/xv6iris-lean/MachCSL/Liveness/FairnessTheory.lean` (`lean-lantana` @ `050cf0808`).  "Green"
means `lake build --wfail`, `lake test`, `scripts/audit.sh` and `scripts/check-imports.sh` (the
repository has no `lake lint` driver: `lake lint` reports "no lint driver configured").  Prover
subagents (Opus) work in `/work/wt/sub-*` on `agent/sub-*`, branched from this branch's HEAD, with
`LEAN_NUM_THREADS=4`; the lead reviews and merges with `--no-ff`.

## 0. M0, baseline (2026-11-08)

- Owner's decisions on the plan of the first step (2026-11-08): (1) the fix of the behavior
  definitions is the removal of the thread label from traces, with fair scheduling the relational
  `Sched.SF` and the schedule chosen inside adequacy; `Language.lean` stays untouched, the
  activity "in the pool and not a value" is defined in `Trace.lean`; (2) safety is strengthened to
  "no thread of the pool is stuck"; (3) the theory lives in `Lantana/Trace/Fairness/`, namespace
  `Lantana.Fairness`, every name of the theory file kept; (4) both commits (the theory port and the
  behavior refactor) in this step.  No merge into `main`: the owner reviews first.
- Baseline build in the worktree: `lake build --wfail` green, 372 jobs, cached.
- Lead's plumbing before handing out tasks: `Nat.exists_min`, `Nat.minWitness`, `_spec`, `_min`
  moved from `Trace/FairScheduling.lean` to the new `Lantana/Prelude/Nat.lean` (the theory's
  `MissHit.minWitness` is this function); 373 jobs, green, check-imports ok, audit ok.

## 1. Commit 1, the theory port: tasks handed out (2026-11-08)

- Task 1a (lean-prover-1): port the theory into `Lantana/Trace/Fairness/{AttemptGrant,Action,Pool,
  Thread,FairLabel}.lean` and the aggregator, names kept; test file with axiom prints.
- Task 1b (lean-prover-2): the per-thread step on configurations (`TraceStepOf i`), activity on
  configurations, the step lemmas (another thread's step keeps an entry, the pool never shrinks, a
  value stays a value) and the convexity of activity along a run.
- Task 1c (after 1a and 1b): the instance `Pool (Cfg Expr State)`, `IsBehavior` at position 0 is
  `PoolRun`, `Action.Convex` of activity, `BehFscnt` from the fair schedule.

Results (2026-11-08).  Task 1b (`531bd56`, merged): `TraceStepOf i`, `TraceStep` its instance at the
scheduled thread, `Cfg.active`/`Cfg.inactive` with their two lemmas, the step facts (`length_le`,
`get?_ne`, `get?_of_val`, `isSome_of_isSome`, `active_of_step_ne`, `inactive_of_step_of_isSome`) and
the run facts (`isSome_mono`, `inactive_mono_of_isSome`, `active_convex`); no downstream proof needed
a change (`rcases` sees through the new layer).  Task 1a (`476f614`, merged): the six modules (505 +
136 + 229 + 260 + 217 + 108 lines) and `LantanaTest/Fairness.lean` (54 lines, seven axiom prints;
`Action.sf_iff_wf_of_convex` uses no axiom).  The lead diffed the module bodies against the source's
`namespace Fairness … end Fairness` (1032 vs 1015 non-blank lines): the only differences are the
least-witness copies replaced by `Lantana.Nat.*` (12 call sites), one `show` → `change`
(`FairLabel.visit_infOften`, the `show` linter) and the section note on the least witnesses; no name
changed.  Lead's fix after the merge: the naming policy's last sentence, which named MachCSL's
`Fairness.lean`, now points at the language instance.  Green after both merges: build 379 jobs,
test 407 jobs, audit ok, check-imports ok (281 imports).  Sub worktrees and branches removed.

Task 1c (`4010d76`, merged, lean-prover-3): the instance `Fairness.Pool (Cfg Expr State)` with
`TraceStepOf` as the step, `IsBehavior.poolRun`, `isBehavior_of_schedule`, `Cfg.active_convex'`,
`fairScheduling_sf_iff_wf` (fair scheduling is weak fairness, since activity is convex),
`BehFscntSched`, `behFscntSched_of_counters`, `exists_behFscntSched_of_fair_schedule`,
`exists_fair_schedule_behFscnt`, `behFscnt_of_behFscntSched`, and the relabelling corollary
`IsBehavior.exists_relabel_behFscnt` (a fairly scheduled behavior relabelled by a fair schedule has
fairness counters); one explicit `(active := Cfg.active)` was needed.  **Commit 1 complete**: the
theory and Lantana's instance, with the labelled traces still in place.  Green: build 379 jobs,
test 407 jobs, audit ok, check-imports ok (282 imports).

## 2. Commit 2, the behavior refactor: tasks handed out (2026-11-08)

- Task 2a (one Opus prover): the label removed from `Trace`, `fairScheduling := ∀ i, Sched.SF
  Cfg.active i τ.seq`, `BehFscnt` the counters of a run under a schedule, the schedule threaded
  through `Guarantee`, `TemporalFormulaRun`, `Adequacy/{Step,RunStep,Temporal,Safety}`, safety
  strengthened to "no thread of the pool is stuck"; target `lake build Lantana.Trace --wfail`.
  Brief: `local-plan/lantana-fairness/briefs/brief-2a.md`.
- Task 2b (after 2a): the examples, the tests and the README; brief `brief-2b.md`.

Result 2a (`d284169`, merged, lean-prover-1): `Trace.seq : Nat → Cfg`, `TraceStep i` per thread,
`IsBehavior` = some thread's trace step at every position, `fairScheduling τ := ∀ i,
Fairness.Sched.SF Cfg.active i τ.seq`, `BehFscnt σ sched γ` (the former `BehFscntSched`), the
schedule threaded as one more binder through `sysStepPre`, `recordPre`, the record lemmas,
`sysStepIter`, `alwaysRun`, `untilRun*`, `run_step`, `threadsRun_safety`, `lwp_adequacy_internal`;
`Cfg.notStuck` quantifies over every thread of the pool and is proved in `run_step` by a classical
case split and `run_step_stuck` (which never needed the stuck thread to be the scheduled one);
`lwp_adequacy_temporal` and `lwp_adequacy_safety` lose the thread argument and take
`hinit : τ.seq 0 = (tp, σ)`; `TraceState`, `turn`, `turnDist`, `fscntNextRel*` gone (Rocq names
`trace_state`, `trace_thread`, `thread_turn`, `fscnt_next_rel_th`, `fscnt_next_rel`,
`exists_fscnt_next` recorded with `#lantana_ignore`).  Prover's decisions accepted: the post-step
facts no longer repeat the two global facts (`Schedule`, `BehFscnt`); `runStepPost` has no `sched`
argument; the stuck case of `run_step` still goes through `run_step_stuck`.  Two files outside the
brief needed the extra binder (`GuaranteeRules.lean`, `TemporalFormulaRules.lean`).  `lake build
Lantana.Trace --wfail` green (62 modules); `Lantana.HeapLang` builds unchanged; the examples and
the tests break as expected (task 2b).  Lead's fix after the merge: one over-long docstring line
in `Safety.lean`.

Result 2b (`6dbcd1f`, merged, lean-prover-2): the end-to-end theorems of eleven example files take
`hinit : τ.seq 0 = (tp0, σ0)` and call the adequacy theorems without the thread argument;
`Flag.flagRun : Nat → Cfg`; `NonstrictMove.loopRun`, `Paradox.loopRun` over configurations with the
new lemmas `loopRun_traceStep` (every thread of the pool steps at every position) and the
fairness proofs redone (`Paradox.sched`, `sched_eventually` deleted);
`TicketLock.releaseProgress_served` over `Nat → Cfg`; four test files; README's adequacy
paragraph and "Fixed concrete choices" bullet.  Lead's edits beside it: `docs/paper-correspondence.md`
(three rows: traces without a label, `Fair` as `Sched.SF`, safety for every thread).
**Commit 2 complete.**  Final checks on `agent/fairness`: `lake build --wfail` 379 jobs, `lake test`
407 jobs (exit 0), `scripts/audit.sh` ok, `scripts/check-imports.sh` ok (281 imports); every
`#print axioms` guard shows the standard three axioms (`Action.sf_iff_wf_of_convex` none,
`fairScheduling_sf_iff_wf` `propext` only).  No sub worktree or branch left.

Not done, for the owner: `docs/rocq-correspondence.md` is stale for the rows `trace_state`,
`trace_thread`, `thread_turn`, `thread_active`, `thread_na`, `thread_active_or_not`,
`thread_active_and_not_false`, `fair_scheduling`, `beh_fscnt`, `fair_scheduling_fscnt`,
`fscnt_next_rel_th`, `fscnt_next_rel`, `exists_fscnt_next`, `adequacy_safety.not_stuck`,
`if_term_val`, `obls_thread_active` and the line numbers of the trace files; regenerating it with
`scripts/rocq-table.sh` needs the Rocq checkout, which this container does not have (without it
the script drops the Rocq grouping and the coverage report).  Next milestone: M2,
`docs/fairness/DESIGN.md`, then the owner's confirmation of D2–D6 before M3.

## 3. Step 2: the language-independent trace layer and the theory over `TrProp` (2026-11-08)

Plan `local-plan/lantana-fairness/PLAN-trace-generalization.md`, approved by the owner with the
recommendations T1–T6.  Lead's decision on the namespaces (brief S1): the generic declarations keep
today's names and namespaces (`Lantana.Trace C`, `Lantana.TrProp C`, the connectives
`Lantana.TrProp.*`), and Lantana's traces are written `Trace (Cfg Expr State)` at the use sites,
since an abbreviation with the old name at a different arity is impossible and re-exporting the
~35 downstream names would be fragile.

- Task S1 (lean-prover-1): the layer `Lantana/Temporal/{Trace,TracePropRules,Pool}.lean`, Lantana's
  instance of `Pool`, the use sites, the layering script, the docs.  Brief `briefs/brief-S1.md`.

Result S1 (`4588f1a`, merged, lean-prover-1): `Lantana/Temporal/{Trace,TracePropRules,Pool}.lean`
(178 + 463 + 92 lines) and `LantanaTest/Temporal.lean` (78); the generic `Trace C`, `TsProp C`,
`TrProp C`, the connectives with the new atoms `step`, `not` (`¬ₜ`), `atPos`, the rules with
tail invariance, the classical dualities, the position bridges and `Absolute`; the class `Pool`
(`Step`, `active`), `Steps`, `active`, `inactive`, `IsBehavior := □ₜ ∃ₜ i, Steps i`,
`IsBehaviorOf`, `Schedule`, `StepsInfOften` with unfolding lemmas (`Iff.rfl`); Lantana's instance
`Pool (Cfg Expr State) := ⟨TraceStep, Cfg.active⟩` in `ProgramLogic/Trace.lean`; 193 replacements
of the two-argument trace types in 43 files; `check-imports.sh` with the layer `Temporal` after
`Prelude`; README and paper-correspondence rows.  Only three proofs needed more than the rename
(the two `loopRun_behavior`, `IsBehavior.poolRun`, all through `isBehavior_iff`).  Note: the layer
has no Iris logic, but `Lantana.Init` and `Prelude.Ids` bring `Iris.Init` and `Iris.Std`.

S2 hand-out.  The lead wrote the skeleton of the theory over `TrProp`
(`Lantana/Temporal/Fairness/{AttemptGrant,Action,Sched,Thread,FairLabel}.lean`,
`Lantana/Temporal/Fairness.lean`, `Lantana/Temporal/FairScheduling.lean`): every definition and
every theorem statement, proofs `sorry`, the ported `MissHit` engine spliced in unchanged; it
typechecks (`lake build Lantana.Temporal`, 77 jobs).  Committed as a WIP on this branch so that
the three provers branch from one base; the branch has `sorry`s until the three merges land, and
the audit is run after them.  Provers: A (lean-prover-1) `AttemptGrant` and `Action`;
B (lean-prover-2) `Sched` and `Thread`; C (lean-prover-3) `FairLabel` and `FairScheduling`.
Two statement fixes while typechecking: dot notation does not work on `TrProp C` (an abbreviation
of a function type), so the bridge is `TrProp.along P τ`; `Sched.stepsInfOften_of_sf` needs the
ascription `: TrProp C`.
The skeleton reuses the namespace `Lantana.Fairness` of the positional theory still in
`Lantana/Trace/Fairness/`, so it is not imported by the `Lantana.Temporal` aggregator until S3
deletes the old theory (both in one environment clash); the provers build their modules by name.

Results S2 so far.  Group B (`306af11`, merged): `Sched.lean` and `Thread.lean`, 24 theorems, no
statement changed, no helper; `labelledView_of_sf` is proved from the definition of `SF` rather
than through `fair_mono`, because `fair_mono`'s hypotheses are entailments on every trace and the
schedule only holds from `τ.pos` on.  Group C (`abfc86c`, merged): `FairLabel.lean` and
`FairScheduling.lean`, 19 theorems, no statement changed; the fair-labelling proof carries over
with the claim's `τ.pos ≤ n` conjunct and the claims taken from `max N τ.pos`.
Group A (`44e3146`, merged): `AttemptGrant.lean` and `Action.lean`, the bridge and 31 theorems, no
statement changed; one helper, `always_eventually_iff_infOften_from` (the bridge with positions
shifted by `τ.pos`), because `IsCounter` constrains the counter from `τ.pos` on while the engine's
counter constrains every position, so the counter-to-fairness direction of `fair_iff_counter`
shifts the run.  **S2 complete**: 74 theorems proved, `lake build Lantana.Temporal.Fairness
Lantana.Temporal.FairScheduling --wfail` green (76 jobs), no `sorry` under `Lantana/Temporal`,
`scripts/audit.sh` ok.  The theory is not yet imported by the aggregator (S3).

- Task S3 (one Opus prover): the switch to the new theory, Lantana's fair-scheduling facts, the
  adequacy proofs on the `TrProp` statements, the examples' fairness proofs, tests, docs.  Brief
  `briefs/brief-S3.md`.

Result S3 (`54e399b`, merged, lean-prover-2): `Lantana/Trace/Fairness/` (positional theory, 1456
lines) deleted; the aggregator `Lantana.Temporal` imports the theory and the generic fair
scheduling; `Lantana/Trace/FairScheduling.lean` holds only Lantana's instance facts
(`Cfg.active_convex' : IsBehavior ⊆ Action.Convex (Cfg.active i)`, `fairScheduling_sf_iff_wf'`);
the adequacy facts are `Schedule sched ⟨0, τf⟩ ∧ BehFscnt sched γ ⟨0, τf⟩ ∧ owitInvLb … ∧ histTrace`,
read at `n` with `schedule_iff`/`behFscnt_iff`; `GuaranteeRules.lean` and
`TemporalFormulaRules.lean` compiled unchanged; `lwp_adequacy_temporal`/`lwp_adequacy_safety`
keep their statements, with `fairScheduling` now the generic trace property at Lantana's instance;
the two `loopRun_fair` proofs redone; `LantanaTest/Fairness.lean` rewritten (nine axiom guards:
`Action.sf_iff_wf_of_convex` and `fairScheduling_sf_iff_wf` use `propext` only,
`labelledView_of_sf` no axiom, the rest the standard three); `Cfg.inactive` kept in the two
stutter lemmas of `Step.lean`.  **Step 2 complete.**  Final checks on `agent/fairness`:
`lake build --wfail` 384 jobs, `lake test` 413 jobs (exit 0), `scripts/audit.sh` ok,
`scripts/check-imports.sh` ok (290 imports).  The new layer `Lantana/Temporal` is 2182 lines
(100 theorems in the fairness modules); the branch differs from `main` in 65 Lean files
(+3226/−1180).  No sub worktree or branch left.  Still for the owner: `docs/rocq-correspondence.md`
is stale (no Rocq checkout here).  Next: M2, `docs/fairness/DESIGN.md`.
