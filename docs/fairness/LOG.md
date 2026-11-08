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
