# Performance of the Lantana-Lean build

Where the build time of Lantana-Lean goes, by layer, module and declaration; how it is measured;
what has been done about it; and what is left. Measured on 2026-10-16 at commit `f281253` (later
commits change only documentation and scripts).

| Measure | Value |
|---|--:|
| Clean `lake build` (`LEAN_NUM_THREADS=6`) | 48.9 s |
| Then `lake test` (the 28 test modules) | 4.4 s |
| Modules of the library | 107 |
| Sum of the per-module times (each module alone, 4 threads) | 154.1 s |
| Critical path (longest import chain, by per-module time) | 48.1 s over 30 modules |
| Commands or proofs of 1 s or more | 26 |

The clean build takes as long as the critical path: the build is bounded by its longest chain of
imports, not by the total work. A module cannot start before all of its imports are built.

## Method

- **Environment:** Lean `v4.34.1`, a 36-core Linux container shared with other agents (load
  average 2–6 during the runs); Iris-Lean and its `Ordinals` package prebuilt. Repeated runs
  differ by about a second.
- **Clean build:** remove this package's build directory and build the library; the dependencies
  are kept.
  ```
  rm -rf .lake/build && time LEAN_NUM_THREADS=6 lake build
  ```
- **Per module and per declaration:** `scripts/profile.py` (after a build) elaborates each module
  alone with `lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=200`, against the
  built `.olean` files of its imports, and prints the tables of this page.
  ```
  scripts/profile.py --threads 4 --json profile.json   # about 2.5 minutes
  scripts/profile.py --load profile.json --top 40      # report again from the saved data
  ```
  A module's time is its wall time, including about 0.3 s for loading its imports. The critical
  path adds up these times along the import graph. The profiler reports two kinds of entries:
  a *command* (a declaration's elaboration on the main thread) and a *proof* (a theorem's proof,
  elaborated asynchronously in parallel with the following commands). Only entries above 200 ms
  are reported, so many small commands are not listed one by one.

## Per layer

| Layer | Modules | Sum (s) | Slowest module (s) |
|---|--:|--:|--:|
| Std, Init | 3 | 1.0 | 0.42 |
| Prelude | 3 | 1.1 | 0.40 |
| Algebra | 7 | 3.9 | 0.75 |
| BaseLogic | 22 | 22.7 | 2.04 |
| ProgramLogic | 14 | 14.9 | 2.23 |
| Trace | 23 | 27.1 | 2.15 |
| HeapLang | 8 | 21.7 | 5.82 |
| Examples | 26 | 61.0 | 6.10 |
| root `Lantana` | 1 | 0.6 | 0.61 |

The longest chain to the end of each layer:

| Up to | Chain (s) |
|---|--:|
| `Lantana.BaseLogic` | 11.0 |
| `Lantana.ProgramLogic` | 18.6 |
| `Lantana.HeapLang` | 22.6 |
| `Lantana.Trace` | 26.7 |
| `Lantana.Examples.Lib` (all of the above) | 27.5 |
| `Lantana` | 48.1 |

## Critical path

`Std.Porting` → `Init` → `Prelude.Ids` → the pure model (`Obligation`, `Witness`, `ModelRel`,
`Forest`; 2.4 s) → the ghost model (`OSat`, `OForest`, `MUpd`, `OPreds`; 6.2 s) → the program logic
(`OblForest`, `OblForestRules`, `WeakestPre`; 5.9 s) → the trace layer (`Guarantee`,
`GuaranteeRules`, `TemporalFormula`, `TemporalFormulaRun`, `TemporalFormulaRules`,
`GuaranteeInfer`, `GuaranteeRec`, `Trace`; 11.0 s) → `Examples.Lib` → the queue family:

| Module | Time (s) |
|---|--:|
| `Examples.TicketLock` | 4.67 |
| `Examples.Queue` | 6.10 |
| `Examples.TaskQueue` | 2.55 |
| `Examples.TaskQueueClient` | 3.02 |
| `Examples.TaskQueueFlagStableClient` | 3.05 |

These five case studies are 19.4 s of the 48.1 s. HeapLang is not on the critical path: its
chain ends at 22.6 s, before the trace layer's.

## Slowest modules

| Module | Time (s) | Note |
|---|--:|---|
| `Examples.Queue` | 6.10 | `dequeue_spec` 4.1 s, `enqueue_spec` 1.7 s |
| `HeapLang.Syntax` | 5.82 | `Exp.enc_inj` 2.8 s, the mutual inductive 0.8 s |
| `HeapLang.Notation` | 5.71 | 73 `syntax` commands; the `hl(...)` `macro_rules` 1.5 s |
| `Examples.TicketLock` | 4.67 | |
| `Examples.ExtendedInt` | 4.55 | `lwp_lt` 3.5 s |
| `Examples.TicketLockMono` | 3.93 | |
| `HeapLang.Instances` | 3.60 | the language instance 1.4 s |
| `Examples.HandoffClient` | 3.10 | |
| `Examples.TaskQueueFlagStableClient` | 3.05 | |
| `Examples.TaskQueueClient` | 3.02 | |
| `Examples.HandoffFlagStableClient` | 3.00 | |
| `Examples.TicketLock2` | 2.79 | |
| `Examples.TaskQueue` | 2.55 | |
| `HeapLang.ProofMode` | 2.50 | |
| `Examples.Nondet` | 2.40 | |

## Slowest commands and proofs

105 entries are above 200 ms, 77.8 s in all, 58.2 s of it in the case studies.

| Time (s) | Kind | Declaration |
|--:|---|---|
| 4.08 | proof | `Examples.Queue.dequeue_spec` |
| 3.46 | proof | `Examples.ExtendedInt.lwp_lt` |
| 2.79 | proof | `HeapLang.Exp.enc_inj` |
| 2.12 | proof | `Examples.HandoffClient.main_spec` |
| 2.11 | proof | `Examples.TicketLockMono.acquire_spec` |
| 2.04 | proof | `Examples.HandoffFlagStableClient.main_spec` |
| 1.98 | proof | `Examples.TaskQueueFlagStableClient.main_spec` |
| 1.97 | proof | `Examples.TaskQueueClient.main_spec` |
| 1.95 | proof | `Examples.TicketLock.acquire_spec` |
| 1.85 | proof | `Examples.TicketLockMono.acquire_loop_inner` |
| 1.80 | proof | `Examples.TicketLock.acquire_loop_inner` |
| 1.67 | proof | `Examples.Queue.enqueue_spec` |
| 1.52 | command | the `hl(...)` `macro_rules` (`HeapLang.Notation`) |
| 1.45 | proof | `mprog_exists_step` (`Trace.Adequacy.Step`) |
| 1.44 | proof | `Examples.Nondet.nest_spec` |
| 1.43 | command | `instEctxItemLanguageExp` (`HeapLang.Instances`) |
| 1.40 | proof | `Examples.TaskQueue.runTask_spec` |

Outside the case studies, only four entries take 1 s or more: `Exp.enc_inj`, the `hl(...)`
`macro_rules`, `mprog_exists_step` and the HeapLang language instance. In the logic layers
(BaseLogic, ProgramLogic, Trace) nothing but `mprog_exists_step` takes more than 0.7 s. The
case-study specifications are long proof-mode proofs, and a proof-mode step (`iintro`, `iapply`,
`imodintro`, …) costs roughly 25–30 ms.

## History

**Proof tuning (milestone M10).** A first profiling pass found a few slow proofs, three of them
in HeapLang's syntax and its language instance, and made them faster:

| Declaration | Before (s) | After (s) |
|---|--:|--:|
| `Val.enc_inj` | 12.62 | 0.53 |
| `fillItem_no_val_inj` | 7.09 | 1.38 |
| `Exp.enc_inj` | 6.50 | 2.81 |
| `ExtendedInt.lwp_lt` | 5.52 | 3.44 |

The module `HeapLang.Syntax` went from 15.6 s to 5.9 s. The fixes:

- constructor disjointness by `decide` on the constructor tags before `grind`;
- `Val.enc_inj` derived from `Exp.enc_inj` instead of a second mutual induction;
- `cases` on equations instead of `simp_all` over 27 × 27 constructor pairs;
- `simp at h ⊢` instead of `simp_all` when the context holds large specification hypotheses.

**Asynchronous proofs (commit `f281253`).** The attribute `@[lantana_alias]` read the declaration
with `Environment.find?`, which waits for the complete constant. So each aliased theorem's command
waited for its own proof, and the proofs of a module were elaborated one after another. Since
almost every theorem carries an alias, this serialised nearly all proofs. The attribute now uses
`findAsync?`, which gives the kind and the signature without waiting. The aliases are unchanged.

| Measure | Before (s) | After (s) |
|---|--:|--:|
| Full rebuild of the library (6 threads; two alternating runs each) | 66.1–67.1 | 48.7–48.8 |
| Sum of the per-module times | 202.7 | 154.1 |
| Critical path | 72.5 | 48.1 |
| `Examples.Queue` | 8.99 | 6.10 |
| `Examples.TicketLock` | 8.12 | 4.67 |
| `Examples.TicketLockMono` | 7.17 | 3.93 |
| `ProgramLogic.OblForestRules` | 3.77 | 2.23 |
| `Trace.TemporalFormulaRules` | 3.67 | 2.15 |

Iris-Lean's `@[rocq_alias]` has the same code; see item 6 of
[`iris-lean-proposal.md`](iris-lean-proposal.md).

## What is left

The build is bounded by the critical path, so only changes on that path shorten it.

- **The queue family** (19.4 s of the path). `TaskQueueFlagStableClient` imports
  `TaskQueueClient` only for its programs (`decrReentrant`, `main`). Moving the programs to a
  module of their own would let the two clients build in parallel, saving about 3 s. Splitting
  `Queue.dequeue_spec` (4.1 s) into lemmas would let its parts run in parallel.
- **Import loading** costs about 0.3 s per module, so about 9 s along the 30 modules of the
  path. Merging the small modules at its start (`Init`, `Prelude.Ids`, the pure model) would save
  a little but lose structure; it is not worth it.
- **Proof-mode cost**, about 25–30 ms a step, dominates the case studies. This is a matter for
  Iris-Lean's proof mode rather than for Lantana.
- **Off the path:** `Exp.enc_inj` (2.8 s), the HeapLang notation (5.7 s) and the HeapLang
  language instance (1.4 s) are in HeapLang modules. HeapLang's longest chain ends 4 s before the
  trace layer's, so speeding them up would not shorten the build.
