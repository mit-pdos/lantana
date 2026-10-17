# From the paper to Lean

This document relates *Decoupling Liveness Obligations from Threads in the Lantana Concurrent
Separation Logic* (POPL 2027) to Lantana-Lean. It follows
[PAPER.md](https://github.com/dongjaelee1/liveness/blob/main/PAPER.md) of the Rocq development,
section by section and row by row, and gives the Lean name of each item. PAPER.md gives the Rocq
names; `#check RocqLantana.rocq_name` finds the Lean declaration of a Rocq name, and
[`rocq-correspondence.md`](rocq-correspondence.md) lists all of them. Lean names are relative to
the namespace `Lantana`, and files to `Lantana/`.

1. [Results](#1-results)
2. [Differences from the paper](#2-differences-from-the-paper)
3. [Predicates](#3-predicates-fig-1-35)
4. [Rules](#4-rules-figs-36-5)
5. [Traces, temporal properties and adequacy](#5-traces-temporal-properties-and-adequacy-6-fig-7)
6. [Case studies](#6-case-studies-27)
7. [Checking the results](#7-checking-the-results)

## 1. Results

| Result | Paper | Lean |
|---|---|---|
| The logic: the predicates and the rules the paper displays, as lemmas about `lWP` and the model update `\|={E}=>m`; the carrier rules become rules of the obligation forest | §1–§5, Figs. 1, 3–6 | `Lantana/` |
| Adequacy: `lwp_adequacy_temporal` (Theorem 1), and Iris-style safety `lwp_adequacy_safety` | §6 | `Trace/Adequacy/Temporal.lean`, `Trace/Adequacy/Safety.lean` |
| The case studies, with end-to-end liveness and safety theorems for the client programs | §2, §4.3, §5, §7 | `Examples/` |
| A pure-step rule that burns no fuel is unsound: `Examples.Paradox.no_lc_absurd` | end of §6.2 | `Examples/Paradox.lean` |
| Nothing is admitted, and the results assume only Lean's standard axioms | — | [§7](#7-checking-the-results) |

## 2. Differences from the paper

The differences that PAPER.md describes hold for Lean as well: the weakest precondition `lWP`
replaces the fuel-burning triple, obligations form a forest without carriers, temporal formulas
are `iProp`s with guarantees `P ⊨ₜ G`, and trace specifications have two entailments. In Lean:

- **The triple** is a texan `lWP` triple whose superscripts are assertions `thKids i G`:
  ```
  l{{{ threadExpr i C e ∗ thKids i G ∗ P }}} e @ i; E
  l{{{ v, RET v; threadExpr i C (.val v) ∗ thKids i G' ∗ Q v }}}
  ```
  The rules of the triple are `lwp_*` lemmas or entailments and model updates `|={E}=>m`, usable
  at any point of an `lWP` proof (`mupd_lwp`, `lwp_mupd`).
- **The obligation forest:** parents are `Parent.thread i` and `Parent.obl k`, and
  `Par.kids p K` says that the children of `p` are `K`. The interface is
  `ProgramLogic/OblForest.lean`, sealed: its predicates are irreducible definitions over the
  model `Model.OPreds` with unfolding lemmas, rather than a class with one instance. Derived rules
  are in `ProgramLogic/OblForestRules.lean`.
- **Temporal formulas** `alwaysI`, `untilI`, `finallyI` are `iProp`s; a guarantee `P ⊨ₜ G`
  (`Guar P G`) is inferred by `IntoGuar` instances, and adequacy concludes the trace reading
  `G.external` (`Trace/Guarantee.lean`, `Trace/GuaranteeInfer.lean`).
- **Two entailments of trace specifications:** in-logic entailment `G ⊑ₛ H` (`TrSpec.le`)
  transports guarantees (`guar_weaken`) but is too weak for temporal reasoning
  (`TrSpec.always_elim_not_le`); trace entailment `G.external ⊆ R` is LTL on traces
  (`Trace/TracePropRules.lean`), and `TrSpec.cast` transports it along a guarantee
  (`guar_cast`). `IntoTrace P R` infers the trace property that `P` guarantees.

Lean also departs from Rocq in its implementation (see *Design* in the
[README](../README.md#design-the-main-departures-from-rocq)): one language per world with thread
ids as positions in the pool, no observations or prophecies, a fixed fair-scheduler bound and
fuel type, and ghost names exposed by allocation.

## 3. Predicates (Fig. 1, §3–§5)

| Paper | Lean | File |
|---|---|---|
| `{P}^G_i e {Q}^G'_E` (fuel-burning triple) | the texan `lWP` triple of §2 (persistent, as the `□`-specifications of §3.4) | `ProgramLogic/Notation.lean`, `ProgramLogic/WeakestPre.lean` |
| carrier superscripts / `carriers_i G` (Thm 1) | no carriers: `thKids i G`, the children of thread `i`; every initial thread starts with `thKids i ∅` | `ProgramLogic/OblForest.lean` |
| `Fuel^ℓ_G μ` | no carrier fuel: `Obl.fuel k ℓ μ` of each child `k` of the thread; for a set, `oblFuels K μ` | `ProgramLogic/OblForest.lean` |
| `obls^ℓ_g K` | `Par.kids p K` (`thKids i K` at a thread, `oblKids k K` at an obligation); below an obligation the layer bound is its witness layer (`parBelow`, `parLe`) | `ProgramLogic/OblForest.lean` |
| `Φ until^k_q Ψ` | `untilI N k q P Q` (variant `untilIGuar` with given readings, e.g. for recursion, `renew` in `Trace/GuaranteeRec.lean`); guarantee `guar_untilI`. A discharged until is `untilIDone k Q` (`untilI_discharge_done`, or `untilIDone_init` for an until fulfilled at its allocation); guarantee `guar_untilIDone` | `Trace/TemporalFormula.lean`, `Trace/TemporalFormulaRules.lean` |
| `finally^k Φ` | `finallyI N k q Q` | `Trace/TemporalFormula.lean` |
| `obl∎ k` (discharged) | `Obl.discharged k` | `ProgramLogic/OblForest.lean` |
| `tr$^ℓ_k m` (transfer credit) | `Obl.fuel k ℓ m` (the only kind of fuel) | `ProgramLogic/OblForest.lean` |
| `wit^ℓ k` (witness) | `Wit.layer k ℓ` | `ProgramLogic/OblForest.lean` |
| `wit€ k` (witness credit, §4.1) | `Wit.cred k a` (`a` an ordinal amount; a step gives `Wit.cred k 1`) | `ProgramLogic/OblForest.lean` |
| `∎ i` (thread finished, Thm 1) | `Th.done i` | `ProgramLogic/OblForest.lean` |
| `always I` | `alwaysI N I` (variants `alwaysIAs`, `alwaysIGuar`); guarantee `guar_alwaysI` | `Trace/TemporalFormula.lean`, `Trace/TemporalFormulaRules.lean` |
| `£ α` (transfinite later credits) | `£ₒ α` (`credit`) and the `tlc_*` lemmas | `BaseLogic/LaterCredits.lean` |
| `Measure` (with extension measure `∇`, §3.2) | inductive `Measure`; `∇` is `Measure.extend`; the interpretation into ordinals is `Measure.rep` | `Algebra/Measure.lean` |
| layers `ℓ` (ordinals) | `Layer := Ordinal.{0}`, from the `Ordinals` package of Iris-Lean (one copy of the ordinals, where Rocq needs two) | `Prelude/Ordinal.lean` |

## 4. Rules (Figs. 3–6, §5)

| Paper rule | Lean | File |
|---|---|---|
| STEP-PURE, STEP-PURE-LC, STEP-PURE-WIT | `lwp_pure_step`; HeapLang instance `HeapLang.lwp_pure_step` | `ProgramLogic/Lifting.lean`, `HeapLang/PrimitiveLaws.lean` |
| STEP-REF / STEP-STORE / STEP-LOAD | `HeapLang.lwp_alloc` / `HeapLang.lwp_store` / `HeapLang.lwp_load` | `HeapLang/PrimitiveLaws.lean` |
| FORK* | `HeapLang.lwp_fork` (the children `K ⊆ G` given to the new thread move with one unit of fuel each) | `HeapLang/PrimitiveLaws.lean` |
| EXIT | `lwp_value`; `Th.terminate` turns `thKids i ∅` into `Th.done i`, which forked threads owe in their postcondition (`liftTerm`) | `ProgramLogic/WeakestPre.lean`, `ProgramLogic/OblForest.lean` |
| FINALLY-EXIT* | `Examples.threadExpr_terminate_finally` | `Examples/Lib.lean` |
| FINALLY-ALLOC* | `untilI_alloc` with left formula `True` (`finallyI`) | `Trace/TemporalFormulaRules.lean` |
| BIND | `lwp_bind` | `ProgramLogic/WeakestPre.lean` |
| FRAME, UPD-ELIM | `lwp_strong_mono`, `fupd_lwp` / `lwp_fupd` / `mupd_lwp` / `lwp_mupd` | `ProgramLogic/WeakestPre.lean` |
| CARRIER-ALLOC | no carriers: `Obl.new` creates an obligation below a parent | `ProgramLogic/OblForest.lean` |
| CARRIER-DELETE | no carriers: `Obl.discharge_leaf` discharges a childless obligation; its children can first move up for free (`Obl.move_up`; both: `obl_discharge_lift_kids`) | `ProgramLogic/OblForest.lean`, `ProgramLogic/OblForestRules.lean` |
| FUELS-ADD / FUELS-UNION / FUELS-EMPTY | `Obl.fuel_add`, `oblFuels_add_obls` / `oblFuels_remove_obls`; FUELS-EMPTY is the empty big-op | `ProgramLogic/OblForest.lean`, `ProgramLogic/OblForestRules.lean` |
| FUELS-LAYER | `Obl.fuel_extend` (and `Obl.fuel_extend_set`) | `ProgramLogic/OblForest.lean`, `ProgramLogic/OblForestRules.lean` |
| ALWAYS-ALLOC / ALWAYS-ACC | `alwaysI_alloc` / `alwaysI_acc`; guarantee `guar_alwaysI` | `Trace/TemporalFormulaRules.lean` |
| LÖB | Löb induction over the transfinite step index of Iris-Lean (`iloeb`) | (Iris-Lean) |
| LC-SPEND | `tlc_later`, `tlc_later_strong` | `BaseLogic/LaterCredits.lean` |
| UNTIL-ALLOC | `untilI_alloc` (or `Obl.new`, then `untilI_init`) | `Trace/TemporalFormulaRules.lean` |
| UNTIL-ACC | `untilI_acc` | `Trace/TemporalFormulaRules.lean` |
| UNTIL-DISCHARGE | `untilI_discharge`, `finallyI_discharge` (`untilI_discharge_done` gives the done until) | `Trace/TemporalFormulaRules.lean` |
| UNTIL-DONE-FALSE | `untilI_discharged_false` | `Trace/TemporalFormulaRules.lean` |
| UNTIL-SPLIT | `untilI_frac_split`, `untilI_frac_add` | `Trace/TemporalFormulaRules.lean` |
| WIT-IND | `Wit.layer_ind` | `ProgramLogic/OblForestRules.lean` |
| OBLS-OFFLOAD | `Obl.move` (an obligation moves with its subtree, burning one unit of its own fuel above the new parent's witness layer, `parBelow`); set versions `obl_move_set_gen` / `obl_move_thread_set` / `obl_move_obl_set` | `ProgramLogic/OblForest.lean`, `ProgramLogic/OblForestRules.lean` |

## 5. Traces, temporal properties and adequacy (§6, Fig. 7)

| Paper | Lean | File |
|---|---|---|
| `Cfg`, `TPool`, THREAD-STEP/THREAD-DONE, `Trace`, `Behavior` | `Cfg`, `ThreadPool` (a list; thread ids are positions), `ThreadStep` / `ThreadDone`, `Trace`, `IsBehaviorOf` / `IsBehaviorOfPool`; no observations. Additionally `ThreadStuck`: a stuck scheduled thread stutters, so stuck executions are behaviors too | `ProgramLogic/Trace.lean` |
| temporal properties `Φ, Ψ` and `⟦·⟧_t` | trace specifications `TrSpec`, trace reading `TrSpec.external` (step-indexed reading `TrSpec.internal`); `Always` = `TrSpec.always`, `Until` = `TrSpec.strongUntil`, `Finally` = `TrSpec.eventually`; trace properties `TrProp` with `□ₜ`, `𝒰ₜ`, `◇ₜ` (`TrProp.always`, `TrProp.strongUntil`, `TrProp.eventually`) | `Trace/TrSpec.lean`, `Trace/TraceProp.lean` (rules: `Trace/TrSpec.lean`, `Trace/TracePropRules.lean`) |
| `Fair` (fair scheduling) | `fairScheduling` | `Trace/FairScheduling.lean` |
| logical assertions `φ` and `⟦·⟧_l` | no syntax: temporal formulas are `iProp`s; guarantee `P ⊨ₜ G` (`Guar P G`), inferred by `IntoGuar` | `Trace/Guarantee.lean`, `Trace/GuaranteeInfer.lean` |
| `lift` | `TrSpec.canon P`, the canonical trace specification guaranteed by `P` (`guar_canon`); `trSpecOf P`, the one inferred by `IntoGuar` | `Trace/Guarantee.lean`, `Trace/GuaranteeInfer.lean` |
| `Label s e`, `ChooseNat`, atomic property `label_i "s" v` | `HeapLang.Exp.label`, `HeapLang.Exp.chooseNat`; atomic properties are state predicates `HeapLang.pointstoSat` / `HeapLang.threadExprSat`, read as `TrSpec.state`; `l ↦ some v` and `threadExpr i C e` (`exits v @ i`) determine them through the state interpretation (`StateFact` instances, `HeapLang/TemporalLaws.lean`), so they guarantee them (`guar_state_fact`) | `HeapLang/Syntax.lean`, `HeapLang/Semantics.lean`, `Trace/GuaranteeRules.lean` |
| `lwp` | `Lwp.lwp`, notation `lWP e @ s; i; E {{ Φ }}`; one step `lwpStep` | `ProgramLogic/Notation.lean`, `ProgramLogic/WeakestPre.lean` |
| obligation state `Ω`, witness state `W` | `Model.Obls`, `Model.Witnesses`; the forest is kept by `Model.oforest` | `BaseLogic/Obligation.lean`, `BaseLogic/Witness.lean`, `BaseLogic/Model/OForest.lean` |
| model interpretation `M` | `Model.modelInterp` (with the forest invariant and the model history `Model.modelHistoryInterp`) | `BaseLogic/Model/MUpd.lean`, `BaseLogic/Model/ModelHistory.lean` |
| model update modality | `mupdBase` / `mupdFancy`; the `lWP`-facing form is `mupd` (`\|={E}=>m`), and the step modalities are `mprog` / `mphys` | `ProgramLogic/OblForest.lean`, `BaseLogic/Model/MUpd.lean` |
| fair-scheduler invariant `H` | `Model.owitInv` | `BaseLogic/ModelRel.lean` |
| state interpretation `S` | `HeapLang.stateInterp` (HeapLang) and `historyInterp` (its wrapper for the adequacy proof) | `HeapLang/PrimitiveLaws.lean`, `ProgramLogic/HistoryInterp.lean` |
| Theorem 1 (Adequacy) | `lwp_adequacy_temporal`: from a guarantee `P ⊨ₜ G` of the initial resources, every fair behavior satisfies `G.external`; the weakest preconditions are `NotStuck`, which refutes the stuck behaviors. Iris-style safety `lwp_adequacy_safety`: on the same fair behaviors the scheduled thread is never stuck, and whenever the chosen thread is a value, its postcondition holds | `Trace/Adequacy/Temporal.lean`, `Trace/Adequacy/Safety.lean` |

As in Rocq, a guarantee turns its formula into a *record* (`record`) of what the formula holds
at each position, and before every step the proof of Theorem 1 certifies every registered
temporal formula (`regCheck`, `Trace/TemporalFormulaRun.lean`).

## 6. Case studies (§2–§7)

All in `Examples/`; each file's names are in `Examples.<File>`.

| Paper | Lean | File |
|---|---|---|
| Flag module: `init`/`set`/`wait`; `isFlag`; `FlagObl`; SPEC-INIT/SPEC-SET/SPEC-WAIT | `init`/`set`/`wait`; `isFlag` (guarantee `guar_isFlag`, trace specification `flagTrSpec`); `flagTk`; `init_spec` / `set_spec` / `wait_spec` | `Flag.lean` |
| `main` (§2) and its trace property | `main`, `main_spec`, end-to-end `main_adequacy` | `FlagFork.lean` |
| `nest` / `nondet` (§4.3); SPEC-NEST/SPEC-NONDET | `nest` / `nondet`; `nest_spec` / `nondet_spec` | `Nondet.lean` |
| Handoff: `send`/`receive`; `HandoffBuf`; `isHandoff`; `TaskSpec`; SPEC-SEND/SPEC-RECEIVE | `send`/`receive`; `handoffInv`; `isHandoff`; `isTask`; `send_spec` / `receive_spec` | `Handoff.lean` |
| `handoffMain` (§5.2); SPEC-HANDOFF-MAIN | `main`, `main_spec`, `handoffClient_adequacy` | `HandoffClient.lean` |
| Ticket lock (§7.1): `TLInv`; `TLObl`; SPEC-ACQUIRE/SPEC-RELEASE | `isFairLock`; `lockToken`; `init_spec` / `acquire_spec` / `release_spec` | `TicketLock.lean` |
| Queue (§7.2): `QInv`; SPEC-ENQUEUE/SPEC-DEQUEUE | `isQueue` (with `worker` for the primary); `init_spec` / `enqueue_spec` / `dequeue_spec` | `Queue.lean` |
| Task queue (§7.3): `TQInv`; SPEC-PUT-TASK/SPEC-WORKER | `isTaskQueue`; `init_spec` / `putTask_spec` / `runTask_spec` / `worker_spec` | `TaskQueue.lean` |
| Reentrant client `decr` / `clientMain` (§7.3); SPEC-DECR/SPEC-DECR-CLIENTMAIN | `decrReentrant` / `main`; `decrReentrant_spec` / `main_spec`; `taskQueueClient_adequacy` | `TaskQueueClient.lean` |

**End-to-end theorems.** Each client program has three, over all fair behaviors from its initial
configuration:

- `*_adequacy` instantiates `lwp_adequacy_temporal`: `FlagFork.main_adequacy`,
  `FlagClient.flagClient_adequacy`, `HandoffClient.handoffClient_adequacy`,
  `TaskQueueClient.taskQueueClient_adequacy`, and beyond the paper
  `TicketLock2Client.ticketLockClient_adequacy` and `CertDischarge.certDischarge_adequacy`;
- `*_safety_adequacy` instantiates `lwp_adequacy_safety` (for example
  `FlagFork.main_safety_adequacy`);
- `*_liveness_safety` states both (for example `FlagFork.main_liveness_safety`).

**Unsound rules.** `Paradox.no_lc_absurd` proves the counterexample at the end of §6.2: a
HeapLang rule for one pure step without fuel would be unsound. In Lean the unsound rule is a
class hypothesis.

**Beyond the paper.** `NonstrictMove.nonstrictMove_absurd` (moving an obligation below one of
the same layer is unsound); `TicketLock2.fairLock_starvationFree` and
`TicketLock2Client.ticketLockClient_adequacy` (a starvation-free ticket lock);
`CertDischarge.certDischarge_adequacy` (a discharge in the pre-step model update);
`FlagStable.flagTrSpec_stays` (a flag that stays set, with its clients `FlagStableClient`,
`HandoffFlagStableClient` and `TaskQueueFlagStableClient`);
`TicketLockMono.aliveFairLock_starvationFree` (`next` never decreases, so a lock that is not
deleted is starvation free).

## 7. Checking the results

`lake build` checks every proof. `lake test` builds `LantanaTest/`, which prints the axioms of
the adequacy theorems and of the end-to-end theorems and checks them against the expected
output. `scripts/audit.sh` checks that no `sorry`, `admit`, `axiom` or `native_decide` occurs in
`Lantana/` and `LantanaTest/`. To read a statement, open a file with the Lean language server, or
run, after `lake build`:

```
lake env lean --stdin <<'EOF2'
import Lantana
#check @Lantana.lwp_adequacy_temporal
#print axioms Lantana.lwp_adequacy_temporal
EOF2
```

The results depend only on Lean's three standard axioms, `propext`, `Classical.choice` and
`Quot.sound`. The Rocq development lists seven axioms of Rocq's standard library.
