# Lantana in Lean

A Lean 4 reimplementation of *Lantana*, a concurrent separation logic for liveness
("Decoupling Liveness Obligations from Threads in the Lantana Concurrent Separation Logic",
POPL 2027), on top of Transfinite Iris-Lean.
[`docs/paper-correspondence.md`](docs/paper-correspondence.md) gives the Lean name of each item of
the paper.

- Lean `v4.34.1`; depends on the `Iris/` package of
  [dongjaelee1/iris-lean](https://github.com/dongjaelee1/iris-lean), branch `transfinite`
  (step index `Iris.SI := Ordinal.{3}`), and through it on its `Ordinals` package.
- Reference: the Rocq development of Lantana,
  [dongjaelee1/liveness](https://github.com/dongjaelee1/liveness) (branch `main`, commit
  `08838e2`). This is a reimplementation, not a line-by-line port: definitions, rules and
  theorem statements follow Rocq, the implementation is redesigned for Lean (see *Design*
  below).
- The development is free of `sorry`, `admit` and `axiom`; its theorems depend only on
  `propext`, `Classical.choice` and `Quot.sound`.

## Build and check

```
lake build --wfail    # the library, warnings (incl. the Iris-Lean linters) as errors
lake test             # LantanaTest: unit tests, closed-world instances, axiom checks
scripts/audit.sh      # no sorry / admit / axiom / native_decide in Lantana/ and LantanaTest/
scripts/check-imports.sh  # layering: Std, Init < Prelude < Algebra < BaseLogic < ProgramLogic
                          #   < Trace < HeapLang < Examples; no module imports a later layer
scripts/rocq-table.sh     # regenerate docs/rocq-correspondence.md (see below)
scripts/profile.py        # build-time profile per layer, module and declaration (docs/performance.md)
```

## The logic

A liveness obligation is a resource that must eventually be discharged. Obligations form a
forest: every live obligation has a parent, which is a thread or another obligation. Each step of
a thread burns a unit of fuel of every obligation in its tree, and fuel is an ordinal measure, so
on a fair behavior no obligation stays assigned forever. Temporal formulas are tied to
obligations: `untilI N k q P Q` says that `P` holds until `Q`, and `Q` comes because `k` must be
discharged. Lean names are in the namespace `Lantana`, and files in `Lantana/`.

| Concept | Lean | File |
|---|---|---|
| Thread-local weakest precondition, a least fixpoint; one step is a model update, the physical step with its progress update, and a model update | `lWP e @ s; i; E {{ Φ }}` (`Lwp.lwp`), texan triples `l{{{ P }}} e @ i; E l{{{ v, RET v; Q }}}`, one step `lwpStep` | `ProgramLogic/WeakestPre.lean`, `ProgramLogic/Notation.lean` |
| The obligation predicates and their rules, as a sealed interface that the program logic uses | obligations `Obl.*`, witnesses `Wit.*`, threads `Th.*`, the children `Par.kids p K` of a parent `p` (`thKids i K`, `oblKids k K`) | `ProgramLogic/OblForest.lean`, `ProgramLogic/OblForestRules.lean` |
| The model update, which changes obligations and witnesses | `\|={E₁,E₂}=>m P` (`mupd`) | `ProgramLogic/OblForest.lean` |
| The model of the interface | `Model.OPreds`, over the obligation model (`ModelGS`) | `BaseLogic/Model/OPreds.lean` |
| Trace properties, with LTL on traces | `TrProp`, `□ₜ` `◇ₜ` `○ₜ` `𝒰ₜ`, entailment `R ⊆ S` | `Trace/TraceProp.lean` |
| Trace specifications: a trace property with an internal, step-indexed reading adequate for it | `TrSpec` (`TrSpec.external`, `TrSpec.internal`), entailment `G ⊑ₛ H` | `Trace/TrSpec.lean` |
| Guarantees: whenever `P` holds, the rest of the execution satisfies `G` | `P ⊨ₜ G` (`Guar P G`), inferred by `IntoGuar` | `Trace/Guarantee.lean`, `Trace/GuaranteeInfer.lean` |
| Temporal formulas, which are `iProp`s with guarantees | `alwaysI N P`, `untilI N k q P Q`, `finallyI N k q Q` | `Trace/TemporalFormula.lean`, `Trace/TemporalFormulaRules.lean` |
| Adequacy | `lwp_adequacy_temporal`, `lwp_adequacy_safety` | `Trace/Adequacy/Temporal.lean`, `Trace/Adequacy/Safety.lean` |
| HeapLang: the language, its `lWP` laws, and points-to and thread termination as trace atoms | `HeapLang.lwp_load`, `HeapLang.lwp_store`, `HeapLang.lwp_fork`, …; `l ↦ some v`, `exits v @ i` | `HeapLang/PrimitiveLaws.lean`, `HeapLang/TemporalLaws.lean` |

The two adequacy theorems:

- `lwp_adequacy_temporal`: if the initial threads have `lWP`s and a resource `P` guarantees a
  trace specification `G` (`P ⊨ₜ G`), then every fair behavior from the initial configuration
  satisfies the trace reading of `G`.
- `lwp_adequacy_safety`: on fair behaviors the scheduled thread is never stuck and a terminated
  initial thread satisfies its postcondition.

## Proving a liveness property

`Examples/FlagFork.lean` follows these steps for the program `main` of the paper's §2, which
forks a thread that sets a flag and waits for the flag.

1. Specify each module with texan `lWP` triples. Their pre- and postconditions hold the
   thread-expression token `threadExpr i C e`, the children `thKids i G` of the thread and fuel
   `Obl.fuel g ℓ μ` for each child `g` (`init_spec`, `set_spec` and `wait_spec` in
   `Examples/Flag.lean`).
2. In the proofs, create obligations (`Obl.new`) and temporal formulas (`alwaysI_alloc`,
   `untilI_alloc`) inside model updates `|={E}=>m`, and discharge an until once its right
   formula holds (`untilI_discharge`, `finallyI_discharge`).
3. Give the initial resources an `iProp` `P` with a guarantee `P ⊨ₜ G`, usually inferred by
   instance search (`IntoGuar.into_guar` in `guar_mainRes`).
4. Show that `G.external` implies the trace property of interest (`gMain_impl`), and apply
   `lwp_adequacy_temporal` (`main_adequacy`). `lwp_adequacy_safety` gives safety in the same way
   (`main_safety_adequacy`), and `main_liveness_safety` states both.

## Layout

| Directory | Contents | Rocq |
|---|---|---|
| `Lantana/Prelude` | thread and obligation ids, `Parent`; layers and fuel (ordinals) | `prelude/` |
| `Lantana/Algebra` | measures `Measure.rep`, ordered commutative monoids, the bank and bounded-credit cameras, `AuthMra` | `algebra/` |
| `Lantana/BaseLogic` | relational update `|==>r`, ordinal later credits `£ₒ α`, the fancy update, satisfiability, invariants; the obligation model (`Model/`: `osat`, `owit`, `oforest`, the model history, `modelInterp`, the model update `mupd` as a least fixpoint, `mprog`/`mphys`, the user predicates) | `base_logic/` |
| `Lantana/ProgramLogic` | languages with thread pools and traces, the history, the temporal registry, the sealed obligation-forest interface (`OblForest.lean`) and its derived rules, `lWP` (a least fixpoint) with its rules and lifting lemmas | `program_logic/` |
| `Lantana/Trace` | trace properties and LTL rules, fair scheduling, step-indexed trace predicates, trace specifications `TrSpec`, guarantees `⊨ₜ` and their inference, the temporal formulas `alwaysI`/`untilI`/`finallyI`, the adequacy theorems | `trace/` |
| `Lantana/HeapLang` | HeapLang with labels and `chooseNat` (forked from Iris-Lean's), its laws, temporal laws and tactics (`lwp_pure`, `lwp_step`, `lwp_pures`, `lwp_bind`) | `lantana_heap_lang/` |
| `Lantana/Examples` | the case studies (below), a closed world `ExGF` for end-to-end theorems | `lantana_heap_lang/examples/` |

## Case studies (`Lantana/Examples`)

All are proved; the clients have end-to-end corollaries through the adequacy theorems.

- `Flag`, `FlagStable` (the flag stays set), `Nondet` (nested waits to a nondeterministic depth);
- `FlagFork` (`main_liveness_safety`: `main` eventually exits with 42 and is safe), `FlagClient`,
  `FlagStableClient`, `Handoff`, `HandoffClient`, `HandoffFlagStableClient`;
- `CertDischarge` (a commitment discharged in a pre-step modality), `NonstrictMove` and
  `Paradox` (two rule variants shown unsound through adequacy, as class hypotheses);
- `TicketLock` (deletable, §7.1; release progress at trace level), `TicketLockMono` (starvation
  freedom with no hypothesis on `next`), `TicketLock2` and `TicketLock2Client`
  (starvation-free), `ExtendedInt`;
- `Queue` (§7.2: a queue protected by the ticket lock whose elements carry obligations;
  `queue_release_progress`), `TaskQueue` (§7.3: a task queue run by a forked worker thread;
  `taskQueue_release_progress`), `TaskQueueClient` (a reentrant task;
  `taskQueueClient_liveness_safety`) and `TaskQueueFlagStableClient` (the same over the stable
  flag; `taskQueueClient_flag_stays`).

`Lib`, `GhostMapP`, `LockLevel` and `World` (the closed world `ExGF`) are shared infrastructure.

## Correspondence with Rocq

Lean declarations carry `@[lantana_alias rocqName]`, which also creates a deprecated alias
`RocqLantana.rocqName` (search for a Rocq name with `#check RocqLantana.rocqName`); Rocq
declarations deliberately not ported are recorded with `#lantana_ignore rocqName "reason"`
(`Lantana/Std/Porting.lean`). Example files prefix their aliases with the Rocq file name when
Rocq reuses short names across files.

The generated table [`docs/rocq-correspondence.md`](docs/rocq-correspondence.md) lists every
alias (Rocq name, Lean declaration, Lean file) and every ignored Rocq name with its reason,
grouped by Rocq file, with summary counts and a coverage report: the Rocq declarations of
`lantana/` and `lantana_heap_lang/` that are neither aliased nor ignored. Regenerate it with
`scripts/rocq-table.sh [rocq-checkout]` (`scripts/RocqTable.lean` walks the environment of
`import Lantana`; without a Rocq checkout the tables are grouped by Lean module and there is
no coverage report).

## Naming

- Rocq's `oblP_*`, `witP_*`, `thP_*` and `parP_*` are `Obl.*`, `Wit.*`, `Th.*` and `Par.*`
  (`oblP_fuel` is `Obl.fuel`); `thP_kids i K` and `oblP_kids k K` are the notations `thKids i K`
  and `oblKids k K`.
- Definitions are lowerCamelCase and types UpperCamelCase (`untilI_done` is `untilIDone`,
  `is_flag` is `isFlag`); lemmas keep Rocq's snake_case over the Lean names (`guar_untilI_done`
  is `guar_untilIDone`).
- Rocq's `trSpec_*`, `trI_*` and `tr_*` are in the namespaces `TrSpec`, `TrIProp` and `TrProp`
  (`trSpec_always` is `TrSpec.always`); `reg_*` are `reg*` (`reg_check` is `regCheck`).
- A case study's names are in `Lantana.Examples.<File>`, without Rocq's module prefix
  (`Flag_set_spec` is `Examples.Flag.set_spec`).

## Design (the main departures from Rocq)

- **One language per world**: languages are universe-monomorphic (`Expr State Val : Type`) and
  the temporal ghost state determines the language; thread ids are list positions and pools are
  `List Expr`; observations and prophecies are dropped.
- **The obligation model** keeps Rocq's rules but not its ghost layout: owners are read from the
  obligation map (no owner ghost state), there is no boolean state flag, the per-thread maps are
  folded into the forest invariant, and ordinal-valued cells live under per-obligation ghost
  names (Iris-Lean's ghost maps store `Type`-valued data only). The interface
  `ProgramLogic/OblForest.lean` seals the model: its predicates are irreducible definitions with
  unfolding lemmas, and nothing outside the model unfolds them.
- **Fixed concrete choices**: the fair-scheduler bound `η a := ω ×ⱼ a +ₕ ω` and fuel `Ordinal.{1}`
  instead of classes; fairness counters are an explicit sequence instead of a coinductive
  predicate; `always` reads a single formula and safety is derived from the generalised single
  step `run_step`.
- **Allocation exposes ghost names**: the ghost-state classes are too large for the existential
  property of the step index, so allocation lemmas return records of names from which the
  instances are rebuilt (used by both adequacy theorems).
- **Guarantee inference** is split into inference (`GuarOf`, an output parameter) and checking
  (`IntoGuar`) by instance search; existentials are ghost or trace-visible by their type.

## Documents

All documents live in `docs/`:

- [`docs/paper-correspondence.md`](docs/paper-correspondence.md): the Lean name of each item of
  the paper, after the Rocq development's `PAPER.md`.
- [`docs/rocq-correspondence.md`](docs/rocq-correspondence.md): the generated Rocq↔Lean table
  (above).
- [`docs/performance.md`](docs/performance.md): where the build time goes, by layer, module and
  declaration, and how to measure it (`scripts/profile.py`).
- [`docs/iris-lean-proposal.md`](docs/iris-lean-proposal.md): changes to Iris-Lean that would
  remove code Lantana-Lean had to copy or work around.

## Credits

Lantana-Lean reimplements the Rocq development, whose README credits the sources of some of its
parts; the Lean counterparts come from them through it:

- HeapLang from Iris's HeapLang, here through a fork of Iris-Lean's;
- the language interface, the lifting lemmas and the `lWP` notations from Iris, here after
  Iris-Lean's, and `ProgramLogic/WeakestPre.lean` follows the structure of Iris's weakest
  precondition;
- fancy updates, invariants, satisfiability and invariant locations from Transfinite Iris, and
  the relational updates and later credits from the artifact of *Later Credits* (Spies et al.,
  ICFP 2022);
- ordered commutative monoids and the bank and bounded-credit cameras from the Lilo and FOS
  developments.

The files adapted from or based on Iris-Lean say so in their headers (see *License*).

## License

Lantana-Lean is licensed under the Apache License 2.0 ([`LICENSE`](LICENSE)); [`NOTICE`](NOTICE)
gives the attributions. It reimplements the Rocq development of Lantana (3-clause BSD license),
whose notice `NOTICE` reproduces. Twenty files are adapted from or based on files of Iris-Lean
(Apache 2.0): the header of each names the Iris-Lean file, reproduces its copyright notice and
authors, and says that the file was modified. To list them:

```
grep -rlE "^(Adapted from|Based on|The section .* is adapted from) " Lantana
```
