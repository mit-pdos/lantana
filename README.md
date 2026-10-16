# Lantana in Lean

A Lean 4 reimplementation of *Lantana*, a concurrent separation logic for liveness
("Decoupling Liveness Obligations from Threads in the Lantana Concurrent Separation Logic",
POPL 2027), on top of Transfinite Iris-Lean.

- Lean `v4.34.1`; depends on the `Iris/` package of
  [dongjaelee1/iris-lean](https://github.com/dongjaelee1/iris-lean), branch `transfinite`
  (step index `Iris.SI := Ordinal.{3}`), and through it on its `Ordinals` package.
- Reference: the Rocq development of Lantana (`dev`, commit `0c1515a`). This is a
  reimplementation, not a line-by-line port: definitions, rules and theorem statements follow
  Rocq, the implementation is redesigned for Lean (see *Design* below).
- The development is free of `sorry`, `admit` and `axiom`; its theorems depend only on
  `propext`, `Classical.choice` and `Quot.sound`.

## Build and check

```
lake build --wfail    # the library, warnings (incl. the Iris-Lean linters) as errors
lake test             # LantanaTest: unit tests, closed-world instances, axiom checks
scripts/audit.sh      # no sorry / admit / axiom / native_decide in Lantana/ and LantanaTest/
```

## The main theorems

- `Lantana.lwp_adequacy_temporal` (`Lantana/Trace/Adequacy/Temporal.lean`): if the initial
  threads have `lWP`s and a resource `P` guarantees a trace specification `G` (`P ⊨ₜ G`), then
  every fair behavior from the initial configuration satisfies the trace reading of `G`.
- `Lantana.lwp_adequacy_safety` (`Lantana/Trace/Adequacy/Safety.lean`): on fair behaviors the
  scheduled thread is never stuck and a terminated initial thread satisfies its postcondition.

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
  (starvation-free), `ExtendedInt`.

## Correspondence with Rocq

Lean declarations carry `@[lantana_alias rocqName]`, which also creates a deprecated alias
`RocqLantana.rocqName` (search for a Rocq name with `#check RocqLantana.rocqName`); Rocq
declarations deliberately not ported are recorded with `#lantana_ignore rocqName "reason"`
(`Lantana/Std/Porting.lean`). Example files prefix their aliases with the Rocq file name when
Rocq reuses short names across files.

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
