# Naming

Lantana follows Iris-Lean's naming conventions (`Iris/style.md` in Iris-Lean), which are
Mathlib's.  This note records them as they apply here (§1), the choices specific to Lantana (§2),
the accepted exceptions (§3), the lint that checks them (§4), and the tools for renaming
declarations (§5).

Rocq names do not constrain Lean names.  The correspondence with the Rocq development is kept
by `@[lantana_alias rocqName]` (`docs/rocq-correspondence.md`), which records the Rocq name
whatever the Lean one is.

## 1. The rules

| Kind | Convention | Examples |
|---|---|---|
| Types, structures, classes; Prop- and Type-valued definitions | UpperCamelCase | `Model.Obligation`, `TrSpec`, `Model.Obligation.Step`, `Cfg.Active`, `Model.ChownRel` |
| Other definitions and abbreviations | lowerCamelCase | `lwp.pre`, `alc`, `guar`, `historyInterp`, `MonoListP.authOwn` |
| Constructors, data fields | lowerCamelCase | `Exp.chooseNat`, `LantanaGS.forkPost` |
| Theorems, Prop fields | snake_case | `lwp_mono`, `Obl.fuel_lt_set`, `IntoGuar.into_guar` |
| Instances | lowerCamelCase head, then a suffix after underscores | `elimModalFupdLwp_wrongMask`, `fuels_timeless`; anonymous ones get Lean's names |
| Hypotheses | Lean ones lowercase (`h`, `hΩ`); Iris ones capitalised (`H`, `Hσ`) | |

Theorem names:

- **Definitions keep their spelling.** A lowerCamelCase definition keeps its spelling inside a
  theorem name, and an UpperCamelCase one is written in lowerCamelCase: `lwp.step_mono`,
  `satFrame_move`, `Obligations.stayOrStep_trans` (about `StayOrStep`),
  `isSome_toVal_of_baseStep`.  A name is not split into snake_case words: `sat_frame` would be
  wrong for `satFrame`.  A name is not abbreviated either: `strongFair_iff_weakFair_of_convex`,
  not `sf_iff_wf_of_convex`.
- **Connecting words:** `_of_` for an implication, `_iff`, `_left`/`_right` (never `_l`/`_r`),
  and `_mp`/`_mpr` for the halves of an iff.  `_2` names a two-element variant
  (`supply_spend_2`, as Iris-Lean's `ghost_map_elem_valid_2`).
- **Vocabulary**, as Iris-Lean's BI:

  | Use | Not |
  |---|---|
  | `exists` | `ex`, `exist` |
  | `forall` | `all` |
  | `mono` | `mon` |
  | `idem` | `idemp` |
  | `inc` (CMRA inclusion) | `included` |
  | `imp` (the connective, `BIBase.imp`) | `impl` |
  | `update` | `upd` |

  The vocabulary also holds for the names of instances (`TrSpec.mono_exists`) and of
  definitions (`TrProp.forall`).  The worked examples of a module are `example_…`
  (`GuaranteeInfer.example_iprop`).
- **Relations.** A name says `le` for `≤` and `⊑ₛ`, and `subset` for `⊆`
  (`TrProp.subset_refl`, `Th.carriers_kids_subset`).
- **Namespaces.**
  - Lemmas used with dot notation live in the namespace of their type or definition
    (`Model.ChownRel.fuel_in`, `HeapLang.Loc.add_assoc`).
  - A family of lemmas about a definition may also be flat, named after it: `Model.oforest_*`
    is about `Model.oforest`, `osat_*` about `osat`.
  - A lemma about a namespaced definition names it with its namespace, wherever the lemma
    lives: `Obl.fuels_add` and `HeapLang.Obl.fuels_add` are about `Obl.fuels`.  The flat
    spelling `oblFuels_add` is not used.
  - A namespace is not repeated in its names: `Examples.FlagClient.adequacy`, not
    `Examples.FlagClient.flagClient_adequacy`.
  - A word has one casing: `OWitRel` and `OWitInv`, as the namespace `OWit`.  Its
    lowerCamelCase form is `owit` (`owitInv_exists_witnesses`), as `oforest` and `osat`.

Instance names follow the instance of Iris-Lean they correspond to:

- an instance of a proof-mode class, or of an inference class such as `IntoGuar`, is
  `class_subject`: `elimModal_mupd`, `fromModal_alc`, `intoGuar_forall`, as Iris-Lean's
  `elimModal_bupd` and `frame_fupd`;
- the instances for `lWP` are those of Iris-Lean's `WP` with `Lwp` for `Wp`:
  `elimModalBupdLwp`, `frameLwp`, `isExcept0Lwp`, as `elimModalBupdWp` and `frameWp`;
- an instance that states a property of a definition is `subject_class`:
  `Par.below_persistent`, `alc_ne`, `TrSpec.exists_complete`, as Iris-Lean's
  `affinely_persistent`.

## 2. Lantana's choices

- **The weakest precondition.**
  - The rules of the modalities are flat, as Iris-Lean's `wp_*`, `fupd_*` and `bupd_*`:
    `lwp_mono`, `lwp_bind`, `lwp_frame_left`, `mupd_*`, `rupd_*`.
  - The construction of `lWP` lives under `lwp.`, as Iris-Lean's `wp.pre`: `lwp.step`,
    `lwp.pre`, `lwp.liftTerm`.  The uncurried construction is under `lwp.Internal`, as
    Iris-Lean's `twp.Internal`: `Args`, `pre'`, the least fixpoint `lfp`, `lfp_unfold`,
    `lfp_ind_strong`.
- **Assertions and predicates.**
  - An IProp-valued definition is lowerCamelCase: `alc` (the allocation modality), `alcIf`
    (as Iris-Lean's `laterIf`), `guar`.
  - `TrProp C = Trace C → Prop` is an assertion type, like `IProp` (or Mathlib's `Set`), so
    its definitions are lowerCamelCase: `isBehavior`, `schedule`, `stepOfInfOften`,
    `Fairness.Action.strongFair`/`weakFair`, `AttemptGrant.fair`/`isCounter`/`certain`.
  - A Prop-valued definition is UpperCamelCase: `Fairness.MissHit.Fair`, `TrProp.Along`.
  - So the case tells the type, and one notion can have both forms: the engine's
    `Fairness.MissHit.Fair` and `IsCounter` are propositions about positions, and
    `Fairness.AttemptGrant.fair` and `isCounter` are the trace properties.  A lowerCamelCase
    `isFoo` is an assertion, as Iris-Lean's `isLock`, not a `Bool`.
- **Order relations.**
  - A relation is a lowercase `le` only as the implementation of `LE`, and then its lemmas are
    `le_refl`, `le_trans`, ….  The `LE` instances are `TrSpec.le` (also `⊑ₛ`),
    `Model.Obligation.le`, `Model.Obligations.le` and `Model.Witness.le`.
  - The entailment of trace properties `R ⊆ S` is `TrProp.Subset`, protected, as Mathlib's
    `Set.Subset`; its lemmas are `TrProp.subset_refl`, `subset_trans`, ….
  - The other relations are UpperCamelCase (`Model.EventLe`, `Model.Witness.NoDischargeLe`).
- **The model and the logic.**
  - The model's types and relations are spelled out:
    - `Model.Obligation`/`Obligations` and `Model.Witness`/`Witnesses`;
    - the rounds `Obligations.NoDischarge` (every obligation stays or makes progress) and
      `Obligations.StayOrStep` (every obligation stays or takes a step), the same for the
      witnesses;
    - the pointwise `Witness.NoDischargeLe`.
  - The assertion families of the program logic keep short namespaces: `Obl.*` (`Obl.fuels`,
    `Obl.discharge_inv`, …), `Par.*` (`Par.below`, `Par.le`), `Wit.*` (`Wit.creds`) and `Th.*`
    (`Th.carriers`, `Th.alloc_threads`).  The model has its own flat definitions under
    `Model.OPreds` (`parBelow`, `witCred`), which the families wrap.
- **Ghost-state classes:** `…G` for a bundle of `inG`s (`MonoListPG`, `HandoffG`), `…GS` with
  its ghost names (`InvHeapGS`), and `…GpreS` before allocation (`InvHeapGpreS`).
- **Namespace constants** are `fooN`, from their label (Iris-Lean's `ticketLockN`):
  `ticketLockN := nroot.@"ticket_lock"`, `invN`, `eventuallyN`, `returnN`.
- **Specification lemmas.** In the examples, the lemmas `(gMain …).external ⊆ rMain` are
  `gMain_external_subset`.
- **General facts** about Lean's types live in `Lantana.Prelude` (`Lantana/Prelude/List.lean`),
  in the type's namespace (`List.getElem?_set_append`, `Option.Rel.inv`).

## 3. Accepted exceptions

- **Functors** and functor bundles are UpperCamelCase (`CreditF`, `LockLevelF`, `ExGF`), as
  Iris-Lean's (`AuthURF`).
- **Declarations in Iris-Lean's namespace.** `Iris.Stuckness.MaybeReducible` and `PureSafe` are
  declared there, for dot notation (`s.MaybeReducible (e, σ)`).  The first is Iris-Lean's
  `Stuckness.MaybeReducible`, with the same signature; it lives in
  `Iris.ProgramLogic.WeakestPre`, which Lantana does not import.
- **lowerCamelCase theorem names.** A theorem may be named in lowerCamelCase in two cases:
  - it is named after its conclusion (`Model.ModelHistoryWf.isPrefix`,
    `Stuckness.PureSafe.maybeReducible`);
  - it is the field of a Prop class (`PureExecCtx.pureExecCtx`), or an instance
    (`PureExecCtx.appR`).
- **`_all`.** In `Obl.discharge_forest_all` and `*_discharge_opened_forest_all`, `_all` is "all
  the roots", not ∀.
- **Example programs.** In the clients of the examples, lemma names keep the name of the
  program they are about (`Examples.FlagStableClient.flagClient_adequacy`, about the flag
  client run over the stable flag).

## 4. The lint

`scripts/naming/lint.sh` checks §1–§3 on the built library and test suite: run it after
`lake build` and `lake test`; exit code 1 on a violation.
- It dumps every declaration with `scripts/naming/Dump.lean`: its kind, its module, its Rocq
  alias, and whether its type ends in `Prop` or `Type`.
- `scripts/naming/lint.py` then flags:
  - a Prop- or Type-valued definition in lowerCamelCase, or a term-valued one in
    UpperCamelCase;
  - a definition with an underscore;
  - a theorem with an UpperCamelCase word, or named in lowerCamelCase without a definition of
    that name;
  - the vocabulary of §1, in the names of theorems and instances and as the name of a
    definition;
  - an abbreviation of a definition's name (`sf`, `ndf`; the list is in `lint.py`);
  - a theorem or an instance named after the flat spelling of a namespaced definition
    (`witLayers_persistent`, when the definition is `Wit.layers`);
  - a word cased differently from the namespace or type it comes from (`OwitRel`);
  - an `N…` namespace constant;
  - types and constructors in the wrong case.

The check of the result sort is syntactic: an IProp-, `TrProp`- or Set-valued definition counts
as term-valued.  Its exceptions are listed in `lint.py` with their reasons.  The lint reads
names, not statements: that a lemma about `⊆` says `subset` is checked by review.

## 5. Renaming declarations

- `scripts/naming/rename.py RENAMES.tsv [NAMESPACES.tsv]` renames declarations everywhere
  from the build's `.ilean` reference data: the declarations, every resolved usage
  (generalized field notation included), the `namespace`/`end`/`open` commands, and the
  backticked mentions in comments and in the documents given with `--docs`.  It keeps each
  usage written relative to the namespace it was resolved through, and reports what it could
  not place.
- `scripts/naming/captures.py` then finds the usages that a new name would capture (a bare
  `exists_mono`, meant for Iris-Lean's BI lemma, inside the namespace that gains
  `TrSpec.exists_mono`) and qualifies them.
- Identifiers inside syntax quotations are not references: the build finds them.
