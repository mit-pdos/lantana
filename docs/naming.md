# Naming: aligning Lantana with Iris-Lean's conventions

**Status: a plan, awaiting decisions D1–D6 (§5).** Nothing has been renamed yet. Written
2026-11-15 on the `fairness` head (`ec53760`), against Iris-Lean pin `439abbb`.

Companion files:
- `docs/naming-inventory.tsv`: every proposed rename, one row per declaration.
- `scripts/naming/`: the scripts that produce the numbers below (§7).

The guiding principle, from the human on 2026-11-15: consistent naming conventions take
priority over keeping the Rocq names. The Rocq↔Lean map does not depend on the Lean names,
because `@[lantana_alias rocqName]` records the Rocq name separately. So every rename keeps
`docs/rocq-correspondence.md` complete once `scripts/rocq-table.sh` regenerates it.

## 1. Summary

- Lantana mostly follows Iris-Lean's conventions already. Its types are UpperCamelCase,
  its constructors and definitions are mostly lowerCamelCase, its theorem names are snake_case,
  and the `dupNamespace`/`nameCheck` linters pass under `--wfail`. The misalignments are
  concentrated in specific places, so the revision is targeted, not wholesale.
- The checks cover all **4,465** Lantana declarations, measured against all **12,406** Iris-Lean
  declarations. They produce **519 candidate renames**:
  - 227 mechanical;
  - 138 needing a wording review;
  - 143 depending on a decision below;
  - 11 optional.
- The renames touch about **3,500 usage sites in about 120 modules**, counted exactly from the
  build's `.ilean` reference data. About 900 of those usages belong to the deferrable D5.
- The largest real gaps are:
  1. **Prop-valued definitions in lowerCamelCase.** Lantana has 21 of 87 in UpperCamelCase;
     Iris-Lean has 67 of 113, and its ProgramLogic follows the rule strictly.
  2. **Rocq vocabulary in theorem names.** Examples: `ex`, `all`, `mon`, `idemp`, `included`,
     `_l`/`_r`.
  3. **The lWP construction.** The pieces live in the shared namespace `Lantana.Internal`, and
     the prefix is spelled two ways (`lwpPre` vs `Internal.pre'`).
  4. **Inconsistent casing across fairness, `TrProp` and IProp definitions.** Examples:
     `IsBehavior`, `SF`, `ALC`, `Guar`.
  5. **Assorted Rocq leftovers.** Theorems named in lowerCamelCase, definitions with
     underscores, `N…` namespace constants, and the namespace repeated in example lemma names.

## 2. The convention

### 2.1 Documented: Iris-Lean's `Iris/style.md`, which adopts Mathlib's naming convention

| Kind | Convention | Iris-Lean example |
|---|---|---|
| Types, structures, classes; **Prop- and Type-valued definitions** | UpperCamelCase | `BIAffine`, `PrimStep.Irreducible`, `Stuckness.MaybeReducible` |
| Other definitions and abbreviations (including IProp-valued ones) | lowerCamelCase | `laterIf`, `ownE`, `wp.pre` |
| Theorems | snake_case; **a lowerCamelCase definition keeps its spelling** inside the name, and an UpperCamelCase one is written in lowerCamelCase | `intuitionisticallyIf_unfold` (#689), `intoSep_pure`, `bigSepL_mono` |
| Instances | lowerCamelCase head, then a suffix after underscores | `elimInv_acc_with_close`, `elimModalFupdWp_wrongMask` |
| Linted | no `__`; no repeated namespace component | |
| Hypotheses | pure Lean ones lowercase (`h`, `hφ`); Iris ones capitalised (`H`, `Hinv`) | |

Mathlib conventions on top of these: `_of_` for implications, `_iff`, `_left`/`_right`, and
`_mp`/`_mpr` for the two halves of an iff. Lemmas about a type go in the type's namespace,
so that dot notation works.

### 2.2 Measured over all Iris-Lean declarations

- **Prop-valued definitions:** 67 of 113 are UpperCamelCase. The lowercase rest are mostly
  `valid`/`validN`/`dist` helpers that feed class fields. ProgramLogic follows the rule without
  exception (`irreducible` → `PrimStep.Irreducible`, `stuck` → `Stuck`, `nsteps` → `NSteps`).
- **Theorem vocabulary in the BI layer** (Lantana's rules for `TrProp`, `TrSpec`, `rupd`, `mupd`
  and `inv` are the analogues):

  | Word | Iris-Lean BI usage |
  |---|---|
  | `left` / `right` | 77 / 81 (against `l`/`r` 10/8) |
  | `exists` | 53, plus 18 `exist` (never `ex`) |
  | `forall` | 86 (`all`: 1) |
  | `idem` | 22 (`idemp`: 3) |
  | `mono` | 100 (`mon`: 0) |
  | `imp` / `impl` | 49 / 36 (the connective is `BIBase.imp`) |

  The Algebra layer uses `inc` 101 times against `included` 27 (CMRA inclusion was renamed).
- **Rocq prefixes:**
  - Modality families stay flat: `bupd_*`, `fupd_*`, and `wp_*` (`wp_unfold`, `wp_mono`,
    `wp_frame_l`). The WP construction goes in a lowercase namespace: `wp.pre`,
    `wp.pre.contractive`.
  - The newer `TotalWeakestPre` (Aug 2026) namespaces everything: `twp.pre`, `twp.Internal.pre'`,
    `twp.Internal.get`, `twp.unfold`, `twp.induction`.
  - Lemmas about a type, with the type as their Rocq prefix, move to the type's namespace:
    `CMRA.*`/`ORA.*`, `BI.BigSepL.*`, `EctxLanguage.*`, `MonoList.*`.
- **Namespace constants:** `ticketLockN`, `invHeapN`, `spinlockN`.
- **Iris-Lean's own inconsistencies, which we do not copy:**
  - The Instances layer keeps Rocq-style definitions (`uPred_fupd`, `ghost_map_elem`, `ghost_var`).
  - Some classes are lowercase (`invHeapGS`, `genHeapGS`, `prophMapGS`).
  - WP keeps `_l`/`_r`.
- **Upstream:** `style.md` is unchanged between the pin's base (`81bc350`) and upstream master
  `8293092`. The last naming commit (#689) is already in the pin.

### 2.3 What Lantana already gets right (no change)

- **Casing basics.** Type and constructor casing is correct (except the three classes in K).
  No real name contains `__`, and the dupNamespace linter is clean.
- **Instance names** follow Iris-Lean's rule, in the same mix of styles as Iris-Lean.
- **Hypotheses:** a spot check found no lowercase Iris hypotheses. Pure `%Hf`-style names appear
  27 times; Iris-Lean has 414.
- **Prop-class fields** are snake_case like Iris-Lean's (`IntoGuar.into_guar` ~ `IntoSep.into_sep`).
- **Lifting lemmas** use the same wording as Iris-Lean's (`lwp_lift_atomic_base_step` ~
  `twp.lift_atomic_base_step`).
- **Flat theorem families named after a definition of the same name.** Examples:
  `Model.oforest_*` (about `Model.oforest`), `osat_*`, `owit_*`, `mapForall2_*`,
  `counterMove_*`. Their namespaced look-alikes are about other definitions:
  `Model.OForest.exec_to_done` is about `statusAuth`/`exec`/`done`, while
  `Model.oforest_exec_to_done` is about `oforest`. These are correct, and the inventory
  does not touch them.
- **`Ordinals.Ordinal.*` lemmas** in `Prelude/Ordinal.lean` extend the type's namespace
  (standard practice).

## 3. `ProgramLogic/WeakestPre.lean`

`Internal.pre'` and `Internal.get` are not Lantana inventions. They are Iris-Lean's own
`TotalWeakestPre` names (`twp.Internal.pre'`, `twp.Internal.get`, `@[rocq_alias twp']`). The
misalignments are elsewhere:

1. **The pieces live in `Lantana.Internal`.** Every Lantana module shares that namespace, so
   `Internal.get` is a library-wide name meaning "the lWP fixpoint". Iris-Lean scopes them
   under `twp.Internal`.
2. **The construction is spelled two ways.** It uses a prefix (`lwpPre`, `lwpStep`) next to a
   namespace (`Internal.pre'`). Iris-Lean writes `wp.pre` (WP) and `twp.pre` (TWP).
   `Lantana.lwp` is itself a definition (`ProgramLogic/Notation.lean:48`), so an `lwp.`
   namespace is exactly Iris-Lean's `wp.pre` pattern.
3. **`lwpStep` reads like the rule names.** `lwpStep_mono` (about the definition) sits next
   to `lwp_step_fupd` (Iris's `wp_step_fupd` rule). `lwp.step_mono` removes the ambiguity.
4. **`liftTerm` is a generic name in the `Lantana` root.** `getElem?_set_append` is a plain
   `List` fact in the same root.
5. **The instances use a different form from Iris-Lean's WP instances:** `frame_lwp` and
   `elimModal_fupd_lwp`, against `frameWp` and `elimModalFupdWp`.

Proposed (D1 and D2 as recommended):

| Now | Proposed |
|---|---|
| `lwpStep`, `lwpStep_mono`, `lwpStep_ne` | `lwp.step`, `lwp.step_mono`, `lwp.step_ne` |
| `lwpPre`, `lwpPre_mono` | `lwp.pre`, `lwp.pre_mono` |
| `liftTerm` | `lwp.liftTerm` |
| `Internal.Args`, `Internal.pre'`, `Internal.pre'_mono` | `lwp.Internal.Args`, `lwp.Internal.pre'`, `lwp.Internal.pre'_mono` |
| `Internal.get`, `get_unfold`, `get_ne`, `get_ind_strong` | `lwp.Internal.lfp`, `lfp_unfold`, `lfp_ne`, `lfp_ind_strong` (D1b) |
| `lwp_unfold`, `lwp_mono`, `lwp_bind`, … | unchanged (flat, as `wp_*`/`fupd_*`), except `lwp_frame_l` → `lwp_frame_left`, etc. (D2) |
| `getElem?_set_append` | `List.getElem?_set_append`, moved to `Prelude` |
| `frame_lwp`, `elimModal_fupd_lwp`, … (11) | `frameLwp`, `elimModalFupdLwp`, … (optional, Q) |

## 4. Findings by category

Counts are rows in `docs/naming-inventory.tsv`. Usages are exact reference counts from `.ilean`.

| Cat. | Rule | Rows | Usages | Examples |
|---|---|---|---|---|
| **A** | lWP construction (§3) | 13 | 161 | `Internal.get` → `lwp.Internal.lfp` |
| **C** | Rocq prefix kept although no definition has that name, while the rest of the family is namespaced | 29 (review) | 187 | `obl_check_witnesses` vs `Obl.check_witness` (both Rocq `oblf.obl_*`): `obl_*` → `Obl.*` (13); `parBelow`/`parLe` → `Par.below`/`Par.le` (+11 lemmas); `witCreds`/`witLayers` → `Wit.creds`/`Wit.layers`; `HeapLang.loc_add_*` → `HeapLang.Loc.add_*` |
| **D** | Theorem vocabulary (§2.2) | 86 + 39 | 220 | `ex` → `exists` (26), `all` → `forall` (12), `mon` → `mono` (11), `idemp` → `idem` (4), `included` → `inc` (8), `impl` → `imp` (14), `upd` → `update` (1); definitions `TrProp.ex`/`all`, `TrSpec.ex`/`all` and `TrIProp.ex`/`all` → `exists`/`forall` (written `«exists»` as in Iris-Lean `BIBase.exists`); `_l`/`_r` → `_left`/`_right` (39, D2); `_1`/`_2` listed for review (6) |
| **E** | Prop-valued definitions in lowerCamelCase → UpperCamelCase; their dot-notation namespaces follow | 103 | 1,053 | `Model.Obl.step` → `Step`, `Cfg.active` → `Active`, `Model.chownRel` → `ChownRel` (its lemmas move to `Model.ChownRel.*`), `HeapLang.pointstoSat` → `PointstoSat`, `uchainLogWf` → `UchainLogWf`; 7 order relations under D3 |
| **F** | IProp-valued definitions in UpperCamelCase → lowerCamelCase | 28 | 170 | `ALC` → `alc`, `ALCb` → `alcIf` (as `laterIf`), `Guar` → `guar`; theorem tokens follow (`ALC_mono` → `alc_mono`, `fromModal_ALCb` → `fromModal_alcIf`) |
| **G** | `TrProp`-valued definitions (`TrProp C := Trace C → Prop`) cased both ways | 18 (D4) | 222 | `IsBehavior`, `StepOfInfOften`, `Schedule`, `SchedCounters`, `Action.SF`/`WF`/`Convex`/`Persists`, `AttemptGrant.Fair`/`IsCounter`/`Certain`, beside `stepOf`, `scheduled`, `TrProp.eventually` |
| **H** | Theorems named in lowerCamelCase (Rocq snake names camelCased) | 14 (review) | 44 | `certifyEntries`, `alwaysRun`, `regMark`, `bundleIntro`, `sysStepIter` (10 in `Trace/TemporalFormulaRun.lean`), `regRegister`, `getOblsThreadActive`, `Examples.initThreads` |
| **I** | Definitions with underscores → lowerCamelCase | 28 | 122 | `MonoListP.lb_own`/`auth_own`/`idx_own` → `lbOwn`/`authOwn`/`idxOwn`; `own_inv` → `ownInv`; `uPred_fupd` → `uPredFUpd`; `Examples.ghostMapP_elem` → `ghostMapPElem`. The lemmas follow; review the ones that name two definitions (`auth_lb_own_valid` → `authOwn_lbOwn_valid`) |
| **J** | A lowerCamelCase definition split into snake_case inside a theorem name | 20 (review) | 17 | `sat_frame_move` → `satFrame_move`, `except_0_inv` → `except0_inv`, `HeapLang.base_step_to_val` → `baseStep_toVal`, `guar_state_fact` → `guar_stateFact`, `*_release_progress` → `*_releaseProgress`; `Examples.lockLevel_lb` collides with the definition `lockLevelLb` → `lockLevelLb_of_lockLevel` |
| **K** | Type names | 6 | 29 | `invHeapGS` → `InvHeapGS`, `invHeapPreS` → `InvHeapGpreS` (Lantana's other pre-classes are all `…GpreS`), `MonoListGP` → `MonoListPG` (as `GhostMapPG`) |
| **L** | Namespace constants `N`, `Ninv`, `Nev`, … → `fooN` | 38 (review) | 316 | `Examples.TicketLock.N` → `ticketLockN`, `Ninv` → `invN`, `Ninv_subseteq` → `invN_subseteq`. The mechanical proposals (`aN`, `lN`) only show the pattern; give each a meaningful word |
| **M** | Namespace repeated in example lemma names | 21 | 34 | `Examples.FlagClient.flagClient_adequacy` → `Examples.FlagClient.adequacy`; `TaskQueue.taskQueue_release_progress` → `TaskQueue.release_progress` |
| **N** | Standard-library facts in Lantana namespaces | 6 (review) | 17 | `getLast?_eq_getElem?_of_length` exists twice verbatim (`Lantana.` and `Lantana.Model.`) → one `List.` lemma in `Prelude`; `Model.getLast?_take` clashes with core `List.getLast?_take` (different statement) → `List.getLast?_take_succ_of_getElem?`; `Model.option_rel_inv` → `Option.Rel.inv` |
| **O** | `Model.Obl`/`Model.Obls` (the model's types) vs `Lantana.Obl` (the IProp assertions) | 59 (D5) | 923 | `Model.Obl.step` vs `Obl.fuel`: one short name, two meanings; the model also writes `Witness`/`Witnesses` in full |
| **Q** | lWP instance names in Iris-Lean's WP form | 11 (optional) | 1 | `elimModal_fupd_lwp` → `elimModalFupdLwp` |

Low priority, not in the inventory: cryptic Rocq abbreviations in the model
(`Obls.lef`, `Obls.ndf`, `Witness.ndLe`) could be spelled out. `Iris.Stuckness.maybeReducible`
and `pureSafe` are Lantana declarations in Iris's namespace. The first is the same predicate as
Iris-Lean's `Stuckness.MaybeReducible` (`ProgramLogic/WeakestPre.lean:69`, not imported by
Lantana), up to currying. The inventory renames them to UpperCamelCase (E). When doing so,
adopt Iris-Lean's uncurried signature, so the two can be merged if Lantana ever imports that
module.

## 5. Decisions needed

- **D1 — the lWP construction.**
  - **(a) Rules** stay flat (`lwp_mono`, as Iris-Lean's `wp_*`, `fupd_*`, `bupd_*` and
    Lantana's `mupd_*`, `rupd_*`). The construction goes under `lwp.` (`lwp.pre`, `lwp.step`,
    `lwp.Internal.*`), like Iris-Lean's `wp.pre`. *Recommended.* The alternative is
    TotalWeakestPre's style for everything (`lwp.mono`, `lwp.unfold`, …); that changes about
    70 rule names and breaks the parallel with `mupd_*`/`rupd_*`/`fupd_*`.
  - **(b) The fixpoint.** `lwp.Internal.lfp` is *recommended*. Iris-Lean's verbatim name is
    `lwp.Internal.get`.
- **D2 — `_l`/`_r`.** `_left`/`_right` everywhere (39 theorems, including `lwp_frame_left`).
  *Recommended*: this is the majority in Iris-Lean (BI, Algebra, ProofMode, Std) and in
  Mathlib. The alternative keeps `_l`/`_r` only on the `lwp_*` rules, to mirror Iris-Lean's
  `wp_frame_l`. That gives up Lantana's internal consistency for the sake of one Iris-Lean file.
- **D3 — order relations.** These are `TrSpec.le` (notation `⊑ₛ`), `TrProp.le`, `Model.Obls.le`,
  `Model.Obl.le`, `Model.Witness.le`, `Model.eventLe` and `Model.Witness.ndLe`.
  - Where a relation is a preorder, give it an `LE` instance and keep the names `le_*`
    (Mathlib practice). *Recommended.*
  - Otherwise name it UpperCamelCase (`Le`, `EventLe`).
  - None of them backs an `LE` instance today (only `HeapLang.Loc` has one).
- **D4 — `TrProp`-valued definitions.** Treat `TrProp C` as an assertion type, like `IProp`
  (or `Set` in Mathlib), and name every `TrProp`-valued definition in lowerCamelCase.
  *Recommended.* Examples: `isBehavior`, `schedule`, `stepOfInfOften`, and `strongFair`/
  `weakFair` for `SF`/`WF` (`wf` would read as "well-founded").
  - The Prop-valued `Fairness.MissHit.Fair`/`IsCounter` stay UpperCamelCase, so the two
    families then differ in case exactly as their types differ.
  - The alternative keeps "property-like" `TrProp`s in UpperCamelCase. That rule is not
    mechanical.
- **D5 — `Model.Obl`/`Model.Obls`.** Rename them to `Model.Obligation`/`Model.Obligations`
  (59 declarations, about 900 usages), matching `Model.Witness`/`Model.Witnesses`. This
  removes the `Obl` vs `Model.Obl` clash. *Recommended, but it is the biggest single item.*
  It can be deferred, since the rest of the plan does not depend on it.
- **D6 — compatibility and scope.**
  - No `@[deprecated]` aliases for the old Lean names: Lantana has no downstream, and
    `lantana_alias` keeps the Rocq map. *Recommended.*
  - Include Q (instance names) and the abbreviation spell-outs, or leave them out.

## 6. Execution plan

**Phase 0 — freeze the map.** After D1–D6:
1. Re-run `scripts/naming/inventory.py` with the decisions applied.
2. Fill in the `new` column for the review rows.
3. Merge the duplicate `getLast?` lemma (the two collisions).
4. The result is one rename map (old full name → new full name).

**Phase 1 — a rename driver** (`scripts/naming/`).
- Read the build's `.ilean` files. Each lists, for every constant, all its resolved usages with
  exact positions: the same data the editor's rename uses.
- Rewrite each usage in reverse position order, from one snapshot. Only the identifier
  components that change are rewritten, so short names under `open`/`namespace` stay short.
  Dot-notation usages (`h.fuel_in`) need no edit when only the namespace moves.
- Declaration sites:
  - A plain rename is a text edit.
  - A namespace move is a structural edit: A, C and N need `namespace lwp … end lwp` blocks,
    or qualified declaration names. Do these by hand.
- What `.ilean` does not see is caught by the build:
  - identifiers inside `macro_rules`/syntax quotations (the lWP and HeapLang notations);
  - `simp`/`unfold` lists generated by macros;
  - `#lantana_ignore` reason strings.
- `docs/*.md` from the same map: `lwpStep`, `ALC`, `Guar` and `Obls.lef` all appear in
  `program-logic.md`, `model.md`, `adequacy.md` and `iris-lean-proposal.md`. Then regenerate
  `docs/rocq-correspondence.md` with `scripts/rocq-table.sh`.

**Phase 2 — bottom-up batches**, one worktree. The renames ripple upward, so the batches run in
sequence. Each batch is one commit and must pass `lake build --wfail`, `lake test` (exit code),
`scripts/audit.sh` and `scripts/check-imports.sh`.
1. Algebra, Prelude, BaseLogic: E (the model predicates), F (`ALC`), I (`MonoListP`, `own_inv`,
   `uPred_fupd`), K, D (in the model), N, and O if D5 is taken.
2. ProgramLogic: A (`WeakestPre`), C (`Obl`, `Par`, `Wit`), J (`satFrame`, `except0`), E
   (`Cfg.*`), Q.
3. Temporal and Trace: G, D (`ex`/`all`/`impl`, `_l`/`_r`), H (`TemporalFormulaRun`), E/D3
   (`TrProp`/`TrSpec` `le`).
4. HeapLang: C (`Loc.add_*`), J (`baseStep_toVal`), E (`PointstoSat`, `ThreadExprSat`,
   `FreedSat`).
5. Examples and LantanaTest: L, M, J (`releaseProgress`, `lockLevelLb`), and the remaining
   ripple.

Within a batch the edits cross files, so the work is serial, done by one agent. The plan does
not need lean-prover parallelism. Expect one full build per batch.

**Phase 3 — keep it from regressing.**
- Turn this note into the record of the convention: the rules of §2 and the D1–D6 outcomes.
  Drop the inventory.
- Optionally ship `scripts/naming/checks.py`'s rules as a lint. Its useful checks: a
  Prop-valued definition in lowerCamelCase, an IProp-valued one in UpperCamelCase, a
  lowerCamelCase theorem, an underscore in a definition name, the `ex`/`all`/`mon`/`idemp`
  vocabulary.

**Risks.**
- The `forall`/`exists` definitions need `«»` at declaration. Iris-Lean does the same.
- New names can shadow under `open`: the collision check in `inventory.py` covers Lantana and
  imported Iris names, but not every name in Lean core.
- The notation macros (`lwpPostcond`, `hl_exp`) refer to names in quotations. The build is
  the check.

## 7. Regenerating the numbers

From the package root, on a built tree, with a scratch directory `$S`:

```
lake env lean --run scripts/naming/Dump.lean Lantana > $S/lan.tsv   # Lantana + the Iris it imports
lake env lean --run scripts/naming/Dump.lean Iris    > $S/iris.tsv  # all of Iris-Lean
cd $S
{ grep -v $'\tIris\\.' lan.tsv; { grep $'\tIris\\.' iris.tsv; grep $'\tIris\\.' lan.tsv; } | sort -u -t$'\t' -k1,1; } > all.tsv
python3 <root>/scripts/naming/checks.py      # per-rule counts, Iris-Lean vs Lantana
python3 <root>/scripts/naming/inventory.py   # writes inventory.tsv (= docs/naming-inventory.tsv)
```

The columns of `all.tsv` are: name, kind, module, private, aliases (`lan:`/`iris:` + Rocq name),
result sort (Prop/Type/-), line.

The columns of `inventory.tsv` are: category, status (auto/review/decision/optional), old, new,
kind, location, Rocq name, note.
