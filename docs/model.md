# The obligation model

The obligation model is the ghost state behind the obligation logic: the obligations with their
fuel and owners, the witnesses, the forest in which every live obligation hangs, and the model
update that changes them.  Program proofs see it only through a sealed interface (§7).  This
note explains the forest and what it keeps for each thread, the model update and the rounds of a
step, and the interface.  `docs/activity.md` describes crashed threads from the user's side.

| Where | What |
|---|---|
| `BaseLogic/Forest.lean` | the pure forest: `ForestWf`, `Forest.kids`, `Forest.owned` |
| `BaseLogic/Model/OForest.lean` | the forest invariant `oforest` and its ghost maps |
| `BaseLogic/Model/MUpd.lean` | `modelInterp`, the model update `mupd`, `mprog`, `mphys` |
| `BaseLogic/Model/OPreds.lean` | the children predicates; the forest operations as model updates |
| `ProgramLogic/OblForest.lean` | the sealed interface |
| `ProgramLogic/OblForestRules.lean` | the rules derived from the interface |

## 1. The forest and its invariant

The model `Ω : Obligations` maps each obligation to its state: assigned, with a fuel and an owner
thread, or discharged.  Every live (assigned) obligation is a node of a forest, given by a parent
map `Par : OidMap Parent`, where a parent is a thread or an obligation.  `ForestWf Ω tc Par`
says that the nodes are exactly the live obligations, that a node below a thread is owned by it,
that a node below an obligation `c` has the owner of `c` and strictly more fuel, and that owners
are threads of the pool `0, …, tc - 1`.  Fuel decreases strictly towards the roots, so the
forest is acyclic without a separate condition.  The children of `p` are defined from `Par`
(`Forest.kids Par p`), the owner of an obligation is read from `Ω` (`Obligations.ownerOf`), and the
obligations of thread `i` are the pure set `Forest.owned Ω Par i`.

The invariant `oforest Ω tc X` holds such a forest with three authoritative ghost maps:

- the children map, which tabulates `Forest.kids` on the threads of the pool and on the nodes
  (`KidsMap`); its exclusive fragment `OForest.kids p K` is the core of the user's children
  predicate;
- the status map of the threads of the pool (`StatusMap`), whose fragments are the fractions
  `OForest.exec i q` of the running status and the persistent `OForest.done i` (the statuses
  have a type of their own, `ThreadStatus`, which keeps this ghost map apart from the one of
  `OSat`, also keyed by numbers);
- the bill map (`BillMap`, §2).

It also holds, for each thread of the pool, its entry `OForest.threadInv`: half of its running
status (the other half is the user's), or its terminated status with its empty children
fragment, in which case it owns no obligation (`oforest_done_owned`); the nodes of the crashed
threads (§4); and, for each node `x` below `p`, `OForest.oblNode Ω x p`: `x` exists, its fuel is
below its bound, and its piece.

**Pieces.**  A node `x` below an obligation `c` holds some fuel `π` of its own above the fuel of
`c` (`OForest.oblPiece`).  Held fuel is a lower bound of the model's fuel (`osat_fuel_le`), so the
piece witnesses that `x` has more fuel than `c`, and it keeps doing so when both lose fuel.  At a
step of their owner (§5), `x` splits a unit off its piece, keeping exactly the old fuel of `c`,
and spends the unit on its own progress.  After the round, `x` still has at least the old fuel of
`c`, which is above the new one, and the piece is above the new fuel of `c` again
(`OForest.oblNode_step`, `OForest.oblNodes_stepped_pieces`, `OForest.oblNode_unstep`).  An owner
change of a subtree works the same way (`OForest.oblNodeMoved`).

**Creating and moving.**  A new obligation below `p` gets the owner of `p`.  Its model fuel is
the user's fuel, an extra `▽`, and a piece, above the fuel of `p` if `p` is an obligation:
`parLe p ℓ` then gives a witness of `p` at a layer at most `ℓ`, which bounds the fuel of `p` by
a fuel at `ℓ` (`parLe_owner`).  A move of `k` below `p₂` costs one unit of fuel at a layer `ℓ`
that dominates `p₂` (`parBelow p₂ ℓ`: any layer for a thread, a layer above a witness layer for
an obligation), so that `▽` at `ℓ` is above the fuel of `p₂` (`parBelow_owner`).  In the
model the unit is `1` and `▽`: `▽` becomes the new piece of `k`, and `1` is burnt by `k` if its
owner changes.  An owner change moves the whole subtree of `k` to the new owner, and must
decrease the fuel of each of its nodes (`ChownRel`, `osat_chown_set`): `k` burns its unit and the
other nodes a unit of their pieces (`oforest_move_cross`, the only lemma that changes owners).  A
move to a parent of the same owner changes no fuel (`oforest_move_same`), and moving a grandchild
up to its grandparent is free, as its piece serves below the grandparent (`oforest_move_up`).

## 2. The children, the bill and the running handle of a thread

For a thread `i` the user holds three predicates (the interface's names in parentheses):

- the children predicate `parKids (.thread i) K` (`thKids i K`): the exclusive children
  fragment and a share of every child (§3);
- the bill `OForest.bill i B` (`thCarriers i B`): an upper bound of the children, what a step of
  `i` pays for;
- the running handle `thActive i`, the user's half of the running status.

The invariant keeps, for each thread of the pool, a bill that contains its children and is
arbitrary beyond them (`BillMap`).  Adding a child below a parent needs the bill of the parent and
adds the child to it (`OForest.parBill`, nothing for an obligation parent; `Par.bill` in the
interface).  Removing a child needs only the children, and leaves the bill larger than the
children: `oforest_bill_resync` brings it back to them, and `oforest_bill_erase` drops an
obligation that is not live.  A step pays one unit for each obligation of the bill, uses
the units of the actual children and drops the others (`oforest_step`).  So the children of a
thread may sit in an invariant shared with other threads, which can only remove from them, while
the thread keeps its bill.

The running handle ends the thread: with `thKids i ∅`, it turns the whole running status into the
persistent `thDone i` (`oforest_exec_to_done`, `Th.terminate`), and the invariant keeps the empty
children fragment, so a terminated thread never gets a child again.  The handle with the empty
children predicate is the *node* of the thread, `OForest.node i` (`node_eq`): what the model
keeps for a crashed thread (§4).

## 3. The fraction scheme of the assignments

The state of an assigned obligation `k` is a fractional ghost cell.  The user's
`oblAssigned k q` (`Obl.assigned k q`) is the fraction `q / 2` of it, and the two children
shares `oblShare k` are quarters: one is held by the children predicate of `k` itself
(`parSelf`), the other by the children predicate of its parent.  Together they make the whole
cell (`oblAssigned_shares`).  Hence:

- a children predicate mentions only live obligations: a share contradicts the discharge
  (`oblKids_discharged_false`, `parKids_discharged`, `Par.kids_diff_discharged`);
- discharging `k` needs the whole cell, so it takes the children predicate of the parent, the
  empty children predicate of `k` and the user's whole assignment `oblAssigned k 1`
  (`obl_discharge_mupd`, `Obl.discharge_leaf`).  This is the only round that discharges, and the
  only forest operation built on `Obligations.StayOrStep` rather than `Obligations.NoDischarge`;
- an obligation invariant `Obl.inv N k P R` keeps half of the user's assignment while `k` is
  live (`Obl.variant`), so a discharge under the invariant opens it to get the other half
  (`Obl.inv_acc_assigned`, `Obl.discharge_inv`).

## 4. The view of the pool and the nodes of crashed threads

The forest sees the pool through a *view*: the thread count `tc` (thread ids are positions in
the pool) and the crashed bits `X : ThreadId → Prop`.  For a thread `i < tc` whose bit is set,
the invariant holds its node, `OForest.crashedInv X i`.  As the children fragment is exclusive,
nobody can then add a child below `i`, and as its children are empty, `i` owns no obligation
(`oforest_crashed_owned`, `Th.crashed_modelInterp_not_owner`).  Its bill can be emptied against
those children (`oforest_bill_crashed`), so its step pays for nothing (`mprog_step_crashed`).

A new thread comes with an empty bill, and its node goes to the user if its bit is not set and
to the invariant otherwise (`oforest_alloc_thread`, `oforest_alloc_threads`).  `oforest_bits`
changes the bits from `X₁` to `X₂`: it takes the nodes of the threads that become crashed and
gives back those of the threads that recover (`oforest_hand_in` and `oforest_hand_out` for one
thread).  Every other lemma keeps the bits.

So the owners of obligations are active: a finished thread owns nothing by its `thDone`, a
crashed one by its bit in the model.  Adequacy needs this at the view of the current
configuration (`docs/activity.md`, §4).

## 5. The model update and the two rounds of a step

The model interpretation `modelInterp h i Ω W n tc X` is the history of the model (`i + 1`
events ending at `(n, Ω)`), the obligations `Ω` (`osat`), the forest at the view `tc`, `X`, and
the witnesses `W` with their invariant.  The position `n` is the step index of the run: the
physical round moves it from `n₁` to `n₂`, and the model updates in between keep it.

The model update `mupd n P` (`|=[n]=>m P`) is the least fixpoint of `mupdPre n`: either `P` holds
now, or the prover plays one round and the update continues.  In a round, given the model at any
view, the prover changes the obligations by `Obligations.StayOrStep`; then, for every choice of
witnesses that the environment may make, it returns the model at the same position and view, the
history extended by `(n, Ω₂)`.  Being a least fixpoint, an update plays finitely many rounds
(`mupd_ind`, `mupd_ind_strong`).  A round takes the model at any view and gives it back at the same
one, so model updates neither read nor change the view and carry only the position.  The operations
of the forest are rounds built from templates: `mupd_noDischarge_step` (a round without discharge,
after which the environment's witnesses satisfy `Witnesses.NoDischarge`), `mupd_model_round`,
`mupd_ghost_round` and `mupd_read`.

Adequacy runs an update against the model with `modelInterp_mupd_steps`: the rounds compose into
`Obligations.le`, and the environment can always choose witnesses that keep a lower bound `γ`,
strictly monotone and below `fairMeasureUb` (`owitInv_exists_witnesses`).

The two rounds of a physical step alone read or change the view:

- the progress round `mprog n tc X i P` of the scheduled thread `i`: every obligation of `i`
  and every assigned witness progress strictly, the witnesses being the environment's choice.
  `mprog_step_kids` plays it with one unit of fuel of each obligation of the bill:
  `oforest_step` gives a unit to every obligation of `i` (§1), `osat_progress_owner` makes them
  progress while keeping the owners (§8), and every assigned witness gets a positive credit
  (`owit_progress`);
- the physical round `mphys n₁ n₂ tc₁ tc₂ X₁ X₂ P`, in three stages: the model moves to the
  position `n₂` and the thread count `tc₂` at the bits `X₁`, the forked threads getting their
  pieces (`mphys_forks`); under the step's later credits, a model update at `n₂`; the bits
  change from `X₁` to `X₂` (`mbits`, `mbits_kids`).  `mphys_run` runs it against the model.

The update of the second stage runs after the step, at the new position and with the old bits:
there a thread can discharge the obligations below a node before handing the node in at the
third stage (`docs/activity.md`, §3).

## 6. The rank of a forest

`Obl.discharge_forest` discharges a whole forest in one model update: the roots `ps` with their
children `K p`, and a finite set `S` of obligations closed under the children `kids k`, each a
child of a root or of an obligation of `S`.  The obligations must go leaves first, but the user
supplies no order: it is read from the model.  In the forest a child has more fuel than its
parent, so the fuel ranks `S` from parent to child (`oforest_kids_rank`); `kids_rank_mupd` reads
it in a ghost round, and the interface gives it as an existential rank (`Obl.kids_rank`).

Given a rank, `Obl.discharge_forest_of_rank` proceeds by well-founded induction on `S`.  A
nonempty `S` closed under children has an obligation without children, one of largest rank
(`Oids.exists_leaf`).  It is discharged below its parent, a root or an obligation of `S`
(`Obl.discharge_leaf_roots`, `Obl.discharge_leaf`), every other children set loses it
(`Par.kids_diff_discharged`), and the induction goes on with the rest of `S`.  The forms for one
root, for every obligation below the roots, and for thread roots are `Obl.discharge_forest_single`,
`Obl.discharge_forest_all` and `Obl.discharge_forest_threads`.

## 7. The sealed interface

`ProgramLogic/OblForest.lean` defines each predicate of the logic (`Par.kids`, `Th.active`,
`Th.carriers`, `Th.done`, `Obl.assigned`, `Obl.discharged`, `Obl.fuel`, `Obl.inv`, `Wit.layer`,
`Wit.cred`, `Wit.fuels`) and each modality (`mupdBase`, written `|=[n]=>m`; `mprog`; `mphys`) as
an `@[irreducible]` definition over the model, with a private unfolding lemma used only in that
file.  Its rules are proved from the model's lemmas through the unfoldings.  Nothing else unfolds
the predicates: the program logic, the temporal formulas and the examples use only the rules, so
they do not depend on the ghost layout of the model, which can change below the interface.

The model update of the interface, `|={E₁,E₂}=>m P` (`mupd`), takes the history interpretation
and runs a base model update at the history's position between two fancy updates
(`mupdFancy`), keeping the history interpretation.  Its three core rules are `mupd_ne`,
`fupd_mupd` and `mupd_bind`; `OblForestRules.lean` derives the others from them.  The forest
operations are proved as base model updates at every position and lifted by `mupd_of_base`.

The last sections of the interface state what adequacy reads of the model, in terms of
`Model.modelInterp`: the predicates of new threads (`Th.alloc_threads`), the runs of the
modalities (`mupdBase_modelInterp_steps`, `mprog_modelInterp`, `mphys_modelInterp_run`,
`mupd_modelInterp_steps`), and the facts that the obligations of the predicates are in the model
and that terminated and crashed threads own none.

## 8. Differences with the Rocq development

- **Ghost layout.**  Rocq keeps owner ghost state and, per thread, maps of owned obligations,
  sets of obligations and pool membership tokens (`othread`).  Here the owner is read from `Ω`,
  the owned obligations are the pure `Forest.owned`, the thread statuses are a ghost map inside
  `oforest`, and the threads of the pool are `i < tc`.  The forest nodes carry no owner and no
  per-thread token, and `oforest_step` does not hand out and take back the running status and the
  obligations of the thread.  Rocq's owner tokens forced a progress round to keep the owners;
  here nothing does, so the round says so (`osat_progress_owner`) and `oforest_step` closes only
  after such a round.
- **Children.**  Rocq's children map `Kids` is defined from `Par` here (`Forest.kids`), so its
  conditions `fwf_kids_dom` and `fwf_par_kids` hold by definition.
- **The thread's predicates.**  In Rocq the children predicate of a thread also holds half of its
  running status and is what a step pays for.  Here these are the children, the running handle
  and the bill (§2).
- **The view.**  Rocq's rounds take the pool `Θ`; here they take the view, a thread count and
  the crashed bits, which Rocq does not have (§4).
- **Moves.**  In Rocq `oforest_move_same` takes a piece `π` with
  `obl_fuel_of Ω q < π ≤ obl_fuel_of Ω k`; here it takes the forest's condition
  `Ω.fuelOf q < Ω.fuelOf k` and a `OForest.oblPiece`.
- **One layer in `Obl.fuel_eq_of_rep`.**  Rocq's `oblP_fuel_proper` takes two layers and
  `ℓ1 == ℓ2`; `Obl.fuel_eq_of_rep` takes one layer.  Without the equality it would be unsound:
  `rep ℓ 1 = rep ℓ' 1`, while the model fuels differ by the `▽` of the encoding, and
  `Obl.fuel_extend` with `Obl.fuel_add` would duplicate fuel.
- **Finite maps and sets.**  The union of `OidMap = Std.ExtTreeMap` takes the values of its right
  argument, so Rocq's `G ∪ F` is `F ∪ G` here (`Wit.fuels_add_map_gen`, `embedFuels_add_map`).
  Rocq's `{[k]} ∪ K` and `K ∖ {[k]}` are `K.insert k` and `K.erase k`; sets moved at once use
  `∪` and `\`.
- **Except-0.**  The model update absorbs `◇` unconditionally (`isExcept0_mupd`), as the fancy
  update does; Rocq requires `IsExcept0 P`.
- **The interface.**  Rocq states it as a class with an instance by the model; with a single
  model, it is here a module of irreducible definitions, which gives the same abstraction (§7).
