# Follow-up proposal for Iris-Lean: findings from Lantana-Lean

Written 2026-10-16, after Lantana-Lean became sorry-free. Audience: the maintainer of
`dongjaelee1/iris-lean` (branch `transfinite`, pinned at `fdc7402f`). Each item says what Lantana
had to copy or work around, what upstream change would remove it, and how much Lantana code would
go. Nothing here is required: Lantana builds and is complete against the pinned Iris-Lean. The
items are independent; (1)–(3) and (6) are mechanical, (4) is the substantial one. (6) is a
ten-line change that made Lantana's build a quarter faster.

## 1. Universe-polymorphic constant functor (`constOF`)

- **Now:** `Iris.constOF (B : Type)`. Lantana's ordinal-valued cameras (`Auth Ordinal.{1}` credits,
  `Bank Fuel`, `BCred Fuel`, `Agree (DiscreteO Fuel)`, `MonoList (Nat × Obls)`) live in `Type 2`, so
  Lantana defines `Lantana.constOFP (B : Type v)` with its four functor instances
  (`Lantana/BaseLogic/LaterCredits.lean`) and includes the cameras through `ULiftOF.{4}` slots.
- **Proposal:** make `constOF` universe-polymorphic (`B : Type v`), keeping `constOFU` for the
  universe-lifted case. Check `ElemG.ofEqLift`/`ofLift` for the `ULiftOF` level inference
  (`max 2 ?w = 4` had to be annotated by hand in every test world).
- **Removes:** `constOFP` and its instances; simplifies every closed world.

## 2. Ghost maps and monotone lists over any universe

- **Now:** `GhostMapG GF K V H` and `MonoListG GF α` use `constOF`, so they store `Type 0` data
  only. Lantana copies them: `Lantana/BaseLogic/MonoListP.lean` (253 lines, the model history of
  `Nat × Obls`) and `Lantana/Examples/GhostMapP.lean` (199 lines, maps to layers/measures in the
  ticket lock). Lantana's obligation model also keeps its ordinal-valued cells under
  per-obligation ghost names, rather than in a single ghost map, for this reason.
- **Proposal:** after (1), generalise the value type of `GhostMapG`/`MonoListG` (and `GhostVarG`,
  `SavedPropG` if they share the pattern) to `Type v`.
- **Removes:** the two copies (~450 lines); would allow simpler ghost layouts in the model.

## 3. Small API gaps found while porting

- `BigSepS.bigSepS_union_2` (the converse of `bigSepS_union` without disjointness, for persistent
  bodies) is missing; Lantana has a private copy in `ProgramLogic/OblForestRules.lean`.
- For `Std.ExtTreeSet`/`Std.ExtTreeMap`, the generic `insert`/`∪` of `Iris.Std` and the containers'
  own `Insert`/`∪` are different terms; `bigSepS_insert`, `set_ind` and `LawfulSet.mem_insert` see
  the generic one, user code the container's. Bridging simp lemmas (`Oids.erase_eq_diff`,
  `OidMap.insert_eq`, `OidMap.union_*` in Lantana) belong upstream, or the instances should reuse
  the containers' operations definitionally.
- `GenHeap.genHeap_valid` is an update (`==∗`); a pure lookup lemma (`genHeapInterp_lookup`, as in
  Lantana's `HeapLang/PrimitiveLaws.lean`) is the usual need.
- Notation precedence: `|==> P` takes `term:40` (so `|==> A ∗ B` is `(|==> A) ∗ B`) while
  `|={E}=> P` takes `term`. Rocq's `|==>` scopes over `∗`. Every Lantana agent hit this; aligning
  `|==>` with `|={E}=>` (a breaking change) or documenting it prominently would help.
- Iris-Lean's HeapLang notation and a fork of it cannot be imported together (they declare the
  same syntax categories); Lantana's fork of HeapLang (labels, `chooseNat`, no prophecies) lives in
  its own module for that reason. Namespacing the categories would allow both.

## 4. Ordinal later credits and the relational update in Iris-Lean

- **Now:** Lantana has its own relational update `|==>r` over a well-founded credit camera
  (`BaseLogic/RUpd.lean`, 305 lines), ordinal later credits `£ₒ α` with `ALC`
  (`LaterCredits.lean`, 576), the fancy update built on `|==>r` with an explicit `◇`
  (`FUpd.lean`, 355), and re-instantiations of Iris-Lean's invariants (`Invariants.lean`, 501) and
  invariant heaps (`InvHeap.lean`, 320) over it — about 2 050 lines, most of them adapted copies.
  Lantana never instantiates Iris-Lean's `InvGS_gen` (two `BIFUpdate (IProp GF)` instances would
  compete), so Iris-Lean libraries stated over its fancy update (e.g. `CInvariants`, `NaInvariants`,
  `Boxes`) are not available to Lantana.
- **Proposal:** parametrise Iris-Lean's later-credit library and fancy update by a credit camera
  with a well-founded "next" relation (Lantana's `CreditCamera A`: discrete UCMRA, `rel`, `next`,
  frame and cancellation laws), with `Nat` credits as the default instance and `Ordinal.{1}` with
  natural addition as another; express `|==£>` as the relational update of the chosen camera and
  derive `lc_fupd_elim_later` and `£ (n+1)`-style rules for the `Nat` instance. Satisfiability
  (`Satisfiable.lean`, 461 lines: `SatPred`, `satFrame`, `rupd_satisfiable`, `satAt`) would move
  with it, since adequacy statements need it.
- **Removes:** most of the ~2 050 lines above (Lantana would keep only its credit instance and the
  `ALC` modality); makes all of Iris-Lean's update-level libraries usable in Lantana.
- **Cost/risk:** touches Iris-Lean's core update and adequacy files; the transfinite branch's
  existing users of `£ n` must keep their statements (instantiate at `Nat`).

## 5. The existential property and large classes

- **Finding:** ghost-state *instances* (`InvGS`, model and temporal classes) live in
  `Type (max 4 u)` because their `ElemG` fields hold maps on `IProp GF`, while `SIdxLarge SI X`
  exists for `X : Type ≤ 3`. Lantana therefore allocates *names* and rebuilds instances
  (`*_alloc_names`, `XGS.ofNames`; `Trace/Adequacy/Alloc.lean`).
- **Option:** if `GS` classes took their `GpreS` as an instance parameter instead of extending it,
  the `GS` types would be small; upstream conventions decide this, so it is only noted here.

## 6. `@[rocq_alias]` waits for asynchronous proofs

- **Finding:** the attribute reads the declaration with `Environment.find?`
  (`Iris/Std/RocqPorting.lean`), which returns the complete `ConstantInfo` and so waits until the
  proof of a theorem has been elaborated. Every aliased theorem's command therefore waits for its
  proof, and the proofs of a module are elaborated one after another instead of in parallel
  (`Elab.async`). Lantana's `@[lantana_alias]` was a copy of this code. Switching it to
  `findAsync?` cut a full rebuild of Lantana from 66–67 s to about 49 s (`LEAN_NUM_THREADS=6`,
  two alternating runs each; `docs/performance.md`), with the same aliases.
- **Proposal:** read the kind and the signature without waiting for the value:
  ```lean
  if env.contains aliasName then throwError ...
  let some info := env.findAsync? declName | throwError ...
  let sig := info.sig.get
  let value := mkConst declName (sig.levelParams.map mkLevelParam)
  match info.kind with
  | .thm => addDecl (.thmDecl { name := aliasName, levelParams := sig.levelParams, type := sig.type, value })
  | _ => addDecl (.defnDecl { name := aliasName, levelParams := sig.levelParams, type := sig.type,
                              value, hints := .abbrev, safety := .safe })
  ```
  Iris-Lean has about 6 000 `rocq_alias` uses, so its own build should gain in the same way
  (not measured here).
- **Removes:** nothing; it is a build-time fix.
