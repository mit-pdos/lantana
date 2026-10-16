/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.BaseLogic.Forest
public import Lantana.BaseLogic.Model.OSat

/-! # The obligation forest and the threads

The invariant `oforest Ω tc` (Rocq `lantana/base_logic/oforest.v`, merged with the thread part of
`othread.v`): every live obligation of `Ω` is a node of a forest `Par : OidMap Parent` whose
roots are the threads `0, …, tc - 1` (`ForestWf`, pure, `Lantana.BaseLogic.Forest`). The
children of each thread of the pool and of each node are tabulated in a ghost map whose
exclusive fragments `OForest.kids p K` are the backbone of the user's children predicates. A
node below an obligation `c` stores a piece of fuel strictly above the fuel of `c`
(`forestNode`), so that when the owner of `c` steps, every descendant can split off a positive
unit (`oforest_step`). Each thread of the pool is running (the invariant keeps half of
`OForest.exec i`, the other half is the user's) or terminated (`OForest.done i`, persistent; the
invariant keeps its empty children fragment, and it owns no node).

Design (plan M4 §1, differences with Rocq):
* No owner ghost state and no per-thread ghost maps of owned obligations: the owner of an
  obligation is read from `Ω` (`Obls.ownerOf`) and the nodes owned by `i` are the pure
  `Forest.owned Ω Par i` (`ForestWf.mem_owned_iff`: the obligations of `Ω` with owner `i`). The
  forest invariant holds no fraction of the states of the obligations.
* The children map is *defined* by `Par` (`Forest.kids`); the authoritative children map `M`
  tabulates it on the threads of the pool and the nodes (`KidsMap`).
* The thread statuses are a ghost map `ThreadId → ThreadStatus` (`OForest.exec i q`, fractional,
  `running`; `OForest.done i`, persistent, `done`). A dedicated type rather than `Bool` keeps its
  `GhostMapG` instance apart from the state map of `OSat` (also keyed by `Nat`).
* Since owners are not ghost state, a progress round of `i` must keep the owners for
  `oforest_step` to close (`osat_progress_owner` produces such rounds); owner changes go through
  `oforest_move_cross`, which changes the owner of a whole subtree with `osat_chown_set`.
-/

@[expose] public noncomputable section

namespace Lantana.Model

open Iris Iris.BI Iris.ProofMode Iris.Std LawfulPartialMap
open Ordinals Ordinal

/-! ## Ghost state -/

/-- The status of a thread in the status ghost map. -/
inductive ThreadStatus where
  | running
  | done
  deriving DecidableEq

/-- Finite maps from parents (the children ghost map). -/
abbrev ParentMap (V : Type _) := Std.ExtTreeMap Parent V compare

/-- Finite maps from thread ids (the status ghost map). -/
abbrev ThreadMap (V : Type _) := Std.ExtTreeMap ThreadId V compare

/-- The ghost state of the forest that a world provides: the children map and the status map. -/
@[lantana_alias oforestGpreS] -- Rocq `oforestGS.oforestGpreS`
class OForestGpreS (GF : BundledGFunctors) where
  [kidsG : GhostMapG GF Parent Oids ParentMap]
  [statusG : GhostMapG GF ThreadId ThreadStatus ThreadMap]

attribute [reducible, instance] OForestGpreS.kidsG OForestGpreS.statusG

attribute [lantana_alias oforestGpreS_kids] OForestGpreS.kidsG
attribute [lantana_alias othreadGpreS_exec] OForestGpreS.statusG

/-- The ghost state of the forest: the names of the children map and of the status map. -/
@[lantana_alias oforestGS] -- Rocq `oforestGS.oforestGS`
class OForestGS (GF : BundledGFunctors) extends OForestGpreS GF where
  /-- The ghost name of the children map. -/
  kidsName : GName
  /-- The ghost name of the status map. -/
  statusName : GName

attribute [lantana_alias oforest_inG] OForestGS.toOForestGpreS
attribute [lantana_alias kids_name] OForestGS.kidsName
attribute [lantana_alias exec_name] OForestGS.statusName

#lantana_ignore «oforestΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#lantana_ignore «subG_oforestΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#lantana_ignore othreadGpreS "merged into `OForestGpreS` (plan M4 §1)"
#lantana_ignore othreadGS "merged into `OForestGS` (plan M4 §1)"
#lantana_ignore othreadGpreS_owns "no per-thread maps of owned obligations: `Forest.owned`"
#lantana_ignore othreadGpreS_obls "no per-thread sets of obligations: `Forest.owned`"
#lantana_ignore othreadGpreS_elem "the threads of the pool are `i < tc`"
#lantana_ignore othread_inG "merged into `OForestGS`"
#lantana_ignore owns_name "no per-thread maps of owned obligations"
#lantana_ignore obls_name "no per-thread sets of obligations"
#lantana_ignore elem_name "the threads of the pool are `i < tc`"
#lantana_ignore «othreadΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#lantana_ignore «subG_othreadΣ» "Subsumed by BundledGFunctors typeclass synthesis"

/-! ## Ghost predicates -/

namespace OForest

variable {GF : BundledGFunctors} [OForestGS GF]

/-- The children of `p` are `K` (exclusive; Rocq `oforestG_kids`). -/
@[lantana_alias oforestG_kids]
def kids (p : Parent) (K : Oids) : IProp GF :=
  OForestGS.kidsName (GF := GF) ↪◯MAP[p] K

/-- The authoritative children map (Rocq: the local `oforestG_kids_auth`). -/
@[lantana_alias oforestG_kids_auth]
def kidsAuth (M : ParentMap Oids) : IProp GF :=
  OForestGS.kidsName (GF := GF) ↪●MAP M

/-- A fraction `q` of the running status of thread `i` (Rocq `othreadG_exec`). -/
@[lantana_alias othreadG_exec]
def exec (i : ThreadId) (q : Qp) : IProp GF :=
  OForestGS.statusName (GF := GF) ↪◯MAP[i]{DFrac.own q} ThreadStatus.running

/-- Thread `i` has terminated (persistent; Rocq `othreadG_done`). -/
@[lantana_alias othreadG_done]
def done (i : ThreadId) : IProp GF :=
  OForestGS.statusName (GF := GF) ↪◯MAP[i]{DFrac.discard} ThreadStatus.done

/-- The authoritative status map. -/
def statusAuth (T : ThreadMap ThreadStatus) : IProp GF :=
  OForestGS.statusName (GF := GF) ↪●MAP T

#lantana_ignore othreadG_owns "no per-thread maps of owned obligations: `Forest.owned`"
#lantana_ignore othreadG_owns_token_id "no reservation maps"
#lantana_ignore othreadG_owns_auth_obls "no per-thread maps of owned obligations"
#lantana_ignore othreadG_obls "no per-thread sets of obligations: `Forest.owned`"
#lantana_ignore othreadG_obls_auth_id "no per-thread sets of obligations"
#lantana_ignore othreadG_done_auth "the status map: `OForest.statusAuth`"
#lantana_ignore othreadG_exec_token_id "no reservation maps: `OForest.statusAuth`"
#lantana_ignore othreadG_elem "the threads of the pool are `i < tc`"
#lantana_ignore othreadG_elem_auth_id "the threads of the pool are `i < tc`"
#lantana_ignore othreadG_done_auth_timeless "the status map: `OForest.statusAuth_timeless`"
#lantana_ignore othreadG_elem_alloc "the threads of the pool are `i < tc`"
#lantana_ignore othreadG_elem_elem "the threads of the pool are `i < tc` (`oforest_exec_lt`)"
#lantana_ignore othreadG_elem_persistent "the threads of the pool are `i < tc`"
#lantana_ignore othreadG_elem_timeless "the threads of the pool are `i < tc`"
#lantana_ignore othreadG_obls_alloc "no per-thread sets of obligations: `Forest.owned`"
#lantana_ignore othreadG_obls_lookup "no per-thread sets of obligations: `Forest.owned`"
#lantana_ignore othreadG_obls_timeless "no per-thread sets of obligations"
#lantana_ignore othreadG_obls_update "no per-thread sets of obligations"
#lantana_ignore othreadG_owns_alloc "no per-thread maps of owned obligations"
#lantana_ignore othreadG_owns_alloc_id "no per-thread maps of owned obligations"
#lantana_ignore othreadG_owns_as_fractional "no per-thread maps of owned obligations"
#lantana_ignore othreadG_owns_delete "no per-thread maps of owned obligations"
#lantana_ignore othreadG_owns_fractional "no per-thread maps of owned obligations"
#lantana_ignore othreadG_owns_lookup "no per-thread maps of owned obligations"
#lantana_ignore othreadG_owns_timeless "no per-thread maps of owned obligations"
#lantana_ignore othreadG_owns_valid "no per-thread maps of owned obligations"

/-! ### Instances -/

@[lantana_alias oforestG_kids_timeless]
instance kids_timeless (p : Parent) (K : Oids) : Timeless (kids (GF := GF) p K) := by
  unfold kids; infer_instance

instance kidsAuth_timeless (M : ParentMap Oids) : Timeless (kidsAuth (GF := GF) M) := by
  unfold kidsAuth; infer_instance

@[lantana_alias othreadG_exec_timeless]
instance exec_timeless (i : ThreadId) (q : Qp) : Timeless (exec (GF := GF) i q) := by
  unfold exec; infer_instance

@[lantana_alias othreadG_exec_fractional]
instance exec_fractional (i : ThreadId) : Fractional (exec (GF := GF) i) where
  fractional p q := by
    unfold exec
    exact (ghost_map_elem_fractional (GF := GF) _ i ThreadStatus.running).fractional p q

@[lantana_alias othreadG_exec_as_fractional]
instance exec_asFractional (i : ThreadId) (q : Qp) {ioΦ ioq : InOut} :
    AsFractional (exec (GF := GF) i q) ioΦ (exec i) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := exec_fractional i

@[lantana_alias othreadG_done_persistent]
instance done_persistent (i : ThreadId) : Persistent (done (GF := GF) i) := by
  unfold done; infer_instance

@[lantana_alias othreadG_done_timeless]
instance done_timeless (i : ThreadId) : Timeless (done (GF := GF) i) := by
  unfold done; infer_instance

instance statusAuth_timeless (T : ThreadMap ThreadStatus) :
    Timeless (statusAuth (GF := GF) T) := by
  unfold statusAuth; infer_instance

/-! ### Children -/

@[lantana_alias oforestG_kids_excl]
theorem kids_excl (p : Parent) (K₁ K₂ : Oids) :
    kids p K₁ ∗ kids p K₂ ⊢@{IProp GF} False := by
  unfold kids
  iintro ⟨H₁, H₂⟩
  icases ghost_map_elem_ne _ p p _ K₁ K₂ $$ H₁ H₂ with %h
  exact (h rfl).elim

@[lantana_alias oforestG_kids_lookup]
theorem kidsAuth_lookup (M : ParentMap Oids) (p : Parent) (K : Oids) :
    kidsAuth M ∗ kids p K ⊢@{IProp GF} ⌜get? M p = some K⌝ := by
  unfold kidsAuth kids
  iintro ⟨Ha, H⟩
  iapply ghost_map_lookup $$ Ha H

theorem kidsAuth_insert {M : ParentMap Oids} {p : Parent} (hp : get? M p = none) (K : Oids) :
    kidsAuth M ⊢@{IProp GF} |==> (kidsAuth (insert M p K) ∗ kids p K) := by
  unfold kidsAuth kids
  iintro Ha
  iapply ghost_map_insert p K hp $$ Ha

theorem kidsAuth_update (M : ParentMap Oids) (p : Parent) (K K' : Oids) :
    kidsAuth M ∗ kids p K ⊢@{IProp GF} |==> (kidsAuth (insert M p K') ∗ kids p K') := by
  unfold kidsAuth kids
  iintro ⟨Ha, H⟩
  iapply ghost_map_update K' $$ Ha H

theorem kidsAuth_delete (M : ParentMap Oids) (p : Parent) (K : Oids) :
    kidsAuth M ∗ kids p K ⊢@{IProp GF} |==> kidsAuth (delete M p) := by
  unfold kidsAuth kids
  iintro ⟨Ha, H⟩
  iapply ghost_map_delete p K $$ Ha H

/-! ### Thread statuses -/

/-- Rocq `othreadG_exec_valid`. -/
@[lantana_alias othreadG_exec_valid]
theorem exec_frac_valid (i : ThreadId) (q : Qp) : exec i q ⊢@{IProp GF} ⌜q ≤ 1⌝ := by
  unfold exec
  iintro H
  icases ghost_map_elem_valid _ _ _ _ $$ H with %h
  ipureintro
  exact DFrac.valid_own.mp h

theorem exec_half (i : ThreadId) :
    exec i 1 ⊣⊢@{IProp GF} exec i (Qp.half 1) ∗ exec i (Qp.half 1) := by
  have h := (exec_fractional (GF := GF) i).fractional (Qp.half 1) (Qp.half 1)
  rw [Qp.half_add_half] at h
  exact h

@[lantana_alias othreadG_exec_done_false]
theorem exec_done_false (i : ThreadId) (q : Qp) :
    exec i q ∗ done i ⊢@{IProp GF} False := by
  unfold exec done
  iintro ⟨H₁, H₂⟩
  icases ghost_map_elem_agree _ _ _ _ _ _ $$ [$H₁ $H₂] with %h
  cases h

theorem statusAuth_lookup_exec (T : ThreadMap ThreadStatus) (i : ThreadId) (q : Qp) :
    statusAuth T ∗ exec i q ⊢@{IProp GF} ⌜get? T i = some .running⌝ := by
  unfold statusAuth exec
  iintro ⟨Ha, H⟩
  iapply ghost_map_lookup $$ Ha H

theorem statusAuth_lookup_done (T : ThreadMap ThreadStatus) (i : ThreadId) :
    statusAuth T ∗ done i ⊢@{IProp GF} ⌜get? T i = some .done⌝ := by
  unfold statusAuth done
  iintro ⟨Ha, H⟩
  iapply ghost_map_lookup $$ Ha H

@[lantana_alias othreadG_exec_alloc]
theorem statusAuth_insert {T : ThreadMap ThreadStatus} {i : ThreadId} (hi : get? T i = none) :
    statusAuth T ⊢@{IProp GF} |==> (statusAuth (insert T i .running) ∗ exec i 1) := by
  unfold statusAuth exec
  iintro Ha
  iapply ghost_map_insert i ThreadStatus.running hi $$ Ha

/-- Termination: the whole running status becomes terminated (Rocq `othreadG_exec_to_done` and
`othreadG_done_auth_done`, here against the authoritative status map). -/
@[lantana_alias othreadG_exec_to_done]
theorem exec_to_done (T : ThreadMap ThreadStatus) (i : ThreadId) :
    statusAuth T ∗ exec i 1 ⊢@{IProp GF} |==> (statusAuth (insert T i .done) ∗ done i) := by
  unfold statusAuth exec done
  iintro ⟨Ha, H⟩
  imod ghost_map_update ThreadStatus.done $$ Ha H with ⟨Ha, H⟩
  imod ghost_map_elem_persist $$ H with H
  imodintro
  iframe

#lantana_ignore othreadG_done_auth_done "`OForest.exec_to_done` gives `OForest.done` directly"

end OForest

/-! ## The authoritative maps, pure part -/

namespace Forest

/-- The parents with an entry in the children map: the threads of the pool and the nodes
(Rocq `fwf_kids_dom`). -/
def keyed (tc : Nat) (Par : OidMap Parent) : Parent → Bool
  | .thread i => decide (i < tc)
  | .obl x => (get? Par x).isSome

@[simp] theorem keyed_thread {tc : Nat} {Par : OidMap Parent} {i : ThreadId} :
    keyed tc Par (.thread i) = decide (i < tc) := rfl

@[simp] theorem keyed_obl {tc : Nat} {Par : OidMap Parent} {x : Oid} :
    keyed tc Par (.obl x) = (get? Par x).isSome := rfl

/-- `keyed` only depends on the domain of `Par`. -/
theorem keyed_congr {tc : Nat} {Par Par' : OidMap Parent}
    (h : ∀ x, (get? Par' x).isSome = (get? Par x).isSome) (p : Parent) :
    keyed tc Par' p = keyed tc Par p := by
  cases p <;> simp [h]

theorem diff_singleton_of_not_mem {s : Oids} {k : Oid} (h : k ∉ s) : s \ {k} = s :=
  LawfulSet.ext fun x => by
    rw [LawfulSet.mem_diff, LawfulSet.mem_singleton]
    exact ⟨And.left, fun hx => ⟨hx, fun e => h (e ▸ hx)⟩⟩

end Forest

/-- The authoritative children map `M` tabulates the children `Forest.kids Par p` of the threads
of the pool and of the nodes (Rocq: `Kids` with `fwf_kids_dom` and `fwf_par_kids`). -/
def KidsMap (tc : Nat) (Par : OidMap Parent) (M : ParentMap Oids) : Prop :=
  ∀ p, get? M p = if Forest.keyed tc Par p then some (Forest.kids Par p) else none

namespace KidsMap

variable {tc : Nat} {Par : OidMap Parent} {M : ParentMap Oids}

open Forest

private theorem ite_true_eq {α : Type _} {a b : α} : (if true = true then a else b) = a := rfl

theorem empty : KidsMap 0 ∅ ∅ := fun p => by
  cases p <;> simp [get?_empty]

theorem lookup (h : KidsMap tc Par M) {p : Parent} {K : Oids} (hp : get? M p = some K) :
    keyed tc Par p = true ∧ kids Par p = K := by
  rw [h p] at hp
  split at hp
  · rename_i hk
    cases hp
    exact ⟨hk, rfl⟩
  · cases hp

theorem thread_lt (h : KidsMap tc Par M) {i : ThreadId} {K : Oids}
    (hp : get? M (.thread i) = some K) : i < tc := by
  have := (h.lookup hp).1
  simpa using this

theorem obl_isSome (h : KidsMap tc Par M) {q : Oid} {K : Oids}
    (hp : get? M (.obl q) = some K) : (get? Par q).isSome := by
  have := (h.lookup hp).1
  simpa using this

theorem none_thread (h : KidsMap tc Par M) : get? M (.thread tc) = none := by
  rw [h]
  simp

/-- A new thread `tc`, without children. -/
theorem alloc_thread (h : KidsMap tc Par M) {Ω : Obls} (wf : ForestWf Ω tc Par) :
    KidsMap (tc + 1) Par (insert M (.thread tc) ∅) := by
  intro q
  by_cases hq : Parent.thread tc = q
  · subst hq
    rw [get?_insert_eq rfl, wf.kids_thread_of_le (Nat.le_refl tc)]
    simp
  · rw [get?_insert_ne hq, h q]
    cases q with
    | thread j =>
      have hj : j ≠ tc := fun e => hq (e ▸ rfl)
      by_cases hjt : j < tc
      · simp [hjt, Nat.lt_succ_of_lt hjt]
      · have hjt' : ¬j < tc + 1 := fun h' => hjt (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h') hj)
        simp [hjt, hjt']
    | obl x => rfl

/-- A new leaf `k` below `p`. -/
theorem alloc_obl (h : KidsMap tc Par M) {Ω : Obls} (wf : ForestWf Ω tc Par) {k : Oid}
    {p : Parent} {K : Oids} (hk : get? Par k = none) (hpK : get? M p = some K) :
    KidsMap tc (insert Par k p) (insert (insert M p ({k} ∪ K)) (.obl k) ∅) := by
  obtain ⟨hkey, hkids⟩ := h.lookup hpK
  have hpk : p ≠ .obl k := by
    rintro rfl
    simp [hk] at hkey
  have hdom : ∀ q, q ≠ .obl k → keyed tc (insert Par k p) q = keyed tc Par q := by
    intro q hq
    cases q with
    | thread j => rfl
    | obl x =>
      have hkx : k ≠ x := fun e => hq (e ▸ rfl)
      simp [get?_insert_ne hkx]
  have hkq : ∀ q, k ∉ kids Par q := fun q hq => by
    rw [mem_kids, hk] at hq
    cases hq
  intro q
  by_cases hq : Parent.obl k = q
  · subst hq
    have hkey' : keyed tc (insert Par k p) (.obl k) = true := by simp [get?_insert_eq]
    rw [get?_insert_eq rfl, hkey', ite_true_eq, kids_insert_ne hpk, wf.kids_obl_of_none hk,
      diff_singleton_of_not_mem LawfulSet.mem_empty]
  · rw [get?_insert_ne hq]
    by_cases hpq : p = q
    · subst hpq
      rw [get?_insert_eq rfl, hdom p hpk, hkey, ite_true_eq, kids_insert_self, hkids]
    · rw [get?_insert_ne hpq, h q, hdom q (Ne.symm hq), kids_insert_ne hpq,
        diff_singleton_of_not_mem (hkq q)]

/-- A childless node `k` below `p` leaves the forest. -/
theorem discharge (h : KidsMap tc Par M) {k : Oid} {p : Parent} {K : Oids}
    (hk : get? Par k = some p) (hkk : kids Par (.obl k) = ∅) (hpK : get? M p = some K) :
    KidsMap tc (delete Par k) (insert (delete M (.obl k)) p (K \ {k})) := by
  obtain ⟨hkey, hkids⟩ := h.lookup hpK
  have hpk : p ≠ .obl k := by
    rintro rfl
    have hmem : k ∈ kids Par (.obl k) := mem_kids.2 hk
    rw [hkk] at hmem
    exact LawfulSet.mem_empty hmem
  have hdom : ∀ q, q ≠ .obl k → keyed tc (delete Par k) q = keyed tc Par q := by
    intro q hq
    cases q with
    | thread j => rfl
    | obl x =>
      have hkx : k ≠ x := fun e => hq (e ▸ rfl)
      simp [get?_delete_ne hkx]
  have hkq : ∀ q, q ≠ p → k ∉ kids Par q := fun q hq hkq => by
    rw [mem_kids, hk] at hkq
    cases hkq
    exact hq rfl
  intro q
  by_cases hpq : p = q
  · subst hpq
    rw [get?_insert_eq rfl, hdom p hpk, hkey, ite_true_eq, kids_delete, hkids]
  · rw [get?_insert_ne hpq]
    by_cases hq : Parent.obl k = q
    · subst hq
      rw [get?_delete_eq rfl]
      simp [get?_delete_eq]
    · rw [get?_delete_ne hq, h q, hdom q (Ne.symm hq), kids_delete,
        diff_singleton_of_not_mem (hkq q (Ne.symm hpq))]

/-- The node `k` moves from `p₁` to `p₂`. -/
theorem move (h : KidsMap tc Par M) {k : Oid} {p₁ p₂ : Parent} {K₁ K₂ : Oids}
    (hk : get? Par k = some p₁) (hp₁ : get? M p₁ = some K₁) (hp₂ : get? M p₂ = some K₂) :
    KidsMap tc (insert Par k p₂) (insert (insert M p₁ (K₁ \ {k})) p₂ ({k} ∪ K₂)) := by
  obtain ⟨hkey₁, hkids₁⟩ := h.lookup hp₁
  obtain ⟨hkey₂, hkids₂⟩ := h.lookup hp₂
  have hdom : ∀ q, keyed tc (insert Par k p₂) q = keyed tc Par q := by
    refine keyed_congr fun x => ?_
    by_cases hkx : k = x
    · subst hkx
      simp [get?_insert_eq, hk]
    · rw [get?_insert_ne hkx]
  have hkq : ∀ q, q ≠ p₁ → k ∉ kids Par q := fun q hq hkq => by
    rw [mem_kids, hk] at hkq
    cases hkq
    exact hq rfl
  intro q
  by_cases hq₂ : p₂ = q
  · subst hq₂
    rw [get?_insert_eq rfl, hdom, hkey₂, ite_true_eq, kids_insert_self, hkids₂]
  · rw [get?_insert_ne hq₂]
    by_cases hq₁ : p₁ = q
    · subst hq₁
      rw [get?_insert_eq rfl, hdom, hkey₁, ite_true_eq, kids_insert_ne hq₂, hkids₁]
    · rw [get?_insert_ne hq₁, h q, hdom, kids_insert_ne hq₂,
        diff_singleton_of_not_mem (hkq q (Ne.symm hq₁))]

end KidsMap

/-- The domain of the authoritative status map is the pool. -/
def StatusMap (tc : Nat) (T : ThreadMap ThreadStatus) : Prop :=
  ∀ i, (get? T i).isSome ↔ i < tc

namespace StatusMap

variable {tc : Nat} {T : ThreadMap ThreadStatus}

theorem empty : StatusMap 0 ∅ := fun i => by
  simp [get?_empty]

theorem lt (h : StatusMap tc T) {i : ThreadId} {s : ThreadStatus} (hi : get? T i = some s) :
    i < tc :=
  (h i).1 (by simp [hi])

theorem none (h : StatusMap tc T) : get? T tc = none := by
  cases e : get? T tc with
  | none => rfl
  | some s => exact absurd (h.lt e) (Nat.lt_irrefl tc)

theorem alloc (h : StatusMap tc T) (s : ThreadStatus) : StatusMap (tc + 1) (insert T tc s) :=
  fun i => by
    by_cases hi : tc = i
    · subst hi
      simp [get?_insert_eq]
    · rw [get?_insert_ne hi, h i]
      have hi' : i ≠ tc := fun e => hi e.symm
      exact ⟨Nat.lt_succ_of_lt, fun h' => Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h') hi'⟩

theorem update (h : StatusMap tc T) {i : ThreadId} (s : ThreadStatus) (hi : i < tc) :
    StatusMap tc (insert T i s) := fun j => by
  by_cases hij : i = j
  · subst hij
    simp [get?_insert_eq, hi]
  · rw [get?_insert_ne hij, h j]

end StatusMap

/-! ## Big operators over the forest -/

section BigOp

variable {PROP : Type _} [BI PROP]

/-- Rocq `big_sepS_filter_dom`. -/
@[lantana_alias big_sepS_filter_dom]
theorem bigSepS_dom_filter {V : Type _} (m : OidMap V) (φ : Oid → V → Bool)
    (Φ : Oid → PROP) :
    ([∗set] x ∈ (FiniteMap.dom_set (PartialMap.filter φ m) : Oids), Φ x) ⊣⊢
      [∗map] x ↦ v ∈ m, if φ x v then Φ x else emp := by
  refine BigSepM.bigSepM_dom.symm.trans ?_
  rw [BigSepM.bigSepM_filter_cond]
  exact .rfl

theorem Forest.bigSepS_kids (Par : OidMap Parent) (p : Parent) (Φ : Oid → PROP) :
    ([∗set] x ∈ Forest.kids Par p, Φ x) ⊣⊢
      [∗map] x ↦ q ∈ Par, if decide (q = p) then Φ x else emp :=
  bigSepS_dom_filter Par _ Φ

theorem Forest.bigSepS_owned (Ω : Obls) (Par : OidMap Parent) (i : ThreadId) (Φ : Oid → PROP) :
    ([∗set] x ∈ Forest.owned Ω Par i, Φ x) ⊣⊢
      [∗map] x ↦ _q ∈ Par, if decide (Ω.ownerOf x = some i) then Φ x else emp :=
  bigSepS_dom_filter Par _ Φ

/-- The nodes of `S` other than `k`, as a big operator over the other nodes. -/
theorem bigSepS_diff_delete (Par : OidMap Parent) (S : Oids) (k : Oid)
    (hS : ∀ x, x ∈ S → (get? Par x).isSome) (Φ : Oid → PROP) :
    ([∗set] x ∈ S \ {k}, Φ x) ⊣⊢
      [∗map] x ↦ _q ∈ delete Par k, if decide (x ∈ S) then Φ x else emp := by
  have heq : (FiniteMap.dom_set (PartialMap.filter (fun x (_ : Parent) => decide (x ∈ S))
      (delete Par k)) : Oids) = S \ {k} := LawfulSet.ext fun x => by
    rw [LawfulFiniteMap.mem_dom_set, get?_filter, LawfulSet.mem_diff, LawfulSet.mem_singleton]
    by_cases hkx : k = x
    · subst hkx
      simp [get?_delete_eq]
    · rw [get?_delete_ne hkx]
      have hne : x ≠ k := fun e => hkx e.symm
      by_cases hxS : x ∈ S
      · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hS x hxS)
        simp [hq, hxS, hne]
      · cases get? Par x <;> simp [hxS]
  rw [← heq]
  exact bigSepS_dom_filter _ _ Φ

end BigOp

theorem Forest.empty_diff (S : Oids) : (∅ : Oids) \ S = ∅ :=
  LawfulSet.ext fun x => by
    rw [LawfulSet.mem_diff]
    exact ⟨fun h => (LawfulSet.mem_empty h.1).elim, fun h => (LawfulSet.mem_empty h).elim⟩

/-! ## The invariant -/

/-! ### Threads -/

namespace OForest

variable {GF : BundledGFunctors} [OForestGS GF]

/-- What the invariant holds for thread `i` of the pool: half of its running status (the other
half is the user's), or its terminated status with its empty children fragment, and then it
owns no node (Rocq: the body of the big separating conjunction over `Θ` in `oforest`). -/
@[reducible] def threadInv (Ω : Obls) (Par : OidMap Parent) (i : ThreadId) : IProp GF :=
  iprop(exec i (Qp.half 1) ∨ (done i ∗ kids (.thread i) ∅ ∗ ⌜Forest.owned Ω Par i = ∅⌝))

instance threadInv_timeless (Ω : Obls) (Par : OidMap Parent) (i : ThreadId) :
    Timeless (threadInv (GF := GF) Ω Par i) := by
  unfold threadInv; infer_instance

theorem threadInv_mono {Ω Ω' : Obls} {Par Par' : OidMap Parent} {i : ThreadId}
    (h : Forest.owned Ω Par i = ∅ → Forest.owned Ω' Par' i = ∅) :
    threadInv Ω Par i ⊢@{IProp GF} threadInv Ω' Par' i := by
  unfold threadInv
  iintro (He | ⟨#Hd, Hk, %hown⟩)
  · ileft
    iexact He
  · iright
    iframe Hd Hk
    ipureintro
    exact h hown

private theorem getElem?_range {n k x : Nat} (h : (List.range n)[k]? = some x) : x = k ∧ k < n := by
  by_cases hk : k < n
  · rw [List.getElem?_range hk] at h
    cases h
    exact ⟨rfl, hk⟩
  · rw [List.getElem?_eq_none (by simpa using hk)] at h
    cases h

theorem threads_mono {Ω Ω' : Obls} {Par Par' : OidMap Parent} {tc : Nat}
    (h : ∀ j, j < tc → Forest.owned Ω Par j = ∅ → Forest.owned Ω' Par' j = ∅) :
    ([∗list] j ∈ List.range tc, threadInv Ω Par j) ⊢@{IProp GF}
      [∗list] j ∈ List.range tc, threadInv Ω' Par' j :=
  BigSepL.bigSepL_mono fun hx => by
    obtain ⟨rfl, hk⟩ := getElem?_range hx
    exact threadInv_mono (h _ hk)

/-- Access to the entry of thread `i`, to be put back in a new forest where the other threads
that owned nothing still own nothing. -/
theorem threads_acc {Ω : Obls} {Par : OidMap Parent} {tc i : Nat} (hi : i < tc) :
    ([∗list] j ∈ List.range tc, threadInv Ω Par j) ⊢@{IProp GF}
      threadInv Ω Par i ∗ ∀ (Ω' : Obls) (Par' : OidMap Parent),
        ⌜∀ j, j < tc → j ≠ i → Forest.owned Ω Par j = ∅ → Forest.owned Ω' Par' j = ∅⌝ -∗
        threadInv Ω' Par' i -∗ [∗list] j ∈ List.range tc, threadInv Ω' Par' j := by
  iintro Hl
  icases BigSepL.bigSepL_lookup_acc_impl (List.getElem?_range hi) $$ Hl with ⟨Hi, Hclose⟩
  iframe Hi
  iintro %Ω' %Par' %h Hi'
  iapply Hclose $$ %(fun _ y => threadInv Ω' Par' y) [] Hi'
  imodintro
  iintro %k %y %hky %hk Hy
  obtain ⟨rfl, hk'⟩ := getElem?_range hky
  iapply threadInv_mono (h _ hk' hk) $$ Hy

end OForest

/-! ### Nodes -/

section Nodes

variable {GF : BundledGFunctors} [OSatGS GF]

/-- The piece of fuel that a node `x` below an obligation `c` stores: strictly above the fuel of
`c`. -/
@[reducible] def forestPiece (Ω : Obls) (x : Oid) : Parent → IProp GF
  | .obl c => iprop(∃ π, ⌜Ω.fuelOf c < π⌝ ∗ OSat.fuel x π)
  | .thread _ => iprop(True)

/-- What the invariant holds for the node `x` with parent `p` (Rocq `forest_node`, without the
owner and the per-thread tokens): it exists, its fuel is below its bound, and its piece. -/
@[lantana_alias forest_node, reducible]
def forestNode (Ω : Obls) (x : Oid) (p : Parent) : IProp GF :=
  iprop(OSat.elem x ∗ (∃ β, OSat.bound x β ∗ ⌜Ω.fuelOf x ≤ β⌝) ∗ forestPiece Ω x p)

/-- The piece of a node right after a step of thread `i`: exactly the fuel of the parent if the
node is owned by `i` (it split off a unit), unchanged otherwise. -/
@[reducible] def forestPieceStepped (Ω : Obls) (i : ThreadId) (x : Oid) : Parent → IProp GF
  | .obl c => iprop(∃ π, ⌜(Ω.ownerOf x = some i → π = Ω.fuelOf c) ∧
      (Ω.ownerOf x ≠ some i → Ω.fuelOf c < π)⌝ ∗ OSat.fuel x π)
  | .thread _ => iprop(True)

/-- A node of the forest right after a step of thread `i`, before the model round (Rocq
`forest_node_stepped`). -/
@[lantana_alias forest_node_stepped, reducible]
def forestNodeStepped (Ω : Obls) (i : ThreadId) (x : Oid) (p : Parent) : IProp GF :=
  iprop(OSat.elem x ∗ (∃ β, OSat.bound x β ∗ ⌜Ω.fuelOf x ≤ β⌝) ∗ forestPieceStepped Ω i x p)

instance forestPiece_timeless (Ω : Obls) (x : Oid) (p : Parent) :
    Timeless (forestPiece (GF := GF) Ω x p) := by
  cases p <;> unfold forestPiece <;> infer_instance

instance forestNode_timeless (Ω : Obls) (x : Oid) (p : Parent) :
    Timeless (forestNode (GF := GF) Ω x p) := by
  unfold forestNode; infer_instance

instance forestPieceStepped_timeless (Ω : Obls) (i : ThreadId) (x : Oid) (p : Parent) :
    Timeless (forestPieceStepped (GF := GF) Ω i x p) := by
  cases p <;> unfold forestPieceStepped <;> infer_instance

instance forestNodeStepped_timeless (Ω : Obls) (i : ThreadId) (x : Oid) (p : Parent) :
    Timeless (forestNodeStepped (GF := GF) Ω i x p) := by
  unfold forestNodeStepped; infer_instance

/-- A piece below `p` is a piece below `p'` if the fuel of the new parent is at most the fuel of
the old one. -/
theorem forestPiece_reparent {Ω Ω' : Obls} {x : Oid} {p p' : Parent}
    (h : ∀ c', p' = .obl c' → ∃ c, p = .obl c ∧ Ω'.fuelOf c' ≤ Ω.fuelOf c) :
    forestPiece Ω x p ⊢@{IProp GF} forestPiece Ω' x p' := by
  cases p' with
  | thread j =>
    iintro -
    ipureintro
    trivial
  | obl c' =>
    obtain ⟨c, rfl, hc⟩ := h c' rfl
    iintro ⟨%π, %hπ, Hf⟩
    iexists π
    iframe Hf
    ipureintro
    exact Ordinal.lt_of_le_of_lt hc hπ

/-- The pieces only need the fuels of the parents not to increase. -/
theorem forestPiece_mono {Ω Ω' : Obls} {x : Oid} {p : Parent}
    (h : ∀ c, p = .obl c → Ω'.fuelOf c ≤ Ω.fuelOf c) :
    forestPiece Ω x p ⊢@{IProp GF} forestPiece Ω' x p :=
  forestPiece_reparent fun c hc => ⟨c, hc, h c hc⟩

/-- A node only needs its fuel and the fuel of its parent not to increase. -/
theorem forestNode_mono {Ω Ω' : Obls} {x : Oid} {p : Parent} (hx : Ω'.fuelOf x ≤ Ω.fuelOf x)
    (hp : ∀ c, p = .obl c → Ω'.fuelOf c ≤ Ω.fuelOf c) :
    forestNode Ω x p ⊢@{IProp GF} forestNode Ω' x p := by
  unfold forestNode
  iintro ⟨#He, ⟨%β, #Hb, %hβ⟩, Hp⟩
  iframe He
  isplitr
  · iexists β
    iframe Hb
    ipureintro
    exact Ordinal.le_trans hx hβ
  · iapply forestPiece_mono hp $$ Hp

theorem nodes_mono {Ω Ω' : Obls} {Par : OidMap Parent}
    (h : ∀ x p, get? Par x = some p →
      Ω'.fuelOf x ≤ Ω.fuelOf x ∧ ∀ c, p = .obl c → Ω'.fuelOf c ≤ Ω.fuelOf c) :
    ([∗map] x ↦ p ∈ Par, forestNode Ω x p) ⊢@{IProp GF}
      [∗map] x ↦ p ∈ Par, forestNode Ω' x p :=
  BigSepM.bigSepM_mono fun hx => forestNode_mono (h _ _ hx).1 (h _ _ hx).2

/-- The nodes are unchanged when the fuels of the nodes are. -/
theorem nodes_congr {Ω Ω' : Obls} {tc : Nat} {Par : OidMap Parent} (wf : ForestWf Ω tc Par)
    (h : ∀ x, (get? Par x).isSome → Ω'.fuelOf x = Ω.fuelOf x) :
    ([∗map] x ↦ p ∈ Par, forestNode Ω x p) ⊢@{IProp GF}
      [∗map] x ↦ p ∈ Par, forestNode Ω' x p :=
  nodes_mono fun x p hx =>
    ⟨Ordinal.le_of_eq (h x (by simp [hx])), fun c hc => by
      subst hc
      exact Ordinal.le_of_eq (h c (wf.par_obl hx))⟩

/-! ### Steps of a thread -/

private theorem ite_decide_pos {α : Type _} {P : Prop} [Decidable P] (h : P) {a b : α} :
    (if decide P = true then a else b) = a := by
  simp [h]

private theorem ite_decide_neg {α : Type _} {P : Prop} [Decidable P] (h : ¬P) {a b : α} :
    (if decide P = true then a else b) = b := by
  simp [h]

/-- A node at a step of thread `i`: a child of `i` takes the unit given by the user, any other
node of `i` splits a unit off its piece, keeping exactly the fuel of its parent. -/
theorem node_step {Ω : Obls} {tc : Nat} {Par : OidMap Parent} (wf : ForestWf Ω tc Par)
    (i : ThreadId) {x : Oid} {p : Parent} (hx : get? Par x = some p) :
    forestNode Ω x p ∗
        (if decide (p = .thread i) then iprop(∃ c, ⌜0 < c⌝ ∗ OSat.fuel x c) else emp)
      ⊢@{IProp GF} |==> (forestNodeStepped Ω i x p ∗
        if decide (Ω.ownerOf x = some i) then iprop(OSat.elem x ∗ ∃ c, ⌜0 < c⌝ ∗ OSat.fuel x c)
        else emp) := by
  cases p with
  | thread j =>
    have hj := wf.thread x j hx
    by_cases hji : j = i
    · subst hji
      rw [ite_decide_pos rfl, ite_decide_pos hj]
      iintro ⟨⟨#He, Hb, -⟩, Hu⟩
      imodintro
      isplitl [Hb]
      · isplitr
        · iexact He
        isplitl [Hb]
        · iexact Hb
        · ipureintro
          trivial
      · iframe He Hu
    · rw [ite_decide_neg (fun h => hji (Parent.thread.inj h)),
        ite_decide_neg (fun h => hji (Option.some.inj (hj.symm.trans h)))]
      iintro ⟨⟨#He, Hb, -⟩, -⟩
      imodintro
      isplitl [Hb]
      · isplitr
        · iexact He
        isplitl [Hb]
        · iexact Hb
        · ipureintro
          trivial
      · iempintro
  | obl c =>
    rw [ite_decide_neg (fun h => Parent.noConfusion h)]
    by_cases ho : Ω.ownerOf x = some i
    · rw [ite_decide_pos ho]
      iintro ⟨⟨#He, Hb, %π, %hπ, Hf⟩, -⟩
      imod OSat.fuel_lt hπ $$ Hf with ⟨Hf, Hu⟩
      imodintro
      isplitl [Hb Hf]
      · isplitr
        · iexact He
        isplitl [Hb]
        · iexact Hb
        · iexists Ω.fuelOf c
          iframe Hf
          ipureintro
          exact ⟨fun _ => rfl, fun h => (h ho).elim⟩
      · iframe He Hu
    · rw [ite_decide_neg ho]
      iintro ⟨⟨#He, Hb, %π, %hπ, Hf⟩, -⟩
      imodintro
      isplitl [Hb Hf]
      · isplitr
        · iexact He
        isplitl [Hb]
        · iexact Hb
        · iexists π
          iframe Hf
          ipureintro
          exact ⟨fun h => (ho h).elim, fun _ => hπ⟩
      · iempintro

theorem nodes_step {Ω : Obls} {tc : Nat} {Par : OidMap Parent} (wf : ForestWf Ω tc Par)
    (i : ThreadId) :
    ([∗map] x ↦ p ∈ Par, forestNode Ω x p) ∗
        ([∗map] x ↦ p ∈ Par,
          if decide (p = .thread i) then iprop(∃ c, ⌜0 < c⌝ ∗ OSat.fuel x c) else emp)
      ⊢@{IProp GF} |==> (([∗map] x ↦ p ∈ Par, forestNodeStepped Ω i x p) ∗
        [∗map] x ↦ _p ∈ Par, if decide (Ω.ownerOf x = some i) then
          iprop(OSat.elem x ∗ ∃ c, ⌜0 < c⌝ ∗ OSat.fuel x c) else emp) := by
  rw [← BigSepM.bigSepM_sep_eq, ← BigSepM.bigSepM_sep_eq]
  exact (BigSepM.bigSepM_mono fun hx => node_step wf i hx).trans (BigSepM.bigSepM_bupd _)

private theorem entails_pure_forall₂ {PROP : Type _} [BI PROP] {P : PROP} {α β : Sort _}
    {φ : α → β → Prop} (h : ∀ a b, P ⊢ ⌜φ a b⌝) : P ⊢ ⌜∀ a b, φ a b⌝ :=
  (BI.forall_intro fun a => (BI.forall_intro fun b => h a b).trans BI.pure_forall.2).trans
    BI.pure_forall.2

/-- After the round, the pieces of the nodes of `i` are below their new fuels. -/
theorem nodes_stepped_pieces {Ω Ω' : Obls} {tc : Nat} {Par : OidMap Parent} {i : ThreadId}
    (wf : ForestWf Ω tc Par) (hp : Obls.condProgress (Obl.condOwner i) Ω Ω') :
    osat Ω' ∗ ([∗map] x ↦ p ∈ Par, forestNodeStepped Ω i x p) ⊢@{IProp GF}
      ⌜∀ x c, get? Par x = some (.obl c) → Ω.ownerOf x = some i →
        Ω.fuelOf c ≤ Ω'.fuelOf x⌝ := by
  refine entails_pure_forall₂ fun x c => ?_
  by_cases hx : get? Par x = some (.obl c)
  · by_cases ho : Ω.ownerOf x = some i
    · refine (?_ : _ ⊢ ⌜Ω.fuelOf c ≤ Ω'.fuelOf x⌝).trans (BI.pure_mono fun h _ _ => h)
      iintro ⟨Hs, Hn⟩
      icases BigSepM.bigSepM_lookup hx $$ Hn with ⟨-, -, %π, %hπ, Hf⟩
      icases osat_fuel_le Ω' x π $$ [$Hs $Hf] with %hle
      ipureintro
      obtain ⟨a', t', hx'⟩ := (prog_live hp x).1 (wf.live_of_isSome (by simp [hx]))
      rw [← hπ.1 ho, Obls.fuelOf_eq hx']
      exact hle a' t' hx'
    · exact BI.pure_intro fun _ h => (ho h).elim
  · exact BI.pure_intro fun h => (hx h).elim

/-- After the round, a stepped node is a node again. -/
theorem node_unstep {Ω Ω' : Obls} {tc : Nat} {Par : OidMap Parent} {i : ThreadId}
    (wf : ForestWf Ω tc Par) (hp : Obls.condProgress (Obl.condOwner i) Ω Ω') {x : Oid}
    {p : Parent} (hx : get? Par x = some p) :
    forestNodeStepped Ω i x p ⊢@{IProp GF} forestNode Ω' x p := by
  cases p with
  | thread j =>
    iintro ⟨#He, ⟨%β, #Hb, %hβ⟩, Hp⟩
    isplitr
    · iexact He
    isplitr
    · iexists β
      iframe Hb
      ipureintro
      exact Ordinal.le_trans (prog_fuelOf_le hp x) hβ
    · iexact Hp
  | obl c =>
    have hoc := (wf.obl x c hx).1
    iintro ⟨#He, ⟨%β, #Hb, %hβ⟩, %π, %hπ, Hf⟩
    isplitr
    · iexact He
    isplitr
    · iexists β
      iframe Hb
      ipureintro
      exact Ordinal.le_trans (prog_fuelOf_le hp x) hβ
    · iexists π
      iframe Hf
      ipureintro
      by_cases ho : Ω.ownerOf x = some i
      · rw [hπ.1 ho]
        exact prog_fuelOf_lt hp (hoc.trans ho)
      · rw [prog_fuelOf_of_ne hp (fun h => ho (hoc.symm.trans h))]
        exact hπ.2 ho

/-! ### Owner changes of a subtree -/

/-- A node `x` during an owner change of the subtree `S`: a node of `S` has split off a unit,
keeping exactly the fuel of its parent; the other nodes are unchanged. -/
@[reducible] def forestNodeMoved (Ω : Obls) (S : Oids) (x : Oid) (p : Parent) : IProp GF :=
  if decide (x ∈ S) then
    iprop(OSat.elem x ∗ (∃ β, OSat.bound x β ∗ ⌜Ω.fuelOf x ≤ β⌝) ∗
      ∃ c, ⌜p = .obl c⌝ ∗ OSat.fuel x (Ω.fuelOf c))
  else forestNode Ω x p

/-- The nodes of `S` other than `k` are below obligations, and split a unit off their piece. -/
theorem node_cross_split {Ω : Obls} {Par : OidMap Parent} {S : Oids} {k : Oid}
    (hS : ∀ x, x ∈ S → x ≠ k → ∃ c, get? Par x = some (.obl c)) {x : Oid} {p : Parent}
    (hx : get? (delete Par k) x = some p) :
    forestNode Ω x p ⊢@{IProp GF}
      |==> ((if decide (x ∈ S) then iprop(∃ c, ⌜0 < c⌝ ∗ OSat.fuel x c) else emp) ∗
        forestNodeMoved Ω S x p) := by
  unfold forestNodeMoved
  by_cases hxS : x ∈ S
  · rw [ite_decide_pos hxS, ite_decide_pos hxS]
    have hkx : k ≠ x := fun e => by
      subst e
      simp [get?_delete_eq] at hx
    rw [get?_delete_ne hkx] at hx
    obtain ⟨c, hc⟩ := hS x hxS (fun e => hkx e.symm)
    rw [hx] at hc
    cases hc
    iintro ⟨#He, Hb, %π, %hπ, Hf⟩
    imod OSat.fuel_lt hπ $$ Hf with ⟨Hf, Hu⟩
    imodintro
    iframe Hu He Hb
    iexists c
    iframe Hf
    ipureintro
    rfl
  · rw [ite_decide_neg hxS, ite_decide_neg hxS]
    iintro H
    imodintro
    iframe H

/-- After the owner change, the moved nodes are nodes again. -/
theorem node_cross_join {Ω Ω' : Obls} {Par : OidMap Parent} {k : Oid}
    {t j : ThreadId} (hrel : chownRel (Forest.subtree Par k) t j Ω Ω') {x : Oid} {p : Parent}
    (hx : get? (delete Par k) x = some p) :
    forestNodeMoved Ω (Forest.subtree Par k) x p ⊢@{IProp GF} forestNode Ω' x p := by
  have hkx : k ≠ x := fun e => by
    subst e
    simp [get?_delete_eq] at hx
  rw [get?_delete_ne hkx] at hx
  unfold forestNodeMoved
  by_cases hxS : x ∈ Forest.subtree Par k
  · rw [ite_decide_pos hxS]
    have hcS : ∀ c, p = .obl c → c ∈ Forest.subtree Par k := by
      rintro c rfl
      rcases Forest.subtree_inv hxS with e | ⟨c', hc', hc'S⟩
      · exact (hkx e.symm).elim
      · rw [hx] at hc'
        cases hc'
        exact hc'S
    iintro ⟨#He, ⟨%β, #Hb, %hβ⟩, %c, %hc, Hf⟩
    isplitr
    · iexact He
    isplitr
    · iexists β
      iframe Hb
      ipureintro
      exact Ordinal.le_trans (Ordinal.le_of_lt (hrel.fuel_in hxS).2) hβ
    · subst hc
      iexists Ω.fuelOf c
      iframe Hf
      ipureintro
      exact (hrel.fuel_in (hcS c rfl)).2
  · rw [ite_decide_neg hxS]
    refine forestNode_mono (Ordinal.le_of_eq (hrel.fuel_out hxS)) fun c hc => ?_
    subst hc
    exact Ordinal.le_of_eq (hrel.fuel_out fun hcS => hxS (Forest.subtree_closed hx hcS))

/-- After the owner change, the pieces of the moved nodes are below their new fuels. -/
theorem nodes_moved_pieces {Ω Ω' : Obls} {Par : OidMap Parent} {k : Oid} {t j : ThreadId}
    (hrel : chownRel (Forest.subtree Par k) t j Ω Ω') :
    osat Ω' ∗ ([∗map] x ↦ p ∈ delete Par k, forestNodeMoved Ω (Forest.subtree Par k) x p)
      ⊢@{IProp GF} ⌜∀ x c, x ∈ Forest.subtree Par k → x ≠ k → get? Par x = some (.obl c) →
        Ω.fuelOf c ≤ Ω'.fuelOf x⌝ := by
  refine entails_pure_forall₂ fun x c => ?_
  by_cases hxS : x ∈ Forest.subtree Par k
  · by_cases hxk : x ≠ k
    · by_cases hx : get? Par x = some (.obl c)
      · refine (?_ : _ ⊢ ⌜Ω.fuelOf c ≤ Ω'.fuelOf x⌝).trans (BI.pure_mono fun h _ _ _ => h)
        have hx' : get? (delete Par k) x = some (.obl c) := by
          rw [get?_delete_ne (fun e => hxk e.symm)]
          exact hx
        iintro ⟨Hs, Hn⟩
        icases BigSepM.bigSepM_lookup hx' $$ Hn with Hx
        unfold forestNodeMoved
        rw [ite_decide_pos hxS]
        icases Hx with ⟨-, -, %c', %hc', Hf⟩
        cases hc'
        icases osat_fuel_le Ω' x _ $$ [$Hs $Hf] with %hle
        ipureintro
        obtain ⟨a, a', -, hx'', -⟩ := hrel.2 x hxS
        rw [Obls.fuelOf_eq hx'']
        exact hle a' j hx''
      · exact BI.pure_intro fun _ _ h => (hx h).elim
    · exact BI.pure_intro fun _ h => (h (Classical.not_not.1 hxk)).elim
  · exact BI.pure_intro fun h => (hxS h).elim

/-- The new piece of a moved node is below its new fuel. -/
theorem osat_forestPiece {Ω Ω' : Obls} {k : Oid} {p : Parent} (hk : Ω'.live k) :
    osat Ω' ∗ forestPiece Ω k p ⊢@{IProp GF} ⌜∀ q, p = .obl q → Ω.fuelOf q < Ω'.fuelOf k⌝ := by
  cases p with
  | thread j =>
    exact BI.pure_intro fun q h => Parent.noConfusion h
  | obl q =>
    iintro ⟨Hs, %π, %hπ, Hf⟩
    icases osat_fuel_le Ω' k π $$ [$Hs $Hf] with %hle
    ipureintro
    rintro q' hq
    cases hq
    obtain ⟨a, t, hka⟩ := hk
    rw [Obls.fuelOf_eq hka]
    exact Ordinal.lt_of_lt_of_le hπ (hle a t hka)

end Nodes

/-! ### The invariant -/

section Oforest

variable {GF : BundledGFunctors} [OSatGS GF] [OForestGS GF]

/-- The forest invariant (Rocq `oforest`, with the thread statuses of `othread`): a forest `Par`
of the live obligations of `Ω` below the threads `< tc`, the authoritative children map `M`
tabulating its children, the authoritative status map `T` of the pool, the entries of the
threads, and the nodes. -/
@[lantana_alias oforest]
def oforest (Ω : Obls) (tc : Nat) : IProp GF :=
  iprop(∃ (Par : OidMap Parent) (M : ParentMap Oids) (T : ThreadMap ThreadStatus),
    ⌜ForestWf Ω tc Par ∧ KidsMap tc Par M ∧ StatusMap tc T⌝ ∗
    OForest.kidsAuth M ∗ OForest.statusAuth T ∗
    ([∗list] i ∈ List.range tc, OForest.threadInv Ω Par i) ∗
    [∗map] x ↦ p ∈ Par, forestNode Ω x p)

@[lantana_alias oforest_timeless]
instance oforest_timeless (Ω : Obls) (tc : Nat) : Timeless (oforest (GF := GF) Ω tc) := by
  unfold oforest; infer_instance

#lantana_ignore othread "merged into `oforest` (plan M4 §1)"
#lantana_ignore oassigned "no owner ghost state: the owner is read from `Ω`"
#lantana_ignore othread_timeless "merged into `oforest_timeless`"
#lantana_ignore oassigned_timeless "no owner ghost state"

/-! ### Lookups -/

/-- The forest invariant has a well-formed forest. -/
theorem oforest_wf (Ω : Obls) (tc : Nat) :
    oforest Ω tc ⊢@{IProp GF} ⌜∃ Par, ForestWf Ω tc Par⌝ := by
  unfold oforest
  iintro ⟨%Par, %M, %T, %⟨wf, -, -⟩, -⟩
  ipureintro
  exact ⟨Par, wf⟩

/-- The owners are threads of the pool (Rocq `othread_assigned_thread_elem`). -/
@[lantana_alias othread_assigned_thread_elem]
theorem oforest_owner_lt (Ω : Obls) (tc : Nat) :
    oforest Ω tc ⊢@{IProp GF} ⌜∀ x i, Ω.ownerOf x = some i → i < tc⌝ := by
  iintro H
  icases oforest_wf Ω tc $$ H with %⟨Par, wf⟩
  ipureintro
  exact wf.owner

/-- The children fragment of `p` holds its children in the forest. -/
theorem oforest_kids_lookup (Ω : Obls) (tc : Nat) (p : Parent) (K : Oids) :
    oforest Ω tc ∗ OForest.kids p K ⊢@{IProp GF}
      ⌜∃ Par, ForestWf Ω tc Par ∧ Forest.keyed tc Par p = true ∧ Forest.kids Par p = K⌝ := by
  unfold oforest
  iintro ⟨⟨%Par, %M, %T, %⟨wf, hM, -⟩, HM, -⟩, Hk⟩
  icases OForest.kidsAuth_lookup M p K $$ [$HM $Hk] with %h
  ipureintro
  exact ⟨Par, wf, hM.lookup h⟩

@[lantana_alias oforest_kids_live]
theorem oforest_kids_live (Ω : Obls) (tc : Nat) (p : Parent) (K : Oids) :
    oforest Ω tc ∗ OForest.kids p K ⊢@{IProp GF}
      ⌜(∀ x, x ∈ K → Ω.live x) ∧ (∀ q, p = .obl q → Ω.live q)⌝ := by
  iintro H
  icases oforest_kids_lookup Ω tc p K $$ H with %⟨Par, wf, hkey, hkids⟩
  ipureintro
  refine ⟨fun x hx => wf.kids_live (hkids ▸ hx), ?_⟩
  rintro q rfl
  exact wf.live_of_isSome (by simpa using hkey)

/-- The children of a thread are owned by it, and it is a thread of the pool. -/
theorem oforest_kids_thread (Ω : Obls) (tc : Nat) (i : ThreadId) (K : Oids) :
    oforest Ω tc ∗ OForest.kids (.thread i) K ⊢@{IProp GF}
      ⌜i < tc ∧ ∀ x, x ∈ K → Ω.ownerOf x = some i⌝ := by
  iintro H
  icases oforest_kids_lookup Ω tc _ K $$ H with %⟨Par, wf, hkey, hkids⟩
  ipureintro
  refine ⟨by simpa using hkey, fun x hx => ?_⟩
  rw [← hkids, Forest.mem_kids] at hx
  exact wf.thread x i hx

/-- The children of an obligation have its owner and more fuel, and it is live. -/
theorem oforest_kids_obl (Ω : Obls) (tc : Nat) (q : Oid) (K : Oids) :
    oforest Ω tc ∗ OForest.kids (.obl q) K ⊢@{IProp GF}
      ⌜Ω.live q ∧ ∀ x, x ∈ K → Ω.ownerOf x = Ω.ownerOf q ∧ Ω.fuelOf q < Ω.fuelOf x⌝ := by
  iintro H
  icases oforest_kids_lookup Ω tc _ K $$ H with %⟨Par, wf, hkey, hkids⟩
  ipureintro
  refine ⟨wf.live_of_isSome (by simpa using hkey), fun x hx => ?_⟩
  rw [← hkids, Forest.mem_kids] at hx
  exact ⟨(wf.obl x q hx).1.symm, (wf.obl x q hx).2⟩

/-- The fuel of an obligation with a children fragment is below its bound. -/
@[lantana_alias oforest_obl_fuel_bound]
theorem oforest_obl_fuel_bound (Ω : Obls) (tc : Nat) (q : Oid) (K : Oids) (β : Fuel) :
    oforest Ω tc ∗ OForest.kids (.obl q) K ∗ OSat.bound q β ⊢@{IProp GF}
      ⌜Ω.fuelOf q ≤ β ∧ Ω.live q⌝ := by
  unfold oforest
  iintro ⟨⟨%Par, %M, %T, %⟨wf, hM, -⟩, HM, -, -, Hn⟩, Hk, #Hb⟩
  icases OForest.kidsAuth_lookup M _ K $$ [$HM $Hk] with %h
  have hq := hM.obl_isSome h
  obtain ⟨pq, hpq⟩ := Option.isSome_iff_exists.mp hq
  icases BigSepM.bigSepM_lookup hpq $$ Hn with ⟨-, ⟨%β', #Hb', %hβ'⟩, -⟩
  icases OSat.bound_agree q β β' $$ [$Hb $Hb'] with %hββ
  subst hββ
  ipureintro
  exact ⟨hβ', wf.live_of_isSome hq⟩

/-- The running threads are threads of the pool (Rocq `othread_elem`, for a running thread). -/
@[lantana_alias othread_elem]
theorem oforest_exec_lt (Ω : Obls) (tc : Nat) (i : ThreadId) (q : Qp) :
    oforest Ω tc ∗ OForest.exec i q ⊢@{IProp GF} ⌜i < tc⌝ := by
  unfold oforest
  iintro ⟨⟨%Par, %M, %T, %⟨-, -, hT⟩, -, HT, -⟩, He⟩
  icases OForest.statusAuth_lookup_exec T i q $$ [$HT $He] with %h
  ipureintro
  exact hT.lt h

/-- The terminated threads are threads of the pool. -/
theorem oforest_done_lt (Ω : Obls) (tc : Nat) (i : ThreadId) :
    oforest Ω tc ∗ OForest.done i ⊢@{IProp GF} ⌜i < tc⌝ := by
  unfold oforest
  iintro ⟨⟨%Par, %M, %T, %⟨-, -, hT⟩, -, HT, -⟩, Hd⟩
  icases OForest.statusAuth_lookup_done T i $$ [$HT $Hd] with %h
  ipureintro
  exact hT.lt h

/-- A terminated thread owns no obligation (Rocq `othread_done_open`, which opens the empty set of
obligations of a terminated thread). -/
@[lantana_alias othread_done_open]
theorem oforest_done_owned (Ω : Obls) (tc : Nat) (i : ThreadId) :
    oforest Ω tc ∗ OForest.done i ⊢@{IProp GF} ⌜∀ x, Ω.ownerOf x ≠ some i⌝ := by
  unfold oforest
  iintro ⟨⟨%Par, %M, %T, %⟨wf, -, hT⟩, -, HT, Hth, -⟩, #Hd⟩
  icases OForest.statusAuth_lookup_done T i $$ [$HT $Hd] with %h
  icases BigSepL.bigSepL_mem (List.mem_range.2 (hT.lt h)) $$ Hth with (He | ⟨-, -, %hown⟩)
  · iexfalso
    iapply OForest.exec_done_false $$ [$He $Hd]
  · ipureintro
    intro x hx
    have hmem : x ∈ Forest.owned Ω Par i := wf.mem_owned_iff.2 hx
    rw [hown] at hmem
    exact LawfulSet.mem_empty hmem

/-- An obligation owned by a terminated thread is impossible (Rocq
`othread_assigned_done_false`). -/
@[lantana_alias othread_assigned_done_false]
theorem oforest_assigned_done_false {Ω : Obls} {tc : Nat} {k : Oid} {a : Fuel} {i : ThreadId}
    (hk : get? Ω k = some (.assigned a i)) :
    oforest Ω tc ∗ OForest.done i ⊢@{IProp GF} False := by
  iintro H
  icases oforest_done_owned Ω tc i $$ H with %h
  exact (h k (Obls.ownerOf_eq hk)).elim

/-- The children fragment of a terminated thread is in the invariant. -/
theorem oforest_done_kids_false (Ω : Obls) (tc : Nat) (i : ThreadId) (K : Oids) :
    oforest Ω tc ∗ OForest.done i ∗ OForest.kids (.thread i) K ⊢@{IProp GF} False := by
  unfold oforest
  iintro ⟨⟨%Par, %M, %T, %⟨wf, -, hT⟩, -, HT, Hth, -⟩, #Hd, Hk⟩
  icases OForest.statusAuth_lookup_done T i $$ [$HT $Hd] with %h
  icases BigSepL.bigSepL_mem (List.mem_range.2 (hT.lt h)) $$ Hth with (He | ⟨-, Hk', -⟩)
  · iapply OForest.exec_done_false $$ [$He $Hd]
  · iapply OForest.kids_excl $$ [$Hk $Hk']

/-! ### Threads: allocation and termination -/

/-- A new thread `tc`, running and without children (Rocq `oforest_alloc_thread` with
`othread_alloc_thread`). -/
@[lantana_alias oforest_alloc_thread, lantana_alias othread_alloc_thread]
theorem oforest_alloc_thread (Ω : Obls) (tc : Nat) :
    oforest Ω tc ⊢@{IProp GF} |==> (oforest Ω (tc + 1) ∗ OForest.kids (.thread tc) ∅ ∗
      OForest.exec tc (Qp.half 1)) := by
  unfold oforest
  iintro ⟨%Par, %M, %T, %⟨wf, hM, hT⟩, HM, HT, Hth, Hn⟩
  imod OForest.kidsAuth_insert hM.none_thread ∅ $$ HM with ⟨HM, Hk⟩
  imod OForest.statusAuth_insert hT.none $$ HT with ⟨HT, He⟩
  icases (OForest.exec_half tc).mp $$ He with ⟨He₁, He₂⟩
  imodintro
  iframe Hk He₂
  iexists Par, insert M (.thread tc) ∅, insert T tc .running
  isplitr
  · ipureintro
    exact ⟨wf.alloc_thread, hM.alloc_thread wf, hT.alloc _⟩
  iframe HM HT Hn
  rw [List.range_succ]
  iapply BigSepL.bigSepL_snoc.mpr
  iframe Hth
  ileft
  iexact He₁

/-- New threads `tc, …, tc + n - 1` (Rocq `oforest_alloc_threads` with `othread_alloc_threads`;
thread ids are positions in the pool). -/
@[lantana_alias oforest_alloc_threads, lantana_alias othread_alloc_threads]
theorem oforest_alloc_threads (Ω : Obls) (tc n : Nat) :
    oforest Ω tc ⊢@{IProp GF} |==> (oforest Ω (tc + n) ∗
      [∗list] i ∈ List.range' tc n, OForest.kids (.thread i) ∅ ∗ OForest.exec i (Qp.half 1)) := by
  induction n generalizing tc with
  | zero =>
    simp only [Nat.add_zero, List.range'_zero]
    iintro H
    imodintro
    iframe H
    iapply BigSepL.bigSepL_nil.mpr
    iempintro
  | succ n ih =>
    rw [List.range'_succ, show tc + (n + 1) = tc + 1 + n by omega]
    iintro H
    imod oforest_alloc_thread Ω tc $$ H with ⟨H, Hk, He⟩
    imod ih (tc + 1) $$ H with ⟨H, Hs⟩
    imodintro
    iframe H
    iapply BigSepL.bigSepL_cons.mpr
    iframe Hk He Hs

/-- A running thread without children terminates (Rocq `oforest_exec_to_done` with
`othread_exec_to_done`). -/
@[lantana_alias oforest_exec_to_done, lantana_alias othread_exec_to_done]
theorem oforest_exec_to_done (Ω : Obls) (tc : Nat) (i : ThreadId) :
    oforest Ω tc ∗ OForest.exec i (Qp.half 1) ∗ OForest.kids (.thread i) ∅ ⊢@{IProp GF}
      |==> (oforest Ω tc ∗ OForest.done i) := by
  unfold oforest
  iintro ⟨⟨%Par, %M, %T, %⟨wf, hM, hT⟩, HM, HT, Hth, Hn⟩, He, Hk⟩
  icases OForest.kidsAuth_lookup M _ _ $$ [$HM $Hk] with %hk
  have hi := hM.thread_lt hk
  have hkids := (hM.lookup hk).2
  icases BigSepL.bigSepL_mem_acc (List.mem_range.2 hi) $$ Hth with ⟨Hi, Hclose⟩
  icases Hi with (He' | ⟨-, Hk', -⟩)
  · icases (OForest.exec_half i).mpr $$ [$He $He'] with He
    imod OForest.exec_to_done T i $$ [$HT $He] with ⟨HT, #Hd⟩
    imodintro
    iframe Hd
    iexists Par, M, insert T i .done
    isplitr
    · ipureintro
      exact ⟨wf, hM, hT.update _ hi⟩
    iframe HM HT Hn
    iapply Hclose
    iright
    iframe Hd Hk
    ipureintro
    exact wf.owned_empty hkids
  · iexfalso
    iapply OForest.kids_excl $$ [$Hk $Hk']

#lantana_ignore othread_obls_owns_elem "no per-thread sets of obligations"
#lantana_ignore othread_alloc_obl "no per-thread sets of obligations: `oforest_alloc_obl`"
#lantana_ignore othread_delete_obl "no per-thread sets of obligations: `oforest_discharge_obl`"
#lantana_ignore othread_owns_open "no per-thread maps of owned obligations"
#lantana_ignore othread_obls_open "no per-thread sets of obligations"
#lantana_ignore oassigned_add_obl "no owner ghost state"
#lantana_ignore oassigned_delete_obl "no owner ghost state"

/-! ### Obligations: allocation and discharge -/

/-- A discharged obligation is outside the forest (Rocq `oforest_alloc_discharged`). -/
@[lantana_alias oforest_alloc_discharged]
theorem oforest_alloc_discharged {Ω : Obls} {tc : Nat} {k : Oid} (hk : get? Ω k = none) :
    oforest Ω tc ⊢@{IProp GF} oforest (insert Ω k .discharged) tc := by
  unfold oforest
  iintro ⟨%Par, %M, %T, %⟨wf, hM, hT⟩, HM, HT, Hth, Hn⟩
  have hkPar := wf.none_of_none hk
  have hne : ∀ x, (get? Par x).isSome → k ≠ x := fun x hx e => by
    subst e
    simp [hkPar] at hx
  have hown : ∀ j, j < tc → Forest.owned Ω Par j = ∅ →
      Forest.owned (insert Ω k .discharged) Par j = ∅ := fun j _ h => by
    rw [Forest.owned_ext fun x hx => Obls.ownerOf_insert_ne (hne x hx)]
    exact h
  iexists Par, M, T
  isplitr
  · ipureintro
    exact ⟨wf.alloc_discharged hk, hM, hT⟩
  iframe HM HT
  isplitl [Hth]
  · iapply OForest.threads_mono hown $$ Hth
  · iapply nodes_congr wf (fun x hx => Obls.fuelOf_insert_ne (hne x hx)) $$ Hn

/-- A new obligation `k` of `i` (allocated in the model), a leaf below `p`; below an obligation
`q`, it brings its piece above the fuel of `q` (Rocq `oforest_alloc_obl`, without the owner and
the per-thread tokens; the existence of `k` follows from its bound). -/
@[lantana_alias oforest_alloc_obl]
theorem oforest_alloc_obl {Ω : Obls} {tc : Nat} {p : Parent} {K : Oids} {k : Oid}
    {a β : Fuel} {i : ThreadId} (hk : get? Ω k = none)
    (hp : match p with
      | .thread j => j = i
      | .obl q => Ω.ownerOf q = some i ∧ Ω.fuelOf q < a)
    (hab : a ≤ β) :
    oforest Ω tc ∗ OForest.kids p K ∗ OSat.bound k β ∗ forestPiece Ω k p ⊢@{IProp GF}
      |==> (oforest (insert Ω k (.assigned a i)) tc ∗ ⌜k ∉ K⌝ ∗ OForest.kids p ({k} ∪ K) ∗
        OForest.kids (.obl k) ∅) := by
  unfold oforest
  iintro ⟨⟨%Par, %M, %T, %⟨wf, hM, hT⟩, HM, HT, Hth, Hn⟩, Hp, #Hb, Hpc⟩
  icases OForest.kidsAuth_lookup M p K $$ [$HM $Hp] with %hpK
  obtain ⟨hkey, hkids⟩ := hM.lookup hpK
  have hkPar : get? Par k = none := wf.none_of_none hk
  have hne : ∀ x, (get? Par x).isSome → k ≠ x := fun x hx e => by
    subst e
    simp [hkPar] at hx
  have hpk : p ≠ .obl k := by
    rintro rfl
    simp [hkPar] at hkey
  have hi : i < tc := by
    cases p with
    | thread j =>
      cases hp
      simpa using hkey
    | obl q => exact wf.owner q i hp.1
  have hkK : k ∉ K := by
    rw [← hkids, Forest.mem_kids, hkPar]
    simp
  have hwf' : ForestWf (insert Ω k (.assigned a i)) tc (insert Par k p) := by
    refine wf.alloc_obl hk ?_
    cases p with
    | thread j => exact ⟨hp, hi⟩
    | obl q => exact hp
  have hMk : get? (insert M p ({k} ∪ K)) (.obl k) = none := by
    rw [get?_insert_ne hpk, hM]
    simp [hkPar]
  have hown : ∀ j, j < tc → j ≠ i → Forest.owned Ω Par j = ∅ →
      Forest.owned (insert Ω k (.assigned a i)) (insert Par k p) j = ∅ := fun j _ hji h => by
    rw [Forest.owned_insert_other hkPar hji]
    exact h
  have hpc : ∀ c, p = .obl c → Obls.fuelOf (insert Ω k (.assigned a i)) c ≤ Ω.fuelOf c := by
    rintro c rfl
    exact Ordinal.le_of_eq (Obls.fuelOf_insert_ne (hne c (by simpa using hkey)))
  icases OForest.threads_acc hi $$ Hth with ⟨Hi, Hclose⟩
  icases Hi with (Hei | ⟨-, Hkd, %hownd⟩)
  · imod OForest.kidsAuth_update M p K ({k} ∪ K) $$ [$HM $Hp] with ⟨HM, Hp⟩
    imod OForest.kidsAuth_insert hMk ∅ $$ HM with ⟨HM, Hk⟩
    imodintro
    iframe Hp Hk
    isplitl
    · iexists insert Par k p, insert (insert M p ({k} ∪ K)) (.obl k) ∅, T
      isplitr
      · ipureintro
        exact ⟨hwf', hM.alloc_obl wf hkPar hpK, hT⟩
      iframe HM HT
      isplitl [Hclose Hei]
      · iapply Hclose $$ %_ %_ %hown
        ileft
        iexact Hei
      · iapply (BigSepM.bigSepM_insert hkPar).mpr
        isplitl [Hpc]
        · isplitr
          · iapply OSat.bound_elem $$ Hb
          isplitr
          · iexists β
            iframe Hb
            ipureintro
            rw [Obls.fuelOf_insert_assigned]
            exact hab
          · iapply forestPiece_mono hpc $$ Hpc
        · iapply nodes_congr wf (fun x hx => Obls.fuelOf_insert_ne (hne x hx)) $$ Hn
    · ipureintro
      exact hkK
  · cases p with
    | thread j =>
      cases hp
      iexfalso
      iapply OForest.kids_excl $$ [$Hp $Hkd]
    | obl q =>
      have hmem : q ∈ Forest.owned Ω Par i := wf.mem_owned_iff.2 hp.1
      rw [hownd] at hmem
      exact (LawfulSet.mem_empty hmem).elim

/-- A childless obligation `k` leaves the forest; it is about to be discharged (Rocq
`oforest_discharge_obl`, without the owner and the per-thread tokens). -/
@[lantana_alias oforest_discharge_obl]
theorem oforest_discharge_obl {Ω : Obls} {tc : Nat} {p : Parent} {K : Oids} {k : Oid}
    (hk : k ∈ K) :
    oforest Ω tc ∗ OForest.kids p K ∗ OForest.kids (.obl k) ∅ ⊢@{IProp GF}
      |==> (oforest (insert Ω k .discharged) tc ∗ OForest.kids p (K \ {k})) := by
  unfold oforest
  iintro ⟨⟨%Par, %M, %T, %⟨wf, hM, hT⟩, HM, HT, Hth, Hn⟩, Hp, Hk⟩
  icases OForest.kidsAuth_lookup M p K $$ [$HM $Hp] with %hpK
  icases OForest.kidsAuth_lookup M (.obl k) ∅ $$ [$HM $Hk] with %hkK
  obtain ⟨-, hkids⟩ := hM.lookup hpK
  have hkkids : Forest.kids Par (.obl k) = ∅ := (hM.lookup hkK).2
  have hPk : get? Par k = some p := Forest.mem_kids.1 (hkids ▸ hk)
  have hnok : ∀ x c, get? Par x = some (.obl c) → c ≠ k := by
    rintro x c hx rfl
    have hmem : x ∈ Forest.kids Par (.obl c) := Forest.mem_kids.2 hx
    rw [hkkids] at hmem
    exact LawfulSet.mem_empty hmem
  have hown : ∀ j, j < tc → Forest.owned Ω Par j = ∅ →
      Forest.owned (insert Ω k .discharged) (delete Par k) j = ∅ := fun j _ h => by
    rw [Forest.owned_remove, h]
    exact Forest.diff_singleton_of_not_mem LawfulSet.mem_empty
  imod OForest.kidsAuth_delete M (.obl k) ∅ $$ [$HM $Hk] with HM
  imod OForest.kidsAuth_update (delete M (.obl k)) p K (K \ {k}) $$ [$HM $Hp] with ⟨HM, Hp⟩
  imodintro
  iframe Hp
  iexists delete Par k, insert (delete M (.obl k)) p (K \ {k}), T
  isplitr
  · ipureintro
    exact ⟨wf.discharge hkkids, hM.discharge hPk hkkids hpK, hT⟩
  iframe HM HT
  isplitl [Hth]
  · iapply OForest.threads_mono hown $$ Hth
  · icases (BigSepM.bigSepM_delete hPk).mp $$ Hn with ⟨-, Hn⟩
    iapply nodes_mono ?_ $$ Hn
    intro x p' hx
    have hxk : k ≠ x := fun e => by
      subst e
      simp [get?_delete_eq] at hx
    rw [get?_delete_ne hxk] at hx
    refine ⟨Ordinal.le_of_eq (Obls.fuelOf_insert_ne hxk), ?_⟩
    rintro c rfl
    exact Ordinal.le_of_eq (Obls.fuelOf_insert_ne (hnok x c hx).symm)

/-! ### Moves without owner change -/

/-- The node `k` moves from `p₁` to a parent `p₂` with its owner and less fuel, with a new piece
below an obligation (Rocq `oforest_move_same`, where the piece is `oblG_fuel k π` with
`obl_fuel_of Ω q < π ≤ obl_fuel_of Ω k`; here the condition on the fuels is the one of the
forest). -/
@[lantana_alias oforest_move_same]
theorem oforest_move_same {Ω : Obls} {tc : Nat} {p₁ p₂ : Parent} {K₁ K₂ : Oids} {k : Oid}
    (hk : k ∈ K₁)
    (hp₂ : match p₂ with
      | .thread j => Ω.ownerOf k = some j
      | .obl q => Ω.ownerOf q = Ω.ownerOf k ∧ Ω.fuelOf q < Ω.fuelOf k) :
    oforest Ω tc ∗ OForest.kids p₁ K₁ ∗ OForest.kids p₂ K₂ ∗ forestPiece Ω k p₂ ⊢@{IProp GF}
      |==> (⌜k ∉ K₂⌝ ∗ oforest Ω tc ∗ OForest.kids p₁ (K₁ \ {k}) ∗
        OForest.kids p₂ ({k} ∪ K₂)) := by
  unfold oforest
  iintro ⟨⟨%Par, %M, %T, %⟨wf, hM, hT⟩, HM, HT, Hth, Hn⟩, H₁, H₂, Hpc⟩
  by_cases hp : p₁ = p₂
  · subst hp
    iexfalso
    iapply OForest.kids_excl $$ [$H₁ $H₂]
  icases OForest.kidsAuth_lookup M p₁ K₁ $$ [$HM $H₁] with %hp₁K
  icases OForest.kidsAuth_lookup M p₂ K₂ $$ [$HM $H₂] with %hp₂K
  obtain ⟨-, hkids₁⟩ := hM.lookup hp₁K
  obtain ⟨-, hkids₂⟩ := hM.lookup hp₂K
  have hPk : get? Par k = some p₁ := Forest.mem_kids.1 (hkids₁ ▸ hk)
  have hkK₂ : k ∉ K₂ := fun h => by
    rw [← hkids₂, Forest.mem_kids, hPk] at h
    cases h
    exact hp rfl
  have hown : ∀ j, j < tc → Forest.owned Ω Par j = ∅ →
      Forest.owned Ω (insert Par k p₂) j = ∅ := fun j _ h => by
    rw [Forest.owned_insert_of_isSome (by simp [hPk])]
    exact h
  imod OForest.kidsAuth_update M p₁ K₁ (K₁ \ {k}) $$ [$HM $H₁] with ⟨HM, H₁⟩
  imod OForest.kidsAuth_update _ p₂ K₂ ({k} ∪ K₂) $$ [$HM $H₂] with ⟨HM, H₂⟩
  imodintro
  iframe H₁ H₂
  isplitr
  · ipureintro
    exact hkK₂
  iexists insert Par k p₂, insert (insert M p₁ (K₁ \ {k})) p₂ ({k} ∪ K₂), T
  isplitr
  · ipureintro
    exact ⟨wf.move_same (by simp [hPk]) hp₂, hM.move hPk hp₁K hp₂K, hT⟩
  iframe HM HT
  isplitl [Hth]
  · iapply OForest.threads_mono hown $$ Hth
  · icases (BigSepM.bigSepM_delete hPk).mp $$ Hn with ⟨⟨#He, Hbnd, -⟩, Hn⟩
    iapply BigSepM.bigSepM_insert_delete.mpr
    iframe Hn
    isplitr
    · iexact He
    isplitl [Hbnd]
    · iexact Hbnd
    · iexact Hpc

/-- A grandchild `x`, child of `k`, moves up to the parent `p` of `k`: no model change and no new
fuel, the piece of `x` above the fuel of `k` is above the fuel of `p` (Rocq
`oforest_move_up`). -/
@[lantana_alias oforest_move_up]
theorem oforest_move_up {Ω : Obls} {tc : Nat} {p : Parent} {K : Oids} {k : Oid} {Kk : Oids}
    {x : Oid} (hk : k ∈ K) (hx : x ∈ Kk) :
    oforest Ω tc ∗ OForest.kids p K ∗ OForest.kids (.obl k) Kk ⊢@{IProp GF}
      |==> (⌜x ∉ K⌝ ∗ oforest Ω tc ∗ OForest.kids p ({x} ∪ K) ∗
        OForest.kids (.obl k) (Kk \ {x})) := by
  unfold oforest
  iintro ⟨⟨%Par, %M, %T, %⟨wf, hM, hT⟩, HM, HT, Hth, Hn⟩, Hp, Hk⟩
  by_cases hp : p = .obl k
  · subst hp
    iexfalso
    iapply OForest.kids_excl $$ [$Hp $Hk]
  icases OForest.kidsAuth_lookup M p K $$ [$HM $Hp] with %hpK
  icases OForest.kidsAuth_lookup M (.obl k) Kk $$ [$HM $Hk] with %hkK
  obtain ⟨-, hkids⟩ := hM.lookup hpK
  obtain ⟨-, hkkids⟩ := hM.lookup hkK
  have hPk : get? Par k = some p := Forest.mem_kids.1 (hkids ▸ hk)
  have hPx : get? Par x = some (.obl k) := Forest.mem_kids.1 (hkkids ▸ hx)
  have hxK : x ∉ K := fun h => by
    rw [← hkids, Forest.mem_kids, hPx] at h
    cases h
    exact hp rfl
  have hown : ∀ j, j < tc → Forest.owned Ω Par j = ∅ →
      Forest.owned Ω (insert Par x p) j = ∅ := fun j _ h => by
    rw [Forest.owned_insert_of_isSome (by simp [hPx])]
    exact h
  have hpc : ∀ c', p = .obl c' → ∃ c, Parent.obl k = .obl c ∧ Ω.fuelOf c' ≤ Ω.fuelOf c := by
    rintro c' rfl
    exact ⟨k, rfl, Ordinal.le_of_lt (wf.obl k c' hPk).2⟩
  imod OForest.kidsAuth_update M (.obl k) Kk (Kk \ {x}) $$ [$HM $Hk] with ⟨HM, Hk⟩
  imod OForest.kidsAuth_update _ p K ({x} ∪ K) $$ [$HM $Hp] with ⟨HM, Hp⟩
  imodintro
  iframe Hp Hk
  isplitr
  · ipureintro
    exact hxK
  iexists insert Par x p, insert (insert M (.obl k) (Kk \ {x})) p ({x} ∪ K), T
  isplitr
  · ipureintro
    exact ⟨wf.move_up hPk hPx, hM.move hPx hkK hpK, hT⟩
  iframe HM HT
  isplitl [Hth]
  · iapply OForest.threads_mono hown $$ Hth
  · icases (BigSepM.bigSepM_delete hPx).mp $$ Hn with ⟨⟨#He, Hbnd, Hpc⟩, Hn⟩
    iapply BigSepM.bigSepM_insert_delete.mpr
    iframe Hn
    isplitr
    · iexact He
    isplitl [Hbnd]
    · iexact Hbnd
    · iapply forestPiece_reparent hpc $$ Hpc

/-! ### Steps of a thread -/

/-- A step of thread `i`, in two phases (Rocq `oforest_step`). First, the children `K` of `i` take
the units given by the user, and every other node of `i` splits a unit off its piece, keeping
exactly the fuel of its parent: this returns the set `G` of the obligations of `i` with a unit
each. Then, after a progress round of `i` that keeps the owners (`osat_progress_owner`), the
invariant holds again: the new pieces are below the new fuels of the nodes (`osat_fuel_le` on the
new `osat`) and above the new fuels of their parents. Rocq also hands out and takes back the
running status and the set of obligations of `i`, which are not ghost state here. -/
@[lantana_alias oforest_step]
theorem oforest_step (Ω : Obls) (tc : Nat) (i : ThreadId) (K : Oids) :
    oforest Ω tc ∗ OForest.kids (.thread i) K ∗ ([∗set] k ∈ K, ∃ c, ⌜0 < c⌝ ∗ OSat.fuel k c)
      ⊢@{IProp GF} |==> ∃ G : Oids, ⌜∀ x, x ∈ G ↔ Ω.ownerOf x = some i⌝ ∗
        OForest.kids (.thread i) K ∗ ([∗set] k ∈ G, OSat.elem k ∗ ∃ c, ⌜0 < c⌝ ∗ OSat.fuel k c) ∗
        ∀ Ω' : Obls, ⌜Obls.condProgress (Obl.condOwner i) Ω Ω'⌝ -∗
          ⌜∀ x, Ω'.ownerOf x = Ω.ownerOf x⌝ -∗ osat Ω' -∗ (osat Ω' ∗ oforest Ω' tc) := by
  unfold oforest
  iintro ⟨⟨%Par, %M, %T, %⟨wf, hM, hT⟩, HM, HT, Hth, Hn⟩, Hk, Hu⟩
  icases OForest.kidsAuth_lookup M _ K $$ [$HM $Hk] with %hK
  obtain ⟨-, hkids⟩ := hM.lookup hK
  subst hkids
  icases (Forest.bigSepS_kids Par _ _).mp $$ Hu with Hu
  imod nodes_step wf i $$ [$Hn $Hu] with ⟨Hn, Hg⟩
  icases (Forest.bigSepS_owned Ω Par i _).mpr $$ Hg with Hg
  imodintro
  iexists Forest.owned Ω Par i
  isplitr
  · ipureintro
    intro x
    exact wf.mem_owned_iff
  iframe Hk Hg
  iintro %Ω' %hp %hown Hs
  icases nodes_stepped_pieces wf hp $$ [$Hs $Hn] with %hpiece
  have howned : ∀ j, j < tc → Forest.owned Ω Par j = ∅ → Forest.owned Ω' Par j = ∅ :=
    fun j _ h => by
      rw [Forest.owned_ext fun x _ => hown x]
      exact h
  iframe Hs
  iexists Par, M, T
  isplitr
  · ipureintro
    exact ⟨wf.prog_piece hp (fun x _ => hown x) hpiece, hM, hT⟩
  iframe HM HT
  isplitl [Hth]
  · iapply OForest.threads_mono howned $$ Hth
  · iapply BigSepM.bigSepM_mono (fun hx => node_unstep wf hp hx) $$ Hn

/-- A step of thread `i` with its progress round: the obligations of `i` make progress and keep
their owner (`oforest_step` closed with `osat_progress_owner`). -/
theorem oforest_osat_step (Ω : Obls) (tc : Nat) (i : ThreadId) (K : Oids) :
    osat Ω ∗ oforest Ω tc ∗ OForest.kids (.thread i) K ∗
        ([∗set] k ∈ K, ∃ c, ⌜0 < c⌝ ∗ OSat.fuel k c)
      ⊢@{IProp GF} |==> ∃ Ω', ⌜Obls.condProgress (Obl.condOwner i) Ω Ω' ∧
        ∀ x, Ω'.ownerOf x = Ω.ownerOf x⌝ ∗ osat Ω' ∗ oforest Ω' tc ∗
        OForest.kids (.thread i) K := by
  iintro ⟨Hs, H⟩
  imod oforest_step Ω tc i K $$ H with ⟨%G, %hG, Hk, Hg, Hclose⟩
  ihave Hg := BigSepS.bigSepS_mono_of_forall (fun _ => BI.sep_elim_right) $$ Hg
  imod osat_progress_owner i G hG $$ [$Hs $Hg] with ⟨%Ω', Hs, %⟨hp, hown⟩⟩
  icases Hclose $$ %Ω' %hp %hown Hs with ⟨Hs, H⟩
  imodintro
  iexists Ω'
  iframe Hs H Hk
  ipureintro
  exact ⟨hp, hown⟩

/-! ### Moves with owner change -/

/-- The node `k`, owned by `t`, moves from `p₁` to a parent `p₂` of another owner `j`: its whole
subtree gets the owner `j`, and each of its nodes burns a unit: `k` burns `u`, the other nodes
split a unit off their piece. Below an obligation, `k` brings its new piece (Rocq
`oforest_move_cross`, without the owner and per-thread tokens; `osat_chown_set` changes the model
`Ω` to `Ω'`, related by `chownRel`). -/
@[lantana_alias oforest_move_cross]
theorem oforest_move_cross {Ω : Obls} {tc : Nat} {p₁ p₂ : Parent} {K₁ K₂ : Oids} {k : Oid}
    {t j : ThreadId} {u : Fuel} (hk : k ∈ K₁) (ht : Ω.ownerOf k = some t) (htj : t ≠ j)
    (hu : 0 < u)
    (hp₂ : match p₂ with
      | .thread j' => j' = j
      | .obl q => Ω.ownerOf q = some j) :
    osat Ω ∗ oforest Ω tc ∗ OForest.kids p₁ K₁ ∗ OForest.kids p₂ K₂ ∗ OSat.fuel k u ∗
        forestPiece Ω k p₂
      ⊢@{IProp GF} |==> ∃ Ω', ⌜Obls.ndf Ω Ω' ∧ (∀ x, (get? Ω' x).isSome ↔ (get? Ω x).isSome) ∧
        k ∉ K₂⌝ ∗ osat Ω' ∗ oforest Ω' tc ∗ OForest.kids p₁ (K₁ \ {k}) ∗
        OForest.kids p₂ ({k} ∪ K₂) := by
  unfold oforest
  iintro ⟨Hs, ⟨%Par, %M, %T, %⟨wf, hM, hT⟩, HM, HT, Hth, Hn⟩, H₁, H₂, Hu, Hpc⟩
  by_cases hp : p₁ = p₂
  · subst hp
    iexfalso
    iapply OForest.kids_excl $$ [$H₁ $H₂]
  icases OForest.kidsAuth_lookup M p₁ K₁ $$ [$HM $H₁] with %hp₁K
  icases OForest.kidsAuth_lookup M p₂ K₂ $$ [$HM $H₂] with %hp₂K
  obtain ⟨-, hkids₁⟩ := hM.lookup hp₁K
  obtain ⟨hkey₂, hkids₂⟩ := hM.lookup hp₂K
  have hPk : get? Par k = some p₁ := Forest.mem_kids.1 (hkids₁ ▸ hk)
  have hkD : (get? Par k).isSome := by simp [hPk]
  have hkK₂ : k ∉ K₂ := fun h => by
    rw [← hkids₂, Forest.mem_kids, hPk] at h
    cases h
    exact hp rfl
  have hkS : k ∈ Forest.subtree Par k := Forest.subtree_root Par k
  have hSown : ∀ x, x ∈ Forest.subtree Par k → Ω.ownerOf x = some t := fun x hx =>
    (wf.subtree_owner hkD hx).2.trans ht
  have hSD : ∀ x, x ∈ Forest.subtree Par k → (get? Par x).isSome := fun x hx =>
    (wf.subtree_owner hkD hx).1
  have hSobl : ∀ x, x ∈ Forest.subtree Par k → x ≠ k → ∃ c, get? Par x = some (.obl c) :=
    fun x hx hxk => by
      rcases Forest.subtree_inv hx with e | ⟨c, hc, -⟩
      · exact (hxk e).elim
      · exact ⟨c, hc⟩
  have hj : j < tc := by
    cases p₂ with
    | thread j' =>
      cases hp₂
      simpa using hkey₂
    | obl q => exact wf.owner q j hp₂
  have hq : ∀ q, p₂ = .obl q → q ∉ Forest.subtree Par k := by
    rintro q rfl hqS
    have h := (hSown q hqS).symm.trans hp₂
    cases h
    exact htj rfl
  -- The entry of the new owner `j`: it is running.
  icases OForest.threads_acc hj $$ Hth with ⟨Hj, Hclose⟩
  icases Hj with (Hej | ⟨-, Hkd, %hownd⟩)
  rotate_left
  · cases p₂ with
    | thread j' =>
      cases hp₂
      iexfalso
      iapply OForest.kids_excl $$ [$H₂ $Hkd]
    | obl q =>
      have hmem : q ∈ Forest.owned Ω Par j := wf.mem_owned_iff.2 hp₂
      rw [hownd] at hmem
      exact (LawfulSet.mem_empty hmem).elim
  -- The node `k`: its old piece is dropped.
  icases (BigSepM.bigSepM_delete hPk).mp $$ Hn with ⟨⟨#Hek, ⟨%βk, #Hbk, %hβk⟩, -⟩, Hn⟩
  -- The other nodes of the subtree split a unit off their piece.
  ihave Hn := (BigSepM.bigSepM_mono fun hx => node_cross_split (Ω := Ω) hSobl hx) $$ Hn
  imod BigSepM.bigSepM_bupd _ $$ Hn with Hn
  rw [BigSepM.bigSepM_sep_eq]
  icases Hn with ⟨Hus, Hn⟩
  icases (bigSepS_diff_delete Par _ k hSD _).mpr $$ Hus with Hus
  ihave Hus := (BigSepS.bigSepS_delete hkS).mpr $$ [Hu Hus]
  · iframe Hus
    iexists u
    iframe Hu
    ipureintro
    exact hu
  imod osat_chown_set (Forest.subtree Par k) j hSown $$ [$Hs $Hus] with ⟨%Ω', Hs, %hrel⟩
  have hkΩ' : Ω'.live k := (hrel.live k).1 (wf.live_of_isSome hkD)
  icases osat_forestPiece hkΩ' $$ [$Hs $Hpc] with %hpk
  icases nodes_moved_pieces hrel $$ [$Hs $Hn] with %hpx
  have hwf' : ForestWf Ω' tc (insert Par k p₂) := by
    refine wf.move_cross hkD ht htj ?_ hrel hpk hpx
    cases p₂ with
    | thread j' => exact ⟨hp₂, hj⟩
    | obl q => exact hp₂
  have howned : ∀ j', j' < tc → j' ≠ j → Forest.owned Ω Par j' = ∅ →
      Forest.owned Ω' (insert Par k p₂) j' = ∅ := fun j' _ hj' h => by
    rw [Forest.owned_insert_of_isSome hkD, Forest.owned_chown hrel hSD j']
    simp only [hj', ↓reduceIte]
    split
    · rw [h]
      exact Forest.empty_diff _
    · exact h
  imod OForest.kidsAuth_update M p₁ K₁ (K₁ \ {k}) $$ [$HM $H₁] with ⟨HM, H₁⟩
  imod OForest.kidsAuth_update _ p₂ K₂ ({k} ∪ K₂) $$ [$HM $H₂] with ⟨HM, H₂⟩
  imodintro
  iexists Ω'
  iframe Hs H₁ H₂
  isplitr
  · ipureintro
    exact ⟨hrel.ndf, hrel.isSome_iff, hkK₂⟩
  iexists insert Par k p₂, insert (insert M p₁ (K₁ \ {k})) p₂ ({k} ∪ K₂), T
  isplitr
  · ipureintro
    exact ⟨hwf', hM.move hPk hp₁K hp₂K, hT⟩
  iframe HM HT
  isplitl [Hclose Hej]
  · iapply Hclose $$ %_ %_ %howned
    ileft
    iexact Hej
  · iapply BigSepM.bigSepM_insert_delete.mpr
    isplitl [Hpc]
    · isplitr
      · iexact Hek
      isplitr
      · iexists βk
        iframe Hbk
        ipureintro
        exact Ordinal.le_trans (Ordinal.le_of_lt (hrel.fuel_in hkS).2) hβk
      · iapply forestPiece_mono ?_ $$ Hpc
        rintro q rfl
        exact Ordinal.le_of_eq (hrel.fuel_out (hq q rfl))
    · iapply BigSepM.bigSepM_mono (fun hx => node_cross_join hrel hx) $$ Hn

end Oforest

/-! ## Allocation -/

/-- Allocation of the ghost state of the forest, with no thread and no obligation (Rocq
`oforest_alloc` and `othread_alloc`). -/
@[lantana_alias oforest_alloc, lantana_alias othread_alloc]
theorem oforest_alloc {GF : BundledGFunctors} [OSatGS GF] [OForestGpreS GF] :
    ⊢@{IProp GF} |==> ∃ _ : OForestGS GF, oforest ∅ 0 := by
  imod ghost_map_alloc_empty (GF := GF) (K := Parent) (V := Oids) (H := ParentMap)
    with ⟨%γk, HK⟩
  imod ghost_map_alloc_empty (GF := GF) (K := ThreadId) (V := ThreadStatus) (H := ThreadMap)
    with ⟨%γs, HS⟩
  imodintro
  iexists { kidsName := γk, statusName := γs }
  unfold oforest OForest.kidsAuth OForest.statusAuth
  iexists ∅, ∅, ∅
  iframe HK HS
  isplitr
  · ipureintro
    exact ⟨ForestWf.empty 0, KidsMap.empty, StatusMap.empty⟩
  isplitr
  · rw [List.range_zero]
    iapply BigSepL.bigSepL_nil.mpr
    iempintro
  · iapply BigSepM.bigSepM_empty.mpr
    iempintro

end Lantana.Model
