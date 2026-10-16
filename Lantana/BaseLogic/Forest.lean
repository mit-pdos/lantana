/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.BaseLogic.ModelRel

/-! # The obligation forest: pure part

The pure part of Rocq `lantana/base_logic/oforest.v` (`Section forest_pure` and the pure
reasoning inside `oforest_step`). Every live obligation is a node of the forest, with a parent:
a thread of the pool or another live obligation. A node below an obligation `c` has the owner of
`c` and strictly more fuel, so fuel decreases strictly towards the roots and the forest is
acyclic for free.

Redesign (D10 item 5): the parent map `Par : OidMap Parent` is the only data; Rocq's children
map `Kids` is *defined* from it as the finite set `Forest.kids Par p` of the nodes whose parent
is `p` (`mem_kids : x ∈ kids Par p ↔ get? Par x = some p`), so Rocq's `fwf_kids_dom` and
`fwf_par_kids` hold by definition and disappear from `ForestWf`, and the shape-change lemmas
no longer carry `Kids` side conditions. Thread pools are a count `tc` of threads
`0, …, tc - 1` (D14).

The subtree of a node `k` is `Forest.subtree Par k`, the finite set of `k` and of the nodes
related to `k` by the transitive closure of the child relation (classical membership test).
-/

@[expose] public section

namespace Lantana.Model

open Iris.Std LawfulPartialMap
open Ordinals

/-! ## Reading the model -/

namespace Obls

/-- `x` is a live (assigned) obligation. -/
def live (Ω : Obls) (x : Oid) : Prop :=
  ∃ a t, get? Ω x = some (.assigned a t)

/-- The fuel of `x` (`0` if `x` is not assigned). -/
@[lantana_alias obl_fuel_of]
def fuelOf (Ω : Obls) (x : Oid) : Fuel :=
  match get? Ω x with
  | some (.assigned a _) => a
  | _ => 0

/-- The owner of `x`, if it is assigned. -/
@[lantana_alias obl_owner_of]
def ownerOf (Ω : Obls) (x : Oid) : Option ThreadId :=
  match get? Ω x with
  | some (.assigned _ t) => some t
  | _ => none

theorem fuelOf_eq {Ω : Obls} {x : Oid} {a : Fuel} {t : ThreadId}
    (h : get? Ω x = some (.assigned a t)) : Ω.fuelOf x = a := by
  simp [fuelOf, h]

theorem ownerOf_eq {Ω : Obls} {x : Oid} {a : Fuel} {t : ThreadId}
    (h : get? Ω x = some (.assigned a t)) : Ω.ownerOf x = some t := by
  simp [ownerOf, h]

theorem ownerOf_eq_some {Ω : Obls} {x : Oid} {t : ThreadId} :
    Ω.ownerOf x = some t ↔ ∃ a, get? Ω x = some (.assigned a t) := by
  unfold ownerOf
  cases get? Ω x with
  | none => simp
  | some g => cases g <;> simp

theorem live_iff_ownerOf {Ω : Obls} {x : Oid} : Ω.live x ↔ (Ω.ownerOf x).isSome := by
  unfold live ownerOf
  cases get? Ω x with
  | none => simp
  | some g => cases g <;> simp

theorem live_of_ownerOf {Ω : Obls} {x : Oid} {t : ThreadId} (h : Ω.ownerOf x = some t) :
    Ω.live x :=
  live_iff_ownerOf.2 (by simp [h])

theorem ownerOf_of_live {Ω : Obls} {x : Oid} (h : Ω.live x) : ∃ t, Ω.ownerOf x = some t := by
  have h' := live_iff_ownerOf.1 h
  cases e : Ω.ownerOf x with
  | none => simp [e] at h'
  | some t => exact ⟨t, rfl⟩

theorem not_live_of_none {Ω : Obls} {x : Oid} (h : get? Ω x = none) : ¬Ω.live x := by
  rintro ⟨a, t, h'⟩
  simp [h] at h'

@[lantana_alias obl_fuel_of_insert_ne]
theorem fuelOf_insert_ne {Ω : Obls} {k x : Oid} {g : Obl} (h : k ≠ x) :
    fuelOf (insert Ω k g) x = Ω.fuelOf x := by
  simp only [fuelOf, get?_insert_ne h]

@[lantana_alias obl_owner_of_insert_ne]
theorem ownerOf_insert_ne {Ω : Obls} {k x : Oid} {g : Obl} (h : k ≠ x) :
    ownerOf (insert Ω k g) x = Ω.ownerOf x := by
  simp only [ownerOf, get?_insert_ne h]

theorem live_insert_ne {Ω : Obls} {k x : Oid} {g : Obl} (h : k ≠ x) :
    live (insert Ω k g) x ↔ Ω.live x := by
  simp only [live, get?_insert_ne h]

@[lantana_alias obl_fuel_of_insert_eq]
theorem fuelOf_insert_assigned {Ω : Obls} {k : Oid} {a : Fuel} {i : ThreadId} :
    fuelOf (insert Ω k (.assigned a i)) k = a :=
  fuelOf_eq (get?_insert_eq rfl)

@[lantana_alias obl_owner_of_insert_eq]
theorem ownerOf_insert_assigned {Ω : Obls} {k : Oid} {a : Fuel} {i : ThreadId} :
    ownerOf (insert Ω k (.assigned a i)) k = some i :=
  ownerOf_eq (get?_insert_eq rfl)

theorem live_insert_assigned {Ω : Obls} {k : Oid} {a : Fuel} {i : ThreadId} :
    live (insert Ω k (.assigned a i)) k :=
  ⟨a, i, get?_insert_eq rfl⟩

theorem fuelOf_insert_discharged {Ω : Obls} {k : Oid} :
    fuelOf (insert Ω k .discharged) k = 0 := by
  simp only [fuelOf, get?_insert_eq]

theorem ownerOf_insert_discharged {Ω : Obls} {k : Oid} :
    ownerOf (insert Ω k .discharged) k = none := by
  simp only [ownerOf, get?_insert_eq]

theorem not_live_insert_discharged {Ω : Obls} {k : Oid} :
    ¬live (insert Ω k .discharged) k := by
  rintro ⟨a, t, h⟩
  simp [get?_insert_eq] at h

end Obls

/-! ## Physical steps of a thread -/

section Prog

variable {Ω Ω' : Obls} {i : ThreadId}

/-- After a progress round of thread `i`, the obligations of `i` have less fuel. -/
@[lantana_alias prog_owned]
theorem prog_owned (hp : Obls.condProgress (Obl.condOwner i) Ω Ω') {x : Oid} {a : Fuel}
    (hx : get? Ω x = some (.assigned a i)) :
    ∃ a' t', get? Ω' x = some (.assigned a' t') ∧ a' < a := by
  obtain ⟨g', e', hr⟩ := mapForall2.lookup_left hp.1 hx
  have hkeep : Obl.keep (.assigned a i) g' := mapForall2.lookup hp.2 hx e'
  rcases hr with ⟨_, hs | hs⟩ | ⟨hn, _⟩
  · cases g' with
    | assigned a' t' => exact ⟨a', t', e', hs⟩
    | discharged => simp at hs
  · cases g' <;> simp_all [Obl.keep]
  · exact absurd rfl hn

/-- After a progress round of thread `i`, the other obligations are unchanged. -/
@[lantana_alias prog_other]
theorem prog_other (hp : Obls.condProgress (Obl.condOwner i) Ω Ω') {x : Oid} {g : Obl}
    (hx : get? Ω x = some g) (hn : ¬Obl.condOwner i x g) : get? Ω' x = some g := by
  obtain ⟨g', e', hr⟩ := mapForall2.lookup_left hp.1 hx
  rcases hr with ⟨hc, _⟩ | ⟨_, rfl⟩
  · exact absurd hc hn
  · exact e'

/-- A progress round keeps the live obligations. -/
@[lantana_alias prog_live]
theorem prog_live (hp : Obls.condProgress (Obl.condOwner i) Ω Ω') (x : Oid) :
    Ω.live x ↔ Ω'.live x := by
  constructor
  · rintro ⟨a, t, hx⟩
    by_cases ht : t = i
    · subst ht
      obtain ⟨a', t', hx', _⟩ := prog_owned hp hx
      exact ⟨a', t', hx'⟩
    · exact ⟨a, t, prog_other hp hx ht⟩
  · rintro ⟨a', t', hx'⟩
    obtain ⟨g, e, hkeep⟩ := mapForall2.lookup_right hp.2 hx'
    cases g with
    | assigned a t => exact ⟨a, t, e⟩
    | discharged => simp [Obl.keep] at hkeep

theorem prog_fuelOf_lt (hp : Obls.condProgress (Obl.condOwner i) Ω Ω') {x : Oid}
    (hx : Ω.ownerOf x = some i) : Ω'.fuelOf x < Ω.fuelOf x := by
  obtain ⟨a, ha⟩ := Obls.ownerOf_eq_some.1 hx
  obtain ⟨a', t', ha', hlt⟩ := prog_owned hp ha
  rw [Obls.fuelOf_eq ha, Obls.fuelOf_eq ha']
  exact hlt

theorem prog_get?_of_ne (hp : Obls.condProgress (Obl.condOwner i) Ω Ω') {x : Oid}
    (hx : Ω.ownerOf x ≠ some i) : get? Ω' x = get? Ω x := by
  cases e : get? Ω x with
  | none => exact mapForall2.none_left hp.1 e
  | some g =>
    refine prog_other hp e ?_
    cases g with
    | assigned a t => exact fun h => hx (Obls.ownerOf_eq (h ▸ e))
    | discharged => exact id

theorem prog_fuelOf_of_ne (hp : Obls.condProgress (Obl.condOwner i) Ω Ω') {x : Oid}
    (hx : Ω.ownerOf x ≠ some i) : Ω'.fuelOf x = Ω.fuelOf x := by
  simp only [Obls.fuelOf, prog_get?_of_ne hp hx]

theorem prog_ownerOf_of_ne (hp : Obls.condProgress (Obl.condOwner i) Ω Ω') {x : Oid}
    (hx : Ω.ownerOf x ≠ some i) : Ω'.ownerOf x = Ω.ownerOf x := by
  simp only [Obls.ownerOf, prog_get?_of_ne hp hx]

end Prog

/-! ## Children, owned nodes and subtrees -/

namespace Forest

/-- The children of `p`: the nodes whose parent is `p` (Rocq's `Kids !! p`, here defined). -/
def kids (Par : OidMap Parent) (p : Parent) : Oids :=
  FiniteMap.dom_set (PartialMap.filter (fun _ q => decide (q = p)) Par)

/-- The nodes owned by thread `i` (Rocq `forest_owned Ω (dom Par) i`). -/
@[lantana_alias forest_owned]
def owned (Ω : Obls) (Par : OidMap Parent) (i : ThreadId) : Oids :=
  FiniteMap.dom_set (PartialMap.filter (fun x _ => decide (Ω.ownerOf x = some i)) Par)

/-- `x` is a child of the obligation `c`. -/
def ChildOf (Par : OidMap Parent) (x c : Oid) : Prop :=
  get? Par x = some (.obl c)

open Classical in
/-- `k` and all its descendants (Rocq `subtree`, defined by iteration there). -/
@[lantana_alias subtree]
noncomputable def subtree (Par : OidMap Parent) (k : Oid) : Oids :=
  {k} ∪ FiniteMap.dom_set
    (PartialMap.filter (fun x _ => decide (Relation.TransGen (ChildOf Par) x k)) Par)

#lantana_ignore par_in "`Forest.subtree` is defined by `Relation.TransGen`"
#lantana_ignore par_in_dec "`Forest.subtree` is defined by `Relation.TransGen`"
#lantana_ignore kids_of "`Forest.subtree` is defined by `Relation.TransGen`"
#lantana_ignore kids_step "`Forest.subtree` is defined by `Relation.TransGen`"
#lantana_ignore elem_of_kids_of "`Forest.subtree` is defined by `Relation.TransGen`"
#lantana_ignore kids_of_dom "`Forest.subtree` is defined by `Relation.TransGen`"
#lantana_ignore iter_kids_step_sub "`Forest.subtree` is defined by `Relation.TransGen`"
#lantana_ignore iter_kids_step_incl "`Forest.subtree` is defined by `Relation.TransGen`"
#lantana_ignore iter_kids_step_size "`Forest.subtree` is defined by `Relation.TransGen`"
#lantana_ignore iter_kids_step_fix_stable "`Forest.subtree` is defined by `Relation.TransGen`"
#lantana_ignore subtree_fix "`Forest.subtree_closed` and `Forest.subtree_inv`"
#lantana_ignore parent_eq_dec "`Parent` derives `DecidableEq` (`Lantana.Prelude.Ids`)"
#lantana_ignore parent_countable "unused: no map is keyed by `Parent` (D10: `Par` is primary)"

@[simp] theorem mem_kids {Par : OidMap Parent} {p : Parent} {x : Oid} :
    x ∈ kids Par p ↔ get? Par x = some p := by
  rw [kids, LawfulFiniteMap.mem_dom_set, get?_filter]
  cases get? Par x <;> simp

@[simp] theorem mem_owned {Ω : Obls} {Par : OidMap Parent} {i : ThreadId} {x : Oid} :
    x ∈ owned Ω Par i ↔ (get? Par x).isSome ∧ Ω.ownerOf x = some i := by
  rw [owned, LawfulFiniteMap.mem_dom_set, get?_filter]
  cases get? Par x <;> simp

theorem transGen_childOf_isSome {Par : OidMap Parent} {x k : Oid}
    (h : Relation.TransGen (ChildOf Par) x k) : (get? Par x).isSome := by
  induction h with
  | single h => simp [ChildOf] at h; simp [h]
  | tail _ _ ih => exact ih

theorem mem_subtree {Par : OidMap Parent} {k x : Oid} :
    x ∈ subtree Par k ↔ x = k ∨ Relation.TransGen (ChildOf Par) x k := by
  classical
  rw [subtree, LawfulSet.mem_union, LawfulSet.mem_singleton, LawfulFiniteMap.mem_dom_set,
    get?_filter]
  refine or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · cases e : get? Par x with
    | none => simp [e] at h
    | some p => simp_all
  · have hs := transGen_childOf_isSome h
    cases e : get? Par x with
    | none => simp [e] at hs
    | some p => simp [h]

/-! ### Children -/

theorem kids_empty (p : Parent) : kids (∅ : OidMap Parent) p = ∅ :=
  LawfulSet.ext fun x => by simp [get?_empty, LawfulSet.mem_empty]

theorem eq_empty_iff_forall_not_mem {s : Oids} : s = ∅ ↔ ∀ x, x ∉ s :=
  ⟨fun h x hx => by rw [h] at hx; exact LawfulSet.mem_empty hx,
   fun h => LawfulSet.ext fun x => ⟨fun hx => (h x hx).elim,
     fun hx => (LawfulSet.mem_empty hx).elim⟩⟩

theorem kids_eq_empty {Par : OidMap Parent} {p : Parent} :
    kids Par p = ∅ ↔ ∀ x, get? Par x ≠ some p := by
  rw [eq_empty_iff_forall_not_mem]
  simp

/-- The children of the new parent `p` of `k`. -/
theorem kids_insert_self {Par : OidMap Parent} {k : Oid} {p : Parent} :
    kids (insert Par k p) p = {k} ∪ kids Par p :=
  LawfulSet.ext fun x => by
    rw [LawfulSet.mem_union, LawfulSet.mem_singleton, mem_kids, mem_kids]
    by_cases h : k = x
    · subst h; simp [get?_insert_eq]
    · rw [get?_insert_ne h]; exact ⟨.inr, fun h' => h'.elim (fun e => (h e.symm).elim) id⟩

/-- The children of a parent `q` other than the new parent of `k`. -/
theorem kids_insert_ne {Par : OidMap Parent} {k : Oid} {p q : Parent} (hpq : p ≠ q) :
    kids (insert Par k p) q = kids Par q \ {k} :=
  LawfulSet.ext fun x => by
    rw [LawfulSet.mem_diff, LawfulSet.mem_singleton, mem_kids, mem_kids]
    by_cases h : k = x
    · subst h; simp [get?_insert_eq, hpq]
    · rw [get?_insert_ne h]; exact ⟨fun h' => ⟨h', fun e => h e.symm⟩, And.left⟩

theorem kids_delete {Par : OidMap Parent} {k : Oid} {q : Parent} :
    kids (delete Par k) q = kids Par q \ {k} :=
  LawfulSet.ext fun x => by
    rw [LawfulSet.mem_diff, LawfulSet.mem_singleton, mem_kids, mem_kids]
    by_cases h : k = x
    · subst h; simp [get?_delete_eq]
    · rw [get?_delete_ne h]; exact ⟨fun h' => ⟨h', fun e => h e.symm⟩, And.left⟩

/-! ### Owned nodes -/

/-- The owned nodes depend only on the owners of the nodes. -/
@[lantana_alias forest_owned_ext]
theorem owned_ext {Ω Ω' : Obls} {Par : OidMap Parent} {i : ThreadId}
    (h : ∀ x, (get? Par x).isSome → Ω'.ownerOf x = Ω.ownerOf x) :
    owned Ω' Par i = owned Ω Par i :=
  LawfulSet.ext fun x => by
    rw [mem_owned, mem_owned]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h x h₁ ▸ h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, (h x h₁).symm ▸ h₂⟩⟩

/-- The owned nodes depend only on the domain of `Par`. -/
theorem owned_insert_of_isSome {Ω : Obls} {Par : OidMap Parent} {k : Oid} {p : Parent}
    {i : ThreadId} (hk : (get? Par k).isSome) : owned Ω (insert Par k p) i = owned Ω Par i :=
  LawfulSet.ext fun x => by
    rw [mem_owned, mem_owned]
    by_cases h : k = x
    · subst h; simp [get?_insert_eq, hk]
    · rw [get?_insert_ne h]

@[lantana_alias forest_owned_insert_same]
theorem owned_insert_same {Ω : Obls} {Par : OidMap Parent} {k : Oid} {p : Parent} {a : Fuel}
    {i : ThreadId} :
    owned (insert Ω k (.assigned a i)) (insert Par k p) i = {k} ∪ owned Ω Par i :=
  LawfulSet.ext fun x => by
    rw [mem_owned, LawfulSet.mem_union, LawfulSet.mem_singleton, mem_owned]
    by_cases h : k = x
    · subst h; simp [get?_insert_eq, Obls.ownerOf_insert_assigned]
    · rw [get?_insert_ne h, Obls.ownerOf_insert_ne h]
      exact ⟨.inr, fun h' => h'.elim (fun e => (h e.symm).elim) id⟩

@[lantana_alias forest_owned_insert_other]
theorem owned_insert_other {Ω : Obls} {Par : OidMap Parent} {k : Oid} {p : Parent} {a : Fuel}
    {i j : ThreadId} (hk : get? Par k = none) (hj : j ≠ i) :
    owned (insert Ω k (.assigned a i)) (insert Par k p) j = owned Ω Par j :=
  LawfulSet.ext fun x => by
    rw [mem_owned, mem_owned]
    by_cases h : k = x
    · subst h; simp [Obls.ownerOf_insert_assigned, hk, Ne.symm hj]
    · rw [get?_insert_ne h, Obls.ownerOf_insert_ne h]

/-- Removing a node (discharge). -/
@[lantana_alias forest_owned_remove]
theorem owned_remove {Ω : Obls} {Par : OidMap Parent} {k : Oid} {g : Obl} {j : ThreadId} :
    owned (insert Ω k g) (delete Par k) j = owned Ω Par j \ {k} :=
  LawfulSet.ext fun x => by
    rw [mem_owned, LawfulSet.mem_diff, LawfulSet.mem_singleton, mem_owned]
    by_cases h : k = x
    · subst h; simp [get?_delete_eq]
    · rw [get?_delete_ne h, Obls.ownerOf_insert_ne h]
      exact ⟨fun h' => ⟨h', fun e => h e.symm⟩, And.left⟩

/-! ### Subtrees -/

@[lantana_alias subtree_root]
theorem subtree_root (Par : OidMap Parent) (k : Oid) : k ∈ subtree Par k :=
  mem_subtree.2 (.inl rfl)

/-- The subtree is closed under children. -/
@[lantana_alias subtree_closed]
theorem subtree_closed {Par : OidMap Parent} {k x c : Oid} (hx : get? Par x = some (.obl c))
    (hc : c ∈ subtree Par k) : x ∈ subtree Par k := by
  rw [mem_subtree] at hc ⊢
  rcases hc with rfl | hc
  · exact .inr (.single hx)
  · exact .inr (.trans (.single hx) hc)

theorem transGen_inv_head {α : Sort _} {r : α → α → Prop} {x k : α}
    (h : Relation.TransGen r x k) : r x k ∨ ∃ c, r x c ∧ Relation.TransGen r c k := by
  induction h with
  | single h => exact .inl h
  | tail _ h₂ ih =>
    rcases ih with h₁ | ⟨c, h₁, h₁'⟩
    · exact .inr ⟨_, h₁, .single h₂⟩
    · exact .inr ⟨c, h₁, .tail h₁' h₂⟩

/-- A node of the subtree is its root or a child of a node of the subtree. -/
@[lantana_alias subtree_inv]
theorem subtree_inv {Par : OidMap Parent} {k x : Oid} (hx : x ∈ subtree Par k) :
    x = k ∨ ∃ c, get? Par x = some (.obl c) ∧ c ∈ subtree Par k := by
  rw [mem_subtree] at hx
  rcases hx with rfl | hx
  · exact .inl rfl
  · rcases transGen_inv_head hx with h | ⟨c, h, hc⟩
    · exact .inr ⟨_, h, subtree_root Par k⟩
    · exact .inr ⟨c, h, mem_subtree.2 (.inr hc)⟩

end Forest

/-! ## Well-formedness of the forest -/

/-- Well-formedness of the forest `Par` over the obligations `Ω` with `tc` threads (Rocq
`forest_wf`; the fields `fwf_kids_dom` and `fwf_par_kids` hold by definition of
`Forest.kids`). -/
@[lantana_alias forest_wf]
structure ForestWf (Ω : Obls) (tc : Nat) (Par : OidMap Parent) : Prop where
  /-- The nodes are the live obligations. -/
  par_live : ∀ x, (get? Par x).isSome ↔ Ω.live x
  /-- A node below a thread is owned by it. -/
  thread : ∀ x i, get? Par x = some (.thread i) → Ω.ownerOf x = some i
  /-- A node below an obligation has its owner and strictly more fuel. -/
  obl : ∀ x c, get? Par x = some (.obl c) →
    Ω.ownerOf c = Ω.ownerOf x ∧ Ω.fuelOf c < Ω.fuelOf x
  /-- Owners are threads of the pool. -/
  owner : ∀ x i, Ω.ownerOf x = some i → i < tc

attribute [lantana_alias fwf_par_live] ForestWf.par_live
attribute [lantana_alias fwf_thread] ForestWf.thread
attribute [lantana_alias fwf_obl] ForestWf.obl
attribute [lantana_alias fwf_owner] ForestWf.owner

#lantana_ignore fwf_kids_dom "`Forest.kids` is defined from `Par`"
#lantana_ignore fwf_par_kids "`Forest.kids` is defined from `Par` (`Forest.mem_kids`)"

namespace ForestWf

variable {Ω Ω' : Obls} {tc : Nat} {Par : OidMap Parent}

open Forest

theorem live_of_isSome (wf : ForestWf Ω tc Par) {x : Oid} (hx : (get? Par x).isSome) :
    Ω.live x :=
  (wf.par_live x).1 hx

theorem isSome_of_live (wf : ForestWf Ω tc Par) {x : Oid} (hx : Ω.live x) :
    (get? Par x).isSome :=
  (wf.par_live x).2 hx

theorem isSome_of_ownerOf (wf : ForestWf Ω tc Par) {x : Oid} {t : ThreadId}
    (hx : Ω.ownerOf x = some t) : (get? Par x).isSome :=
  wf.isSome_of_live (Obls.live_of_ownerOf hx)

theorem none_of_none (wf : ForestWf Ω tc Par) {x : Oid} (hx : get? Ω x = none) :
    get? Par x = none := by
  cases e : get? Par x with
  | none => rfl
  | some p => exact absurd (wf.live_of_isSome (by simp [e])) (Obls.not_live_of_none hx)

/-- A parent that is a thread is a thread of the pool. -/
theorem thread_lt (wf : ForestWf Ω tc Par) {x : Oid} {i : ThreadId}
    (hx : get? Par x = some (.thread i)) : i < tc :=
  wf.owner x i (wf.thread x i hx)

/-- A parent that is an obligation is itself a node. -/
theorem par_obl (wf : ForestWf Ω tc Par) {x c : Oid} (hx : get? Par x = some (.obl c)) :
    (get? Par c).isSome := by
  obtain ⟨t, ht⟩ := Obls.ownerOf_of_live (wf.live_of_isSome (x := x) (by simp [hx]))
  exact wf.isSome_of_ownerOf ((wf.obl x c hx).1.trans ht)

theorem kids_live (wf : ForestWf Ω tc Par) {p : Parent} {x : Oid} (hx : x ∈ kids Par p) :
    Ω.live x :=
  wf.live_of_isSome (by rw [mem_kids] at hx; simp [hx])

/-- An obligation that is not a node has no children. -/
theorem kids_obl_of_none (wf : ForestWf Ω tc Par) {k : Oid} (hk : get? Par k = none) :
    kids Par (.obl k) = ∅ :=
  kids_eq_empty.2 fun x hx => by simpa [hk] using wf.par_obl hx

@[lantana_alias forest_wf_empty]
theorem empty (tc : Nat) : ForestWf ∅ tc ∅ where
  par_live x := by simp [get?_empty, Obls.not_live_of_none (get?_empty x)]
  thread x i h := by simp [get?_empty] at h
  obl x c h := by simp [get?_empty] at h
  owner x i h := by simp [Obls.ownerOf, get?_empty] at h

/-- More threads. -/
theorem mono_tc (wf : ForestWf Ω tc Par) {tc' : Nat} (h : tc ≤ tc') : ForestWf Ω tc' Par where
  par_live := wf.par_live
  thread := wf.thread
  obl := wf.obl
  owner x i hx := Nat.lt_of_lt_of_le (wf.owner x i hx) h

/-- A new thread. -/
@[lantana_alias forest_wf_alloc_thread]
theorem alloc_thread (wf : ForestWf Ω tc Par) : ForestWf Ω (tc + 1) Par :=
  wf.mono_tc (Nat.le_succ tc)

/-- A thread outside the pool has no children. -/
theorem kids_thread_of_le (wf : ForestWf Ω tc Par) {i : ThreadId} (hi : tc ≤ i) :
    kids Par (.thread i) = ∅ :=
  kids_eq_empty.2 fun x hx =>
    Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (wf.owner x i (wf.thread x i hx)) hi)

/-- A thread outside the pool owns nothing. -/
@[lantana_alias forest_owned_not_in_pool]
theorem owned_of_le (wf : ForestWf Ω tc Par) {i : ThreadId} (hi : tc ≤ i) :
    owned Ω Par i = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun x hx => by
    rw [mem_owned] at hx
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (wf.owner x i hx.2) hi)

/-- A thread without children owns no node: every node has a chain of parents ending at its
owner (well-founded induction on the fuel). -/
@[lantana_alias forest_wf_owned_empty]
theorem owned_empty (wf : ForestWf Ω tc Par) {i : ThreadId} (hi : kids Par (.thread i) = ∅) :
    owned Ω Par i = ∅ := by
  rw [kids_eq_empty] at hi
  refine eq_empty_iff_forall_not_mem.2 fun x hx => ?_
  rw [mem_owned] at hx
  suffices h : ∀ f : Fuel, ∀ x, Ω.fuelOf x = f → (get? Par x).isSome →
      Ω.ownerOf x = some i → False from h _ x rfl hx.1 hx.2
  intro f
  induction f using Ordinal.induction with
  | _ f ih =>
    intro x hf hx ho
    cases e : get? Par x with
    | none => simp [e] at hx
    | some p =>
      cases p with
      | thread j =>
        have hj := wf.thread x j e
        rw [ho] at hj
        cases hj
        exact hi x e
      | obl c =>
        obtain ⟨hoc, hlt⟩ := wf.obl x c e
        exact ih _ (hf ▸ hlt) c rfl (wf.par_obl e) (hoc.trans ho)

/-- The forest only depends on the owners, fuels and liveness of the obligations. -/
theorem congr (wf : ForestWf Ω tc Par) (hown : ∀ x, Ω'.ownerOf x = Ω.ownerOf x)
    (hfuel : ∀ x, Ω'.fuelOf x = Ω.fuelOf x) : ForestWf Ω' tc Par where
  par_live x := by
    rw [wf.par_live, Obls.live_iff_ownerOf, Obls.live_iff_ownerOf, hown]
  thread x i hx := (hown x).trans (wf.thread x i hx)
  obl x c hx := by rw [hown, hown, hfuel, hfuel]; exact wf.obl x c hx
  owner x i hx := wf.owner x i ((hown x).symm.trans hx)

/-- A discharged obligation outside the forest. -/
theorem alloc_discharged (wf : ForestWf Ω tc Par) {k : Oid} (hk : get? Ω k = none) :
    ForestWf (insert Ω k .discharged) tc Par := by
  have hown : ∀ x, Obls.ownerOf (insert Ω k .discharged) x = Ω.ownerOf x := fun x => by
    by_cases h : k = x
    · subst h; rw [Obls.ownerOf_insert_discharged]; simp [Obls.ownerOf, hk]
    · exact Obls.ownerOf_insert_ne h
  have hfuel : ∀ x, Obls.fuelOf (insert Ω k .discharged) x = Ω.fuelOf x := fun x => by
    by_cases h : k = x
    · subst h; rw [Obls.fuelOf_insert_discharged]; simp [Obls.fuelOf, hk]
    · exact Obls.fuelOf_insert_ne h
  exact wf.congr hown hfuel

/-- A new leaf `k` below `p`, owned by `i`. -/
@[lantana_alias forest_wf_alloc_obl]
theorem alloc_obl (wf : ForestWf Ω tc Par) {k : Oid} {p : Parent} {a : Fuel} {i : ThreadId}
    (hk : get? Ω k = none)
    (hp : match p with
      | .thread j => j = i ∧ i < tc
      | .obl q => Ω.ownerOf q = some i ∧ Ω.fuelOf q < a) :
    ForestWf (insert Ω k (.assigned a i)) tc (insert Par k p) := by
  have hkPar : get? Par k = none := wf.none_of_none hk
  have hi : i < tc := by
    cases p with
    | thread j => exact hp.2
    | obl q => exact wf.owner q i hp.1
  -- A node of `Par` is not `k`.
  have hne : ∀ x, (get? Par x).isSome → k ≠ x := fun x hx e => by
    subst e; simp [hkPar] at hx
  constructor
  · intro x
    by_cases h : k = x
    · subst h; simp [get?_insert_eq, Obls.live_insert_assigned]
    · rw [get?_insert_ne h, Obls.live_insert_ne h]; exact wf.par_live x
  · intro x j hx
    by_cases h : k = x
    · subst h
      rw [get?_insert_eq rfl] at hx
      cases hx
      rw [Obls.ownerOf_insert_assigned, hp.1]
    · rw [get?_insert_ne h] at hx
      rw [Obls.ownerOf_insert_ne h]
      exact wf.thread x j hx
  · intro x c hx
    by_cases h : k = x
    · subst h
      rw [get?_insert_eq rfl] at hx
      cases hx
      have hc : k ≠ c := hne c (wf.isSome_of_ownerOf hp.1)
      rw [Obls.ownerOf_insert_ne hc, Obls.fuelOf_insert_ne hc, Obls.ownerOf_insert_assigned,
        Obls.fuelOf_insert_assigned]
      exact hp
    · rw [get?_insert_ne h] at hx
      have hc : k ≠ c := hne c (wf.par_obl hx)
      rw [Obls.ownerOf_insert_ne hc, Obls.fuelOf_insert_ne hc, Obls.ownerOf_insert_ne h,
        Obls.fuelOf_insert_ne h]
      exact wf.obl x c hx
  · intro x j hx
    by_cases h : k = x
    · subst h
      rw [Obls.ownerOf_insert_assigned] at hx
      cases hx
      exact hi
    · rw [Obls.ownerOf_insert_ne h] at hx
      exact wf.owner x j hx

/-- Removing a childless node `k` (it is about to be discharged). -/
@[lantana_alias forest_wf_discharge]
theorem discharge (wf : ForestWf Ω tc Par) {k : Oid} (hk : kids Par (.obl k) = ∅) :
    ForestWf (insert Ω k .discharged) tc (delete Par k) := by
  rw [kids_eq_empty] at hk
  constructor
  · intro x
    by_cases h : k = x
    · subst h; simp [get?_delete_eq, Obls.not_live_insert_discharged]
    · rw [get?_delete_ne h, Obls.live_insert_ne h]; exact wf.par_live x
  · intro x j hx
    by_cases h : k = x
    · subst h; simp [get?_delete_eq] at hx
    · rw [get?_delete_ne h] at hx
      rw [Obls.ownerOf_insert_ne h]
      exact wf.thread x j hx
  · intro x c hx
    by_cases h : k = x
    · subst h; simp [get?_delete_eq] at hx
    · rw [get?_delete_ne h] at hx
      have hc : k ≠ c := fun e => by subst e; exact hk x hx
      rw [Obls.ownerOf_insert_ne hc, Obls.fuelOf_insert_ne hc, Obls.ownerOf_insert_ne h,
        Obls.fuelOf_insert_ne h]
      exact wf.obl x c hx
  · intro x j hx
    by_cases h : k = x
    · subst h; simp [Obls.ownerOf_insert_discharged] at hx
    · rw [Obls.ownerOf_insert_ne h] at hx
      exact wf.owner x j hx

theorem ownerOf_of_transGen (wf : ForestWf Ω tc Par) {k x : Oid}
    (hx : Relation.TransGen (ChildOf Par) x k) : Ω.ownerOf x = Ω.ownerOf k := by
  induction hx with
  | single h => exact (wf.obl _ _ h).1.symm
  | tail _ h ih => exact ih.trans (wf.obl _ _ h).1.symm

/-- The nodes of the subtree of a node `k` are nodes with the owner of `k`. -/
@[lantana_alias subtree_owner]
theorem subtree_owner (wf : ForestWf Ω tc Par) {k x : Oid} (hk : (get? Par k).isSome)
    (hx : x ∈ subtree Par k) : (get? Par x).isSome ∧ Ω.ownerOf x = Ω.ownerOf k := by
  rw [mem_subtree] at hx
  rcases hx with rfl | hx
  · exact ⟨hk, rfl⟩
  · exact ⟨transGen_childOf_isSome hx, wf.ownerOf_of_transGen hx⟩

/-! ### Physical steps -/

/-- The forest after a progress round of thread `i` (Rocq: the pure part of `oforest_step`),
provided the owners of the nodes do not change and every node `x` of `i` below an obligation
`c` keeps more fuel than the new fuel of `c`. -/
theorem prog (wf : ForestWf Ω tc Par) {i : ThreadId}
    (hp : Obls.condProgress (Obl.condOwner i) Ω Ω')
    (hown : ∀ x, (get? Par x).isSome → Ω'.ownerOf x = Ω.ownerOf x)
    (hpiece : ∀ x c, get? Par x = some (.obl c) → Ω.ownerOf x = some i →
      Ω'.fuelOf c < Ω'.fuelOf x) :
    ForestWf Ω' tc Par where
  par_live x := (wf.par_live x).trans (prog_live hp x)
  thread x j hx := (hown x (by simp [hx])).trans (wf.thread x j hx)
  obl x c hx := by
    have hxs : (get? Par x).isSome := by simp [hx]
    have hcs := wf.par_obl hx
    obtain ⟨hoc, hlt⟩ := wf.obl x c hx
    refine ⟨by rw [hown x hxs, hown c hcs, hoc], ?_⟩
    by_cases ho : Ω.ownerOf x = some i
    · exact hpiece x c hx ho
    · rw [prog_fuelOf_of_ne hp ho, prog_fuelOf_of_ne hp (hoc ▸ ho)]
      exact hlt
  owner x j hx := by
    have hxs : (get? Par x).isSome :=
      wf.isSome_of_live ((prog_live hp x).2 (Obls.live_of_ownerOf hx))
    exact wf.owner x j ((hown x hxs).symm.trans hx)

/-- `prog` in the form used by the forest invariant: the piece of a node `x` of `i` below `c`
is the old fuel of `c`, and it is at most the new fuel of `x`. -/
theorem prog_piece (wf : ForestWf Ω tc Par) {i : ThreadId}
    (hp : Obls.condProgress (Obl.condOwner i) Ω Ω')
    (hown : ∀ x, (get? Par x).isSome → Ω'.ownerOf x = Ω.ownerOf x)
    (hpiece : ∀ x c, get? Par x = some (.obl c) → Ω.ownerOf x = some i →
      Ω.fuelOf c ≤ Ω'.fuelOf x) :
    ForestWf Ω' tc Par :=
  wf.prog hp hown fun x c hx ho =>
    Ordinal.lt_of_lt_of_le (prog_fuelOf_lt hp ((wf.obl x c hx).1.trans ho)) (hpiece x c hx ho)

/-- The owned nodes do not change in a progress round that keeps the owners of the nodes. -/
theorem owned_prog {j : ThreadId}
    (hown : ∀ x, (get? Par x).isSome → Ω'.ownerOf x = Ω.ownerOf x) :
    owned Ω' Par j = owned Ω Par j :=
  owned_ext hown

/-! ### Moving a node -/

/-- Moving the node `k` below `p₂`, possibly changing the obligations to `Ω'` with the same live
set, provided the new parent relation satisfies the conditions of `ForestWf`. -/
@[lantana_alias forest_wf_reparent]
theorem reparent (wf : ForestWf Ω tc Par) {k : Oid} {p₂ : Parent} (hk : (get? Par k).isSome)
    (hlive : ∀ x, Ω.live x ↔ Ω'.live x)
    (hthread : ∀ x i, get? (insert Par k p₂) x = some (.thread i) → Ω'.ownerOf x = some i)
    (hobl : ∀ x c, get? (insert Par k p₂) x = some (.obl c) →
      Ω'.ownerOf c = Ω'.ownerOf x ∧ Ω'.fuelOf c < Ω'.fuelOf x)
    (hown : ∀ x i, Ω'.ownerOf x = some i → i < tc) :
    ForestWf Ω' tc (insert Par k p₂) where
  par_live x := by
    by_cases h : k = x
    · subst h; simp [get?_insert_eq, ← hlive, wf.live_of_isSome hk]
    · rw [get?_insert_ne h, wf.par_live, hlive]
  thread := hthread
  obl := hobl
  owner := hown

/-- Without owner change, `k` can move below any parent with its owner and less fuel. -/
@[lantana_alias forest_wf_move_same]
theorem move_same (wf : ForestWf Ω tc Par) {k : Oid} {p₂ : Parent} (hk : (get? Par k).isSome)
    (hp₂ : match p₂ with
      | .thread j => Ω.ownerOf k = some j
      | .obl q => Ω.ownerOf q = Ω.ownerOf k ∧ Ω.fuelOf q < Ω.fuelOf k) :
    ForestWf Ω tc (insert Par k p₂) := by
  refine wf.reparent hk (fun _ => Iff.rfl) (fun x i hx => ?_) (fun x c hx => ?_) wf.owner
  · by_cases h : k = x
    · subst h; rw [get?_insert_eq rfl] at hx; cases hx; exact hp₂
    · rw [get?_insert_ne h] at hx; exact wf.thread x i hx
  · by_cases h : k = x
    · subst h; rw [get?_insert_eq rfl] at hx; cases hx; exact hp₂
    · rw [get?_insert_ne h] at hx; exact wf.obl x c hx

/-- A child `x` of `k` moves up to the parent of `k` (the pure part of Rocq
`oforest_move_up`). -/
theorem move_up (wf : ForestWf Ω tc Par) {k x : Oid} {p : Parent}
    (hk : get? Par k = some p) (hx : get? Par x = some (.obl k)) :
    ForestWf Ω tc (insert Par x p) := by
  obtain ⟨hokx, hlt⟩ := wf.obl x k hx
  refine wf.move_same (by simp [hx]) ?_
  cases p with
  | thread j => exact hokx.symm.trans (wf.thread k j hk)
  | obl q =>
    obtain ⟨hoqk, hlt'⟩ := wf.obl k q hk
    exact ⟨hoqk.trans hokx, Ordinal.lt_trans hlt' hlt⟩

end ForestWf

/-! ## Changing the owner of a set of nodes -/

/-- `Ω'` is `Ω` where all obligations of `S`, owned by `t`, have the new owner `j` and less
fuel. -/
@[lantana_alias chown_rel]
def chownRel (S : Oids) (t j : ThreadId) (Ω Ω' : Obls) : Prop :=
  (∀ x, x ∉ S → get? Ω' x = get? Ω x) ∧
  ∀ x, x ∈ S → ∃ a a', get? Ω x = some (.assigned a t) ∧ get? Ω' x = some (.assigned a' j) ∧
    a' < a

namespace chownRel

variable {S : Oids} {t j : ThreadId} {Ω Ω' : Obls}

@[lantana_alias chown_rel_empty]
theorem empty (t j : ThreadId) (Ω : Obls) : chownRel ∅ t j Ω Ω :=
  ⟨fun _ _ => rfl, fun _ hx => (LawfulSet.mem_empty hx).elim⟩

@[lantana_alias chown_rel_insert]
theorem insert {x : Oid} {a a' : Fuel} (hx : x ∉ S) (h : chownRel S t j Ω Ω')
    (hxa : get? Ω' x = some (.assigned a t)) (hlt : a' < a) :
    chownRel ({x} ∪ S) t j Ω (Iris.Std.insert Ω' x (.assigned a' j)) := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [LawfulSet.mem_union, LawfulSet.mem_singleton, not_or] at hy
    rw [get?_insert_ne (Ne.symm hy.1)]
    exact h.1 y hy.2
  · rw [LawfulSet.mem_union, LawfulSet.mem_singleton] at hy
    rcases hy with rfl | hy
    · exact ⟨a, a', (h.1 y hx) ▸ hxa, get?_insert_eq rfl, hlt⟩
    · have hne : x ≠ y := fun e => hx (e ▸ hy)
      obtain ⟨b, b', hb, hb', hlt'⟩ := h.2 y hy
      exact ⟨b, b', hb, by rw [get?_insert_ne hne]; exact hb', hlt'⟩

@[lantana_alias chown_rel_ndf]
theorem ndf (h : chownRel S t j Ω Ω') : Ω.ndf Ω' := by
  intro x g hx
  by_cases hS : x ∈ S
  · obtain ⟨a, a', ha, ha', hlt⟩ := h.2 x hS
    rw [ha] at hx
    cases hx
    exact ⟨.assigned a' j, ha', .inr hlt⟩
  · exact ⟨g, (h.1 x hS).trans hx, .inl rfl⟩

@[lantana_alias chown_rel_live]
theorem live (h : chownRel S t j Ω Ω') (x : Oid) : Ω.live x ↔ Ω'.live x := by
  by_cases hS : x ∈ S
  · obtain ⟨a, a', ha, ha', _⟩ := h.2 x hS
    exact ⟨fun _ => ⟨a', j, ha'⟩, fun _ => ⟨a, t, ha⟩⟩
  · simp only [Obls.live, h.1 x hS]

theorem owner_of_mem (h : chownRel S t j Ω Ω') {x : Oid} (hx : x ∈ S) :
    Ω'.ownerOf x = some j := by
  obtain ⟨a, a', _, ha', _⟩ := h.2 x hx
  exact Obls.ownerOf_eq ha'

theorem owner_of_not_mem (h : chownRel S t j Ω Ω') {x : Oid} (hx : x ∉ S) :
    Ω'.ownerOf x = Ω.ownerOf x := by
  simp only [Obls.ownerOf, h.1 x hx]

@[lantana_alias chown_rel_owner]
theorem owner (h : chownRel S t j Ω Ω') (x : Oid) :
    Ω'.ownerOf x = if x ∈ S then some j else Ω.ownerOf x := by
  split
  · exact h.owner_of_mem ‹_›
  · exact h.owner_of_not_mem ‹_›

@[lantana_alias chown_rel_fuel_out]
theorem fuel_out (h : chownRel S t j Ω Ω') {x : Oid} (hx : x ∉ S) :
    Ω'.fuelOf x = Ω.fuelOf x := by
  simp only [Obls.fuelOf, h.1 x hx]

@[lantana_alias chown_rel_fuel_in]
theorem fuel_in (h : chownRel S t j Ω Ω') {x : Oid} (hx : x ∈ S) :
    Ω.ownerOf x = some t ∧ Ω'.fuelOf x < Ω.fuelOf x := by
  obtain ⟨a, a', ha, ha', hlt⟩ := h.2 x hx
  rw [Obls.ownerOf_eq ha, Obls.fuelOf_eq ha, Obls.fuelOf_eq ha']
  exact ⟨rfl, hlt⟩

end chownRel

namespace Forest

/-- The owned nodes after a change of owner of the nodes `S` from `t` to `j`. -/
@[lantana_alias forest_owned_chown]
theorem owned_chown {S : Oids} {t j : ThreadId} {Ω Ω' : Obls} {Par : OidMap Parent}
    (h : chownRel S t j Ω Ω') (hS : ∀ x, x ∈ S → (get? Par x).isSome) (i : ThreadId) :
    owned Ω' Par i =
      if i = j then S ∪ owned Ω Par i
      else if i = t then owned Ω Par i \ S
      else owned Ω Par i := by
  refine LawfulSet.ext fun x => ?_
  by_cases hx : x ∈ S
  · have ho := h.owner_of_mem hx
    have hot := (h.fuel_in hx).1
    rw [mem_owned, ho]
    split
    · rename_i hij
      subst hij
      simp [LawfulSet.mem_union, hx, hS x hx]
    · rename_i hij
      split
      · simp [LawfulSet.mem_diff, hx, Ne.symm hij]
      · rename_i hit
        simp [hot, Ne.symm hij, Ne.symm hit]
  · have ho := h.owner_of_not_mem hx
    rw [mem_owned, ho]
    split
    · simp [LawfulSet.mem_union, hx]
    · split
      · simp [LawfulSet.mem_diff, hx]
      · simp

end Forest

namespace ForestWf

variable {Ω Ω' : Obls} {tc : Nat} {Par : OidMap Parent}

open Forest

/-- With an owner change from `t` to `j`, the whole subtree of `k` moves to `j`; the subtree
nodes other than `k` keep more fuel than the old fuel of their parents. -/
@[lantana_alias forest_wf_move_cross]
theorem move_cross (wf : ForestWf Ω tc Par) {k : Oid} {p₂ : Parent} {t j : ThreadId}
    (hk : (get? Par k).isSome) (ht : Ω.ownerOf k = some t) (htj : t ≠ j)
    (hp₂ : match p₂ with
      | .thread j' => j' = j ∧ j < tc
      | .obl q => Ω.ownerOf q = some j)
    (hrel : chownRel (subtree Par k) t j Ω Ω')
    (hpk : ∀ q, p₂ = .obl q → Ω.fuelOf q < Ω'.fuelOf k)
    (hpx : ∀ x c, x ∈ subtree Par k → x ≠ k → get? Par x = some (.obl c) →
      Ω.fuelOf c ≤ Ω'.fuelOf x) :
    ForestWf Ω' tc (insert Par k p₂) := by
  have hSown : ∀ x, x ∈ subtree Par k → Ω.ownerOf x = some t := fun x hx =>
    (wf.subtree_owner hk hx).2.trans ht
  have hj : j < tc := by
    cases p₂ with
    | thread j' => exact hp₂.2
    | obl q => exact wf.owner q j hp₂
  have hq : ∀ q, p₂ = .obl q → q ∉ subtree Par k := by
    rintro q rfl hqS
    have := (hSown q hqS).symm.trans hp₂
    cases this
    exact htj rfl
  refine wf.reparent hk hrel.live (fun x i hx => ?_) (fun x c hx => ?_) (fun x i hx => ?_)
  · by_cases h : k = x
    · subst h
      rw [get?_insert_eq rfl] at hx
      cases hx
      rw [hrel.owner_of_mem (subtree_root Par k), hp₂.1]
    · rw [get?_insert_ne h] at hx
      have hxS : x ∉ subtree Par k := fun hxS => by
        rcases subtree_inv hxS with e | ⟨c, hc, _⟩
        · exact h e.symm
        · rw [hx] at hc; cases hc
      rw [hrel.owner_of_not_mem hxS]
      exact wf.thread x i hx
  · by_cases h : k = x
    · subst h
      rw [get?_insert_eq rfl] at hx
      cases hx
      have hcS := hq c rfl
      rw [hrel.owner_of_not_mem hcS, hrel.owner_of_mem (subtree_root Par k),
        hrel.fuel_out hcS]
      exact ⟨hp₂, hpk c rfl⟩
    · rw [get?_insert_ne h] at hx
      by_cases hxS : x ∈ subtree Par k
      · have hcS : c ∈ subtree Par k := by
          rcases subtree_inv hxS with e | ⟨c', hc', hc'S⟩
          · exact absurd e.symm h
          · rw [hx] at hc'; cases hc'; exact hc'S
        rw [hrel.owner_of_mem hcS, hrel.owner_of_mem hxS]
        exact ⟨rfl, Ordinal.lt_of_lt_of_le (hrel.fuel_in hcS).2
          (hpx x c hxS (fun e => h e.symm) hx)⟩
      · have hcS : c ∉ subtree Par k := fun hcS => hxS (subtree_closed hx hcS)
        rw [hrel.owner_of_not_mem hcS, hrel.owner_of_not_mem hxS, hrel.fuel_out hcS,
          hrel.fuel_out hxS]
        exact wf.obl x c hx
  · by_cases hxS : x ∈ subtree Par k
    · rw [hrel.owner_of_mem hxS] at hx
      cases hx
      exact hj
    · rw [hrel.owner_of_not_mem hxS] at hx
      exact wf.owner x i hx

end ForestWf

/-! ## Additions for the forest invariant (`Model.OForest`) -/

namespace ForestWf

variable {Ω : Obls} {tc : Nat} {Par : OidMap Parent}

open Forest

/-- The nodes owned by `i` are the obligations with owner `i` (Rocq `othread_obls_lookup` and
`othread_assigned_obls_lookup`, which relate the set of obligations of a thread to `Ω`). -/
@[lantana_alias othread_obls_lookup]
theorem mem_owned_iff (wf : ForestWf Ω tc Par) {i : ThreadId} {x : Oid} :
    x ∈ owned Ω Par i ↔ Ω.ownerOf x = some i := by
  rw [mem_owned]
  exact ⟨And.right, fun h => ⟨wf.isSome_of_ownerOf h, h⟩⟩

#lantana_ignore othread_assigned_obls_lookup "`ForestWf.mem_owned_iff`"

/-- An obligation that is a parent of a node is a node. -/
theorem kids_obl_isSome (wf : ForestWf Ω tc Par) {q : Oid} {x : Oid}
    (hx : x ∈ kids Par (.obl q)) : (get? Par q).isSome :=
  wf.par_obl (mem_kids.1 hx)

end ForestWf

namespace chownRel

variable {S : Oids} {t j : ThreadId} {Ω Ω' : Obls}

/-- An owner change keeps the domain. -/
theorem isSome_iff (h : chownRel S t j Ω Ω') (x : Oid) :
    (get? Ω' x).isSome ↔ (get? Ω x).isSome := by
  by_cases hS : x ∈ S
  · obtain ⟨a, a', ha, ha', _⟩ := h.2 x hS
    simp [ha, ha']
  · rw [h.1 x hS]

/-- An owner change to the same owner keeps the owners. -/
theorem ownerOf_self {i : ThreadId} (h : chownRel S i i Ω Ω') (x : Oid) :
    Ω'.ownerOf x = Ω.ownerOf x := by
  by_cases hS : x ∈ S
  · rw [h.owner_of_mem hS, (h.fuel_in hS).1]
  · exact h.owner_of_not_mem hS

/-- An owner change to the same owner `i` of all the obligations of `i` is a progress round of
`i`. -/
theorem condProgress {i : ThreadId} (h : chownRel S i i Ω Ω')
    (hS : ∀ x, Ω.ownerOf x = some i → x ∈ S) :
    Obls.condProgress (Obl.condOwner i) Ω Ω' := by
  have hrel : ∀ x, (get? Ω x = none ∧ get? Ω' x = none) ∨ ∃ g g', get? Ω x = some g ∧
      get? Ω' x = some g' ∧
        ((Obl.condOwner i x g ∧ Obl.step g g') ∨ (¬Obl.condOwner i x g ∧ g = g')) ∧
        Obl.keep g g' := by
    intro x
    by_cases hxS : x ∈ S
    · obtain ⟨a, a', ha, ha', hlt⟩ := h.2 x hxS
      exact .inr ⟨_, _, ha, ha', .inl ⟨rfl, .inl hlt⟩, trivial⟩
    · rw [h.1 x hxS]
      cases e : get? Ω x with
      | none => exact .inl ⟨rfl, rfl⟩
      | some g =>
        refine .inr ⟨g, g, rfl, rfl, .inr ⟨fun hc => hxS (hS x ?_), rfl⟩, Obl.keep_refl g⟩
        cases g with
        | assigned a t => cases hc; exact Obls.ownerOf_eq e
        | discharged => exact hc.elim
  refine ⟨mapForall2_intro fun x => ?_, mapForall2_intro fun x => ?_⟩
  · rcases hrel x with h₀ | ⟨g, g', e, e', hr, _⟩
    · exact .inl h₀
    · exact .inr ⟨g, g', e, e', hr⟩
  · rcases hrel x with h₀ | ⟨g, g', e, e', _, hk⟩
    · exact .inl h₀
    · exact .inr ⟨g, g', e, e', hk⟩

end chownRel

/-- A progress round of `i` does not increase any fuel. -/
theorem prog_fuelOf_le {Ω Ω' : Obls} {i : ThreadId}
    (hp : Obls.condProgress (Obl.condOwner i) Ω Ω') (x : Oid) : Ω'.fuelOf x ≤ Ω.fuelOf x := by
  by_cases ho : Ω.ownerOf x = some i
  · exact Ordinal.le_of_lt (prog_fuelOf_lt hp ho)
  · exact Ordinal.le_of_eq (prog_fuelOf_of_ne hp ho)

end Lantana.Model
