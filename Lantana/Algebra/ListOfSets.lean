/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Std.GenSets
public import Lantana.Init

/-! # Lists of finite sets

Rocq `lantana/algebra/list_of_sets.v`: the union `unionList L` of a list of sets and their
pairwise disjointness `disjointList L`, under list operations. The sets are those of Iris-Lean's
`LawfulSet` interface (used with `Oids` by the queue of `Lantana.Examples.Queue`).

`disjointList` is `List.Pairwise (· ## ·)`; Rocq's definition by lookups is the lemma
`disjointList_iff_lookup`. The lemmas about `delete j L` and `<[j := s]> L` (lists updated at
an index) are not ported: the examples only add at the end and remove at the front.
-/

@[expose] public section

namespace Lantana

open Iris.Std

variable {S A : Type _} [LawfulSet S A]

/-- The union of a list of sets (Rocq `union_list_of_sets`). -/
@[lantana_alias union_list_of_sets]
def unionList (L : List S) : S := L.foldr (· ∪ ·) ∅

/-- The sets of a list are pairwise disjoint (Rocq `disjoint_list_of_sets`, stated with
lookups there: `disjointList_iff_lookup`). -/
@[lantana_alias disjoint_list_of_sets]
def disjointList (L : List S) : Prop := L.Pairwise (· ## ·)

/-! ## The union -/

@[lantana_alias union_list_of_sets_nil]
theorem unionList_nil : unionList ([] : List S) = ∅ := rfl

@[lantana_alias union_list_of_sets_cons]
theorem unionList_cons (s : S) (L : List S) : unionList (s :: L) = s ∪ unionList L := rfl

@[lantana_alias union_list_of_sets_singleton]
theorem unionList_singleton (s : S) : unionList [s] = s := by
  rw [unionList_cons, unionList_nil, LawfulSet.union_empty_right]

@[lantana_alias union_list_of_sets_app]
theorem unionList_append (L₁ L₂ : List S) :
    unionList (L₁ ++ L₂) = unionList L₁ ∪ unionList L₂ := by
  induction L₁ with
  | nil => rw [List.nil_append, unionList_nil, LawfulSet.union_empty_left]
  | cons s L₁ ih => rw [List.cons_append, unionList_cons, unionList_cons, ih,
      LawfulSet.union_assoc]

/-- Membership in the union, through a set of the list (Rocq
`elem_of_union_list_of_sets_elem_of`). -/
@[lantana_alias elem_of_union_list_of_sets_elem_of]
theorem mem_unionList {L : List S} {e : A} : e ∈ unionList L ↔ ∃ s ∈ L, e ∈ s := by
  induction L with
  | nil => simp [unionList_nil, LawfulSet.mem_empty]
  | cons x L ih =>
    rw [unionList_cons, LawfulSet.mem_union, ih]
    constructor
    · rintro (h | ⟨s, hs, he⟩)
      · exact ⟨x, List.mem_cons_self, h⟩
      · exact ⟨s, List.mem_cons_of_mem x hs, he⟩
    · rintro ⟨s, hs, he⟩
      rcases List.mem_cons.mp hs with rfl | hs
      · exact .inl he
      · exact .inr ⟨s, hs, he⟩

/-- Membership in the union, through a lookup (Rocq `elem_of_union_list_of_sets`). -/
@[lantana_alias elem_of_union_list_of_sets]
theorem mem_unionList_lookup {L : List S} {e : A} :
    e ∈ unionList L ↔ ∃ (j : Nat) (s : S), L[j]? = some s ∧ e ∈ s := by
  rw [mem_unionList]
  constructor
  · rintro ⟨s, hs, he⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    exact ⟨j, _, List.getElem?_eq_getElem hj, he⟩
  · rintro ⟨j, s, hj, he⟩
    exact ⟨s, List.mem_of_getElem? hj, he⟩

@[lantana_alias not_elem_of_union_list_of_sets]
theorem not_mem_unionList_lookup {L : List S} {e : A} :
    e ∉ unionList L ↔ ∀ (j : Nat) (s : S), L[j]? = some s → e ∉ s := by
  rw [mem_unionList_lookup]
  grind

@[lantana_alias union_list_of_sets_lookup_subseteq]
theorem subset_unionList_of_lookup {L : List S} {j : Nat} {s : S} (h : L[j]? = some s) :
    s ⊆ unionList L :=
  fun _ he => mem_unionList.mpr ⟨s, List.mem_of_getElem? h, he⟩

@[lantana_alias union_list_of_sets_mono]
theorem unionList_mono {L₁ L₂ : List S} (h : ∀ s, s ∈ L₁ → s ∈ L₂) :
    unionList L₁ ⊆ unionList L₂ := fun _ he => by
  obtain ⟨s, hs, he⟩ := mem_unionList.mp he
  exact mem_unionList.mpr ⟨s, h s hs, he⟩

@[lantana_alias union_list_of_sets_sublist]
theorem unionList_sublist {L₁ L₂ : List S} (h : L₁.Sublist L₂) : unionList L₁ ⊆ unionList L₂ :=
  unionList_mono fun _ hs => h.subset hs

/-! ## Disjointness -/

/-- Rocq's definition of `disjoint_list_of_sets`, by lookups. -/
theorem disjointList_iff_lookup {L : List S} :
    disjointList L ↔ ∀ (j₁ j₂ : Nat) (s₁ s₂ : S), j₁ ≠ j₂ → L[j₁]? = some s₁ →
      L[j₂]? = some s₂ → s₁ ## s₂ := by
  unfold disjointList
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h j₁ j₂ s₁ s₂ hne h₁ h₂
    obtain ⟨hj₁, rfl⟩ := List.getElem?_eq_some_iff.mp h₁
    obtain ⟨hj₂, rfl⟩ := List.getElem?_eq_some_iff.mp h₂
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact h j₁ j₂ hj₁ hj₂ hlt
    · exact LawfulSet.disjoint_symm (h j₂ j₁ hj₂ hj₁ hlt)
  · intro h j₁ j₂ hj₁ hj₂ hlt
    exact h j₁ j₂ _ _ (Nat.ne_of_lt hlt) (List.getElem?_eq_getElem hj₁)
      (List.getElem?_eq_getElem hj₂)

@[lantana_alias disjoint_list_of_sets_lookup]
theorem disjointList_lookup {L : List S} {j₁ j₂ : Nat} {s₁ s₂ : S} (h : disjointList L)
    (hne : j₁ ≠ j₂) (h₁ : L[j₁]? = some s₁) (h₂ : L[j₂]? = some s₂) : s₁ ## s₂ :=
  disjointList_iff_lookup.mp h j₁ j₂ s₁ s₂ hne h₁ h₂

@[lantana_alias disjoint_list_of_sets_nil]
theorem disjointList_nil : disjointList ([] : List S) := List.Pairwise.nil

@[lantana_alias disjoint_list_of_sets_singleton]
theorem disjointList_singleton (s : S) : disjointList [s] := List.pairwise_singleton _ s

/-- Disjoint from every set of a list is disjoint from the union (Rocq
`Forall_disjoint_union_list_of_sets`). -/
@[lantana_alias Forall_disjoint_union_list_of_sets]
theorem forall_disjoint_unionList {L : List S} {s : S} :
    (∀ s' ∈ L, s ## s') ↔ s ## unionList L := by
  constructor
  · intro h e ⟨he₁, he₂⟩
    obtain ⟨s', hs', he'⟩ := mem_unionList.mp he₂
    exact h s' hs' e ⟨he₁, he'⟩
  · intro h s' hs' e ⟨he₁, he₂⟩
    exact h e ⟨he₁, mem_unionList.mpr ⟨s', hs', he₂⟩⟩

@[lantana_alias disjoint_list_of_sets_cons_iff]
theorem disjointList_cons_iff {s : S} {L : List S} :
    disjointList (s :: L) ↔ (∀ s' ∈ L, s ## s') ∧ disjointList L :=
  List.pairwise_cons

@[lantana_alias disjoint_list_of_sets_cons_union_list_of_sets]
theorem disjointList_cons {s : S} {L : List S} :
    disjointList (s :: L) ↔ s ## unionList L ∧ disjointList L := by
  rw [disjointList_cons_iff, forall_disjoint_unionList]

@[lantana_alias disjoint_list_of_sets_cons_2]
theorem disjointList_cons_2 {s : S} {L : List S} (h₁ : s ## unionList L) (h₂ : disjointList L) :
    disjointList (s :: L) :=
  disjointList_cons.mpr ⟨h₁, h₂⟩

@[lantana_alias disjoint_list_of_sets_cons_inv]
theorem disjointList_cons_inv {s : S} {L : List S} (h : disjointList (s :: L)) :
    s ## unionList L ∧ disjointList L :=
  disjointList_cons.mp h

@[lantana_alias disjoint_list_of_sets_app_iff]
theorem disjointList_append_iff {L₁ L₂ : List S} :
    disjointList (L₁ ++ L₂) ↔
      disjointList L₁ ∧ disjointList L₂ ∧ ∀ s ∈ L₁, s ## unionList L₂ := by
  unfold disjointList
  rw [List.pairwise_append]
  simp only [← forall_disjoint_unionList]

@[lantana_alias disjoint_list_of_sets_app_inv]
theorem disjointList_append_inv {L₁ L₂ : List S} (h : disjointList (L₁ ++ L₂)) :
    disjointList L₁ ∧ disjointList L₂ ∧ ∀ s ∈ L₁, s ## unionList L₂ :=
  disjointList_append_iff.mp h

@[lantana_alias disjoint_list_of_sets_app]
theorem disjointList_append {L₁ L₂ : List S} (h₁ : disjointList L₁) (h₂ : disjointList L₂)
    (h : ∀ s ∈ L₁, s ## unionList L₂) : disjointList (L₁ ++ L₂) :=
  disjointList_append_iff.mpr ⟨h₁, h₂, h⟩

@[lantana_alias disjoint_list_of_sets_app_disjoint_iff]
theorem disjointList_append_disjoint_iff {L₁ L₂ : List S} :
    disjointList (L₁ ++ L₂) ↔
      disjointList L₁ ∧ disjointList L₂ ∧ unionList L₁ ## unionList L₂ := by
  rw [disjointList_append_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h e ⟨he₁, he₂⟩
    obtain ⟨s, hs, he⟩ := mem_unionList.mp he₁
    exact h s hs e ⟨he, he₂⟩
  · intro h s hs e ⟨he₁, he₂⟩
    exact h e ⟨mem_unionList.mpr ⟨s, hs, he₁⟩, he₂⟩

#lantana_ignore union_list_of_sets_delete_L "Lists updated at an index are not used."
#lantana_ignore union_list_of_sets_eq_union_list "Rocq's `⋃ L`; `unionList` is the definition."
#lantana_ignore disjoint_list_of_sets_delete "Lists updated at an index are not used."
#lantana_ignore disjoint_list_of_sets_lookup_disjoint_union_list_of_sets_delete
  "Lists updated at an index are not used."
#lantana_ignore disjoint_list_of_sets_lookup_iff "Lists updated at an index are not used."
#lantana_ignore union_list_of_sets_insert_replace "Lists updated at an index are not used."
#lantana_ignore union_list_of_sets_insert_union_L "Lists updated at an index are not used."
#lantana_ignore union_list_of_sets_insert_difference_subseteq
  "Lists updated at an index are not used."
#lantana_ignore union_list_of_sets_insert_difference_L "Lists updated at an index are not used."
#lantana_ignore union_list_of_sets_insert_difference_subseteq_L
  "Lists updated at an index are not used."
#lantana_ignore union_list_of_sets_insert_difference_singleton_L
  "Lists updated at an index are not used."
#lantana_ignore disjoint_list_of_sets_insert_subseteq "Lists updated at an index are not used."
#lantana_ignore disjoint_list_of_sets_insert_difference "Lists updated at an index are not used."
#lantana_ignore disjoint_list_of_sets_insert_union_iff "Lists updated at an index are not used."
#lantana_ignore disjoint_list_of_sets_insert_union "Lists updated at an index are not used."
#lantana_ignore disjoint_list_of_sets_insert_union_inv "Lists updated at an index are not used."
#lantana_ignore disjoint_list_of_sets_insert_union_singleton
  "Lists updated at an index are not used."
#lantana_ignore disjoint_list_of_sets_insert_union_singleton_not_in
  "Lists updated at an index are not used."

end Lantana
