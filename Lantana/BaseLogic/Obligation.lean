/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Prelude.Ids
public import Lantana.Prelude.Ordinal

/-! # Obligations

An obligation is assigned (with fuel and an owner thread) or discharged (Rocq
`lantana/base_logic/obligation.v`). This file defines the steps of one obligation and the
relations on obligation maps `Obls` used by the model: allocation, conditional steps and progress,
and the order `Obls.le` seen by adequacy.

Design (D10): ids are `Nat` (`Oid`), fuel is fixed to `Fuel` (no `obl_class`), owners are
positional thread ids (`ThreadId`), and the unused boolean state flag of Rocq is dropped. The
pointwise relations on maps (`mapForall2`, `condRel`) are generic in the value type and shared
with witnesses (`Witness.lean`), where Rocq duplicates them.

Everything lives in the namespace `Lantana.Model`: the names `Lantana.Obl.assigned`,
`Lantana.Obl.discharged`, … are taken by the predicates of the obligation-forest interface
(`Lantana.Prelude.Ids`).

Maps are `OidMap V = Std.ExtTreeMap Oid V compare`, read through Iris-Lean's `PartialMap`
interface (`get?`, `insert`, `delete`), whose lemmas (`get?_insert_eq/ne`, `get?_delete_eq/ne`,
…) are used throughout. The domain of a map is described pointwise by `(get? m k).isSome`.
-/

@[expose] public section

namespace Lantana.Model

open Iris.Std LawfulPartialMap
open Ordinals

/-! ## Pointwise relations on finite maps -/

section MapRel

universe u

variable {A B V : Type _}

/-- Inversion of `Option.Rel`. -/
theorem option_rel_inv {α β : Type _} {r : α → β → Prop} {o₁ : Option α} {o₂ : Option β}
    (h : Option.Rel r o₁ o₂) :
    (o₁ = none ∧ o₂ = none) ∨ ∃ a b, o₁ = some a ∧ o₂ = some b ∧ r a b := by
  cases h with
  | none => exact .inl ⟨rfl, rfl⟩
  | some hab => exact .inr ⟨_, _, rfl, rfl, hab⟩

/-- `mapForall2 P m₁ m₂`: `m₁` and `m₂` have the same domain and `P k` relates their values at
every key `k` (stdpp `map_Forall2`). -/
def mapForall2 (P : Oid → A → B → Prop) (m₁ : OidMap A) (m₂ : OidMap B) : Prop :=
  ∀ k, Option.Rel (P k) (get? m₁ k) (get? m₂ k)

theorem mapForall2.inv {P : Oid → A → B → Prop} {m₁ : OidMap A} {m₂ : OidMap B}
    (h : mapForall2 P m₁ m₂) (k : Oid) :
    (get? m₁ k = none ∧ get? m₂ k = none) ∨
      ∃ a b, get? m₁ k = some a ∧ get? m₂ k = some b ∧ P k a b :=
  option_rel_inv (h k)

theorem mapForall2_intro {P : Oid → A → B → Prop} {m₁ : OidMap A} {m₂ : OidMap B}
    (h : ∀ k, (get? m₁ k = none ∧ get? m₂ k = none) ∨
      ∃ a b, get? m₁ k = some a ∧ get? m₂ k = some b ∧ P k a b) : mapForall2 P m₁ m₂ := by
  intro k
  rcases h k with ⟨e₁, e₂⟩ | ⟨a, b, e₁, e₂, hab⟩
  · rw [e₁, e₂]; exact .none
  · rw [e₁, e₂]; exact .some hab

theorem mapForall2.isSome_iff {P : Oid → A → B → Prop} {m₁ : OidMap A} {m₂ : OidMap B}
    (h : mapForall2 P m₁ m₂) (k : Oid) : (get? m₁ k).isSome ↔ (get? m₂ k).isSome := by
  rcases h.inv k with ⟨e₁, e₂⟩ | ⟨a, b, e₁, e₂, _⟩ <;> simp [e₁, e₂]

theorem mapForall2.lookup_left {P : Oid → A → B → Prop} {m₁ : OidMap A} {m₂ : OidMap B}
    (h : mapForall2 P m₁ m₂) {k : Oid} {a : A} (ha : get? m₁ k = some a) :
    ∃ b, get? m₂ k = some b ∧ P k a b := by
  rcases h.inv k with ⟨e₁, _⟩ | ⟨a', b, e₁, e₂, hab⟩
  · rw [ha] at e₁; cases e₁
  · rw [ha] at e₁; cases e₁; exact ⟨b, e₂, hab⟩

theorem mapForall2.lookup_right {P : Oid → A → B → Prop} {m₁ : OidMap A} {m₂ : OidMap B}
    (h : mapForall2 P m₁ m₂) {k : Oid} {b : B} (hb : get? m₂ k = some b) :
    ∃ a, get? m₁ k = some a ∧ P k a b := by
  rcases h.inv k with ⟨_, e₂⟩ | ⟨a, b', e₁, e₂, hab⟩
  · rw [hb] at e₂; cases e₂
  · rw [hb] at e₂; cases e₂; exact ⟨a, e₁, hab⟩

theorem mapForall2.lookup {P : Oid → A → B → Prop} {m₁ : OidMap A} {m₂ : OidMap B}
    (h : mapForall2 P m₁ m₂) {k : Oid} {a : A} {b : B} (ha : get? m₁ k = some a)
    (hb : get? m₂ k = some b) : P k a b := by
  obtain ⟨b', e₂, hab⟩ := h.lookup_left ha
  rw [hb] at e₂; cases e₂; exact hab

theorem mapForall2.none_left {P : Oid → A → B → Prop} {m₁ : OidMap A} {m₂ : OidMap B}
    (h : mapForall2 P m₁ m₂) {k : Oid} (hk : get? m₁ k = none) : get? m₂ k = none := by
  rcases h.inv k with ⟨_, e₂⟩ | ⟨a, b, e₁, _, _⟩
  · exact e₂
  · rw [hk] at e₁; cases e₁

theorem mapForall2.none_right {P : Oid → A → B → Prop} {m₁ : OidMap A} {m₂ : OidMap B}
    (h : mapForall2 P m₁ m₂) {k : Oid} (hk : get? m₂ k = none) : get? m₁ k = none := by
  rcases h.inv k with ⟨e₁, _⟩ | ⟨a, b, _, e₂, _⟩
  · exact e₁
  · rw [hk] at e₂; cases e₂

theorem mapForall2.impl {P Q : Oid → A → B → Prop} {m₁ : OidMap A} {m₂ : OidMap B}
    (h : mapForall2 P m₁ m₂) (hPQ : ∀ k a b, P k a b → Q k a b) : mapForall2 Q m₁ m₂ :=
  mapForall2_intro fun k => (h.inv k).imp id fun ⟨a, b, e₁, e₂, hab⟩ =>
    ⟨a, b, e₁, e₂, hPQ k a b hab⟩

theorem mapForall2_refl {P : Oid → V → V → Prop} (hP : ∀ k a, P k a a) (m : OidMap V) :
    mapForall2 P m m := by
  refine mapForall2_intro fun k => ?_
  cases e : get? m k with
  | none => exact .inl ⟨rfl, rfl⟩
  | some a => exact .inr ⟨a, a, rfl, rfl, hP k a⟩

theorem mapForall2.symm {P : Oid → V → V → Prop} (hP : ∀ k a b, P k a b → P k b a)
    {m₁ m₂ : OidMap V} (h : mapForall2 P m₁ m₂) : mapForall2 P m₂ m₁ :=
  mapForall2_intro fun k => (h.inv k).imp (fun ⟨e₁, e₂⟩ => ⟨e₂, e₁⟩)
    fun ⟨a, b, e₁, e₂, hab⟩ => ⟨b, a, e₂, e₁, hP k a b hab⟩

theorem mapForall2.trans {P : Oid → V → V → Prop} (hP : ∀ k a b c, P k a b → P k b c → P k a c)
    {m₁ m₂ m₃ : OidMap V} (h₁₂ : mapForall2 P m₁ m₂) (h₂₃ : mapForall2 P m₂ m₃) :
    mapForall2 P m₁ m₃ := by
  refine mapForall2_intro fun k => ?_
  rcases h₁₂.inv k with ⟨e₁, e₂⟩ | ⟨a, b, e₁, e₂, hab⟩
  · exact .inl ⟨e₁, h₂₃.none_left e₂⟩
  · obtain ⟨c, e₃, hbc⟩ := h₂₃.lookup_left e₂
    exact .inr ⟨a, c, e₁, e₃, hP k a b c hab hbc⟩

theorem mapForall2_empty {P : Oid → A → B → Prop} :
    mapForall2 P (∅ : OidMap A) (∅ : OidMap B) :=
  mapForall2_intro fun _ => .inl ⟨get?_empty _, get?_empty _⟩

/-- A relation that holds for every value of `m₁` can be realised by a map
(Rocq `map_Forall2_choice`, classical). -/
@[lantana_alias map_Forall2_choice]
theorem mapForall2_choice {A B : Type u} {P : Oid → A → B → Prop} (m₁ : OidMap A)
    (hP : ∀ k a, get? m₁ k = some a → ∃ b, P k a b) : ∃ m₂ : OidMap B, mapForall2 P m₁ m₂ := by
  classical
  let f : Oid → A → Option B := fun k a =>
    if h : ∃ b, P k a b then some (Classical.choose h) else none
  refine ⟨bindAlter f m₁, mapForall2_intro fun k => ?_⟩
  rw [get?_bindAlter]
  cases e : get? m₁ k with
  | none => exact .inl ⟨rfl, rfl⟩
  | some a =>
    have h := hP k a e
    refine .inr ⟨a, Classical.choose h, rfl, ?_, Classical.choose_spec h⟩
    simp [f, h]

/-! ### Conditional relations -/

/-- `condRel C R m₁ m₂`: the values satisfying `C` take an `R` step, the others stay (Rocq
`obls_cond_rel`, `wits_cond_rel`). -/
def condRel (C : Oid → V → Prop) (R : V → V → Prop) : OidMap V → OidMap V → Prop :=
  mapForall2 fun k v₁ v₂ => (C k v₁ ∧ R v₁ v₂) ∨ (¬C k v₁ ∧ v₁ = v₂)

/-- `R` preserves the condition `C` (Rocq `gl_rel_preserves_cond`, `wit_rel_preserves_cond`). -/
@[lantana_alias gl_rel_preserves_cond, lantana_alias wit_rel_preserves_cond]
def relPreservesCond (C : Oid → V → Prop) (R : V → V → Prop) : Prop :=
  ∀ k v₁ v₂, C k v₁ → R v₁ v₂ → C k v₂

@[lantana_alias obls_cond_rel_dom, lantana_alias wits_cond_rel_dom]
theorem condRel_dom {C : Oid → V → Prop} {R : V → V → Prop} {m₁ m₂ : OidMap V}
    (h : condRel C R m₁ m₂) (k : Oid) : (get? m₁ k).isSome ↔ (get? m₂ k).isSome :=
  mapForall2.isSome_iff h k

@[lantana_alias obls_cond_rel_tc_dom, lantana_alias wits_cond_rel_tc_dom]
theorem condRel_transGen_dom {C : Oid → V → Prop} {R : V → V → Prop} {m₁ m₂ : OidMap V}
    (h : Relation.TransGen (condRel C R) m₁ m₂) (k : Oid) :
    (get? m₁ k).isSome ↔ (get? m₂ k).isSome := by
  induction h with
  | single h => exact condRel_dom h k
  | tail _ h ih => exact ih.trans (condRel_dom h k)

#lantana_ignore obls_cond_rel_rtc_dom
  "the reflexive case is trivial; see `condRel_transGen_dom`"
#lantana_ignore wits_cond_rel_rtc_dom
  "the reflexive case is trivial; see `condRel_transGen_dom`"

/-- If `C₁` and `C₂` are disjoint and `R` preserves `C₁`, the two steps compose to a step for
`C = C₁ ∨ C₂`. -/
@[lantana_alias obls_cond_rel_split_cond, lantana_alias wits_cond_rel_split_cond]
theorem condRel_split_cond {C C₁ C₂ : Oid → V → Prop} {R : V → V → Prop}
    {m₁ m₂ m₃ : OidMap V} (hC : ∀ k v, C k v ↔ C₁ k v ∨ C₂ k v)
    (hdisj : ∀ k v, ¬C₁ k v ∨ ¬C₂ k v) (hpres : relPreservesCond C₁ R)
    (h₁₂ : condRel C₁ R m₁ m₂) (h₂₃ : condRel C₂ R m₂ m₃) : condRel C R m₁ m₃ := by
  refine mapForall2_intro fun k => ?_
  rcases mapForall2.inv h₁₂ k with ⟨e₁, e₂⟩ | ⟨a, b, e₁, e₂, hab⟩
  · exact .inl ⟨e₁, mapForall2.none_left h₂₃ e₂⟩
  obtain ⟨c, e₃, hbc⟩ := mapForall2.lookup_left h₂₃ e₂
  refine .inr ⟨a, c, e₁, e₃, ?_⟩
  rcases hab with ⟨hC₁, hR₁⟩ | ⟨hC₁, rfl⟩ <;> rcases hbc with ⟨hC₂, hR₂⟩ | ⟨hC₂, rfl⟩
  · exact ((hdisj k b).resolve_left (fun h => h (hpres _ _ _ hC₁ hR₁)) hC₂).elim
  · exact .inl ⟨(hC k a).2 (.inl hC₁), hR₁⟩
  · exact .inl ⟨(hC k a).2 (.inr hC₂), hR₂⟩
  · exact .inr ⟨fun h => ((hC k a).1 h).elim hC₁ hC₂, rfl⟩

@[lantana_alias obls_cond_rel_iff_lookup, lantana_alias wits_cond_rel_iff_lookup]
theorem condRel_iff_lookup {C₁ C₂ : Oid → V → Prop} {R : V → V → Prop} {m₁ m₂ : OidMap V}
    (h : condRel C₁ R m₁ m₂) (hC : ∀ k v, get? m₁ k = some v → (C₁ k v ↔ C₂ k v)) :
    condRel C₂ R m₁ m₂ := by
  refine mapForall2_intro fun k => ?_
  rcases mapForall2.inv h k with ⟨e₁, e₂⟩ | ⟨a, b, e₁, e₂, hab⟩
  · exact .inl ⟨e₁, e₂⟩
  refine .inr ⟨a, b, e₁, e₂, ?_⟩
  have hCk := hC k a e₁
  rcases hab with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact .inl ⟨hCk.1 h₁, h₂⟩
  · exact .inr ⟨fun h => h₁ (hCk.2 h), h₂⟩

@[lantana_alias obls_cond_rel_iff, lantana_alias wits_cond_rel_iff]
theorem condRel_iff {C₁ C₂ : Oid → V → Prop} {R : V → V → Prop} {m₁ m₂ : OidMap V}
    (h : condRel C₁ R m₁ m₂) (hC : ∀ k v, C₁ k v ↔ C₂ k v) : condRel C₂ R m₁ m₂ :=
  condRel_iff_lookup h fun k v _ => hC k v

end MapRel

/-! ## Obligations -/

/-- An obligation: assigned with its fuel and owner thread, or discharged. -/
@[lantana_alias obl]
inductive Obl where
  | assigned (fuel : Fuel) (owner : ThreadId)
  | discharged

attribute [lantana_alias obl_assigned] Obl.assigned
attribute [lantana_alias obl_discharged] Obl.discharged

#lantana_ignore obl_class "D6/D10: fuel is fixed to `Fuel`"
#lantana_ignore obl_owner "D14: owners are thread ids, `ThreadId`"
#lantana_ignore obl_cond "the type `Oid → Obl → Prop` is written out"

namespace Obl

/-- Progress: the fuel decreases strictly; the owner may change. -/
@[lantana_alias obl_progress]
def progress : Obl → Obl → Prop
  | assigned f₁ _, assigned f₂ _ => f₂ < f₁
  | _, _ => False

/-- Discharge: an assigned obligation becomes discharged. -/
@[lantana_alias obl_discharge]
def discharge : Obl → Obl → Prop
  | assigned _ _, discharged => True
  | _, _ => False

/-- A step of an obligation: progress or discharge. -/
@[lantana_alias obl_step]
def step (g₁ g₂ : Obl) : Prop :=
  progress g₁ g₂ ∨ discharge g₁ g₂

/-- Same status (both assigned or both discharged). -/
@[lantana_alias obl_keep]
def keep : Obl → Obl → Prop
  | assigned _ _, assigned _ _ => True
  | discharged, discharged => True
  | _, _ => False

/-- The order on obligations seen by adequacy: the fuel does not increase, and it decreases
strictly if the owner changes; discharge is a step down. -/
@[lantana_alias obl_le]
def le : Obl → Obl → Prop
  | assigned f₁ o₁, assigned f₂ o₂ => (f₂ ≤ f₁ ∧ o₁ = o₂) ∨ f₂ < f₁
  | assigned _ _, discharged => True
  | discharged, discharged => True
  | discharged, assigned _ _ => False

/-- The obligations owned by thread `i`. -/
@[lantana_alias obl_cond_owner]
def condOwner (i : ThreadId) : Oid → Obl → Prop
  | _, assigned _ j => j = i
  | _, discharged => False

@[lantana_alias obl_cond_owner_dec]
instance condOwner_decidable (i : ThreadId) (k : Oid) : (g : Obl) → Decidable (condOwner i k g)
  | assigned _ j => inferInstanceAs (Decidable (j = i))
  | discharged => inferInstanceAs (Decidable False)

@[simp] theorem progress_assigned {f₁ f₂ : Fuel} {o₁ o₂ : ThreadId} :
    progress (assigned f₁ o₁) (assigned f₂ o₂) ↔ f₂ < f₁ := Iff.rfl

@[simp] theorem not_progress_discharged_left (g : Obl) : ¬progress discharged g := by
  cases g <;> simp [progress]

@[simp] theorem not_progress_discharged_right (g : Obl) : ¬progress g discharged := by
  cases g <;> simp [progress]

@[simp] theorem discharge_iff {g₁ g₂ : Obl} :
    discharge g₁ g₂ ↔ (∃ f o, g₁ = assigned f o) ∧ g₂ = discharged := by
  cases g₁ <;> cases g₂ <;> simp [discharge]

@[simp] theorem condOwner_assigned {i : ThreadId} {k : Oid} {f : Fuel} {j : ThreadId} :
    condOwner i k (assigned f j) ↔ j = i := Iff.rfl

@[simp] theorem not_condOwner_discharged {i : ThreadId} {k : Oid} :
    ¬condOwner i k discharged := id

@[lantana_alias obl_keep_reflexive]
theorem keep_refl (g : Obl) : keep g g := by
  cases g <;> trivial

@[lantana_alias obl_keep_transitive]
theorem keep_trans {g₁ g₂ g₃ : Obl} (h₁₂ : keep g₁ g₂) (h₂₃ : keep g₂ g₃) : keep g₁ g₃ := by
  cases g₁ <;> cases g₂ <;> cases g₃ <;> simp_all [keep]

@[lantana_alias obl_keep_symmetric]
theorem keep_symm {g₁ g₂ : Obl} (h : keep g₁ g₂) : keep g₂ g₁ := by
  cases g₁ <;> cases g₂ <;> simp_all [keep]

#lantana_ignore obl_keep_equivalence "`keep_refl`, `keep_symm`, `keep_trans`"

@[lantana_alias obl_le_reflexive]
theorem le_refl (g : Obl) : le g g := by
  cases g
  · exact .inl ⟨Ordinal.le_rfl, rfl⟩
  · trivial

@[lantana_alias obl_le_transitive]
theorem le_trans {g₁ g₂ g₃ : Obl} (h₁₂ : le g₁ g₂) (h₂₃ : le g₂ g₃) : le g₁ g₃ := by
  cases g₁ with
  | discharged => cases g₂ <;> cases g₃ <;> simp_all [le]
  | assigned f₁ o₁ =>
    cases g₂ with
    | discharged => cases g₃ <;> simp_all [le]
    | assigned f₂ o₂ =>
      cases g₃ with
      | discharged => trivial
      | assigned f₃ o₃ =>
        simp only [le] at h₁₂ h₂₃ ⊢
        rcases h₁₂ with ⟨h₁, rfl⟩ | h₁ <;> rcases h₂₃ with ⟨h₂, rfl⟩ | h₂
        · exact .inl ⟨Ordinal.le_trans h₂ h₁, rfl⟩
        · exact .inr (Ordinal.lt_of_lt_of_le h₂ h₁)
        · exact .inr (Ordinal.lt_of_le_of_lt h₂ h₁)
        · exact .inr (Ordinal.lt_trans h₂ h₁)

/-- `le` is antisymmetric up to the status (Rocq `obl_le_antisymmetric`). -/
@[lantana_alias obl_le_antisymmetric]
theorem keep_of_le_of_le {g₁ g₂ : Obl} (h₁₂ : le g₁ g₂) (h₂₁ : le g₂ g₁) : keep g₁ g₂ := by
  cases g₁ <;> cases g₂ <;> simp_all [le, keep]

@[lantana_alias obl_step_le]
theorem step_le {g₁ g₂ : Obl} (h : step g₁ g₂) : le g₁ g₂ := by
  rcases h with h | h
  · cases g₁ <;> cases g₂ <;> simp_all [progress, le]
  · cases g₁ <;> cases g₂ <;> simp_all [discharge, le]

theorem progress_le {g₁ g₂ : Obl} (h : progress g₁ g₂) : le g₁ g₂ :=
  step_le (.inl h)

end Obl

/-! ## Maps of obligations -/

/-- Obligation maps. -/
@[lantana_alias obls]
abbrev Obls := OidMap Obl

namespace Obls

/-- `Ω₂` is `Ω₁` with one more obligation, at a fresh id. -/
@[lantana_alias obls_alloc]
def alloc (Ω₁ Ω₂ : Obls) : Prop :=
  ∃ k, get? Ω₁ k = none ∧ ∃ g, Ω₂ = insert Ω₁ k g

/-- The obligations satisfying `C` take an `R` step, the others stay. -/
@[lantana_alias obls_cond_rel]
abbrev condRel (C : Oid → Obl → Prop) (R : Obl → Obl → Prop) : Obls → Obls → Prop :=
  Model.condRel C R

/-- The obligations satisfying `C` take a step, the others stay. -/
@[lantana_alias obls_cond_step]
def condStep (C : Oid → Obl → Prop) (Ω₁ Ω₂ : Obls) : Prop :=
  condRel C Obl.step Ω₁ Ω₂

/-- Same domain and same status everywhere. -/
@[lantana_alias obls_keep]
def keep (Ω₁ Ω₂ : Obls) : Prop :=
  mapForall2 (fun _ => Obl.keep) Ω₁ Ω₂

/-- Progress: a conditional step that keeps the status of every obligation. -/
@[lantana_alias obls_cond_progress]
def condProgress (C : Oid → Obl → Prop) (Ω₁ Ω₂ : Obls) : Prop :=
  condStep C Ω₁ Ω₂ ∧ keep Ω₁ Ω₂

/-- The order on obligation maps seen by adequacy. -/
@[lantana_alias obls_le]
def le (Ω₁ Ω₂ : Obls) : Prop :=
  (∀ k, (get? Ω₁ k).isSome → (get? Ω₂ k).isSome) ∧
  ∀ k g₁ g₂, get? Ω₁ k = some g₁ → get? Ω₂ k = some g₂ → g₁.le g₂

@[lantana_alias obls_keep_reflexive]
theorem keep_refl (Ω : Obls) : keep Ω Ω :=
  mapForall2_refl (fun _ => Obl.keep_refl) Ω

@[lantana_alias obls_keep_transitive]
theorem keep_trans {Ω₁ Ω₂ Ω₃ : Obls} (h₁₂ : keep Ω₁ Ω₂) (h₂₃ : keep Ω₂ Ω₃) : keep Ω₁ Ω₃ :=
  mapForall2.trans (P := fun _ => Obl.keep) (fun _ _ _ _ => Obl.keep_trans) h₁₂ h₂₃

@[lantana_alias obls_keep_symmetric]
theorem keep_symm {Ω₁ Ω₂ : Obls} (h : keep Ω₁ Ω₂) : keep Ω₂ Ω₁ :=
  mapForall2.symm (P := fun _ => Obl.keep) (fun _ _ _ => Obl.keep_symm) h

#lantana_ignore obls_keep_equivalence "`keep_refl`, `keep_symm`, `keep_trans`"

@[lantana_alias obls_le_reflexive]
theorem le_refl (Ω : Obls) : le Ω Ω :=
  ⟨fun _ h => h, fun k g₁ g₂ h₁ h₂ => by rw [h₁] at h₂; cases h₂; exact Obl.le_refl g₁⟩

@[lantana_alias obls_le_transitive]
theorem le_trans {Ω₁ Ω₂ Ω₃ : Obls} (h₁₂ : le Ω₁ Ω₂) (h₂₃ : le Ω₂ Ω₃) : le Ω₁ Ω₃ := by
  refine ⟨fun k h => h₂₃.1 k (h₁₂.1 k h), fun k g₁ g₃ e₁ e₃ => ?_⟩
  have h₂ := h₁₂.1 k (by simp [e₁])
  cases e₂ : get? Ω₂ k with
  | none => simp [e₂] at h₂
  | some g₂ => exact Obl.le_trans (h₁₂.2 k g₁ g₂ e₁ e₂) (h₂₃.2 k g₂ g₃ e₂ e₃)

/-- `le` is antisymmetric up to the status (Rocq `obls_le_antisymmetric`). -/
@[lantana_alias obls_le_antisymmetric]
theorem keep_of_le_of_le {Ω₁ Ω₂ : Obls} (h₁₂ : le Ω₁ Ω₂) (h₂₁ : le Ω₂ Ω₁) : keep Ω₁ Ω₂ := by
  intro k
  cases e₁ : get? Ω₁ k with
  | none =>
    cases e₂ : get? Ω₂ k with
    | none => exact .none
    | some g₂ => have := h₂₁.1 k (by simp [e₂]); simp [e₁] at this
  | some g₁ =>
    cases e₂ : get? Ω₂ k with
    | none => have := h₁₂.1 k (by simp [e₁]); simp [e₂] at this
    | some g₂ => exact .some (Obl.keep_of_le_of_le (h₁₂.2 k g₁ g₂ e₁ e₂) (h₂₁.2 k g₂ g₁ e₂ e₁))

theorem condRel_le {C : Oid → Obl → Prop} {R : Obl → Obl → Prop} {Ω₁ Ω₂ : Obls}
    (hR : ∀ g₁ g₂, R g₁ g₂ → g₁.le g₂) (h : condRel C R Ω₁ Ω₂) : le Ω₁ Ω₂ := by
  refine ⟨fun k => (condRel_dom h k).1, fun k g₁ g₂ e₁ e₂ => ?_⟩
  rcases mapForall2.lookup h e₁ e₂ with ⟨_, hr⟩ | ⟨_, rfl⟩
  · exact hR _ _ hr
  · exact Obl.le_refl g₁

theorem condStep_le {C : Oid → Obl → Prop} {Ω₁ Ω₂ : Obls} (h : condStep C Ω₁ Ω₂) :
    le Ω₁ Ω₂ :=
  condRel_le (fun _ _ => Obl.step_le) h

@[lantana_alias obls_cond_progress_obls_le]
theorem condProgress_le {C : Oid → Obl → Prop} {Ω₁ Ω₂ : Obls} (h : condProgress C Ω₁ Ω₂) :
    le Ω₁ Ω₂ :=
  condStep_le h.1

theorem condStep_dom {C : Oid → Obl → Prop} {Ω₁ Ω₂ : Obls} (h : condStep C Ω₁ Ω₂) (k : Oid) :
    (get? Ω₁ k).isSome ↔ (get? Ω₂ k).isSome :=
  condRel_dom h k

theorem condProgress_dom {C : Oid → Obl → Prop} {Ω₁ Ω₂ : Obls} (h : condProgress C Ω₁ Ω₂)
    (k : Oid) : (get? Ω₁ k).isSome ↔ (get? Ω₂ k).isSome :=
  condRel_dom h.1 k

end Obls

end Lantana.Model

/-! ## Fresh ids -/

namespace Lantana.Model

open Iris.Std LawfulPartialMap

private theorem le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- An id above every key of `m`, hence not in `m`. -/
def freshOid {V : Type _} (m : OidMap V) : Oid :=
  ((toList m).map Prod.fst).foldr max 0 + 1

theorem get?_freshOid {V : Type _} (m : OidMap V) : get? m (freshOid m) = none := by
  cases e : get? m (freshOid m) with
  | none => rfl
  | some v =>
    have hmem : freshOid m ∈ (toList m).map Prod.fst :=
      List.mem_map.mpr ⟨(freshOid m, v), toList_get.mpr e, rfl⟩
    have := le_foldr_max hmem
    simp only [freshOid] at this
    omega

/-- A fresh obligation id: not in `Ω`. -/
def Obls.fresh (Ω : Obls) : Oid :=
  freshOid Ω

theorem Obls.get?_fresh (Ω : Obls) : get? Ω Ω.fresh = none :=
  get?_freshOid Ω

end Lantana.Model
