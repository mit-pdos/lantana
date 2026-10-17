/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Instances.IProp
public import Iris.BI
public import Iris.ProofMode
public import Lantana.BaseLogic.Obligation

/-! # Big separating conjunctions along a pointwise relation between maps

The invariants of the model are big separating conjunctions over the obligation and witness
maps; a round replaces the map by a pointwise related one (`mapForall2 R m₁ m₂`). These lemmas
transfer the big conjunction from `m₁` to `m₂` (Rocq does this with `big_sepM_impl` and
`map_Forall2` inductions in each proof).
-/

@[expose] public noncomputable section

namespace Lantana.Model

open Iris Iris.BI Iris.ProofMode Iris.Std LawfulPartialMap

variable {GF : BundledGFunctors} {A B : Type _}

theorem mapForall2.insert_some {R : Oid → A → B → Prop} {m₁ : OidMap A} {m₂ : OidMap B}
    {k : Oid} {a : A} (h : mapForall2 R (insert m₁ k a) m₂) :
    ∃ b, get? m₂ k = some b ∧ R k a b :=
  mapForall2.lookup_left h (get?_insert_eq rfl)

theorem mapForall2.delete_of_insert {R : Oid → A → B → Prop} {m₁ : OidMap A} {m₂ : OidMap B}
    {k : Oid} {a : A} (hk : get? m₁ k = none) (h : mapForall2 R (insert m₁ k a) m₂) :
    mapForall2 R m₁ (delete m₂ k) := by
  refine mapForall2_intro fun k' => ?_
  by_cases hkk : k = k'
  · subst hkk
    exact .inl ⟨hk, get?_delete_eq rfl⟩
  · rw [get?_delete_ne hkk]
    have := h.inv k'
    rwa [get?_insert_ne hkk] at this

theorem mapForall2.and {P Q : Oid → A → B → Prop} {m₁ : OidMap A} {m₂ : OidMap B}
    (hP : mapForall2 P m₁ m₂) (hQ : mapForall2 Q m₁ m₂) :
    mapForall2 (fun k a b => P k a b ∧ Q k a b) m₁ m₂ := by
  refine mapForall2_intro fun k => ?_
  rcases hP.inv k with ⟨e₁, e₂⟩ | ⟨a, b, e₁, e₂, hp⟩
  · exact .inl ⟨e₁, e₂⟩
  · exact .inr ⟨a, b, e₁, e₂, hp, hQ.lookup e₁ e₂⟩

theorem mapForall2.eq_empty {R : Oid → A → B → Prop} {m₂ : OidMap B}
    (h : mapForall2 R (∅ : OidMap A) m₂) : m₂ = ∅ := by
  rw [eq_empty_iff]
  intro k
  rcases h.inv k with ⟨-, e₂⟩ | ⟨a, -, e₁, -, -⟩
  · exact e₂
  · rw [get?_empty] at e₁
    cases e₁

/-- Transfer a big separating conjunction along `mapForall2 R m₁ m₂`. -/
theorem bigSepM_mapForall2 {R : Oid → A → B → Prop} {m₁ : OidMap A} {m₂ : OidMap B}
    (h : mapForall2 R m₁ m₂) {Φ : Oid → A → IProp GF} {Ψ : Oid → B → IProp GF}
    (hΦΨ : ∀ k a b, R k a b → Φ k a ⊢ Ψ k b) :
    ([∗map] k ↦ a ∈ m₁, Φ k a) ⊢ [∗map] k ↦ b ∈ m₂, Ψ k b := by
  induction m₁ using LawfulFiniteMap.induction_on generalizing m₂ with
  | hemp =>
    rw [h.eq_empty]
    exact (BigSepM.bigSepM_empty.1.trans BigSepM.bigSepM_empty.2)
  | hins k a m₁ hk ih =>
    obtain ⟨b, hb, hR⟩ := h.insert_some
    refine (BigSepM.bigSepM_insert hk).1.trans ?_
    refine (sep_mono (hΦΨ k a b hR) (ih (h.delete_of_insert hk))).trans ?_
    exact (BigSepM.bigSepM_delete hb).2

/-- Transfer a big separating conjunction along `mapForall2 R m₁ m₂` under a basic update,
keeping a by-product for every entry of `m₁`. -/
theorem bigSepM_mapForall2_bupd {R : Oid → A → B → Prop} {m₁ : OidMap A} {m₂ : OidMap B}
    (h : mapForall2 R m₁ m₂) {Φ Θ : Oid → A → IProp GF} {Ψ : Oid → B → IProp GF}
    (hΦΨ : ∀ k a b, R k a b → Φ k a ⊢ |==> (Ψ k b ∗ Θ k a)) :
    ([∗map] k ↦ a ∈ m₁, Φ k a) ⊢
      |==> (([∗map] k ↦ b ∈ m₂, Ψ k b) ∗ [∗map] k ↦ a ∈ m₁, Θ k a) := by
  induction m₁ using LawfulFiniteMap.induction_on generalizing m₂ with
  | hemp =>
    rw [h.eq_empty]
    iintro -
    imodintro
    isplitl []
    · iapply BigSepM.bigSepM_empty.2
      iempintro
    · iapply BigSepM.bigSepM_empty.2
      iempintro
  | hins k a m₁ hk ih =>
    obtain ⟨b, hb, hR⟩ := h.insert_some
    iintro H
    icases (BigSepM.bigSepM_insert hk).1 $$ H with ⟨Hk, HM⟩
    imod hΦΨ k a b hR $$ Hk with ⟨Hψ, Hθ⟩
    imod ih (h.delete_of_insert hk) $$ HM with ⟨HΨ, HΘ⟩
    imodintro
    isplitl [Hψ HΨ]
    · iapply (BigSepM.bigSepM_delete hb).2
      iframe
    · iapply (BigSepM.bigSepM_insert hk).2
      iframe

end Lantana.Model
