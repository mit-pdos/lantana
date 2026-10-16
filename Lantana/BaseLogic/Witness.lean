/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.BaseLogic.Obligation

/-! # Witnesses

A witness of an obligation is assigned (with a bound) or discharged (Rocq
`lantana/base_logic/witness.v`). As for obligations: the steps of a witness and the
conditional relations on witness maps, plus `Witnesses.mono` (Rocq `wits_mon`), the relation
"witnesses do not increase" in which the witness invariant is monotone.

The conditional relations are the generic `condRel` of `Obligation.lean`; its lemmas
(`condRel_dom`, `condRel_split_cond`, `condRel_iff_lookup`, `condRel_iff`) serve both
obligations and witnesses.
-/

@[expose] public section

namespace Lantana.Model

open Iris.Std LawfulPartialMap
open Ordinals

/-- A witness: assigned with a bound, or discharged. -/
@[lantana_alias witness]
inductive Witness where
  | assigned (bound : Fuel)
  | discharged

attribute [lantana_alias witness_assigned] Witness.assigned
attribute [lantana_alias witness_discharged] Witness.discharged

#lantana_ignore wit_cond "the type `Oid → Witness → Prop` is written out"

namespace Witness

/-- Progress: the bound decreases strictly. -/
@[lantana_alias witness_progress]
def progress : Witness → Witness → Prop
  | assigned f₁, assigned f₂ => f₂ < f₁
  | _, _ => False

/-- Discharge: an assigned witness becomes discharged. -/
@[lantana_alias witness_discharge]
def discharge : Witness → Witness → Prop
  | assigned _, discharged => True
  | _, _ => False

/-- A step of a witness: progress or discharge. -/
@[lantana_alias witness_step]
def step (w₁ w₂ : Witness) : Prop :=
  progress w₁ w₂ ∨ discharge w₁ w₂

/-- Same status (both assigned or both discharged). -/
@[lantana_alias witness_keep]
def keep : Witness → Witness → Prop
  | assigned _, assigned _ => True
  | discharged, discharged => True
  | _, _ => False

/-- The assigned witnesses. -/
@[lantana_alias wit_cond_assigned]
def condAssigned : Oid → Witness → Prop
  | _, assigned _ => True
  | _, discharged => False

@[lantana_alias wit_cond_assigned_dec]
instance condAssigned_decidable (k : Oid) : (w : Witness) → Decidable (condAssigned k w)
  | assigned _ => inferInstanceAs (Decidable True)
  | discharged => inferInstanceAs (Decidable False)

/-- The bound does not increase and the status is kept: the pointwise relation of
`Witnesses.mono` and of the no-discharge rounds `Witnesses.ndf`. -/
@[lantana_alias wit_nd_le]
def ndLe : Witness → Witness → Prop
  | assigned a₁, assigned a₂ => a₂ ≤ a₁
  | discharged, discharged => True
  | _, _ => False

@[simp] theorem progress_assigned {f₁ f₂ : Fuel} :
    progress (assigned f₁) (assigned f₂) ↔ f₂ < f₁ := Iff.rfl

@[simp] theorem condAssigned_assigned {k : Oid} {f : Fuel} : condAssigned k (assigned f) :=
  trivial

@[simp] theorem not_condAssigned_discharged {k : Oid} : ¬condAssigned k discharged := id

@[lantana_alias witness_keep_reflexive]
theorem keep_refl (w : Witness) : keep w w := by
  cases w <;> trivial

@[lantana_alias witness_keep_transitive]
theorem keep_trans {w₁ w₂ w₃ : Witness} (h₁₂ : keep w₁ w₂) (h₂₃ : keep w₂ w₃) : keep w₁ w₃ := by
  cases w₁ <;> cases w₂ <;> cases w₃ <;> simp_all [keep]

theorem keep_symm {w₁ w₂ : Witness} (h : keep w₁ w₂) : keep w₂ w₁ := by
  cases w₁ <;> cases w₂ <;> simp_all [keep]

theorem ndLe_refl (w : Witness) : ndLe w w := by
  cases w
  · exact Ordinal.le_rfl
  · trivial

theorem ndLe_trans {w₁ w₂ w₃ : Witness} (h₁₂ : ndLe w₁ w₂) (h₂₃ : ndLe w₂ w₃) :
    ndLe w₁ w₃ := by
  cases w₁ <;> cases w₂ <;> cases w₃ <;> simp_all [ndLe]
  exact Ordinal.le_trans h₂₃ h₁₂

end Witness

/-! ## Maps of witnesses -/

/-- Witness maps. -/
@[lantana_alias witnesses]
abbrev Witnesses := OidMap Witness

namespace Witnesses

/-- The witnesses satisfying `C` take an `R` step, the others stay. -/
@[lantana_alias wits_cond_rel]
abbrev condRel (C : Oid → Witness → Prop) (R : Witness → Witness → Prop) :
    Witnesses → Witnesses → Prop :=
  Model.condRel C R

/-- The witnesses satisfying `C` take a step, the others stay. -/
@[lantana_alias wits_cond_step]
def condStep (C : Oid → Witness → Prop) (W₁ W₂ : Witnesses) : Prop :=
  condRel C Witness.step W₁ W₂

/-- Same domain and same status everywhere. -/
@[lantana_alias wits_keep]
def keep (W₁ W₂ : Witnesses) : Prop :=
  mapForall2 (fun _ => Witness.keep) W₁ W₂

/-- Progress: a conditional step that keeps the status of every witness. -/
@[lantana_alias wits_cond_progress]
def condProgress (C : Oid → Witness → Prop) (W₁ W₂ : Witnesses) : Prop :=
  condStep C W₁ W₂ ∧ keep W₁ W₂

/-- Witnesses do not increase and keep their status. -/
@[lantana_alias wits_mon]
def mono (W₁ W₂ : Witnesses) : Prop :=
  mapForall2 (fun _ => Witness.ndLe) W₁ W₂

@[lantana_alias wits_keep_reflexive]
theorem keep_refl (W : Witnesses) : keep W W :=
  mapForall2_refl (fun _ => Witness.keep_refl) W

@[lantana_alias wits_keep_transitive]
theorem keep_trans {W₁ W₂ W₃ : Witnesses} (h₁₂ : keep W₁ W₂) (h₂₃ : keep W₂ W₃) :
    keep W₁ W₃ :=
  mapForall2.trans (P := fun _ => Witness.keep) (fun _ _ _ _ => Witness.keep_trans) h₁₂ h₂₃

theorem keep_symm {W₁ W₂ : Witnesses} (h : keep W₁ W₂) : keep W₂ W₁ :=
  mapForall2.symm (P := fun _ => Witness.keep) (fun _ _ _ => Witness.keep_symm) h

@[lantana_alias wits_mon_reflexive]
theorem mono_refl (W : Witnesses) : mono W W :=
  mapForall2_refl (fun _ => Witness.ndLe_refl) W

@[lantana_alias wits_mon_transitive]
theorem mono_trans {W₁ W₂ W₃ : Witnesses} (h₁₂ : mono W₁ W₂) (h₂₃ : mono W₂ W₃) :
    mono W₁ W₃ :=
  mapForall2.trans (P := fun _ => Witness.ndLe) (fun _ _ _ _ => Witness.ndLe_trans) h₁₂ h₂₃

theorem condStep_dom {C : Oid → Witness → Prop} {W₁ W₂ : Witnesses} (h : condStep C W₁ W₂)
    (k : Oid) : (get? W₁ k).isSome ↔ (get? W₂ k).isSome :=
  condRel_dom h k

theorem condProgress_dom {C : Oid → Witness → Prop} {W₁ W₂ : Witnesses}
    (h : condProgress C W₁ W₂) (k : Oid) : (get? W₁ k).isSome ↔ (get? W₂ k).isSome :=
  condRel_dom h.1 k

/-- Progress does not increase the witnesses. -/
@[lantana_alias wits_cond_progress_mon]
theorem condProgress_mono {C : Oid → Witness → Prop} {W₁ W₂ : Witnesses}
    (h : condProgress C W₁ W₂) : mono W₁ W₂ := by
  refine mapForall2_intro fun k => ?_
  rcases mapForall2.inv h.1 k with ⟨e₁, e₂⟩ | ⟨w₁, w₂, e₁, e₂, hw⟩
  · exact .inl ⟨e₁, e₂⟩
  refine .inr ⟨w₁, w₂, e₁, e₂, ?_⟩
  have hkeep : Witness.keep w₁ w₂ := mapForall2.lookup h.2 e₁ e₂
  rcases hw with ⟨_, hs | hs⟩ | ⟨_, rfl⟩
  · cases w₁ <;> cases w₂ <;> simp_all [Witness.progress, Witness.ndLe]
    exact Ordinal.le_of_lt hs
  · cases w₁ <;> cases w₂ <;> simp_all [Witness.discharge, Witness.keep]
  · exact Witness.ndLe_refl w₁

end Witnesses

end Lantana.Model
