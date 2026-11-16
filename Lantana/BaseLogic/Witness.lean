/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.BaseLogic.Obligation

/-! # Witnesses

A witness of an obligation is assigned (with a bound) or discharged (Rocq
`lantana/base_logic/witness.v`). As for obligations: the steps of a witness and the
conditional relations on witness maps, plus `Witnesses.Mono` (Rocq `wits_mon`), the relation
"witnesses do not increase" in which the witness invariant is monotone.

The conditional relations are the generic `CondRel` of `Obligation.lean`; its lemmas
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
def Progress : Witness → Witness → Prop
  | assigned f₁, assigned f₂ => f₂ < f₁
  | _, _ => False

/-- Discharge: an assigned witness becomes discharged. -/
@[lantana_alias witness_discharge]
def Discharge : Witness → Witness → Prop
  | assigned _, discharged => True
  | _, _ => False

/-- A step of a witness: progress or discharge. -/
@[lantana_alias witness_step]
def Step (w₁ w₂ : Witness) : Prop :=
  Progress w₁ w₂ ∨ Discharge w₁ w₂

/-- Same status (both assigned or both discharged). -/
@[lantana_alias witness_keep]
def Keep : Witness → Witness → Prop
  | assigned _, assigned _ => True
  | discharged, discharged => True
  | _, _ => False

/-- The assigned witnesses. -/
@[lantana_alias wit_cond_assigned]
def CondAssigned : Oid → Witness → Prop
  | _, assigned _ => True
  | _, discharged => False

@[lantana_alias wit_cond_assigned_dec]
instance condAssigned_decidable (k : Oid) : (w : Witness) → Decidable (CondAssigned k w)
  | assigned _ => inferInstanceAs (Decidable True)
  | discharged => inferInstanceAs (Decidable False)

/-- The bound does not increase and the status is kept: the pointwise relation of
`Witnesses.Mono` and of the no-discharge rounds `Witnesses.NoDischarge`. -/
@[lantana_alias wit_nd_le]
def NoDischargeLe : Witness → Witness → Prop
  | assigned a₁, assigned a₂ => a₂ ≤ a₁
  | discharged, discharged => True
  | _, _ => False

@[simp] theorem progress_assigned {f₁ f₂ : Fuel} :
    Progress (assigned f₁) (assigned f₂) ↔ f₂ < f₁ := Iff.rfl

@[simp] theorem condAssigned_assigned {k : Oid} {f : Fuel} : CondAssigned k (assigned f) :=
  trivial

@[simp] theorem not_condAssigned_discharged {k : Oid} : ¬CondAssigned k discharged := id

@[lantana_alias witness_keep_reflexive]
theorem keep_refl (w : Witness) : Keep w w := by
  cases w <;> trivial

@[lantana_alias witness_keep_transitive]
theorem keep_trans {w₁ w₂ w₃ : Witness} (h₁₂ : Keep w₁ w₂) (h₂₃ : Keep w₂ w₃) : Keep w₁ w₃ := by
  cases w₁ <;> cases w₂ <;> cases w₃ <;> simp_all [Keep]

theorem keep_symm {w₁ w₂ : Witness} (h : Keep w₁ w₂) : Keep w₂ w₁ := by
  cases w₁ <;> cases w₂ <;> simp_all [Keep]

theorem noDischargeLe_refl (w : Witness) : NoDischargeLe w w := by
  cases w
  · exact Ordinal.le_rfl
  · trivial

theorem noDischargeLe_trans {w₁ w₂ w₃ : Witness} (h₁₂ : NoDischargeLe w₁ w₂)
    (h₂₃ : NoDischargeLe w₂ w₃) :
    NoDischargeLe w₁ w₃ := by
  cases w₁ <;> cases w₂ <;> cases w₃ <;> simp_all [NoDischargeLe]
  exact Ordinal.le_trans h₂₃ h₁₂

end Witness

/-! ## Maps of witnesses -/

/-- Witness maps. -/
@[lantana_alias witnesses]
abbrev Witnesses := OidMap Witness

namespace Witnesses

/-- The witnesses satisfying `C` take an `R` step, the others stay. -/
@[lantana_alias wits_cond_rel]
abbrev CondRel (C : Oid → Witness → Prop) (R : Witness → Witness → Prop) :
    Witnesses → Witnesses → Prop :=
  Model.CondRel C R

/-- The witnesses satisfying `C` take a step, the others stay. -/
@[lantana_alias wits_cond_step]
def CondStep (C : Oid → Witness → Prop) (W₁ W₂ : Witnesses) : Prop :=
  CondRel C Witness.Step W₁ W₂

/-- Same domain and same status everywhere. -/
@[lantana_alias wits_keep]
def Keep (W₁ W₂ : Witnesses) : Prop :=
  MapForall2 (fun _ => Witness.Keep) W₁ W₂

/-- Progress: a conditional step that keeps the status of every witness. -/
@[lantana_alias wits_cond_progress]
def CondProgress (C : Oid → Witness → Prop) (W₁ W₂ : Witnesses) : Prop :=
  CondStep C W₁ W₂ ∧ Keep W₁ W₂

/-- Witnesses do not increase and keep their status. -/
@[lantana_alias wits_mon]
def Mono (W₁ W₂ : Witnesses) : Prop :=
  MapForall2 (fun _ => Witness.NoDischargeLe) W₁ W₂

@[lantana_alias wits_keep_reflexive]
theorem keep_refl (W : Witnesses) : Keep W W :=
  mapForall2_refl (fun _ => Witness.keep_refl) W

@[lantana_alias wits_keep_transitive]
theorem keep_trans {W₁ W₂ W₃ : Witnesses} (h₁₂ : Keep W₁ W₂) (h₂₃ : Keep W₂ W₃) :
    Keep W₁ W₃ :=
  MapForall2.trans (P := fun _ => Witness.Keep) (fun _ _ _ _ => Witness.keep_trans) h₁₂ h₂₃

theorem keep_symm {W₁ W₂ : Witnesses} (h : Keep W₁ W₂) : Keep W₂ W₁ :=
  MapForall2.symm (P := fun _ => Witness.Keep) (fun _ _ _ => Witness.keep_symm) h

@[lantana_alias wits_mon_reflexive]
theorem mono_refl (W : Witnesses) : Mono W W :=
  mapForall2_refl (fun _ => Witness.noDischargeLe_refl) W

@[lantana_alias wits_mon_transitive]
theorem mono_trans {W₁ W₂ W₃ : Witnesses} (h₁₂ : Mono W₁ W₂) (h₂₃ : Mono W₂ W₃) :
    Mono W₁ W₃ :=
  MapForall2.trans (P := fun _ => Witness.NoDischargeLe)
    (fun _ _ _ _ => Witness.noDischargeLe_trans) h₁₂ h₂₃

theorem condStep_dom {C : Oid → Witness → Prop} {W₁ W₂ : Witnesses} (h : CondStep C W₁ W₂)
    (k : Oid) : (get? W₁ k).isSome ↔ (get? W₂ k).isSome :=
  condRel_dom h k

theorem condProgress_dom {C : Oid → Witness → Prop} {W₁ W₂ : Witnesses}
    (h : CondProgress C W₁ W₂) (k : Oid) : (get? W₁ k).isSome ↔ (get? W₂ k).isSome :=
  condRel_dom h.1 k

/-- Progress does not increase the witnesses. -/
@[lantana_alias wits_cond_progress_mon]
theorem condProgress_mono {C : Oid → Witness → Prop} {W₁ W₂ : Witnesses}
    (h : CondProgress C W₁ W₂) : Mono W₁ W₂ := by
  refine mapForall2_intro fun k => ?_
  rcases MapForall2.inv h.1 k with ⟨e₁, e₂⟩ | ⟨w₁, w₂, e₁, e₂, hw⟩
  · exact .inl ⟨e₁, e₂⟩
  refine .inr ⟨w₁, w₂, e₁, e₂, ?_⟩
  have hkeep : Witness.Keep w₁ w₂ := MapForall2.lookup h.2 e₁ e₂
  rcases hw with ⟨_, hs | hs⟩ | ⟨_, rfl⟩
  · cases w₁ <;> cases w₂ <;> simp_all [Witness.Progress, Witness.NoDischargeLe]
    exact Ordinal.le_of_lt hs
  · cases w₁ <;> cases w₂ <;> simp_all [Witness.Discharge, Witness.Keep]
  · exact Witness.noDischargeLe_refl w₁

end Witnesses

end Lantana.Model
