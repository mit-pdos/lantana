/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests of the pure obligation model: steps, round relations, the witness choice and the
forest invariant. -/

open Iris.Std LawfulPartialMap
open Ordinals Ordinal Lantana Lantana.Model

/-! Obligations and witnesses. -/

example :
    Obligation.Step (.assigned 2 0) (.assigned 1 3) := .inl (ofNat_lt_ofNat_iff.mpr (by decide))

example : Obligation.Step (.assigned 2 0) .discharged := .inr trivial

example : ¬Obligation.Step .discharged (.assigned 1 0) := by
  simp [Obligation.Step]

example (g : Obligation) : g.le g := Obligation.le_refl g

example : Obligation.CondOwner 3 0 (.assigned 1 3) := rfl

example : decide (Obligation.CondOwner 3 0 (.assigned 1 4)) = false := rfl

example : decide (Witness.CondAssigned 0 .discharged) = false := rfl

/-! Round relations. -/

example (Ω : Obligations) (k : Oid) (hk : get? Ω k = none) :
    Ω.NoDischarge (insert Ω k (.assigned 1 0)) :=
  Obligations.noDischarge_insert_fresh _ hk

example (Ω₁ Ω₂ : Obligations) (h : Ω₁.StayOrStep Ω₂) : Ω₁.le Ω₂ := h.le

/-- After any round, witnesses keeping the invariants exist; here with the scheduler bound
`γ i a := a` and `η := fairMeasureUb`. -/
example (Ω₁ Ω₂ : Obligations) (W₁ : Witnesses) (h : Ω₁.StayOrStep Ω₂) (hI : OWitInvFair Ω₁ W₁)
    (hLb : OWitInvLb (fun _ a => a) Ω₁ W₁) :
    ∃ W₂, W₁.StayOrStep W₂ ∧ OWitInvFair Ω₂ W₂ ∧ OWitInvLb (fun _ a => a) Ω₂ W₂ :=
  owitInv_exists_witnesses ⟨fun _ _ _ _ h => h, fun _ a => le_fairMeasureUb a⟩ h hI hLb

/-! The forest: thread `0` with a child `0` (fuel `5`), which has a child `1` (fuel `7`). -/

section Forest

def Ω₀ : Obligations := insert (insert ∅ 0 (.assigned 5 0)) 1 (.assigned 7 0)

def par₀ : OidMap Parent := insert (insert ∅ 0 (.thread 0)) 1 (.obl 0)

example : ForestWf Ω₀ 1 par₀ := by
  have h₀ : ForestWf (insert ∅ 0 (.assigned 5 0)) 1 (insert ∅ 0 (.thread 0)) :=
    (ForestWf.empty 1).alloc_obl (get?_empty 0) ⟨rfl, by decide⟩
  refine h₀.alloc_obl (get?_insert_ne (by decide)) ⟨?_, ?_⟩
  · exact Obligations.ownerOf_eq (get?_insert_eq rfl)
  · rw [Obligations.fuelOf_eq (get?_insert_eq rfl)]
    exact ofNat_lt_ofNat_iff.mpr (by decide)

example : (1 : Oid) ∈ Forest.kids par₀ (.obl 0) := by
  simp [par₀, get?_insert_eq]

example : (1 : Oid) ∈ Forest.subtree par₀ 0 :=
  Forest.subtree_closed (get?_insert_eq rfl) (Forest.subtree_root _ _)

/-- Thread `0` owns both nodes. -/
example : (0 : Oid) ∈ Forest.owned Ω₀ par₀ 0 := by
  rw [Forest.mem_owned]
  refine ⟨?_, ?_⟩
  · simp [par₀, get?_insert_ne, get?_insert_eq]
  · simp [Ω₀, Obligations.ownerOf, get?_insert_ne, get?_insert_eq]

/-- A thread outside the pool owns nothing. -/
example (wf : ForestWf Ω₀ 1 par₀) : Forest.owned Ω₀ par₀ 1 = ∅ :=
  wf.owned_of_le (Nat.le_refl 1)

end Forest
