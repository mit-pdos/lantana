/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Instances.IProp
public import Iris.ProofMode
public import Lantana.Algebra.AuthMra
public import Lantana.BaseLogic.LaterCredits

/-! # Lock levels

The ghost state of the levels of the ticket locks (Rocq `inG Σ (auth_mraUR (ord.le))` of
`ticket_lock.v` and `ticket_lock2.v`, with `own γc (●AM{dq}[ord.le] ℓ)` and
`own γc (◯AM[ord.le] ℓ)`): authoritative monotone knowledge of a layer (`AuthMra (· ≤ ·)` on
`Layer`). The authority `lockLevel γ dq ℓ` owns the current level `ℓ`, which can only grow
(`lockLevel_update`); `lockLevelLb γ ℓ` knows that the level is at least `ℓ`.

The camera is in `Type 1` (layers are `Ordinal.{0}`), so its functor is Lantana's universe-
polymorphic constant functor `constOFP`; in a world it sits in a slot `ULiftOF.{4} …` with the
instance `(ElemG.ofEq τ h).ofLift` (as the ordinal cameras of `Examples.World`).
-/

@[expose] public noncomputable section

namespace Lantana.Examples

open Iris Iris.BI Iris.ProofMode Lantana Lantana.AuthMra

/-- The order of layers. -/
abbrev LayerLe : Layer → Layer → Prop := (· ≤ ·)

/-- The functor of the lock levels. -/
abbrev LockLevelF : COFE.OFunctorPre := constOFP (AuthMra LayerLe)

/-- The camera of the lock levels. -/
class LockLevelG (GF : BundledGFunctors) where
  elem : ElemG GF LockLevelF

attribute [reducible, instance] LockLevelG.elem

section LockLevel
variable {GF : BundledGFunctors} [LockLevelG GF]

/-- The fraction `dq` of the authority of the level `γ`, at `ℓ`. -/
def lockLevel (γ : GName) (dq : DFrac) (ℓ : Layer) : IProp GF :=
  iOwn (F := LockLevelF) γ (●AM{dq}[LayerLe] ℓ)

/-- The level `γ` is at least `ℓ`. -/
def lockLevelLb (γ : GName) (ℓ : Layer) : IProp GF :=
  iOwn (F := LockLevelF) γ (◯AM[LayerLe] ℓ)

instance lockLevelLb_persistent (γ : GName) (ℓ : Layer) :
    Persistent (lockLevelLb (GF := GF) γ ℓ) := by
  unfold lockLevelLb; infer_instance

instance lockLevel_discard_persistent (γ : GName) (ℓ : Layer) :
    Persistent (lockLevel (GF := GF) γ .discard ℓ) := by
  unfold lockLevel; infer_instance

/-- A new level. -/
theorem lockLevel_alloc (ℓ : Layer) : ⊢@{IProp GF} |==> ∃ γ : GName, lockLevel γ (.own 1) ℓ := by
  unfold lockLevel
  exact iOwn_alloc (F := LockLevelF) _ auth_valid

/-- The authority knows its level. -/
theorem lockLevel_lb (γ : GName) (dq : DFrac) (ℓ : Layer) :
    lockLevel (GF := GF) γ dq ℓ ⊢ lockLevelLb γ ℓ := by
  unfold lockLevel lockLevelLb
  exact iOwn_mono (included dq ℓ)

/-- The authority knows its level, and keeps it. -/
theorem lockLevel_get_lb (γ : GName) (dq : DFrac) (ℓ : Layer) :
    lockLevel (GF := GF) γ dq ℓ ⊢ lockLevel γ dq ℓ ∗ lockLevelLb γ ℓ := by
  unfold lockLevel lockLevelLb
  conv => lhs; rw [auth_know_op]
  exact iOwn_op.mp

/-- What is known is below the level. -/
theorem lockLevel_lb_valid (γ : GName) (dq : DFrac) (ℓ ℓ' : Layer) :
    lockLevel (GF := GF) γ dq ℓ ⊢ lockLevelLb γ ℓ' -∗ lockLevel γ dq ℓ ∗ ⌜ℓ' ≤ ℓ⌝ := by
  unfold lockLevel lockLevelLb
  iintro H1 #H2
  ihave H := iOwn_valid_r (F := LockLevelF) (a := (●AM{dq}[LayerLe] ℓ) • (◯AM[LayerLe] ℓ'))
    $$ [H1 H2]
  · iapply iOwn_op.mpr
    iframe H1
    iexact H2
  icases H with ⟨H, %h⟩
  icases iOwn_op.mp $$ H with ⟨H1, -⟩
  iframe H1
  ipureintro
  exact (both_dfrac_valid.mp h).2

/-- The level grows. -/
theorem lockLevel_update (γ : GName) {ℓ₁ ℓ₂ : Layer} (h : ℓ₁ ≤ ℓ₂) :
    lockLevel (GF := GF) γ (.own 1) ℓ₁ ⊢ |==> lockLevel γ (.own 1) ℓ₂ := by
  unfold lockLevel
  exact iOwn_update (update h)

/-- The authority becomes read-only. -/
theorem lockLevel_persist (γ : GName) (dq : DFrac) (ℓ : Layer) :
    lockLevel (GF := GF) γ dq ℓ ⊢ |==> lockLevel γ .discard ℓ := by
  unfold lockLevel
  exact iOwn_update (auth_persist ℓ dq)

end LockLevel

end Lantana.Examples
