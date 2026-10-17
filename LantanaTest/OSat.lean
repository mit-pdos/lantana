/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for the ghost state of obligations: a closed world `TestGF : BundledGFunctors.{0}` with
the ghost maps of states (slot 0) and of names (slot 1) and the per-obligation cameras of the
bound (slot 2) and of the bank (slot 3), its `OSatGpreS` instance (the universe check), the
allocation of `osat`, and the life of one obligation.

Universes: the ghost maps hold `Type` values, so their slots are `ULiftOF` of `constOF` of the
camera (`ElemG.ofEqLift`), as for the history. The bound and bank cameras
`Agree (DiscreteO Fuel)` and `Bank Fuel` are in `Type 2`: their slots are
`ULiftOF.{4} (constOFP …)` and the instances `(ElemG.ofEq τ h).ofLift`, as for the credits.
Inside a structure instance, the level of `ULiftOF` in the type of `ElemG.ofEq τ h` must be
given by an ascription (Lean cannot solve `4 =?= max 2 ?u`). -/

namespace LantanaTest.OSat

open Iris Iris.BI Iris.ProofMode Iris.Std LawfulPartialMap
open Ordinals Ordinal Lantana Lantana.Model

noncomputable def TestGF : BundledGFunctors.{0} := fun n =>
  match n with
  | 0 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO Bool)) OidMap))⟩
  | 1 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO OblNames)) OidMap))⟩
  | 2 => ⟨ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel)))⟩
  | 3 => ⟨ULiftOF.{4} (constOFP (Bank Fuel))⟩
  | _ => ⟨constOFU Unit⟩

noncomputable instance : OSatGpreS TestGF where
  stateG := ⟨ElemG.ofEqLift 0 (by unfold TestGF; rfl)⟩
  namesG := ⟨ElemG.ofEqLift 1 (by unfold TestGF; rfl)⟩
  boundG := (ElemG.ofEq 2 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel))))).ofLift
  bankG := (ElemG.ofEq 3 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (Bank Fuel)))).ofLift

/-! Allocation. -/

example : ⊢@{IProp TestGF} |==> ∃ _ : OSatGS TestGF, osat ∅ :=
  osat_alloc

/-- Allocate the ghost state and one assigned obligation at id `0`. -/
example : ⊢@{IProp TestGF} |==> ∃ _ : OSatGS TestGF,
    osat (insert ∅ 0 (.assigned (1 : Ordinal.{1}) 0)) ∗ OSat.assigned 0 1 ∗
      OSat.fuel 0 (1 : Ordinal.{1}) := by
  imod osat_alloc with ⟨%G, Hs⟩
  imod @osat_alloc_obl_assigned _ G ∅ 0 (get?_empty 0) (1 : Ordinal.{1}) 0 $$ Hs
    with ⟨Hs, -, -, Ha, Hf, -⟩
  imodintro
  iexists G
  iframe

section
variable [OSatGS TestGF]

/-- The life of an obligation at a fresh id: allocation with fuel `1`, one step of progress
with the unit of fuel, and discharge. -/
example (Ω : Obls) : osat Ω ⊢@{IProp TestGF} |==> ∃ Ω', osat Ω' ∗ OSat.discharged Ω.fresh := by
  iintro Hs
  imod osat_alloc_obl_assigned (Obls.get?_fresh Ω) (1 : Ordinal.{1}) 0 $$ Hs
    with ⟨Hs, -, -, Ha, Hf, -⟩
  imod osat_progress_one (get?_insert_eq rfl) Ordinal.zero_lt_one $$ [$Hs $Hf]
    with ⟨%a', Hs, -⟩
  imod osat_discharge _ _ $$ [$Hs $Ha] with ⟨Hs, Hd, -⟩
  imodintro
  iexists _
  iframe

/-- The proof mode splits fuel along `+ₕ`. -/
example (k : Oid) (a b : Fuel) :
    OSat.fuel k (a +ₕ b) ⊢@{IProp TestGF} OSat.fuel k b ∗ OSat.fuel k a := by
  iintro ⟨Ha, Hb⟩
  iframe

/-- The cash of an obligation is at most its model fuel. -/
example (Ω : Obls) (k : Oid) (a f : Fuel) (t : ThreadId)
    (hk : get? Ω k = some (.assigned f t)) :
    osat Ω ∗ OSat.fuel k a ⊢@{IProp TestGF} ⌜a ≤ f⌝ := by
  iintro H
  icases osat_fuel_le Ω k a $$ H with %h
  ipureintro
  exact h f t hk

end

end LantanaTest.OSat
