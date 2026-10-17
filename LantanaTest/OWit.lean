/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for the ghost state of witnesses: a closed world with the ghost state of obligations
(slots 0–3, as in `LantanaTest/OSat.lean`) and of witnesses (slot 4: the name map, slot 5: the
credit camera `BCred Fuel` in `Type 2`), its `OWitGpreS` instance (the universe check), the
allocation of `owit`, and the allocation of a witness. -/

namespace LantanaTest.OWit

open Iris Iris.BI Iris.ProofMode Iris.Std LawfulPartialMap
open Ordinals Ordinal Lantana Lantana.Model

noncomputable def TestGF : BundledGFunctors.{0} := fun n =>
  match n with
  | 0 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO Bool)) OidMap))⟩
  | 1 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO OblNames)) OidMap))⟩
  | 2 => ⟨ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel)))⟩
  | 3 => ⟨ULiftOF.{4} (constOFP (Bank Fuel))⟩
  | 4 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO GName)) OidMap))⟩
  | 5 => ⟨ULiftOF.{4} (constOFP (BCred Fuel))⟩
  | _ => ⟨constOFU Unit⟩

noncomputable instance : OSatGpreS TestGF where
  stateG := ⟨ElemG.ofEqLift 0 (by unfold TestGF; rfl)⟩
  namesG := ⟨ElemG.ofEqLift 1 (by unfold TestGF; rfl)⟩
  boundG := (ElemG.ofEq 2 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel))))).ofLift
  bankG := (ElemG.ofEq 3 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (Bank Fuel)))).ofLift

noncomputable instance : OWitGpreS TestGF where
  namesG := ⟨ElemG.ofEqLift 4 (by unfold TestGF; rfl)⟩
  credG := (ElemG.ofEq 5 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (BCred Fuel)))).ofLift

section
variable [OSatGS TestGF]

example : ⊢@{IProp TestGF} |==> ∃ _ : OWitGS TestGF, owit ∅ :=
  owit_alloc

/-- Allocate the witnesses and one assigned witness at id `0` with bound `1`; its bound is
persistent and its credits are below the bound. -/
example : ⊢@{IProp TestGF} |==> ∃ _ : OWitGS TestGF,
    owit (insert ∅ 0 (.assigned (1 : Ordinal.{1}))) ∗ OWit.bound 0 (1 : Ordinal.{1}) := by
  imod owit_alloc with ⟨%G, Hw⟩
  imod @owit_alloc_witness_assigned _ _ G ∅ 0 (get?_empty 0) (1 : Ordinal.{1}) $$ Hw
    with ⟨Hw, #Hb⟩
  imodintro
  iexists G
  iframe Hw
  iexact Hb

example [OWitGS TestGF] (k : Oid) (a b : Ordinal.{1}) :
    OWit.bound k a ∗ OWit.cred k b ⊢@{IProp TestGF} ⌜b ≤ a⌝ :=
  OWit.compare k a b

end

end LantanaTest.OWit
