/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for Lantana's fancy update, invariants and satisfiability: a closed world `TestGF`
with the ghost state of world satisfaction (slots 0–2, as in Iris-Lean's
`Iris.Examples.ClosedProofs`) and of transfinite later credits (slot 3, as in
`LantanaTest.Credits`), and its `InvGpreS` instance. -/

namespace LantanaTest.FUpd

open Iris Iris.BI Iris.ProofMode Lantana Ordinals Ordinal

noncomputable def TestGF : BundledGFunctors.{0} := fun n =>
  match n with
  | 0 => ⟨InvMapF⟩
  | 1 => ⟨ULiftOF (constOF CoPsetDisjL)⟩
  | 2 => ⟨ULiftOF (constOF (DisjointLeibnizSet PosSet))⟩
  | 3 => ⟨ULiftOF.{4} (CreditF Ordinal.{1})⟩
  | _ => ⟨constOFU Unit⟩

noncomputable instance : WsatGpreS TestGF where
  inv := ElemG.ofEq 0 (by unfold TestGF; rfl)
  enabled := ElemG.ofEqLift 1 (by unfold TestGF; rfl)
  disabled := ElemG.ofEqLift 2 (by unfold TestGF; rfl)

noncomputable instance : TlcGpreS TestGF where
  elem := (ElemG.ofEq 3 (by unfold TestGF; rfl)).ofLift

noncomputable instance : InvGpreS TestGF where
  toWsatGpreS := inferInstance
  toTlcGpreS := inferInstance

/-! The fancy update of `IProp TestGF` is Lantana's. -/

example [InvGS TestGF] (P : IProp TestGF) : iprop(|={⊤}=> P) = uPred_fupd ⊤ ⊤ P := rfl

example [InvGS TestGF] : (inferInstance : BIFUpdate (IProp TestGF)) = uPred_bi_fupd := rfl

/-! Allocation of the ghost state. -/

example : ⊢@{IProp TestGF} |==> ∃ _ : InvGS TestGF,
    (∃ x : Ordinal.{1}, ●£ₒ x) ∗ wsat ∗ ownE ⊤ :=
  invGS_alloc

section Invariants

variable [InvGS TestGF] {N : Namespace}

/-- Allocate an invariant, open it with `iinv`, and strip the later with a credit. -/
example (P : IProp TestGF) [Persistent P] : ⊢ £ₙ 1 -∗ ▷ P -∗ |={⊤}=> P := by
  iintro Hc HP
  imod inv_alloc N ⊤ P $$ HP with #Hinv
  iinv Hinv with HP Hclose
  imod Lantana.lc_fupd_elim_later $$ Hc HP with #HP
  imod Hclose $$ [] with -
  · inext
    iexact HP
  imodintro
  iexact HP

/-- `iinv` without closing hypothesis. -/
example {P : IProp TestGF} : inv N iprop(<pers> P) ={⊤}=∗ ▷ P := by
  iintro #Hinv
  iinv Hinv with #H
  imodintro
  isplit
  · iexact H
  · imodintro
    inext
    iexact H

/-- `iinv` with a mask given by a hypothesis. -/
example {E} {P : IProp TestGF} {h : ↑N ⊆ E} : inv N iprop(<pers> P) ={E}=∗ ▷ P := by
  iintro #Hinv
  iinv Hinv with #H Hclose
  imod Hclose $$ H
  imodintro
  inext
  iexact H

/-- Timeless invariants are opened without a later. -/
example {P : IProp TestGF} [Timeless P] (h : ↑N ⊆ (⊤ : CoPset)) : inv N P ={⊤}=∗ True := by
  iintro #Hinv
  imod inv_acc_timeless h $$ Hinv with ⟨HP, Hclose⟩
  iapply Hclose $$ HP

/-- A credit strips a later in front of a fancy update. -/
example {E₁ E₂ : CoPset} {P : IProp TestGF} :
    £ₙ 2 ∗ ▷^[2] (|={E₁,E₂}=> P) ⊢@{IProp TestGF} |={E₁,E₂}=> P := by
  iintro ⟨Hc, HP⟩
  iapply Lantana.lc_fupd_add_laterN 2 $$ Hc HP

/-- Relational updates and `ALC?` inside fancy updates. -/
example {E : CoPset} {P : IProp TestGF} : (|==>r P) ⊢@{IProp TestGF} |={E}=> P := rupd_fupd

example (b : Bool) (P : IProp TestGF) : P ⊢ ALC? b P := by
  iintro HP
  imodintro
  iexact HP

example (b : Bool) (P Q : IProp TestGF) : (ALC? b P) ∗ Q ⊢ ALC? b iprop(P ∗ Q) := by
  iintro ⟨HP, HQ⟩
  imod HP
  iframe

example (b : Bool) (P : IProp TestGF) : (ALC? b P) = ALCb b P := rfl

end Invariants

/-! Satisfiability: the instances adequacy needs resolve for `iPropSatLcAtFrame`. -/

section Satisfiable

variable [InvGS TestGF] (F : IProp TestGF)

example : SatAtLaws (iPropSatLcAtFrame F) := inferInstance
example (E : CoPset) : SatRUpd (iPropSatLcAtFrame F E) := inferInstance
example (E : CoPset) : SatRUpdUpdate (iPropSatLcAtFrame F E) := inferInstance
example (E : CoPset) : SatExists (iPropSatLcAtFrame F E) Ordinal.{1} := inferInstance
example (E : CoPset) : SatExists (iPropSatLcAtFrame F E) Bool := inferInstance

/-- A typical step of adequacy: eliminate a fancy update, a later, a fancy update and `ALC`. -/
example (E₁ E₂ : CoPset) (P : IProp TestGF)
    (h : (iPropSatLcAtFrame F E₁).sat iprop(|={E₁,E₂}=> ▷ |={E₂}=> ALC P)) :
    (iPropSatLcAtFrame F E₂).sat P :=
  sat_ALC (SatFUpd.fupd (SatPred.sat_later _ (SatFUpd.fupd h)))

example (E : CoPset) (P : IProp TestGF) :
    (iPropSatLcAtFrame F E).sat P ↔
      iPropSat.sat iprop((∃ x : Ordinal.{1}, ●£ₒ x) ∗ ((wsat ∗ ownE E) ∗ (F ∗ P))) :=
  iPropSatLcAtFrame_sat

end Satisfiable

end LantanaTest.FUpd
