/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for the model behind the sealed obligation-forest interface: a closed world `TestGF`
with all the ghost state of the model — world satisfaction and transfinite later credits (slots
0 to 3, as in `LantanaTest.FUpd`), obligations (slots 4 to 7, as in `LantanaTest.OSat`), the
forest (slots 8 and 9, as in `LantanaTest.OForest`), witnesses (slots 10 and 11, as in
`LantanaTest.OWit`) and the model history (slot 12, a `MonoList` of events in `Type 2`) — with
its `ModelGpreS` instance (the universe check); the allocation of the model; a fork of thread `0`
through the interface (`step_fork`, run against the model with `mphys_modelInterp`); and
`Obl.new` through the interface, alone, followed by `Obl.discharge_leaf`, and run against the
model (`mupd_modelInterp_steps`). -/

namespace LantanaTest.OPreds

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.MonoList LawfulPartialMap
open Ordinals Ordinal Lantana Lantana.Model

noncomputable def TestGF : BundledGFunctors.{0} := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨ULiftOF (constOF CoPsetDisjL), by infer_instance⟩
  | 2 => ⟨ULiftOF (constOF (DisjointLeibnizSet PosSet)), by infer_instance⟩
  | 3 => ⟨ULiftOF.{4} (CreditF Ordinal.{1}), by infer_instance⟩
  | 4 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO Bool)) OidMap)), by infer_instance⟩
  | 5 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO OblNames)) OidMap)), by infer_instance⟩
  | 6 => ⟨ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel))), by infer_instance⟩
  | 7 => ⟨ULiftOF.{4} (constOFP (Bank Fuel)), by infer_instance⟩
  | 8 => ⟨ULiftOF (constOF (HeapView Parent (Agree (DiscreteO Oids)) ParentMap)),
      by infer_instance⟩
  | 9 => ⟨ULiftOF (constOF (HeapView ThreadId (Agree (DiscreteO ThreadStatus)) ThreadMap)),
      by infer_instance⟩
  | 10 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO GName)) OidMap)), by infer_instance⟩
  | 11 => ⟨ULiftOF.{4} (constOFP (BCred Fuel)), by infer_instance⟩
  | 12 => ⟨ULiftOF.{4} (constOFP (MonoList (DiscreteO MEvent))), by infer_instance⟩
  | _ => ⟨constOFU Unit, by infer_instance⟩

noncomputable instance : WsatGpreS TestGF where
  inv := ElemG.ofEq 0 (by unfold TestGF; rfl)
  enabled := ElemG.ofEqLift 1 (by unfold TestGF; rfl)
  disabled := ElemG.ofEqLift 2 (by unfold TestGF; rfl)

noncomputable instance : TlcGpreS TestGF where
  elem := (ElemG.ofEq 3 (by unfold TestGF; rfl)).ofLift

noncomputable instance : InvGpreS TestGF where
  toWsatGpreS := inferInstance
  toTlcGpreS := inferInstance

noncomputable instance : OSatGpreS TestGF where
  stateG := ⟨ElemG.ofEqLift 4 (by unfold TestGF; rfl)⟩
  namesG := ⟨ElemG.ofEqLift 5 (by unfold TestGF; rfl)⟩
  boundG := (ElemG.ofEq 6 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel))))).ofLift
  bankG := (ElemG.ofEq 7 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (Bank Fuel)))).ofLift

noncomputable instance : OForestGpreS TestGF where
  kidsG := ⟨ElemG.ofEqLift 8 (by unfold TestGF; rfl)⟩
  statusG := ⟨ElemG.ofEqLift 9 (by unfold TestGF; rfl)⟩

noncomputable instance : OWitGpreS TestGF where
  namesG := ⟨ElemG.ofEqLift 10 (by unfold TestGF; rfl)⟩
  credG := (ElemG.ofEq 11 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (BCred Fuel)))).ofLift

noncomputable instance : MHistGpreS TestGF where
  elem := (ElemG.ofEq 12 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (MonoList (DiscreteO MEvent))))).ofLift

noncomputable instance : ModelGpreS TestGF := {}

/-! Allocation of the model. -/

example : ⊢@{IProp TestGF} |==> ∃ _ : ModelGS TestGF,
    (∃ x : Ordinal.{1}, ●£ₒ x) ∗ wsat ∗ ownE ⊤ ∗ modelInterp [(0, ∅)] 0 ∅ ∅ 0 0 :=
  modelInterp_alloc 0

/-- Allocate the model and fork thread `0` (a physical round of the interface, run against the
model): thread `0` runs, without children. -/
example : ⊢@{IProp TestGF} |==> ∃ _ : ModelGS TestGF,
    |={∅}=> (modelInterp ([(0, ∅)] ++ [(0, ∅)]) (0 + 1) ∅ ∅ 0 1 ∗ thKids 0 ∅) := by
  imod modelInterp_alloc (GF := TestGF) 0 with ⟨%G, -, -, -, HM⟩
  imodintro
  iexists G
  have hfork : ⊢@{IProp TestGF} Lantana.mphys 0 0 0 1 (thKids 0 ∅) := by
    refine (?_ : ⊢ _).trans (step_fork 0 0 0 1 _ (Nat.le_refl 0) (Nat.zero_le 1))
    rw [show List.range' 0 (1 - 0) = [0] from rfl]
    iintro Hl
    imodintro
    icases BigSepL.bigSepL_cons.mp $$ Hl with ⟨Hk, -⟩
    iexact Hk
  ihave Hrun := hfork.trans (mphys_modelInterp 0 0 0 1 (thKids 0 ∅))
  imod Hrun $$ [] %([(0, ∅)] : List MEvent) %0 %(∅ : Obls) %(∅ : Witnesses) HM with ⟨HM, Hk⟩
  · iempintro
  imodintro
  iframe HM Hk

section Interface

variable {Expr State : Type} [ModelGS TestGF] [TemporalGS Expr State TestGF]
  [StateInterp Expr State TestGF] [TemporalInterp Expr State TestGF]

/-- `Obl.new` through the interface: a new obligation below thread `0`. -/
example (E : CoPset) (ℓ : Layer) :
    thKids 0 ∅ ⊢@{IProp TestGF} |={E}=>m ∃ k : Oid, thKids 0 ((∅ : Oids).insert k) ∗
      oblKids k ∅ ∗ Obl.assigned k 1 ∗ Obl.fuel k ℓ 1 ∗ Wit.layer k ℓ := by
  iintro Hk
  ihave #Hb := parLe_thread (GF := TestGF) 0 ℓ
  imod Obl.new (Expr := Expr) (State := State) E (.thread 0) ∅ ℓ 1 $$ Hb Hk
    with ⟨%k, -, Hk, Hkk, Ha, Hf, #Hw⟩
  imodintro
  iexists k
  iframe Hk Hkk Ha Hf
  iexact Hw

/-- A new obligation below thread `0`, discharged at once (`Obl.new`, `Obl.discharge_leaf`). -/
example (E : CoPset) (ℓ : Layer) :
    thKids 0 ∅ ⊢@{IProp TestGF} |={E}=>m ∃ k : Oid, Obl.discharged k ∗ Wit.layer k ℓ := by
  iintro Hk
  ihave #Hb := parLe_thread (GF := TestGF) 0 ℓ
  imod Obl.new (Expr := Expr) (State := State) E (.thread 0) ∅ ℓ 1 $$ Hb Hk
    with ⟨%k, -, Hk, Hkk, Ha, -, #Hw⟩
  imod Obl.discharge_leaf (Expr := Expr) (State := State) E (.thread 0) _ k
    Std.ExtTreeSet.mem_insert_self $$ Hk Hkk Ha with ⟨-, #Hd⟩
  imodintro
  iexists k
  isplitl []
  · iexact Hd
  · iexact Hw

/-- Running `Obl.new` against the model, with the lower bound `γ i a := a` of the witnesses. -/
example (E : CoPset) (ℓ : Layer) (h : List (HistEntry Expr State)) (n : Nat) (σ : State)
    (tp : ThreadPool Expr) (g : List MEvent) (v : Nat) (Ω : Obls) (W : Witnesses)
    (hLb : owitInvLb (fun _ a => a) Ω W) :
    thKids 0 ∅ ∗ historyTInterp h n σ tp ∗ modelInterp g v Ω W n tp.length ⊢@{IProp TestGF}
      |={E}=> ∃ k : Oid, Obl.assigned k 1 ∗ historyTInterp h n σ tp := by
  iintro ⟨Hk, HT, HM⟩
  ihave #Hb := parLe_thread (GF := TestGF) 0 ℓ
  ihave H := Obl.new (Expr := Expr) (State := State) E (.thread 0) ∅ ℓ 1 $$ Hb Hk
  imod mupd_modelInterp_steps (fun _ a => a) ⟨fun _ _ _ _ h => h, fun _ a => le_fairMeasureUb a⟩
    E E h n σ tp g v Ω W _ hLb $$ H HT HM with ⟨⟨%k, -, -, -, Ha, -⟩, HT, -⟩
  imodintro
  iexists k
  iframe Ha HT

end Interface

end LantanaTest.OPreds
