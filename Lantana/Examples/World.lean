/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.Instances.Lib.GhostVar
public import Iris.BI.Lib.MonoNat
public import Lantana.Examples.Lib
public import Lantana.Examples.LockLevel

/-! # A closed world for the examples

The world `ExGF` in which the adequacy corollaries of the examples are stated (Rocq's
`Σ := #[mupdΣ; histGS.histΣ …; tregGS.tregΣ heap_lang; heap_stateΣ; …]`): the ghost state of
the temporal layer before allocation (slots 0–15, as in the test world of
`LantanaTest.TrSpecModel`: world satisfaction and credits, obligations, witnesses, the forest,
the model history, the registry and the history), the heap with its meta data (16–18) and the
thread-expression map (19) of HeapLang, a ghost variable of obligation ids for the handoff
(20), and the counters (mono-nat, 21) and the ghost map from indices to obligations (22) of the
paradox, and the lock level (40) and the ghost maps from tickets to obligations (41) and to
acknowledgements (42) of the starvation-free ticket lock. Its instances are
`TemporalGpreS Exp State ExGF`, the premise of the adequacy theorems,
and `HeapStateGpreS ExGF`, from which `heapState_init` allocates HeapLang's ghost state.

Universes: as in `LantanaTest.TrSpecModel`, the slots holding ordinals are `ULiftOF.{4}` of
`constOFP` of the camera, the others `ULiftOF` of `constOF`.
-/

@[expose] public noncomputable section

namespace Lantana.Examples

open Iris Iris.BI Iris.Std
open Ordinals Ordinal Lantana Lantana.Model Lantana.HeapLang

/-- The functor of saved trace predicates of HeapLang. -/
abbrev TrPredF : COFE.OFunctorPre := DiscreteFunOF fun _ : Trace Exp State => LaterOF IdOF

/-- The contractivity of the ghost variable's functor, as `GhostVarG` expects it (here, instance
search would find Lantana's `constOFP_rFunctorContractive` instead). -/
abbrev ghostVarF_contractive : RFunctorContractive (GhostVarF Oid) :=
  @instRFunctorContractiveProdOF _ _ OFunctor.constOF_RFunctorContractive
    instRFunctorContractiveAgreeRFOfOFunctorContractive

/-- The world of the examples. -/
def ExGF : BundledGFunctors.{0} := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨ULiftOF (constOF CoPsetDisjL), by infer_instance⟩
  | 2 => ⟨ULiftOF (constOF (DisjointLeibnizSet PosSet)), by infer_instance⟩
  | 3 => ⟨ULiftOF.{4} (CreditF Ordinal.{1}), by infer_instance⟩
  | 4 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO Bool)) OidMap)), by infer_instance⟩
  | 5 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO OblNames)) OidMap)), by infer_instance⟩
  | 6 => ⟨ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel))), by infer_instance⟩
  | 7 => ⟨ULiftOF.{4} (constOFP (Bank Fuel)), by infer_instance⟩
  | 8 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO GName)) OidMap)), by infer_instance⟩
  | 9 => ⟨ULiftOF.{4} (constOFP (BCred Fuel)), by infer_instance⟩
  | 10 => ⟨ULiftOF (constOF (HeapView Parent (Agree (DiscreteO Oids)) ParentMap)),
      by infer_instance⟩
  | 11 => ⟨ULiftOF (constOF (HeapView ThreadId (Agree (DiscreteO ThreadStatus)) ThreadMap)),
      by infer_instance⟩
  | 12 => ⟨ULiftOF.{4} (constOFP (MonoList (DiscreteO MEvent))), by infer_instance⟩
  | 13 => ⟨ULiftOF (constOF (MonoList (DiscreteO (Nat × RegEntry)))), by infer_instance⟩
  | 14 => ⟨DFracAgree.DFracAgreeRF TrPredF, by infer_instance⟩
  | 15 => ⟨ULiftOF (constOF (MonoList (DiscreteO (HistEntry Exp State)))), by infer_instance⟩
  | 16 => ⟨ULiftOF (constOF (HeapView Loc (Agree (DiscreteO (Option Val))) HeapF)),
      by infer_instance⟩
  | 17 => ⟨ULiftOF (constOF (HeapView Loc (Agree (DiscreteO GName)) HeapF)), by infer_instance⟩
  | 18 => ⟨ULiftOF (constOF MetaUR), by infer_instance⟩
  | 19 => ⟨ULiftOF (constOF (HeapView ThreadId (Agree (DiscreteO Exp)) ThreadMapF)),
      by infer_instance⟩
  | 20 => ⟨ULiftOF (GhostVarF Oid),
      @ULiftOF.instRFunctorContractive _ ghostVarF_contractive⟩
  | 21 => ⟨ULiftOF MonoNatRF, by infer_instance⟩
  | 22 => ⟨ULiftOF (constOF (HeapView Nat (Agree (DiscreteO Oid)) OidMap)), by infer_instance⟩
  | 40 => ⟨ULiftOF.{4} LockLevelF, by infer_instance⟩
  | 41 => ⟨ULiftOF (constOF (HeapView Int (Agree (DiscreteO Oid)) IntMap)), by infer_instance⟩
  | 42 => ⟨ULiftOF (constOF (HeapView Int (Agree (DiscreteO Bool)) IntMap)), by infer_instance⟩
  | _ => ⟨constOFU Unit, by infer_instance⟩

instance : WsatGpreS ExGF where
  inv := ElemG.ofEq 0 (by unfold ExGF; rfl)
  enabled := ElemG.ofEqLift 1 (by unfold ExGF; rfl)
  disabled := ElemG.ofEqLift 2 (by unfold ExGF; rfl)

instance : TlcGpreS ExGF where
  elem := (ElemG.ofEq 3 (by unfold ExGF; rfl)).ofLift

instance : InvGpreS ExGF where
  toWsatGpreS := inferInstance
  toTlcGpreS := inferInstance

instance : OSatGpreS ExGF where
  stateG := ⟨ElemG.ofEqLift 4 (by unfold ExGF; rfl)⟩
  namesG := ⟨ElemG.ofEqLift 5 (by unfold ExGF; rfl)⟩
  boundG := (ElemG.ofEq 6 (by unfold ExGF; rfl) :
    ElemG ExGF (ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel))))).ofLift
  bankG := (ElemG.ofEq 7 (by unfold ExGF; rfl) :
    ElemG ExGF (ULiftOF.{4} (constOFP (Bank Fuel)))).ofLift

instance : OWitGpreS ExGF where
  namesG := ⟨ElemG.ofEqLift 8 (by unfold ExGF; rfl)⟩
  credG := (ElemG.ofEq 9 (by unfold ExGF; rfl) :
    ElemG ExGF (ULiftOF.{4} (constOFP (BCred Fuel)))).ofLift

instance : OForestGpreS ExGF where
  kidsG := ⟨ElemG.ofEqLift 10 (by unfold ExGF; rfl)⟩
  statusG := ⟨ElemG.ofEqLift 11 (by unfold ExGF; rfl)⟩

instance : MHistGpreS ExGF where
  elem := (ElemG.ofEq 12 (by unfold ExGF; rfl) :
    ElemG ExGF (ULiftOF.{4} (constOFP (MonoList (DiscreteO MEvent))))).ofLift

instance : ModelGpreS ExGF where

instance : RegGpreS Exp State ExGF where
  listG := ⟨ElemG.ofEqLift 13 (by unfold ExGF; rfl)⟩
  predG := { elemG := ElemG.ofEq 14 (by unfold ExGF; rfl) }

instance : MonoListG ExGF (HistEntry Exp State) :=
  ⟨ElemG.ofEqLift 15 (by unfold ExGF; rfl)⟩

instance : TemporalGpreS Exp State ExGF where

instance : HeapStateGpreS ExGF where
  genHeapPre :=
    { heap := ⟨ElemG.ofEqLift 16 (by unfold ExGF; rfl)⟩
      metaInfo := ⟨ElemG.ofEqLift 17 (by unfold ExGF; rfl)⟩
      metaData := ElemG.ofEqLift 18 (by unfold ExGF; rfl) }
  threadMapPre := ⟨ElemG.ofEqLift 19 (by unfold ExGF; rfl)⟩

instance : GhostVarG ExGF Oid where
  elemG := @ElemG.ofEqLift _ (GhostVarF Oid) ghostVarF_contractive 20
    (by unfold ExGF; rfl)

instance : MonoNatG ExGF where
  elem := ElemG.ofEqLift 21 (by unfold ExGF; rfl)
  name := 0

instance : GhostMapG ExGF Nat Oid OidMap := ⟨ElemG.ofEqLift 22 (by unfold ExGF; rfl)⟩

instance : LockLevelG ExGF where
  elem := (ElemG.ofEq 40 (by unfold ExGF; rfl) : ElemG ExGF (ULiftOF.{4} LockLevelF)).ofLift

instance : GhostMapG ExGF Int Oid IntMap := ⟨ElemG.ofEqLift 41 (by unfold ExGF; rfl)⟩

instance : GhostMapG ExGF Int Bool IntMap := ⟨ElemG.ofEqLift 42 (by unfold ExGF; rfl)⟩

end Lantana.Examples
