/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Instances.Lib.GhostVar
public import Iris.BI.Lib.MonoNat
public import Lantana.Examples.Lib
public import Lantana.Examples.LockLevel
public import Lantana.Examples.Queue

/-! # A closed world for the examples

The world `ExGF` in which the adequacy corollaries of the examples are stated (Rocq's
`Σ := #[mupdΣ; histGS.histΣ …; tregGS.tregΣ heap_lang; heap_stateΣ; …]`): the ghost state of
the temporal layer before allocation (slots 0–15, as in the test world of
`LantanaTest.TrSpecModel`: world satisfaction and credits, obligations, witnesses, the forest,
the model history, the registry and the history), the heap with its meta data (16–18) and the
thread-expression map (19) of HeapLang, a ghost variable of obligation ids for the handoff
(20), and the counters (mono-nat, 21) and the ghost map from indices to obligations (22) of the
paradox, the lock level (40) and the ghost maps from tickets to obligations (41) and
to acknowledgements (42) of the starvation-free ticket lock. Slots 50–55 hold the cameras
of the queue of `Lantana.Examples.Queue` (its list of elements, 50; its inbox is the ghost
variable of slot 20) and of the ticket lock of `Lantana.Examples.TicketLock` (51–55), for
the task-queue clients. Its instances are `TemporalGpreS Exp State ExGF`, the premise of the
adequacy theorems, `HeapStateGpreS ExGF`, from which `heapState_init` allocates HeapLang's
ghost state, and the cameras of the examples (`TicketLockG ExGF`, `QueueG ExGF`, …).

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

/-- The contractivity of a ghost variable's functor, as `GhostVarG` expects it. -/
abbrev ghostVarOfF_contractive (A : Type) : RFunctorContractive (GhostVarF A) :=
  @instRFunctorContractiveProdOF _ _ OFunctor.constOF_RFunctorContractive
    instRFunctorContractiveAgreeRFOfOFunctorContractive

/-- The world of the examples. -/
def ExGF : BundledGFunctors.{0} := fun n =>
  match n with
  | 0 => ⟨InvMapF⟩
  | 1 => ⟨ULiftOF (constOF CoPsetDisjL)⟩
  | 2 => ⟨ULiftOF (constOF (DisjointLeibnizSet PosSet))⟩
  | 3 => ⟨ULiftOF.{4} (CreditF Ordinal.{1})⟩
  | 4 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO Bool)) OidMap))⟩
  | 5 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO OblNames)) OidMap))⟩
  | 6 => ⟨ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel)))⟩
  | 7 => ⟨ULiftOF.{4} (constOFP (Bank Fuel))⟩
  | 8 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO GName)) OidMap))⟩
  | 9 => ⟨ULiftOF.{4} (constOFP (BCred Fuel))⟩
  | 10 => ⟨ULiftOF (constOF (HeapView Parent (Agree (DiscreteO Oids)) ParentMap))⟩
  | 11 => ⟨ULiftOF (constOF (HeapView ThreadId (Agree (DiscreteO ThreadStatus)) ThreadMap))⟩
  | 12 => ⟨ULiftOF.{4} (constOFP (MonoList (DiscreteO MEvent)))⟩
  | 13 => ⟨ULiftOF (constOF (MonoList (DiscreteO (Nat × RegEntry))))⟩
  | 14 => ⟨DFracAgree.DFracAgreeRF TrPredF⟩
  | 15 => ⟨ULiftOF (constOF (MonoList (DiscreteO (HistEntry Exp State))))⟩
  | 16 => ⟨ULiftOF (constOF (HeapView Loc (Agree (DiscreteO (Option Val))) HeapF))⟩
  | 17 => ⟨ULiftOF (constOF (HeapView Loc (Agree (DiscreteO GName)) HeapF))⟩
  | 18 => ⟨ULiftOF (constOF MetaUR)⟩
  | 19 => ⟨ULiftOF (constOF (HeapView ThreadId (Agree (DiscreteO Exp)) ThreadMapF))⟩
  | 20 => { F := ULiftOF (GhostVarF Oid)
            contractive := @ULiftOF.instRFunctorContractive _ ghostVarF_contractive }
  | 21 => ⟨ULiftOF MonoNatRF⟩
  | 22 => ⟨ULiftOF (constOF (HeapView Nat (Agree (DiscreteO Oid)) OidMap))⟩
  | 40 => ⟨ULiftOF.{4} LockLevelF⟩
  | 41 => ⟨ULiftOF (constOF (HeapView Int (Agree (DiscreteO Oid)) IntMap))⟩
  | 42 => ⟨ULiftOF (constOF (HeapView Int (Agree (DiscreteO Bool)) IntMap))⟩
  | 50 => { F := ULiftOF (GhostVarF (List (Val × Oids)))
            contractive :=
              @ULiftOF.instRFunctorContractive _ (ghostVarOfF_contractive (List (Val × Oids))) }
  | 51 => ⟨ULiftOF.{4} (constOFP (HeapView Int (Agree (DiscreteO TicketLock.TicketInfo))
      TicketLock.TMap))⟩
  | 52 => { F := ULiftOF (constOF (HeapView Int (Agree (DiscreteO (Option Oid))) TicketLock.TMap))
            contractive := @ULiftOF.instRFunctorContractive _ OFunctor.constOF_RFunctorContractive }
  | 53 => { F := ULiftOF (GhostVarF Int)
            contractive := @ULiftOF.instRFunctorContractive _ (ghostVarOfF_contractive Int) }
  | 54 => ⟨ULiftOF.{4} (constOFP (AuthMra (α := Layer) (· ≤ ·)))⟩
  | 55 => { F := ULiftOF (GhostVarF Unit)
            contractive := @ULiftOF.instRFunctorContractive _ (ghostVarOfF_contractive Unit) }
  | _ => ⟨constOFU Unit⟩

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
  elemG := @ElemG.ofEqLift _ (GhostVarF Oid) ghostVarF_contractive _ 20
    (by unfold ExGF; rfl)

instance : MonoNatG ExGF where
  elem := ElemG.ofEqLift 21 (by unfold ExGF; rfl)
  name := 0

instance : GhostMapG ExGF Nat Oid OidMap := ⟨ElemG.ofEqLift 22 (by unfold ExGF; rfl)⟩

instance : LockLevelG ExGF where
  elem := (ElemG.ofEq 40 (by unfold ExGF; rfl) : ElemG ExGF (ULiftOF.{4} LockLevelF)).ofLift

instance : GhostMapG ExGF Int Oid IntMap := ⟨ElemG.ofEqLift 41 (by unfold ExGF; rfl)⟩

instance : GhostMapG ExGF Int Bool IntMap := ⟨ElemG.ofEqLift 42 (by unfold ExGF; rfl)⟩

/-- The cameras of the ticket lock (slots 51–55). -/
instance : TicketLock.TicketLockG ExGF where
  ticketG := ⟨(ElemG.ofEq 51 (by unfold ExGF; rfl) : ElemG ExGF (ULiftOF.{4}
    (constOFP (HeapView Int (Agree (DiscreteO TicketLock.TicketInfo)) TicketLock.TMap)))).ofLift⟩
  oblG := ⟨@ElemG.ofEqLift ExGF (constOF (HeapView Int (Agree (DiscreteO (Option Oid)))
    TicketLock.TMap)) OFunctor.constOF_RFunctorContractive _ 52 (by unfold ExGF; rfl)⟩
  tokenG := { elemG :=
    @ElemG.ofEqLift _ (GhostVarF Int) (ghostVarOfF_contractive Int) _ 53 (by unfold ExGF; rfl) }
  configG := (ElemG.ofEq 54 (by unfold ExGF; rfl) : ElemG ExGF (ULiftOF.{4}
    (constOFP (AuthMra (α := Layer) (· ≤ ·))))).ofLift
  aliveG := { elemG :=
    @ElemG.ofEqLift _ (GhostVarF Unit) (ghostVarOfF_contractive Unit) _ 55 (by unfold ExGF; rfl) }

/-- The cameras of the queue: its list of elements (slot 50) and its inbox (the ghost variable
of obligation ids of slot 20). -/
instance : Queue.QueueG ExGF where
  queueG := { elemG :=
    (@ElemG.ofEqLift _ (GhostVarF (List (Val × Oids))) (ghostVarOfF_contractive _) _ 50
      (by unfold ExGF; rfl)) }
  dataG := inferInstance

end Lantana.Examples
