/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests of the ticket lock with a monotone `next`: a world with its cameras (the class
`TicketLockMonoG` can be instantiated: the five cameras of `TicketLock` and the monotone
integers), the coercion of the ghost names, starvation freedom with no hypothesis about `next`,
and the axioms of the specifications. -/

namespace LantanaTest.ExamplesTicketLockMono

open Iris Iris.Std Lantana Lantana.HeapLang Lantana.Examples Lantana.Examples.TicketLockMono
open Lantana.Examples.TicketLock (TicketInfo TMap vLock)
open scoped Lantana.TrProp Lantana.TrSpec

noncomputable section

/-- The contractivity of a ghost variable's functor, as `GhostVarG` expects it. -/
abbrev ghostVarF_contractive (A : Type) : RFunctorContractive (GhostVarF A) :=
  @instRFunctorContractiveProdOF _ _ OFunctor.constOF_RFunctorContractive
    instRFunctorContractiveAgreeRFOfOFunctorContractive

/-- A world with the cameras of the ticket lock (slots `0`–`4`) and the monotone integers
(slot `5`). -/
noncomputable def TLMGF : BundledGFunctors.{0} := fun n =>
  match n with
  | 0 => ⟨ULiftOF.{4} (constOFP (HeapView Int (Agree (DiscreteO TicketInfo)) TMap)),
      by infer_instance⟩
  | 1 => ⟨ULiftOF (constOF (HeapView Int (Agree (DiscreteO (Option Oid))) TMap)),
      @ULiftOF.instRFunctorContractive _ OFunctor.constOF_RFunctorContractive⟩
  | 2 => ⟨ULiftOF (GhostVarF Int), @ULiftOF.instRFunctorContractive _ (ghostVarF_contractive Int)⟩
  | 3 => ⟨ULiftOF.{4} (constOFP (AuthMra (α := Layer) (· ≤ ·))), by infer_instance⟩
  | 4 => ⟨ULiftOF (GhostVarF Unit), @ULiftOF.instRFunctorContractive _ (ghostVarF_contractive Unit)⟩
  | 5 => ⟨ULiftOF MonoNatRF, by infer_instance⟩
  | _ => ⟨constOFU Unit, by infer_instance⟩

noncomputable instance : TicketLockMonoG TLMGF where
  ticketG := ⟨(ElemG.ofEq 0 (by unfold TLMGF; rfl) : ElemG TLMGF (ULiftOF.{4}
    (constOFP (HeapView Int (Agree (DiscreteO TicketInfo)) TMap)))).ofLift⟩
  oblG := ⟨@ElemG.ofEqLift TLMGF (constOF (HeapView Int (Agree (DiscreteO (Option Oid))) TMap))
    OFunctor.constOF_RFunctorContractive 1 (by unfold TLMGF; rfl)⟩
  tokenG := { elemG :=
    @ElemG.ofEqLift _ (GhostVarF Int) (ghostVarF_contractive Int) 2 (by unfold TLMGF; rfl) }
  configG := (ElemG.ofEq 3 (by unfold TLMGF; rfl) : ElemG TLMGF (ULiftOF.{4}
    (constOFP (AuthMra (α := Layer) (· ≤ ·))))).ofLift
  aliveG := { elemG :=
    @ElemG.ofEqLift _ (GhostVarF Unit) (ghostVarF_contractive Unit) 4 (by unfold TLMGF; rfl) }
  monoG := ⟨{ elem := ElemG.ofEqLift 5 (by unfold TLMGF; rfl), name := 0 }⟩

/-- The ghost names extend those of `TicketLock`, whose ghost state is reused through the
coercion. -/
example (γ : TicketLockMono.TicketLockName) : (γ : TicketLock.TicketLockName).γa = γ.γa := rfl

variable {GF : BundledGFunctors}

/-- A lock that cannot be deleted is starvation free, with no hypothesis about `next` (compare
`LantanaTest.ExamplesTicketLock`, where `next` is assumed monotone). -/
example (tl : Val) (τ : Trace Exp State) (h : (aliveFairLockTrSpec (GF := GF) tl).external τ) :
    ∃ next curr : Loc, tl = vLock next curr ∧ TicketLock.starvationFree next curr τ :=
  aliveFairLock_starvationFree tl τ h

set_option linter.deprecated false in
example : @RocqLantana.ticket_lock_mono.TicketLock_acquire_spec = @acquire_spec := rfl

set_option linter.deprecated false in
example : @RocqLantana.ticket_lock_mono.lock_alive_persist = @TicketLock.lock_alive_persist :=
  rfl

/-! The specifications depend only on the standard axioms. -/

/--
info: 'Lantana.Examples.TicketLockMono.acquire_spec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms acquire_spec

/--
info: 'Lantana.Examples.TicketLockMono.release_spec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms release_spec

/--
info: 'Lantana.Examples.TicketLockMono.delete_spec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms delete_spec

/--
info: 'Lantana.Examples.TicketLockMono.init_spec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms init_spec

/--
info: 'Lantana.Examples.TicketLockMono.guar_isFairLockAlive' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms guar_isFairLockAlive

/--
info: 'Lantana.Examples.TicketLockMono.aliveFairLock_starvationFree' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms aliveFairLock_starvationFree

end

end LantanaTest.ExamplesTicketLockMono
