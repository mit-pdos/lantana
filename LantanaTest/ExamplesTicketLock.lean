/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests of the ticket lock: its program, a world with its cameras (the class `TicketLockG` can
be instantiated, with the layer-valued cameras in lifted slots), the trace-level corollaries,
and the axioms of the specifications. -/

namespace LantanaTest.ExamplesTicketLock

open Iris Iris.Std Lantana Lantana.HeapLang Lantana.Examples Lantana.Examples.TicketLock
open scoped Lantana.TrProp Lantana.TrSpec

noncomputable section

/-- `acquire` takes a ticket and spins on `curr`. -/
example : TicketLock.acquire = hl_val(λ lnc, let next := fst(lnc); let curr := snd(lnc);
    let my := faa(next, #1); (rec loop _ := if !curr = my then #() else loop #()) #()) := rfl

/-- `delete` increments `curr` as `release` does, then frees both cells. -/
example : TicketLock.delete = hl_val(λ lnc, let next := fst(lnc); let curr := snd(lnc);
    curr ← !curr + #1; free(next); free(curr)) := rfl

/-- The contractivity of a ghost variable's functor, as `GhostVarG` expects it. -/
abbrev ghostVarF_contractive (A : Type) : RFunctorContractive (GhostVarF A) :=
  @instRFunctorContractiveProdOF _ _ OFunctor.constOF_RFunctorContractive
    instRFunctorContractiveAgreeRFOfOFunctorContractive

/-- A world with the cameras of the ticket lock (slots `0`–`4`). -/
noncomputable def TLGF : BundledGFunctors.{0} := fun n =>
  match n with
  | 0 => ⟨ULiftOF.{4} (constOFP (HeapView Int (Agree (DiscreteO TicketInfo)) TMap))⟩
  | 1 => { F := ULiftOF (constOF (HeapView Int (Agree (DiscreteO (Option Oid))) TMap))
           contractive := @ULiftOF.instRFunctorContractive _ OFunctor.constOF_RFunctorContractive }
  | 2 => { F := ULiftOF (GhostVarF Int)
           contractive := @ULiftOF.instRFunctorContractive _ (ghostVarF_contractive Int) }
  | 3 => ⟨ULiftOF.{4} (constOFP (AuthMra (α := Layer) (· ≤ ·)))⟩
  | 4 => { F := ULiftOF (GhostVarF Unit)
           contractive := @ULiftOF.instRFunctorContractive _ (ghostVarF_contractive Unit) }
  | _ => ⟨constOFU Unit⟩

noncomputable instance : TicketLockG TLGF where
  ticketG := ⟨(ElemG.ofEq 0 (by unfold TLGF; rfl) : ElemG TLGF (ULiftOF.{4}
    (constOFP (HeapView Int (Agree (DiscreteO TicketInfo)) TMap)))).ofLift⟩
  oblG := ⟨@ElemG.ofEqLift TLGF (constOF (HeapView Int (Agree (DiscreteO (Option Oid))) TMap))
    OFunctor.constOF_RFunctorContractive _ 1 (by unfold TLGF; rfl)⟩
  tokenG := { elemG :=
    @ElemG.ofEqLift _ (GhostVarF Int) (ghostVarF_contractive Int) _ 2 (by unfold TLGF; rfl) }
  configG := (ElemG.ofEq 3 (by unfold TLGF; rfl) : ElemG TLGF (ULiftOF.{4}
    (constOFP (AuthMra (α := Layer) (· ≤ ·))))).ofLift
  aliveG := { elemG :=
    @ElemG.ofEqLift _ (GhostVarF Unit) (ghostVarF_contractive Unit) _ 4 (by unfold TLGF; rfl) }

variable {GF : BundledGFunctors}

/-- A lock that cannot be deleted makes progress, and with a monotone `next` every pending
ticket is served. -/
example (tl : Val) (τ : Trace Exp State) (h : (aliveFairLockTrSpec (GF := GF) tl).external τ)
    (hmon : ∀ next curr : Loc, tl = vLock next curr → nextMonotone next τ) :
    ∃ next curr : Loc, tl = vLock next curr ∧ starvationFree next curr τ := by
  obtain ⟨next, curr, htl, hrp⟩ := aliveFairLock_release_progress tl τ h
  exact ⟨next, curr, htl, releaseProgress_starvationFree next curr τ hrp (hmon next curr htl)⟩

set_option linter.deprecated false in
example : @RocqLantana.ticket_lock.TicketLock_acquire_spec = @acquire_spec := rfl

/-! The specifications depend only on the standard axioms. -/

/--
info: 'Lantana.Examples.TicketLock.acquire_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms acquire_spec

/--
info: 'Lantana.Examples.TicketLock.release_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms release_spec

/--
info: 'Lantana.Examples.TicketLock.delete_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms delete_spec

/--
info: 'Lantana.Examples.TicketLock.init_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms init_spec

/--
info: 'Lantana.Examples.TicketLock.guar_isFairLockAlive' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms guar_isFairLockAlive

end

end LantanaTest.ExamplesTicketLock
