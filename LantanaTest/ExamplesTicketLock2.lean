/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests of the starvation-free ticket lock (`ticket_lock2.v`) and its client
(`ticket_lock2_client.v`): the programs, the world, the trace properties, the end-to-end
corollaries and their axioms. -/

namespace LantanaTest.ExamplesTicketLock2

open Lantana Lantana.HeapLang Lantana.Examples
open scoped Lantana.TrProp Lantana.TrSpec

/-- `release` increments the ticket being served. -/
example : TicketLock2.release = hl_val(λ lnc, let curr := snd(lnc); curr ← !curr + #1) := rfl

/-- The client acquires and releases a new lock, and returns `42`. -/
example : TicketLock2Client.main = hl_val(λ _,
    let l := v(&TicketLock2.init) #();
    v(&TicketLock2.acquire) l;
    v(&TicketLock2.release) l;
    #42) := rfl

/-- The world has the cameras of the lock. -/
noncomputable example : TicketLock2.TicketLock2G ExGF := inferInstance

/-- Starvation freedom of a lock, from its guarantee. -/
example (tl : Val) :
    (TicketLock2.fairLockTrSpec (GF := ExGF) tl).external ⊆ TicketLock2.fairLockSf tl :=
  TicketLock2.fairLock_starvationFree tl

/-- The end-to-end statement of `ticket_lock2_client.v`, liveness and safety. -/
example (τ : Trace Exp State) (hbeh : IsBehavior τ) (hfair : fairScheduling τ) (hpos : τ.pos = 0)
    (hinit : τ.seq 0 = ⟨(TicketLock2Client.tp0, TicketLock2Client.σ0), 0⟩) :
    (◇ₜ TrProp.state (threadExprSat 0 [] (.val TicketLock2Client.v42)) ∧ₜ
      ◇ₜ (∃ₜ (next : Loc) (curr : Loc), TicketLock2.starvationFree next curr)) τ ∧
      safetyIris 0 (fun _ v => v = TicketLock2Client.v42) τ :=
  TicketLock2Client.ticketLockClient_liveness_safety τ hbeh hfair hpos hinit

set_option linter.deprecated false in
example : @RocqLantana.ticket_lock2_client.ticket_lock_client_adequacy =
    @TicketLock2Client.ticketLockClient_adequacy := rfl

/-! The specifications and the end-to-end corollaries depend only on the standard axioms. -/

/--
info: 'Lantana.Examples.TicketLock2.acquire_spec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TicketLock2.acquire_spec

/--
info: 'Lantana.Examples.TicketLock2.release_spec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TicketLock2.release_spec

/--
info: 'Lantana.Examples.TicketLock2Client.ticketLockClient_liveness_safety' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TicketLock2Client.ticketLockClient_liveness_safety

end LantanaTest.ExamplesTicketLock2
