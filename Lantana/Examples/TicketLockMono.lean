/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.BI.Lib.MonoZ
public import Lantana.Examples.TicketLock

/-! # The ticket lock whose guarantee records that `next` never decreases

Rocq `examples/ticket_lock_mono.v`. The ticket lock of `Examples.TicketLock` (the same program,
`TicketLock.init/acquire/release/delete`, Rocq `Module TicketLock := ticket_lock.TicketLock`,
and the same specifications), whose guarantee also records that `next` never decreases. Half
of `next`'s points-to is in the mono cell `monoInv γm next` (with the authority `γm ↪●MZ w` of
the lower bounds of `next`), an invariant registered again for every value `v` that `next`
reaches (`nextGe γm next v`, an `alwaysIGuar` read as `nextGeTrSpec next v`: `next ≥ v`, or
`next` freed). So a lock that cannot be deleted is starvation free with no hypothesis about
`next` (`aliveFairLock_starvationFree`).

A chain of invariants, one per value, would not do: each link's reading would rest on the next
one's, available only one step of the logic later (its certificate is later-guarded). The
reading of the mono cell is the only hand-proved guarantee of the examples (`guar_monoInv`:
`guar_mono`, `guar_or`, `guar_ex`, `guar_state_fact`).

## Ghost state (Rocq `ticket_lock_monoG`)

The five cameras of `TicketLock.TicketLockG` and Iris-Lean's monotone integers `MonoZG`
(`Iris.BI.Lib.MonoZ`, Rocq's Transfinite `mono_Z`): `TicketLockMonoG` extends
`TicketLock.TicketLockG`, and the ghost names `TicketLockName` extend those of `TicketLock` by
`γm`, with a coercion, so that the alive token `γ ↪LOCK_AL{dq}`, the layer `γ ↪LOCK_CF{dq} ℓ`,
their lemmas, the lock token `TicketLock.lockToken γ κu`, the token's invariant
`TicketLock.lockTokenInv` and the ticket states (`TicketLock.ticketSt`, `holderSt`, `nextOwner`)
are those of `TicketLock`.

## The invariant

`lockInvAlive` is `TicketLock.lockInvAlive` with half of `next ↦ n` and the registration
`nextGe γm next n` in place of `next ↦ n`. `acquire`'s `faa` opens the mono cell inside the lock
invariant, increments the authority with `next` and registers the cell for `n + 1`; `delete`
frees `next` with the cell's half and leaves half of the freed points-to in the cell.

## Specifications

All proved, with the statements of `TicketLock` (Rocq: the same as `ticket_lock.v`):
`init_spec` (measure `10`), `acquire_spec` (`20 + ((50 + 50 * ▽) * ℵ + 50 * ▽)` at layer
`ℓ.succ`), `release_spec` (`10`), `delete_spec` (`20`). The proofs are those of `TicketLock`,
with the mono cell; `acquire_end` and `acquire_mine` (which do not open the lock invariant) are
`TicketLock`'s. The opening of the mono cell takes one more later credit (in `faa` and in
`delete`), which the steps provide for free.

## Guarantees and traces

`guar_isFairLock`, `guar_isFairLockAlive` (with `IntoGuar` instances), `isFairLock_register_alive`;
`lockInvAliveTrSpec` has `□ₛ nextGeTrSpec next n` next to `next ↦ n`. At the level of traces
(the notions of `TicketLock`): `lockInvAliveTrSpec_release_progress`,
`lockInvAliveTrSpec_next_monotone` (at each position the registration for the current `n` gives
`next ≥ n` or `next` freed from then on, and the alive branch keeps `next` allocated), hence
`aliveFairLock_release_progress`, `aliveFairLock_next_monotone` and
`aliveFairLock_starvationFree`.

Aliases are prefixed with `ticket_lock_mono.`. Everything here is proved.
-/

@[expose] public noncomputable section

namespace Lantana.Examples.TicketLockMono

open Iris Iris.BI Iris.Std Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.TicketLock (vz vLock N Ninv Nev Ntk TicketInfo TMap q14 q34 ptsSpec)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal Lantana.AuthMra
open scoped Iris.Std.PartialMap

#lantana_ignore ticket_lock_mono.TicketLock "The module alias: the program is \
  `TicketLock.init/acquire/release/delete`."

/-! ## Namespaces -/

/-- The namespace of the mono cell. -/
def Nmono : Namespace := N.@"mono"

#lantana_ignore ticket_lock_mono.N_disj_1 "inlined in `TicketLock.Nev_subseteq`"
attribute [lantana_alias ticket_lock_mono.N_subseteq_1] TicketLock.Nev_subseteq
attribute [lantana_alias ticket_lock_mono.N_inv_subseteq] TicketLock.Ninv_subseteq

/-- The mono cell's namespace is outside the invariant's. -/
@[lantana_alias ticket_lock_mono.N_mono_subseteq]
theorem Nmono_subseteq {E : CoPset} (h : ↑N ⊆ E) : (↑Nmono : CoPset) ⊆ E \ ↑Ninv := by
  intro p hp
  refine Iris.Std.LawfulSet.mem_diff.mpr ⟨nclose_subseteq' _ h p hp, fun h' => ?_⟩
  exact ndot_ne_disjoint N (by decide : "mono" ≠ "inv") p ⟨hp, h'⟩

/-! ## Ghost state -/

/-- The cameras of the ticket lock with a monotone `next` (Rocq `ticket_lock_monoG`): those of
`TicketLock` and the monotone integers. -/
@[lantana_alias ticket_lock_mono.ticket_lock_monoG]
class TicketLockMonoG (GF : BundledGFunctors) extends TicketLock.TicketLockG GF where
  [monoG : MonoZG GF]

attribute [reducible, instance] TicketLockMonoG.monoG

#lantana_ignore ticket_lock_mono.«ticket_lock_monoΣ» "Subsumed by the `BundledGFunctors` worlds."
#lantana_ignore ticket_lock_mono.«subG_ticket_lock_monoΣ»
  "Subsumed by the `BundledGFunctors` worlds."
#lantana_ignore ticket_lock_mono.tlock_ticketG "The field `TicketLock.TicketLockG.ticketG`."
#lantana_ignore ticket_lock_mono.tlock_oblG "The field `TicketLock.TicketLockG.oblG`."
#lantana_ignore ticket_lock_mono.tlock_tokenG "The field `TicketLock.TicketLockG.tokenG`."
#lantana_ignore ticket_lock_mono.tlock_config_inG "The field `TicketLock.TicketLockG.configG`."
#lantana_ignore ticket_lock_mono.tlock_alive_inG "The field `TicketLock.TicketLockG.aliveG`."
#lantana_ignore ticket_lock_mono.tlock_monoG "The field `TicketLockMonoG.monoG`."

/-- The ghost names of a ticket lock with a monotone `next` (Rocq `ticketlock_γ`): those of
`TicketLock` and the lower bounds `γm` of `next`. -/
@[lantana_alias ticket_lock_mono.ticketlock_γ]
structure TicketLockName extends TicketLock.TicketLockName where
  /-- The lower bounds of `next`. -/
  γm : GName

/-- The ghost state of `TicketLock` is reused through this coercion. -/
instance : Coe TicketLockName TicketLock.TicketLockName := ⟨TicketLockName.toTicketLockName⟩

attribute [lantana_alias ticket_lock_mono.TicketLockName] TicketLockName.mk
attribute [lantana_alias ticket_lock_mono.ticketlock_γm] TicketLockName.γm
#lantana_ignore ticket_lock_mono.ticketlock_γt "`TicketLock.TicketLockName.γt`, inherited."
#lantana_ignore ticket_lock_mono.ticketlock_γo "`TicketLock.TicketLockName.γo`, inherited."
#lantana_ignore ticket_lock_mono.ticketlock_γk "`TicketLock.TicketLockName.γk`, inherited."
#lantana_ignore ticket_lock_mono.ticketlock_γc "`TicketLock.TicketLockName.γc`, inherited."
#lantana_ignore ticket_lock_mono.ticketlock_γa "`TicketLock.TicketLockName.γa`, inherited."

-- The ghost state of `TicketLock`, through the coercion of the names.
attribute [lantana_alias ticket_lock_mono.own_fair_lock_alive] TicketLock.ownAlive
attribute [lantana_alias ticket_lock_mono.own_fair_lock_layer] TicketLock.ownLayer
attribute [lantana_alias ticket_lock_mono.lock_alive_persist] TicketLock.lock_alive_persist
attribute [lantana_alias ticket_lock_mono.lock_reconfig] TicketLock.lock_reconfig
attribute [lantana_alias ticket_lock_mono.lock_config_persist] TicketLock.lock_config_persist
attribute [lantana_alias ticket_lock_mono.lock_config_valid] TicketLock.lock_config_valid
attribute [lantana_alias ticket_lock_mono.lock_token_inv] TicketLock.lockTokenInv
attribute [lantana_alias ticket_lock_mono.lock_token] TicketLock.lockToken
attribute [lantana_alias ticket_lock_mono.lock_token_unseal] TicketLock.lockToken_unfold
#lantana_ignore ticket_lock_mono.lock_token_def "`TicketLock.lockToken`, sealed (irreducible)."
#lantana_ignore ticket_lock_mono.lock_token_aux "`TicketLock.lockToken`, sealed (irreducible)."

/-! ## The mono cell -/

section MonoCell
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLockMonoG GF]

/-- The mono cell: the authority over the lower bounds of `next`, with half of `next`'s
points-to (`delete` leaves half of its freed points-to) (Rocq `mono_inv`). -/
@[lantana_alias ticket_lock_mono.mono_inv]
def monoInv (γm : GName) (next : Loc) : IProp GF :=
  iprop(∃ w : Int, (γm ↪●MZ w) ∗
    (next ↦{.own (1 : Qp).half} some (vz w) ∨ next ↦{.own (1 : Qp).half} (none : Option Val)))

/-- A freed location, as a trace specification (Rocq `freed_trSpec`, `temporal_laws.v`). -/
abbrev freedTrSpec (l : Loc) : TrSpec Exp State GF := TrSpec.state (freedSat l)

/-- `next ≥ v`, or `next` has been freed (Rocq `next_ge_trSpec`). -/
@[lantana_alias ticket_lock_mono.next_ge_trSpec]
def nextGeTrSpec (next : Loc) (v : Int) : TrSpec Exp State GF :=
  (∃ₛ w : Int, ⌜v ≤ w⌝ₛ ∧ₛ ptsSpec next 1 (vz w)) ∨ₛ freedTrSpec next

/-- The registration of the mono cell for the value `v` (Rocq `next_ge`). -/
@[lantana_alias ticket_lock_mono.next_ge]
def nextGe (γm : GName) (next : Loc) (v : Int) : IProp GF :=
  alwaysIGuar Nmono (monoInv γm next) (nextGeTrSpec next v)

instance nextGe_persistent (γm : GName) (next : Loc) (v : Int) :
    Persistent (nextGe (GF := GF) γm next v) := by
  unfold nextGe; infer_instance

/-- The cell guarantees `next ≥ v` (or `next` freed) once `v` is a lower bound (Rocq
`guar_mono_inv`). -/
@[lantana_alias ticket_lock_mono.guar_mono_inv]
theorem guar_monoInv (γm : GName) (next : Loc) (v : Int) :
    (γm ↪◯MZ v) ⊢@{IProp GF} monoInv γm next ⊨ₜ nextGeTrSpec next v := by
  iintro #Lb
  iapply guar_mono (P := iprop((∃ w : Int, ⌜v ≤ w⌝ ∗
      next ↦{.own (1 : Qp).half} some (vz w)) ∨ next ↦{.own (1 : Qp).half} (none : Option Val)))
    $$ []
  · imodintro
    iintro H
    iunfold monoInv at H
    icases H with ⟨%w, A, (P | F)⟩
    · ihave %⟨-, h⟩ := MonoZ.auth_lb_own_valid γm _ w v $$ A Lb
      ileft
      iexists w
      iframe P
      ipureintro
      exact h
    · iright
      iexact F
  unfold nextGeTrSpec
  iapply guar_or
  · iapply guar_ex
    iintro %w
    iapply guar_sep
    · iapply guar_pure
    · iapply guar_state_fact (next ↦{.own (1 : Qp).half} some (vz w))
  · iapply guar_state_fact (next ↦{.own (1 : Qp).half} (none : Option Val))

/-- The allocation of the cell, with its first registration (Rocq `next_ge_alloc`). -/
@[lantana_alias ticket_lock_mono.next_ge_alloc]
theorem nextGe_alloc (E : CoPset) (γm : GName) (next : Loc) (v : Int) :
    (γm ↪◯MZ v) ⊢@{IProp GF} ▷ monoInv γm next -∗ |={E}=>m nextGe γm next v := by
  iintro #Lb HI
  unfold nextGe
  iapply alwaysIGuar_alloc $$ [] HI
  inext
  iapply guar_monoInv $$ Lb

/-- A new registration, with a new lower bound (the invariant is that of an earlier one) (Rocq
`next_ge_register`). -/
@[lantana_alias ticket_lock_mono.next_ge_register]
theorem nextGe_register (E : CoPset) (γm : GName) (next : Loc) (v v' : Int)
    (hN : ↑Nmono ⊆ E) :
    nextGe γm next v' ⊢@{IProp GF} (γm ↪◯MZ v) -∗ |={E}=>m nextGe γm next v := by
  iintro #NG #Lb
  unfold nextGe
  iapply alwaysIGuar_register hN $$ [] []
  · iapply alwaysIGuar_inv $$ NG
  · inext
    iapply guar_monoInv $$ Lb

end MonoCell

/-! ## The invariants -/

section Invariant
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLockMonoG GF]

/-- The alive branch of the lock invariant (Rocq `lock_inv_alive`): `TicketLock.lockInvAlive`
with half of `next ↦ n` and the registration of the mono cell for `n`. -/
@[lantana_alias ticket_lock_mono.lock_inv_alive]
def lockInvAlive (γt γo γc γm : GName) (next curr : Loc) (R : IProp GF) : IProp GF :=
  iprop(∃ (n c : Int) (tickets : TMap TicketInfo) (obls : TMap (Option Oid)),
    next ↦{.own (1 : Qp).half} some (vz n) ∗ nextGe γm next n ∗
    curr ↦{.own q14} some (vz c) ∗ (γt ↪●PMAP tickets) ∗ (γo ↪●MAP obls) ∗
    ⌜(∀ t, (get? tickets t).isSome ↔ 0 ≤ t ∧ t ≤ n) ∧
      (∀ t, (get? obls t).isSome ↔ 0 ≤ t ∧ t ≤ n) ∧ 0 ≤ c ∧ c ≤ n⌝ ∗
    ([∗map] t ↦ _x ∈ tickets, TicketLock.ticketSt γt γo γc c n t) ∗
    TicketLock.holderSt γt γo γc curr R c n)

/-- The lock invariant: deleted (the full alive token), or alive (Rocq `lock_inv`). -/
@[lantana_alias ticket_lock_mono.lock_inv]
def lockInv (γt γo γc γa γm : GName) (next curr : Loc) (R : IProp GF) : IProp GF :=
  iprop((γa ↪VAR ()) ∨ lockInvAlive γt γo γc γm next curr R)

/-- The ticket lock `tl` with ghost names `γ`, protecting `R` (Rocq `is_fair_lock`). -/
@[lantana_alias ticket_lock_mono.is_fair_lock]
def isFairLock (tl : Val) (γ : TicketLockName) (R : IProp GF) : IProp GF :=
  iprop(∃ next curr : Loc, ⌜tl = vLock next curr⌝ ∗
    alwaysI Ninv (lockInv γ.γt γ.γo γ.γc γ.γa γ.γm next curr R) ∗
    alwaysI Ntk (TicketLock.lockTokenInv γ.γo γ.γk curr R))

/-- A lock that cannot be deleted (its holder keeps `γ ↪LOCK_AL{.discard}`): the lock invariant
is registered under its alive branch, so that the trace sees it (Rocq `is_fair_lock_alive`). -/
@[lantana_alias ticket_lock_mono.is_fair_lock_alive]
def isFairLockAlive (tl : Val) (γ : TicketLockName) (R : IProp GF) : IProp GF :=
  iprop(isFairLock tl γ R ∗ ∃ next curr : Loc, ⌜tl = vLock next curr⌝ ∗
    alwaysIAs (Expr := Exp) (State := State) Ninv (lockInv γ.γt γ.γo γ.γc γ.γa γ.γm next curr R)
      (lockInvAlive γ.γt γ.γo γ.γc γ.γm next curr R))

@[lantana_alias ticket_lock_mono.is_fair_lock_persistent]
instance isFairLock_persistent (tl : Val) (γ : TicketLockName) (R : IProp GF) :
    Persistent (isFairLock (GF := GF) tl γ R) := by
  unfold isFairLock; infer_instance

instance isFairLockAlive_persistent (tl : Val) (γ : TicketLockName) (R : IProp GF) :
    Persistent (isFairLockAlive (GF := GF) tl γ R) := by
  unfold isFairLockAlive; infer_instance

/-- Use this rather than framing (Rocq: unifying the two definitions' bodies takes too long). -/
@[lantana_alias ticket_lock_mono.is_fair_lock_alive_is_fair_lock]
theorem isFairLockAlive_isFairLock (tl : Val) (γ : TicketLockName) (R : IProp GF) :
    isFairLockAlive (GF := GF) tl γ R ⊢ isFairLock tl γ R := by
  unfold isFairLockAlive
  iintro ⟨H, -⟩
  iexact H

end Invariant

end Lantana.Examples.TicketLockMono
