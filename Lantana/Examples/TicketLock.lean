/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.Instances.Lib.GhostVar
public import Iris.Instances.Lib.GhostMap
public import Lantana.Algebra.AuthMra
public import Lantana.Examples.GhostMapP
public import Lantana.Examples.Lib

/-! # A ticket lock that can be deleted

Rocq `examples/ticket_lock.v` (§7.1 of the paper).
-/

@[expose] public noncomputable section

namespace Lantana.Examples.TicketLock

open Iris Iris.BI Iris.Std Lantana Lantana.HeapLang Lantana.Language
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal Lantana.AuthMra

/-! ## The program -/

/-- `λ _, (ref 0, ref 0)`: the pair `(next, curr)` of the next ticket and the ticket served. -/
@[lantana_alias TicketLock.init]
def init : Val := hl_val(λ _, (ref(#0), ref(#0)))

/-- Take a ticket (`faa next 1`) and wait until it is served. -/
@[lantana_alias TicketLock.acquire]
def acquire : Val := hl_val(λ lnc, let next := fst(lnc); let curr := snd(lnc);
  let my := faa(next, #1); (rec loop _ := if !curr = my then #() else loop #()) #())

/-- Serve the next ticket. -/
@[lantana_alias TicketLock.release]
def release : Val := hl_val(λ lnc, let curr := snd(lnc); curr ← !curr + #1)

/-- Increment `curr` as `release` does (this discharges the holder's `finallyI`), then free
both cells. -/
@[lantana_alias TicketLock.delete]
def delete : Val := hl_val(λ lnc, let next := fst(lnc); let curr := snd(lnc);
  curr ← !curr + #1; free(next); free(curr))

/-- The integer `n` as a value. -/
abbrev vz (n : Int) : Val := .lit (.int n)

/-- The unit value. -/
abbrev vUnit : Val := .lit .unit

/-- The lock `(next, curr)`. -/
abbrev vLock (next curr : Loc) : Val := .pair (.lit (.loc next)) (.lit (.loc curr))

/-- The namespaces of the lock. -/
def N : Namespace := nroot.@"ticket_lock"
def Ninv : Namespace := N.@"inv"
def Nev : Namespace := N.@"ev"
def Ntk : Namespace := N.@"token"

theorem Ninv_subseteq {E : CoPset} (h : ↑N ⊆ E) : (↑Ninv : CoPset) ⊆ E :=
  nclose_subseteq' _ h

theorem Ntk_subseteq {E : CoPset} (h : ↑N ⊆ E) : (↑Ntk : CoPset) ⊆ E :=
  nclose_subseteq' _ h

/-- The events' namespace is outside the invariant's. -/
@[lantana_alias N_subseteq_1]
theorem Nev_subseteq {E : CoPset} (h : ↑N ⊆ E) : (↑Nev : CoPset) ⊆ E \ ↑Ninv := by
  intro p hp
  refine Iris.Std.LawfulSet.mem_diff.mpr ⟨nclose_subseteq' _ h p hp, fun h' => ?_⟩
  exact ndot_ne_disjoint N (by decide : "ev" ≠ "inv") p ⟨hp, h'⟩

/-! ## Ghost state -/

/-- What the ticket map records of a waiting ticket: its container, the layer of the container
and the measure of the unlock obligation it will get; `none` once served. -/
abbrev TicketInfo := Option (Oid × Layer × Measure)

/-- Finite maps from tickets. -/
abbrev TMap (V : Type _) := Std.ExtTreeMap Int V compare

/-- The cameras of the ticket lock (Rocq `ticket_lockG`): the ticket map (with layers and
measures, hence `GhostMapPG`), the map of unlock obligations, the ghost variable of the lock
token, the authoritative layer of the lock (`AuthMra` on layers) and the alive token (a ghost
variable of `Unit`, Rocq's `dfrac_agreeR unit`). -/
@[lantana_alias ticket_lockG]
class TicketLockG (GF : BundledGFunctors) where
  [ticketG : GhostMapPG GF Int TicketInfo (Std.ExtTreeMap Int · compare)]
  [oblG : GhostMapG GF Int (Option Oid) (Std.ExtTreeMap Int · compare)]
  [tokenG : GhostVarG GF Int]
  configG : ElemG GF (constOFP (AuthMra (α := Layer) (· ≤ ·)))
  [aliveG : GhostVarG GF Unit]

attribute [reducible, instance] TicketLockG.ticketG TicketLockG.oblG TicketLockG.tokenG
  TicketLockG.configG TicketLockG.aliveG

#lantana_ignore «ticket_lockΣ» "Subsumed by the `BundledGFunctors` worlds."
#lantana_ignore «subG_ticket_lockΣ» "Subsumed by the `BundledGFunctors` worlds."

/-- The ghost names of a ticket lock (Rocq `ticketlock_γ`). -/
@[lantana_alias ticketlock_γ]
structure TicketLockName where
  /-- The ticket map. -/
  γt : GName
  /-- The map of unlock obligations. -/
  γo : GName
  /-- The lock token. -/
  γk : GName
  /-- The layer of the lock. -/
  γc : GName
  /-- The alive token. -/
  γa : GName

attribute [lantana_alias TicketLockName] TicketLockName.mk
attribute [lantana_alias ticketlock_γt] TicketLockName.γt
attribute [lantana_alias ticketlock_γo] TicketLockName.γo
attribute [lantana_alias ticketlock_γk] TicketLockName.γk
attribute [lantana_alias ticketlock_γc] TicketLockName.γc
attribute [lantana_alias ticketlock_γa] TicketLockName.γa

section Ghost
variable {GF : BundledGFunctors} [TicketLockG GF]

/-- The alive token: the full one deletes the lock (Rocq `own_fair_lock_alive`). -/
@[lantana_alias own_fair_lock_alive]
def ownAlive (γ : TicketLockName) (dq : DFrac) : IProp GF :=
  ghost_var γ.γa dq ()

/-- The layer of the lock (Rocq `own_fair_lock_layer`). -/
@[lantana_alias own_fair_lock_layer]
def ownLayer (γ : TicketLockName) (ℓ : Layer) (dq : DFrac) : IProp GF :=
  iOwn (E := TicketLockG.configG) γ.γc (●AM{dq}[(· ≤ ·)] ℓ)

/-- A lower bound of the layer of the lock (Rocq `own γc (◯AM[ord.le] ℓ)`). -/
def layerLb (γc : GName) (ℓ : Layer) : IProp GF :=
  iOwn (E := TicketLockG.configG) γc (◯AM[(· ≤ ·)] ℓ)

instance layerLb_persistent (γc : GName) (ℓ : Layer) : Persistent (layerLb (GF := GF) γc ℓ) := by
  unfold layerLb; infer_instance

@[inherit_doc ownAlive] notation γ " ↪LOCK_AL{" dq "}" => ownAlive γ dq
@[inherit_doc ownAlive] notation γ " ↪LOCK_AL" => ownAlive γ (DFrac.own 1)
@[inherit_doc ownLayer] notation γ " ↪LOCK_CF{" dq "} " l => ownLayer γ l dq
@[inherit_doc ownLayer] notation γ " ↪LOCK_CF " l => ownLayer γ l (DFrac.own 1)

/-! ### Ghost-state lemmas -/

@[lantana_alias lock_alive_persist]
theorem lock_alive_persist (γ : TicketLockName) (dq : DFrac) :
    (γ ↪LOCK_AL{dq}) ⊢@{IProp GF} |==> γ ↪LOCK_AL{.discard} := by
  unfold ownAlive
  iintro H
  iapply ghost_var_persist $$ H

/-- An alive token and the full one (the deleted lock) are incompatible. -/
theorem ownAlive_full_false (γ : TicketLockName) (dq : DFrac) :
    (γ ↪LOCK_AL{dq}) ⊢@{IProp GF} (γ.γa ↪VAR ()) -∗ False := by
  unfold ownAlive
  iintro H1 H2
  ihave %⟨h, -⟩ := ghost_var_valid_2 _ _ _ _ _ $$ H1 H2
  exact absurd (DFrac.valid_op_own h) (by simp)

@[lantana_alias lock_reconfig]
theorem lock_reconfig (γ : TicketLockName) {ℓ₁ ℓ₂ : Layer} (h : ℓ₁ ≤ ℓ₂) :
    (γ ↪LOCK_CF ℓ₁) ⊢@{IProp GF} |==> γ ↪LOCK_CF ℓ₂ := by
  unfold ownLayer
  exact iOwn_update (AuthMra.update h)

@[lantana_alias lock_config_persist]
theorem lock_config_persist (γ : TicketLockName) (dq : DFrac) (ℓ : Layer) :
    (γ ↪LOCK_CF{dq} ℓ) ⊢@{IProp GF} |==> γ ↪LOCK_CF{.discard} ℓ := by
  unfold ownLayer
  exact iOwn_update (AuthMra.auth_persist ℓ dq)

@[lantana_alias lock_config_valid]
theorem lock_config_valid (γ : TicketLockName) (dq₁ dq₂ : DFrac) (ℓ₁ ℓ₂ : Layer) :
    (γ ↪LOCK_CF{dq₁} ℓ₁) ⊢@{IProp GF} (γ ↪LOCK_CF{dq₂} ℓ₂) -∗ ⌜✓ (dq₁ • dq₂) ∧ ℓ₁ = ℓ₂⌝ := by
  unfold ownLayer
  iintro H1 H2
  icombine H1 H2 gives %h
  ipureintro
  exact AuthMra.auth_dfrac_op_valid.mp h

/-- The layer of the lock is above its lower bounds. -/
theorem ownLayer_lb (γ : TicketLockName) (dq : DFrac) (ℓ : Layer) :
    (γ ↪LOCK_CF{dq} ℓ) ⊢@{IProp GF} (γ ↪LOCK_CF{dq} ℓ) ∗ layerLb γ.γc ℓ := by
  unfold ownLayer layerLb
  refine (BIBase.BiEntails.of_eq ?_).1.trans iOwn_op.1
  exact congrArg _ (AuthMra.auth_know_op dq ℓ)

theorem ownLayer_lb_le (γ : TicketLockName) (dq : DFrac) (ℓ ℓ' : Layer) :
    (γ ↪LOCK_CF{dq} ℓ) ⊢@{IProp GF} layerLb γ.γc ℓ' -∗ ⌜ℓ' ≤ ℓ⌝ := by
  unfold ownLayer layerLb
  iintro H1 H2
  icombine H1 H2 gives %h
  ipureintro
  exact (AuthMra.both_dfrac_valid.mp h).2

end Ghost


/-! ## The invariants -/

section Invariant
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLockG GF]

/-- The fractions of `curr`: a quarter in the lock invariant, three quarters with the holder. -/
abbrev q14 : Qp := Qp.quarter
abbrev q34 : Qp := Qp.threeQuarters

/-- The holder's part of `curr` after its release, and the lock's resource: what the holder's
`finallyI` promises. -/
abbrev released (curr : Loc) (c : Int) (R : IProp GF) : IProp GF :=
  iprop(curr ↦{.own q34} some (vz (c + 1)) ∗ R)

/-- The lock token's invariant: nobody holds the lock (the full ghost variable), or the holder of
ticket `c + 1` (half of the variable) with its part of `curr` and its unlock obligation `κ`, to
be incremented eventually (Rocq `lock_token_inv`). -/
@[lantana_alias lock_token_inv]
def lockTokenInv (γo γk : GName) (curr : Loc) (R : IProp GF) : IProp GF :=
  iprop(∃ c : Int, (γk ↪VAR c) ∨
    (∃ κ : Oid, (γk ↪VAR{.own (1 : Qp).half} c) ∗ curr ↦{.own q34} some (vz c) ∗
      (γo ↪◯MAP[c + 1]{.discard} some κ) ∗ finallyI Nev κ (1 : Qp).half (released curr c R)))

/-- The state of ticket `t` when `c` is served and `n` was taken last: finished (with its unlock
obligation discharged), the next one, or waiting in its container `g` at layer `ℓ`. -/
def ticketSt (γt γo γc : GName) (c n t : Int) : IProp GF :=
  iprop((∃ κ : Oid, ⌜0 ≤ t ∧ t ≤ c⌝ ∗ (γt ↪◯PMAP[t]{.discard} (none : TicketInfo)) ∗
      (γo ↪◯MAP[t]{.discard} some κ) ∗ Obl.discharged κ) ∨
    ⌜t = c + 1⌝ ∨
    (∃ (g : Oid) (ℓ : Layer) (μ : Measure), ⌜c + 1 < t ∧ t ≤ n⌝ ∗
      (γt ↪◯PMAP[t]{.own (1 : Qp).half} (some (g, ℓ, μ) : TicketInfo)) ∗
      (γo ↪◯MAP[t] (none : Option Oid)) ∗ layerLb γc ℓ ∗ oblKids g ∅ ∗ Wit.layer g ℓ))

/-- The next owner, not yet aware of its turn: its container `g` holds the unlock obligation `κ`
that the releasing thread allocated, with fuel `μ`, and the lock's resources. -/
def nextOwner (γt : GName) (curr : Loc) (R : IProp GF) (c : Int) (ℓ : Layer) (κ : Oid) :
    IProp GF :=
  iprop(∃ (g : Oid) (μ : Measure),
    (γt ↪◯PMAP[c + 1]{.own (1 : Qp).half} (some (g, ℓ, μ) : TicketInfo)) ∗
    finallyI Nev κ (1 : Qp).half (released curr c R) ∗ oblKids g {κ} ∗ oblKids κ ∅ ∗
    Obl.fuel κ ℓ μ ∗ curr ↦{.own q34} some (vz c) ∗ R)

/-- The lock is free (`c = n`), or ticket `c + 1` holds it or is about to, with its unlock
obligation `κ` (Rocq: the last conjunct of `lock_inv_alive`). -/
def holderSt (γt γo γc : GName) (curr : Loc) (R : IProp GF) (c n : Int) : IProp GF :=
  iprop((⌜c = n⌝ ∗ curr ↦{.own q34} some (vz c) ∗ R) ∨
    (⌜c < n⌝ ∗ ∃ (ℓ : Layer) (κ : Oid), layerLb γc ℓ ∗ Wit.layer κ ℓ ∗
      (γo ↪◯MAP[c + 1]{.discard} some κ) ∗ finallyI Nev κ (1 : Qp).half (released curr c R) ∗
      (nextOwner γt curr R c ℓ κ ∨ (γt ↪◯PMAP[c + 1]{.discard} (none : TicketInfo)))))

/-- The alive branch of the lock invariant (Rocq `lock_inv_alive`). Rocq's `dom tickets = dom
obls` and `t ∈ dom tickets ↔ 0 ≤ t ≤ n` are the two domain conditions here. -/
@[lantana_alias lock_inv_alive]
def lockInvAlive (γt γo γc : GName) (next curr : Loc) (R : IProp GF) : IProp GF :=
  iprop(∃ (n c : Int) (tickets : TMap TicketInfo) (obls : TMap (Option Oid)),
    next ↦ some (vz n) ∗ curr ↦{.own q14} some (vz c) ∗ (γt ↪●PMAP tickets) ∗
    (γo ↪●MAP obls) ∗
    ⌜(∀ t, (get? tickets t).isSome ↔ 0 ≤ t ∧ t ≤ n) ∧
      (∀ t, (get? obls t).isSome ↔ 0 ≤ t ∧ t ≤ n) ∧ 0 ≤ c ∧ c ≤ n⌝ ∗
    ([∗map] t ↦ _x ∈ tickets, ticketSt γt γo γc c n t) ∗ holderSt γt γo γc curr R c n)

/-- The lock invariant: deleted (the full alive token), or alive (Rocq `lock_inv`). -/
@[lantana_alias lock_inv]
def lockInv (γt γo γc γa : GName) (next curr : Loc) (R : IProp GF) : IProp GF :=
  iprop((γa ↪VAR ()) ∨ lockInvAlive γt γo γc next curr R)

/-- The ticket lock `tl` with ghost names `γ`, protecting `R` (Rocq `is_fair_lock`). -/
@[lantana_alias is_fair_lock]
def isFairLock (tl : Val) (γ : TicketLockName) (R : IProp GF) : IProp GF :=
  iprop(∃ next curr : Loc, ⌜tl = vLock next curr⌝ ∗
    alwaysI Ninv (lockInv γ.γt γ.γo γ.γc γ.γa next curr R) ∗
    alwaysI Ntk (lockTokenInv γ.γo γ.γk curr R))

/-- A lock that cannot be deleted (its holder keeps `γ ↪LOCK_AL{.discard}`): the lock invariant
is registered under its alive branch, so that the trace sees it (Rocq `is_fair_lock_alive`). -/
@[lantana_alias is_fair_lock_alive]
def isFairLockAlive (tl : Val) (γ : TicketLockName) (R : IProp GF) : IProp GF :=
  iprop(isFairLock tl γ R ∗ ∃ next curr : Loc, ⌜tl = vLock next curr⌝ ∗
    alwaysIAs (Expr := Exp) (State := State) Ninv (lockInv γ.γt γ.γo γ.γc γ.γa next curr R)
      (lockInvAlive γ.γt γ.γo γ.γc next curr R))

/-- The lock token of the holder of the unlock obligation `κu` (Rocq `lock_token`, sealed). -/
@[lantana_alias lock_token, irreducible]
def lockToken (γ : TicketLockName) (κu : Oid) : IProp GF :=
  iprop(∃ c : Int, (γ.γk ↪VAR{.own (1 : Qp).half} c) ∗
    (γ.γt ↪◯PMAP[c + 1]{.discard} (none : TicketInfo)) ∗ (γ.γo ↪◯MAP[c + 1]{.discard} some κu))

omit [ModelGS GF] [HeapGS GF] in
@[lantana_alias lock_token_unseal]
theorem lockToken_unfold (γ : TicketLockName) (κu : Oid) :
    lockToken (GF := GF) γ κu = iprop(∃ c : Int, (γ.γk ↪VAR{.own (1 : Qp).half} c) ∗
      (γ.γt ↪◯PMAP[c + 1]{.discard} (none : TicketInfo)) ∗
      (γ.γo ↪◯MAP[c + 1]{.discard} some κu)) := by
  unfold lockToken; rfl

@[lantana_alias is_fair_lock_persistent]
instance isFairLock_persistent (tl : Val) (γ : TicketLockName) (R : IProp GF) :
    Persistent (isFairLock (GF := GF) tl γ R) := by
  unfold isFairLock; infer_instance

instance isFairLockAlive_persistent (tl : Val) (γ : TicketLockName) (R : IProp GF) :
    Persistent (isFairLockAlive (GF := GF) tl γ R) := by
  unfold isFairLockAlive; infer_instance

/-- Use this rather than framing (Rocq: unifying the two definitions' bodies takes too long). -/
@[lantana_alias is_fair_lock_alive_is_fair_lock]
theorem isFairLockAlive_isFairLock (tl : Val) (γ : TicketLockName) (R : IProp GF) :
    isFairLockAlive (GF := GF) tl γ R ⊢ isFairLock tl γ R := by
  unfold isFairLockAlive
  iintro ⟨H, -⟩
  iexact H

end Invariant

end Lantana.Examples.TicketLock
