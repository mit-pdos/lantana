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
open scoped Iris.Std.PartialMap

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

section GhostVarHalves
variable {A : Type} [GhostVarG GF A]

omit [TicketLockG GF] in
/-- A ghost variable is two halves. -/
theorem ghostVar_halves (γ : GName) (a : A) :
    (γ ↪VAR a) ⊢@{IProp GF} (γ ↪VAR{.own (1 : Qp).half} a) ∗ (γ ↪VAR{.own (1 : Qp).half} a) := by
  have h := ghost_var_split (GF := GF) γ a (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  iintro H
  iapply h $$ H

omit [TicketLockG GF] in
/-- Two halves of a ghost variable agree, and make the whole. -/
theorem ghostVar_combine_halves (γ : GName) (a b : A) :
    (γ ↪VAR{.own (1 : Qp).half} a) ∗ (γ ↪VAR{.own (1 : Qp).half} b) ⊢@{IProp GF}
      (γ ↪VAR a) ∗ ⌜a = b⌝ := by
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_agree γ a _ b _ $$ H1 H2
  subst h
  icombine H1 H2 as H
  iframe H
  ipureintro
  rfl

omit [TicketLockG GF] in
/-- A half and a whole of a ghost variable are incompatible. -/
theorem ghostVar_half_whole_false (γ : GName) (a b : A) :
    (γ ↪VAR{.own (1 : Qp).half} a) ∗ (γ ↪VAR b) ⊢@{IProp GF} False := by
  iintro ⟨H1, H2⟩
  ihave %⟨h, -⟩ := ghost_var_valid_2 γ a _ b _ $$ H1 H2
  have := DFrac.valid_op_own h
  simp at this

end GhostVarHalves

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

/-! ### The tickets when the lock changes -/

omit [HeapGS GF] in
/-- A new ticket taken: the bound `n` grows. -/
theorem ticketSt_mono_n (γt γo γc : GName) {c n n' : Int} (t : Int) (h : n ≤ n') :
    ticketSt (GF := GF) γt γo γc c n t ⊢ ticketSt γt γo γc c n' t := by
  unfold ticketSt
  iintro (H | H | ⟨%g, %ℓ, %μ, %ht, H⟩)
  · ileft
    iexact H
  · iright
    ileft
    iexact H
  · iright
    iright
    iexists g, ℓ, μ
    iframe H
    ipureintro
    omega

omit [HeapGS GF] in
/-- The ticket `c + 1` is served (its unlock obligation `κu` is discharged): every ticket but
`c + 2` keeps its state for `c + 1`. -/
theorem ticketSt_release (γt γo γc : GName) {c n : Int} (κu : Oid) (t : Int) (hc : 0 ≤ c)
    (ht : t ≠ c + 1 + 1) :
    (γt ↪◯PMAP[c + 1]{.discard} (none : TicketInfo)) ⊢@{IProp GF}
      (γo ↪◯MAP[c + 1]{.discard} some κu) -∗ Obl.discharged κu -∗
      ticketSt γt γo γc c n t -∗ ticketSt γt γo γc (c + 1) n t := by
  unfold ticketSt
  iintro #Ht #Ho #Hd (⟨%κ, %h, H⟩ | %h | ⟨%g, %ℓ, %μ, %h, H⟩)
  · ileft
    iexists κ
    iframe H
    ipureintro
    omega
  · subst h
    ileft
    iexists κu
    iframe Ht Ho Hd
    ipureintro
    omega
  · iright
    iright
    iexists g, ℓ, μ
    iframe H
    ipureintro
    omega

end Invariant

/-! ## Specifications

Specs hide implementation details such as the number of steps, so that they survive changes of
the fuel (Rocq): a function that terminates without witness induction has layer `0` and an
`∃ μ` in front of its spec. -/

section Specs
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLockG GF]

omit [ModelGS GF] [TicketLockG GF] in
/-- A points-to is a quarter and three quarters. -/
theorem pointsTo_quarters (l : Loc) (v : Option Val) :
    l ↦ v ⊣⊢@{IProp GF} l ↦{.own q14} v ∗ l ↦{.own q34} v := by
  have h := (inferInstance : Fractional (PROP := IProp GF) (l ↦{.own ·} v)).fractional
    q14 q34
  rw [Qp.quarter_add_threeQuarters] at h
  exact h

@[lantana_alias TicketLock_init_spec]
theorem init_spec : ∃ μ : Measure, ∀ (lc : Fuel) (ℓ : Layer) (i : ThreadId) (G : Oids)
    (E : CoPset) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&init) #()) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) }}}
        hl(v(&init) #()) @ i; E
      l{{{ (tl : Val) (γ : TicketLockName), RET tl; threadExpr i C hl(&tl) ∗ £ₒ lc ∗
        thKids i G ∗ (γ ↪LOCK_AL) ∗ (γ ↪LOCK_CF ℓ) ∗
        (∀ (E₁ : CoPset) (R : IProp GF), R -∗ |={E₁}=>m isFairLock tl γ R) }}} := by
  refine ⟨10, fun lc ℓ i G E C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF⟩ HΦ
  ihave HF := oblFuels_init G 10 0 $$ HF
  unfold init
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(ref(#0)) HT
  icases oblFuels_add 1 8 G $$ HF with ⟨HF1, HF⟩
  iapply lwp_alloc (o := 0) (G := G) (R := ∅) $$ [HT HG HF1]
  · iframe HT
    iapply stepPre_nil $$ HG HF1
  iintro %curr ⟨HT, ⟨-, HG, -⟩, Hcurr⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_bind hl(ref(#0)) HT
  icases oblFuels_add 1 7 G $$ HF with ⟨HF1, HF⟩
  iapply lwp_alloc (o := 0) (G := G) (R := ∅) $$ [HT HG HF1]
  · iframe HT
    iapply stepPre_nil $$ HG HF1
  iintro %next ⟨HT, ⟨-, HG, -⟩, Hnext⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF with Hlc : lc
  imod Obl.new_discharged E ℓ with ⟨%κu, #Dk, -⟩
  imod ghostMapP_alloc (GF := GF) (K := Int) (V := TicketInfo) (H := TMap)
    ({[0 := none]} : TMap TicketInfo) with ⟨%γt, Ht, Hte⟩
  ihave Hte := BigSepM.bigSepM_singleton.mp $$ Hte
  imod ghostMapP_elem_persist $$ Hte with #Hte
  imod ghost_map_alloc (GF := GF) (K := Int) (V := Option Oid) (H := TMap)
    ({[0 := some κu]} : TMap (Option Oid)) with ⟨%γo, Ho, Hoe⟩
  ihave Hoe := BigSepM.bigSepM_singleton.mp $$ Hoe
  imod ghost_map_elem_persist $$ Hoe with #Hoe
  imod ghost_var_alloc (GF := GF) () with ⟨%γa, Ha⟩
  imod ghost_var_alloc (GF := GF) (0 : Int) with ⟨%γk, Hk⟩
  imod iOwn_alloc (E := TicketLockG.configG) (●AM[(· ≤ ·)] ℓ) AuthMra.auth_valid with ⟨%γc, Hc⟩
  icases (pointsTo_quarters curr _).mp $$ Hcurr with ⟨Hcurr, Hcurr34⟩
  iapply lwp_value'
  iapply HΦ $$ %(vLock next curr) %⟨γt, γo, γk, γc, γa⟩
  iframe HT Hlc HG
  isplitl [Ha]
  · unfold ownAlive
    iexact Ha
  isplitl [Hc]
  · unfold ownLayer
    iexact Hc
  iintro %E₁ %R HR
  imod alwaysI_alloc (E := E₁) (N := Ninv) (P := lockInv γt γo γc γa next curr R) $$
    [Hnext Hcurr Hcurr34 Ht Ho HR] with #HI
  · inext
    unfold lockInv lockInvAlive
    iright
    iexists 0, 0, ({[0 := none]} : TMap TicketInfo), ({[0 := some κu]} : TMap (Option Oid))
    iframe Hnext Hcurr Ht Ho
    isplitr
    · ipureintro
      refine ⟨fun t => ?_, fun t => ?_, by omega, by omega⟩ <;>
        · rw [LawfulPartialMap.get?_singleton]
          grind
    isplitl []
    · iapply BigSepM.bigSepM_singleton.mpr
      unfold ticketSt
      ileft
      iexists κu
      iframe Hte Hoe Dk
      ipureintro
      omega
    · unfold holderSt
      ileft
      iframe Hcurr34 HR
      ipureintro
      rfl
  imod alwaysI_alloc (E := E₁) (N := Ntk) (P := lockTokenInv γo γk curr R) $$ [Hk] with #HK
  · inext
    unfold lockTokenInv
    iexists 0
    ileft
    iexact Hk
  imodintro
  unfold isFairLock
  iexists next, curr
  isplitr
  · ipureintro
    rfl
  iframe HI HK

/-- The holder of ticket `c + 1` exchanges its half of the token's ghost variable for its part
of `curr` and its half of the `finallyI` on its unlock obligation `κu`. -/
theorem lockToken_exchange (E : CoPset) (hE : ↑N ⊆ E) (γ : TicketLockName) (curr : Loc)
    (R : IProp GF) (κu : Oid) (c : Int) :
    alwaysI (Expr := Exp) (State := State) Ntk (lockTokenInv γ.γo γ.γk curr R) ⊢ £ₙ 1 -∗
      (γ.γk ↪VAR{.own (1 : Qp).half} c) -∗ (γ.γo ↪◯MAP[c + 1]{.discard} some κu) -∗
      |={E}=> curr ↦{.own q34} some (vz c) ∗ finallyI Nev κu (1 : Qp).half (released curr c R) := by
  iintro #ITK Hc1 GV #GMEo
  ihave Hacc := alwaysI_acc (E := E) (N := Ntk) (P := lockTokenInv γ.γo γ.γk curr R)
    (Ntk_subseteq hE) $$ ITK
  imod Hacc with ⟨H, Hclose⟩
  imod lc_fupd_elim_later $$ Hc1 H with H
  iunfold lockTokenInv at H
  icases H with ⟨%c', (TK | ⟨%κ, GV0, PtrCurr0, #GMEo0, GEku⟩)⟩
  · iexfalso
    iapply ghostVar_half_whole_false $$ [GV TK]
    iframe
  ihave %h := ghost_var_agree _ _ _ _ _ $$ GV0 GV
  subst h
  ihave %h := ghost_map_elem_agree _ _ _ _ (some κu) (some κ) $$ [GMEo GMEo0]
  · iframe GMEo GMEo0
  cases h
  icases ghostVar_combine_halves _ _ _ $$ [GV0 GV] with ⟨GV, -⟩
  · iframe
  imod Hclose $$ [GV] with -
  · inext
    iunfold lockTokenInv
    iexists c'
    ileft
    iexact GV
  imodintro
  iframe

@[lantana_alias TicketLock_release_spec]
theorem release_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids) (tl : Val)
    (γ : TicketLockName) (dq : DFrac) (R : IProp GF) (κu : Oid) (E : CoPset) (_ : ↑N ⊆ E)
    (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&release) v(&tl)) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ ⌜κu ∈ G⌝ ∗ oblKids κu ∅ ∗ lockToken γ κu ∗ R ∗
          (γ ↪LOCK_AL{dq}) ∗ isFairLock tl γ R }}}
        hl(v(&release) v(&tl)) @ i; E
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i (G.erase κu) ∗
        (γ ↪LOCK_AL{dq}) }}} := by
  refine ⟨10, fun lc i G tl γ dq R κu E hE C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hκu, Kku, LT, HR, AL, #IFL⟩ HΦ
  ihave HF := oblFuels_init G 10 0 $$ HF
  rw [lockToken_unfold]
  icases LT with ⟨%c, GV, #GMEtku, #GMEo⟩
  unfold isFairLock
  icases IFL with ⟨%next, %curr, %htl, #INV, #ITK⟩
  subst htl
  unfold release
  lwp_step HT HG HF with Hlc : lc +ₕ 1 +ₕ 1 +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc3⟩
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc2⟩
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc1⟩
  -- Exchange the token.
  ihave Hc1 := tlc_one_nat.mpr $$ Hc1
  imod lockToken_exchange E hE γ curr R κu c $$ ITK Hc1 GV GMEo with ⟨PtrCurr0, GEku⟩
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(!#curr) HT
  icases oblFuels_add 1 5 G $$ HF with ⟨HF1, HF⟩
  iapply lwp_load (o := 0) (G := G) (R := ∅) $$ [HT HG HF1 PtrCurr0]
  · iframe HT PtrCurr0
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, PtrCurr0⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  -- The store, in the lock invariant.
  ihave Hacc := alwaysI_acc (E := E) (N := Ninv)
    (P := lockInv γ.γt γ.γo γ.γc γ.γa next curr R) (Ninv_subseteq hE) $$ INV
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨H, Hclose⟩
  iclear Hacc
  iapply lwp_credit_later $$ Hc2
  inext
  iunfold lockInv at H
  icases H with (Hdel | H)
  · iexfalso
    iapply ownAlive_full_false $$ AL Hdel
  iunfold lockInvAlive at H
  icases H with ⟨%n, %c', %tickets, %obls, PtrNext, PtrCurr, GMAt, GMAo, %⟨Domt, Domo, hc0, hcn⟩,
    HMt, Hc⟩
  ihave %h := pointsTo_agree (l := curr) $$ [PtrCurr PtrCurr0]
  · iframe
  obtain rfl : c = c' := by simpa [vz] using h.symm
  ihave PtrCurr := (pointsTo_quarters curr _).mpr $$ [PtrCurr PtrCurr0]
  · iframe
  ihave %hlt := ghostMapP_lookup $$ GMAt GMEtku
  have hc1 := (Domt (c + 1)).mp (by simp [hlt])
  iunfold holderSt at Hc
  icases Hc with (⟨%hcn', -⟩ | ⟨%hcn', %ℓ0, %κ, #CFl, #Wl, #GMEo1, HE, -⟩)
  · iexfalso
    ipureintro
    omega
  ihave %h := ghost_map_elem_agree _ _ _ _ (some κu) (some κ) $$ [GMEo GMEo1]
  · iframe GMEo GMEo1
  cases h
  iunfold finallyI at GEku HE
  ihave HU := untilI_frac_add (q := 1) (Qp.half_add_half 1).symm $$ GEku HE
  ihave HU := untilI_discharge (E := E \ ↑Ninv) (Nev_subseteq hE) $$ HU
  ihave HU := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ HU
  imod HU
  iapply lwp_credit_later $$ Hc3
  inext
  icases HU with ⟨-, Hdis⟩
  icases oblFuels_add 1 3 G $$ HF with ⟨HF1, -⟩
  iapply lwp_store (o := 0) (G := G) (R := ∅) $$ [HT HG HF1 PtrCurr]
  · iframe HT PtrCurr
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, PtrCurr⟩
  icases (pointsTo_quarters curr _).mp $$ PtrCurr with ⟨PtrCurr, PtrCurr34⟩
  imod Hdis $$ %(Parent.thread i) %G %hκu HG Kku [PtrCurr34 HR] %_ with H
  · isplitl [PtrCurr34]
    · iexact PtrCurr34
    · iexact HR
  imod H with ⟨⟨PtrCurr34, HR⟩, HG, #Dku⟩
  imodintro
  by_cases hn : n = c + 1
  · -- No waiting thread.
    imod Hclose $$ [PtrNext PtrCurr GMAt GMAo HMt PtrCurr34 HR] with -
    · inext
      iunfold lockInv
      iright
      iunfold lockInvAlive
      iexists n, c + 1, tickets, obls
      iframe PtrNext GMAt GMAo
      isplitl [PtrCurr]
      · iexact PtrCurr
      isplitr
      · ipureintro
        exact ⟨Domt, Domo, by omega, by omega⟩
      isplitl [HMt]
      · iapply BigSepM.bigSepM_impl $$ HMt
        imodintro
        iintro %t %v %hv H
        have ht : t ≠ c + 1 + 1 := by
          have := (Domt t).mp (by simp [hv])
          omega
        iapply ticketSt_release γ.γt γ.γo γ.γc κu t hc0 ht $$ GMEtku GMEo Dku H
      · iunfold holderSt
        ileft
        isplitr
        · ipureintro
          omega
        isplitl [PtrCurr34]
        · iexact PtrCurr34
        · iexact HR
    imodintro
    iapply HΦ
    iframe
  · -- A waiting thread: allocate its unlock obligation, in its container.
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((Domt (c + 1 + 1)).mpr ⟨by omega, by omega⟩)
    icases (BigSepM.bigSepM_delete hv).mp $$ HMt with ⟨Ht2, HMt⟩
    iunfold ticketSt at Ht2
    icases Ht2 with (⟨%κ', %h, -⟩ | %h | ⟨%g, %ℓ1, %μ, %h, GMEt1, GMEo2, #CFl1, Gg1, #Wg1⟩)
    · iexfalso
      ipureintro
      omega
    · iexfalso
      ipureintro
      omega
    imod untilI_alloc (E := E \ ↑Ninv) (.obl g) ∅ ℓ1 μ $$ [] Gg1 with
      ⟨%κu1, -, Gg1, Kku1, OGF1, #Wlku1, ALLOC⟩
    · iapply parLe_obl g Ordinals.Ordinal.le_rfl $$ Wg1
    imod ALLOC $$ %(E \ ↑Ninv) %Nev %iprop(True) %(released curr (c + 1) R) [] with HU1
    · inext
      ipureintro
      trivial
    icases untilI_frac_split (q₁ := (1 : Qp).half) (q₂ := (1 : Qp).half)
      (Qp.half_add_half 1).symm $$ HU1 with ⟨HU1, HU2⟩
    imod ghost_map_update (some κu1) $$ GMAo GMEo2 with ⟨GMAo, GMEo2⟩
    imod ghost_map_elem_persist $$ GMEo2 with #GMEo2
    imod Hclose $$ [PtrNext PtrCurr GMAt GMAo HMt PtrCurr34 HR GMEt1 HU1 HU2 Gg1 Kku1 OGF1]
      with -
    · inext
      iunfold lockInv
      iright
      iunfold lockInvAlive
      iexists n, c + 1, tickets, (insert obls (c + 1 + 1) (some κu1))
      iframe PtrNext GMAt GMAo
      isplitl [PtrCurr]
      · iexact PtrCurr
      isplitr
      · ipureintro
        refine ⟨Domt, fun t => ?_, by omega, by omega⟩
        rw [LawfulPartialMap.get?_insert_isSome, Domo t]
        omega
      isplitl [HMt]
      · iapply (BigSepM.bigSepM_delete hv).mpr
        isplitr
        · iunfold ticketSt
          iright
          ileft
          ipureintro
          rfl
        iapply BigSepM.bigSepM_impl $$ HMt
        imodintro
        iintro %t %v' %hv' H
        have ht : t ≠ c + 1 + 1 := by
          intro h
          subst h
          simp [LawfulPartialMap.get?_delete] at hv'
        iapply ticketSt_release γ.γt γ.γo γ.γc κu t hc0 ht $$ GMEtku GMEo Dku H
      · iunfold holderSt
        iright
        isplitr
        · ipureintro
          omega
        iexists ℓ1, κu1
        iunfold finallyI
        iframe CFl1 Wlku1 GMEo2 HU2
        ileft
        iunfold nextOwner
        iexists g, μ
        iunfold finallyI
        iframe GMEt1 HU1 Kku1 OGF1 HR
        isplitl [Gg1]
        · iapply Par.kids_congr _ $$ Gg1
          intro z
          simp
        · iexact PtrCurr34
    imodintro
    iapply HΦ
    iframe

@[lantana_alias TicketLock_delete_spec]
theorem delete_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids) (tl : Val)
    (γ : TicketLockName) (R : IProp GF) (κu : Oid) (E : CoPset) (_ : ↑N ⊆ E)
    (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&delete) v(&tl)) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ ⌜κu ∈ G⌝ ∗ oblKids κu ∅ ∗ lockToken γ κu ∗ R ∗
          (γ ↪LOCK_AL) ∗ isFairLock tl γ R }}}
        hl(v(&delete) v(&tl)) @ i; E
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i (G.erase κu) ∗ R }}} := by
  refine ⟨20, fun lc i G tl γ R κu E hE C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hκu, Kku, LT, HR, AL, #IFL⟩ HΦ
  ihave HF := oblFuels_init G 20 0 $$ HF
  rw [lockToken_unfold]
  icases LT with ⟨%c, GV, #GMEtku, #GMEo⟩
  unfold isFairLock
  icases IFL with ⟨%next, %curr, %htl, #INV, #ITK⟩
  subst htl
  unfold delete
  lwp_step HT HG HF with Hlc : lc +ₕ 1 +ₕ 1 +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc3⟩
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc2⟩
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc1⟩
  -- Exchange the token.
  ihave Hc1 := tlc_one_nat.mpr $$ Hc1
  imod lockToken_exchange E hE γ curr R κu c $$ ITK Hc1 GV GMEo with ⟨PtrCurr0, GEku⟩
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(!#curr) HT
  icases oblFuels_add 1 12 G $$ HF with ⟨HF1, HF⟩
  iapply lwp_load (o := 0) (G := G) (R := ∅) $$ [HT HG HF1 PtrCurr0]
  · iframe HT PtrCurr0
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, PtrCurr0⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  -- The store, in the lock invariant.
  lwp_bind hl(#curr ← #((c + 1 : Int))) HT
  ihave Hacc := alwaysI_acc (E := E) (N := Ninv)
    (P := lockInv γ.γt γ.γo γ.γc γ.γa next curr R) (Ninv_subseteq hE) $$ INV
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨H, Hclose⟩
  iclear Hacc
  iapply lwp_credit_later $$ Hc2
  inext
  iunfold lockInv at H
  icases H with (Hdel | H)
  · iexfalso
    iapply ownAlive_full_false $$ AL Hdel
  iunfold lockInvAlive at H
  icases H with ⟨%n, %c', %tickets, %obls, PtrNext, PtrCurr, GMAt, GMAo, %⟨Domt, Domo, hc0, hcn⟩,
    HMt, Hc⟩
  ihave %h := pointsTo_agree (l := curr) $$ [PtrCurr PtrCurr0]
  · iframe
  obtain rfl : c = c' := by simpa [vz] using h.symm
  ihave PtrCurr := (pointsTo_quarters curr _).mpr $$ [PtrCurr PtrCurr0]
  · iframe
  ihave %hlt := ghostMapP_lookup $$ GMAt GMEtku
  have hc1 := (Domt (c + 1)).mp (by simp [hlt])
  iunfold holderSt at Hc
  icases Hc with (⟨%hcn', -⟩ | ⟨%hcn', %ℓ0, %κ, #CFl, #Wl, #GMEo1, HE, -⟩)
  · iexfalso
    ipureintro
    omega
  ihave %h := ghost_map_elem_agree _ _ _ _ (some κu) (some κ) $$ [GMEo GMEo1]
  · iframe GMEo GMEo1
  cases h
  iunfold finallyI at GEku HE
  ihave HU := untilI_frac_add (q := 1) (Qp.half_add_half 1).symm $$ GEku HE
  ihave HU := untilI_discharge (E := E \ ↑Ninv) (Nev_subseteq hE) $$ HU
  ihave HU := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ HU
  imod HU
  iapply lwp_credit_later $$ Hc3
  inext
  icases HU with ⟨-, Hdis⟩
  icases oblFuels_add 1 10 G $$ HF with ⟨HF1, HF⟩
  iapply lwp_store (o := 0) (G := G) (R := ∅) $$ [HT HG HF1 PtrCurr]
  · iframe HT PtrCurr
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, PtrCurr⟩
  icases (pointsTo_quarters curr _).mp $$ PtrCurr with ⟨PtrCurr, PtrCurr34⟩
  imod Hdis $$ %(Parent.thread i) %G %hκu HG Kku [PtrCurr34 HR] %_ with H
  · isplitl [PtrCurr34]
    · iexact PtrCurr34
    · iexact HR
  imod H with ⟨⟨PtrCurr34, HR⟩, HG, -⟩
  imodintro
  -- The lock is deleted: the full alive token goes to the invariant.
  imod Hclose $$ [AL] with -
  · inext
    iunfold lockInv
    ileft
    unfold ownAlive
    iexact AL
  imodintro
  ihave PtrCurr := (pointsTo_quarters curr _).mpr $$ [PtrCurr PtrCurr34]
  · iframe
  ihave HF := oblFuels_remove_obl κu G _ $$ HF
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(free(#next)) HT
  icases oblFuels_add 1 7 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_free (o := 0) (G := G.erase κu) (R := ∅) $$ [HT HG HF1 PtrNext]
  · iframe HT PtrNext
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, -⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  icases oblFuels_add 1 4 _ $$ HF with ⟨HF1, -⟩
  iapply lwp_free (o := 0) (G := G.erase κu) (R := ∅) $$ [HT HG HF1 PtrCurr]
  · iframe HT PtrCurr
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, -⟩
  iapply HΦ
  iframe

end Specs

end Lantana.Examples.TicketLock
