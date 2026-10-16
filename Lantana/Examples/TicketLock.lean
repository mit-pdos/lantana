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

instance ownAlive_discard_persistent (γ : TicketLockName) :
    Persistent (ownAlive (GF := GF) γ .discard) := by
  unfold ownAlive; infer_instance

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

omit [HeapGS GF] in
/-- A ticket waiting with its half of the ticket map is not served: `c + 1 ≤ t`. -/
theorem ticketSt_waiting (γt γo γc : GName) (c n t : Int) (x : Oid × Layer × Measure) :
    ticketSt (GF := GF) γt γo γc c n t ⊢
      (γt ↪◯PMAP[t]{.own (1 : Qp).half} (some x : TicketInfo)) -∗
      ⌜c + 1 ≤ t⌝ ∗ ticketSt γt γo γc c n t ∗
        (γt ↪◯PMAP[t]{.own (1 : Qp).half} (some x : TicketInfo)) := by
  iintro Ht H
  unfold ticketSt
  icases Ht with (⟨%κ, %h, #H1, #H2, #H3⟩ | %h | ⟨%g, %ℓ, %μ, %h, Ht⟩)
  · ihave %h' := ghostMapP_elem_agree _ _ _ _ (none : TicketInfo) (some x) $$ [H]
    · iframe H1 H
    simp at h'
  · iframe H
    isplitr
    · ipureintro
      omega
    iright
    ileft
    ipureintro
    exact h
  · iframe H
    isplitr
    · ipureintro
      omega
    iright
    iright
    iexists g, ℓ, μ
    iframe Ht
    ipureintro
    exact h

omit [HeapGS GF] in
/-- A ticket with a recorded unlock obligation is served, or the next one: `t ≤ c + 1`. -/
theorem ticketSt_obl (γt γo γc : GName) (c n t : Int) (κ : Oid) :
    ticketSt (GF := GF) γt γo γc c n t ⊢ (γo ↪◯MAP[t]{.discard} some κ) -∗
      ⌜t ≤ c + 1⌝ ∗ ticketSt γt γo γc c n t := by
  iintro Ht #H
  unfold ticketSt
  icases Ht with (⟨%κ', %h, Ht⟩ | %h | ⟨%g, %ℓ, %μ, %h, H1, H2, Ht⟩)
  · isplitr
    · ipureintro
      omega
    ileft
    iexists κ'
    iframe Ht
    ipureintro
    exact h
  · isplitr
    · ipureintro
      omega
    iright
    ileft
    ipureintro
    exact h
  · ihave %h' := ghost_map_elem_agree _ _ _ _ (none : Option Oid) (some κ) $$ [H2]
    · iframe H2 H
    simp at h'

/-- A ticket is taken: the bound `n` grows. -/
theorem holderSt_mono_n (γt γo γc : GName) (curr : Loc) (R : IProp GF) {c n : Int}
    (h : c < n) : holderSt (GF := GF) γt γo γc curr R c n ⊢ holderSt γt γo γc curr R c (n + 1) := by
  unfold holderSt
  iintro (⟨%h', -⟩ | ⟨%h', H⟩)
  · iexfalso
    ipureintro
    omega
  · iright
    iframe H
    ipureintro
    omega

omit [HeapGS GF] in
/-- A new ticket `n + 1` in the map. -/
theorem tickets_insert (γt γo γc : GName) {c n : Int} (tickets : TMap TicketInfo)
    (v : TicketInfo) (h : get? tickets (n + 1) = none) :
    ([∗map] t ↦ _x ∈ tickets, ticketSt (GF := GF) γt γo γc c n t) ⊢
      ticketSt γt γo γc c (n + 1) (n + 1) -∗
      [∗map] t ↦ _x ∈ insert tickets (n + 1) v, ticketSt γt γo γc c (n + 1) t := by
  iintro HM Ht
  iapply (BigSepM.bigSepM_insert h).mpr
  iframe Ht
  iapply BigSepM.bigSepM_mono (fun _ => ticketSt_mono_n γt γo γc _ (by omega)) $$ HM

/-- The domain conditions after taking the ticket `n + 1`. -/
theorem dom_insert_succ {V : Type _} {m : TMap V} {n : Int}
    (h : ∀ t, (get? m t).isSome ↔ 0 ≤ t ∧ t ≤ n) (hn : 0 ≤ n) (v : V) :
    get? m (n + 1) = none ∧ ∀ t, (get? (insert m (n + 1) v) t).isSome ↔ 0 ≤ t ∧ t ≤ n + 1 := by
  refine ⟨?_, fun t => ?_⟩
  · have := h (n + 1)
    cases hm : get? m (n + 1) with
    | none => rfl
    | some _ => simp [hm] at this; omega
  · rw [LawfulPartialMap.get?_insert_isSome, h t]
    omega

/-- The domain conditions after updating a ticket. -/
theorem dom_insert_same {V : Type _} {m : TMap V} {n k : Int}
    (h : ∀ t, (get? m t).isSome ↔ 0 ≤ t ∧ t ≤ n) (hk : 0 ≤ k ∧ k ≤ n) (v : V) :
    ∀ t, (get? (insert m k v) t).isSome ↔ 0 ≤ t ∧ t ≤ n := by
  intro t
  rw [LawfulPartialMap.get?_insert_isSome, h t]
  omega

omit [HeapGS GF] in
/-- The states of the tickets do not depend on the values of the ticket map. -/
theorem tickets_update (γt γo γc : GName) {c n : Int} {tickets : TMap TicketInfo} {k : Int}
    {x : TicketInfo} (hk : get? tickets k = some x) (v : TicketInfo) :
    ([∗map] t ↦ _x ∈ tickets, ticketSt (GF := GF) γt γo γc c n t) ⊢
      [∗map] t ↦ _x ∈ insert tickets k v, ticketSt γt γo γc c n t := by
  iintro HM
  icases BigSepM.bigSepM_insert_acc hk $$ HM with ⟨Ht, HM⟩
  iapply HM $$ %v Ht

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

/-! ## Acquire -/

section Acquire
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLockG GF]

/-- The loop of `acquire`, waiting on `curr` for the ticket `my`. -/
abbrev loopV (curr : Loc) (my : Int) : Val :=
  hl_val(rec loop _ := if !#curr = #my then #() else loop #())

/-- The postcondition of `acquire`. -/
abbrev acqPost (Φ : Val → IProp GF) (i : ThreadId) (C : List ECtxItem) (lc : Fuel) (G : Oids)
    (γ : TicketLockName) (dq₁ dq₂ : DFrac) (ℓ : Layer) (m : Measure) (R : IProp GF) :
    IProp GF :=
  iprop(∀ κu : Oid, threadExpr i C hl(#()) ∗ £ₒ lc ∗ ⌜κu ∉ G⌝ ∗ thKids i (G.insert κu) ∗
    oblKids κu ∅ ∗ Obl.fuel κu ℓ m ∗ (γ ↪LOCK_AL{dq₁}) ∗ (γ ↪LOCK_CF{dq₂} ℓ) ∗
    lockToken γ κu ∗ R -∗ Φ hl_val(#()))

/-- The end of `acquire`, once `curr` holds `my`: the unlock obligation `κu` moves up from the
container `gu` to the thread, `gu` is discharged, and the lock token is taken from its
invariant. -/
theorem acquire_end (lc : Fuel) (i : ThreadId) (G : Oids) (γ : TicketLockName) (dq₁ dq₂ : DFrac)
    (ℓ : Layer) (m : Measure) (R : IProp GF) (E : CoPset) (hE : ↑N ⊆ E) (C : List ECtxItem)
    (Φ : Val → IProp GF) (curr : Loc) (my : Int) (gu κu : Oid) (hgu : gu ∉ G) :
    ⊢ alwaysI (Expr := Exp) (State := State) Ntk (lockTokenInv γ.γo γ.γk curr R) -∗
      (γ.γt ↪◯PMAP[my + 1]{.discard} (none : TicketInfo)) -∗
      (γ.γo ↪◯MAP[my + 1]{.discard} some κu) -∗
      acqPost Φ i C lc G γ dq₁ dq₂ ℓ m R -∗ (γ ↪LOCK_AL{dq₁}) -∗ (γ ↪LOCK_CF{dq₂} ℓ) -∗
      thKids i (G.insert gu) -∗ oblFuels (G.insert gu) 2 -∗ oblKids gu {κu} -∗
      Obl.assigned gu 1 -∗ oblKids κu ∅ -∗ Obl.fuel κu ℓ m -∗
      curr ↦{.own q34} some (vz my) -∗ R -∗
      finallyI Nev κu (1 : Qp).half (released curr my R) -∗
      threadExpr i C hl(if #my = #my then #() else v(&(loopV curr my)) #()) -∗
      lWP hl(if #my = #my then #() else v(&(loopV curr my)) #()) @ i; E {{ Φ }} := by
  iintro #ITK #GMEt #GMEo HΦ AL CF HG HF Kgu Agu Kk Of PtrCurr0 HR HE0 HT
  lwp_step HT HG HF
  rw [show (vz my == vz my) = true from beq_self_eq_true _]
  lwp_step HT HG HF with Hlc : lc +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc1⟩
  ihave Hc1 := tlc_one_nat.mpr $$ Hc1
  -- The unlock obligation moves up to the thread; the container is discharged.
  imod Obl.move_up E (.thread i) (G.insert gu) gu {κu} κu (by simp) (by simp) $$ HG Kgu
    with ⟨%hκu, HG, Kgu⟩
  imod Obl.discharge_leaf E (.thread i) _ gu (by simp) $$ HG [Kgu] Agu with ⟨HG, -⟩
  · iapply Par.kids_congr _ $$ Kgu
    intro z
    simp
  ihave HG := Par.kids_congr (B := G.insert κu) ?_ $$ HG
  · intro z
    simp only [Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.mem_insert] at hκu ⊢
    grind
  -- The lock token.
  iapply lwp_value_mupd'.mpr
  ihave Hacc := alwaysI_acc (E := E) (N := Ntk) (P := lockTokenInv γ.γo γ.γk curr R)
    (Ntk_subseteq hE) $$ ITK
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨H, Hclose⟩
  iclear Hacc
  iapply lc_mupd_add_later $$ Hc1
  inext
  iunfold lockTokenInv at H
  icases H with ⟨%c', (GV | ⟨%κ', -, PtrCurr1, -⟩)⟩
  rotate_left
  · iexfalso
    ihave ⟨%h, -⟩ := pointsTo_op_cmraValid $$ [PtrCurr0 PtrCurr1]
    · iframe
    exact absurd h (by simp [CMRA.Valid, CMRA.op, DFrac.op, DFrac.valid]; grind)
  imod ghost_var_update my $$ GV with GV
  icases ghostVar_halves _ _ $$ GV with ⟨GV, GV0⟩
  imod Hclose $$ [GV0 PtrCurr0 HE0] with -
  · inext
    iunfold lockTokenInv
    iexists my
    iright
    iexists κu
    iframe GV0 PtrCurr0 HE0 GMEo
  imodintro
  iapply HΦ $$ %κu
  iframe HT Hlc HG Kk Of AL CF HR
  isplitr
  · ipureintro
    simp only [Std.ExtTreeSet.mem_insert] at hκu
    grind
  rw [lockToken_unfold]
  iexists my
  iframe GV GMEt GMEo

/-- The loop of `acquire` when its ticket is served and the thread has `curr`'s part. -/
theorem acquire_mine (lc : Fuel) (i : ThreadId) (G : Oids) (γ : TicketLockName)
    (dq₁ dq₂ : DFrac) (ℓ : Layer) (m : Measure) (R : IProp GF) (E : CoPset) (hE : ↑N ⊆ E)
    (C : List ECtxItem) (Φ : Val → IProp GF) (curr : Loc) (my : Int) (gu κu : Oid)
    (hgu : gu ∉ G) :
    ⊢ alwaysI (Expr := Exp) (State := State) Ntk (lockTokenInv γ.γo γ.γk curr R) -∗
      (γ.γt ↪◯PMAP[my + 1]{.discard} (none : TicketInfo)) -∗
      (γ.γo ↪◯MAP[my + 1]{.discard} some κu) -∗
      acqPost Φ i C lc G γ dq₁ dq₂ ℓ m R -∗ (γ ↪LOCK_AL{dq₁}) -∗ (γ ↪LOCK_CF{dq₂} ℓ) -∗
      thKids i (G.insert gu) -∗ oblFuels (G.insert gu) 4 -∗ oblKids gu {κu} -∗
      Obl.assigned gu 1 -∗ oblKids κu ∅ -∗ Obl.fuel κu ℓ m -∗
      curr ↦{.own q34} some (vz my) -∗ R -∗
      finallyI Nev κu (1 : Qp).half (released curr my R) -∗
      threadExpr i C hl(v(&(loopV curr my)) #()) -∗
      lWP hl(v(&(loopV curr my)) #()) @ i; E {{ Φ }} := by
  iintro #ITK #GMEt #GMEo HΦ AL CF HG HF Kgu Agu Kk Of PtrCurr0 HR HE0 HT
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(!#curr) HT
  icases oblFuels_add 1 2 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_load (o := 0) (G := G.insert gu) (R := ∅) $$ [HT HG HF1 PtrCurr0]
  · iframe HT PtrCurr0
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, PtrCurr0⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  iapply acquire_end lc i G γ dq₁ dq₂ ℓ m R E hE C Φ curr my gu κu hgu $$ ITK GMEt GMEo HΦ AL CF
    HG HF Kgu Agu Kk Of PtrCurr0 HR HE0 HT

@[lantana_alias TicketLock_acquire_spec]
theorem acquire_spec : ∃ μ : Measure, ∀ (lc : Fuel) (m : Measure) (i : ThreadId) (G : Oids)
    (tl : Val) (γ : TicketLockName) (dq₁ dq₂ : DFrac) (ℓ : Layer) (R : IProp GF) (E : CoPset)
    (_ : ↑N ⊆ E) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&acquire) v(&tl)) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g ℓ.succ μ) ∗ (γ ↪LOCK_AL{dq₁}) ∗ (γ ↪LOCK_CF{dq₂} ℓ) ∗
          isFairLock tl γ R }}}
        hl(v(&acquire) v(&tl)) @ i; E
      l{{{ (κu : Oid), RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ ⌜κu ∉ G⌝ ∗
        thKids i (G.insert κu) ∗ oblKids κu ∅ ∗ Obl.fuel κu ℓ m ∗ (γ ↪LOCK_AL{dq₁}) ∗
        (γ ↪LOCK_CF{dq₂} ℓ) ∗ lockToken γ κu ∗ R }}} := by
  refine ⟨20 + ((50 + 50 * ▽) * ℵ + 50 * ▽), fun lc m i G tl γ dq₁ dq₂ ℓ R E hE C => ?_⟩
  iintro %Φ !> ⟨HT, HG, Fs, AL, CF, #IFL⟩ HΦ
  icases (Obl.fuel_add_set G ℓ.succ 20 _).mp $$ Fs with ⟨HF, Fsloop⟩
  ihave HF := oblFuels_init G 20 ℓ.succ $$ HF
  unfold isFairLock
  icases IFL with ⟨%next, %curr, %htl, #INV, #ITK⟩
  subst htl
  unfold acquire
  lwp_step HT HG HF with Hc : 1
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
  lwp_bind hl(faa(#next, #1)) HT
  -- The atomic FAA, in the lock invariant.
  ihave Hacc := alwaysI_acc (E := E) (N := Ninv)
    (P := lockInv γ.γt γ.γo γ.γc γ.γa next curr R) (Ninv_subseteq hE) $$ INV
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨H, Hclose⟩
  iclear Hacc
  iapply lwp_credit_later $$ Hc
  inext
  iunfold lockInv at H
  icases H with (Hdel | H)
  · iexfalso
    iapply ownAlive_full_false $$ AL Hdel
  iunfold lockInvAlive at H
  icases H with ⟨%n, %c, %tickets, %obls, PtrNext, PtrCurr, GMAt, GMAo, %⟨Domt, Domo, hc0, hcn⟩,
    HMt, Hc⟩
  icases oblFuels_add 1 12 G $$ HF with ⟨HF1, HF⟩
  iapply lwp_faa (o := 0) (G := G) (R := ∅) $$ [HT HG HF1 PtrNext]
  · iframe HT PtrNext
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, PtrNext⟩
  -- A new container, at the lock's layer, to receive the unlock obligation.
  imod Obl.new (E \ ↑Ninv) (.thread i) G ℓ 12 $$ [] HG with ⟨%gu, %hgu, HG, Kgu, Agu, Fgu, #Wgu⟩
  · iapply parLe_thread
  ihave HF := oblFuels_add_obl G gu ℓ 12 $$ Fgu HF
  icases ownLayer_lb γ dq₂ ℓ $$ CF with ⟨CF, #CFl⟩
  iunfold holderSt at Hc
  icases Hc with (⟨%hcn', PtrCurr0, HR⟩ | ⟨%hcn', Hc⟩)
  · -- The lock is free: the unlock obligation, in the container, and the token.
    subst hcn'
    imod untilI_alloc (E := E \ ↑Ninv) (.obl gu) ∅ ℓ m $$ [] Kgu with
      ⟨%κu, -, Kgu, Kk, Of, #Wlku, ALLOC⟩
    · iapply parLe_obl gu Ordinals.Ordinal.le_rfl $$ Wgu
    imod ALLOC $$ %(E \ ↑Ninv) %Nev %iprop(True) %(released curr c R) [] with HU
    · inext
      ipureintro
      trivial
    icases untilI_frac_split (q₁ := (1 : Qp).half) (q₂ := (1 : Qp).half)
      (Qp.half_add_half 1).symm $$ HU with ⟨HU1, HU2⟩
    obtain ⟨hft, Domt'⟩ := dom_insert_succ Domt hc0 (none : TicketInfo)
    obtain ⟨hfo, Domo'⟩ := dom_insert_succ Domo hc0 (some κu : Option Oid)
    imod ghostMapP_insert (c + 1) (none : TicketInfo) hft $$ GMAt with ⟨GMAt, GMEt⟩
    imod ghostMapP_elem_persist $$ GMEt with #GMEt
    imod ghost_map_insert (c + 1) (some κu) hfo $$ GMAo with ⟨GMAo, GMEo⟩
    imod ghost_map_elem_persist $$ GMEo with #GMEo
    imod Hclose $$ [PtrNext PtrCurr GMAt GMAo HMt HU1] with -
    · inext
      iunfold lockInv
      iright
      iunfold lockInvAlive
      iexists c + 1, c, insert tickets (c + 1) (none : TicketInfo),
        insert obls (c + 1) (some κu : Option Oid)
      iframe PtrNext PtrCurr GMAt GMAo
      isplitr
      · ipureintro
        exact ⟨Domt', Domo', hc0, by omega⟩
      isplitl [HMt]
      · iapply tickets_insert γ.γt γ.γo γ.γc tickets _ hft $$ HMt
        iunfold ticketSt
        iright
        ileft
        ipureintro
        rfl
      · iunfold holderSt
        iright
        isplitr
        · ipureintro
          omega
        iexists ℓ, κu
        iunfold finallyI
        iframe CFl Wlku GMEo HU1
        iright
        iexact GMEt
    imodintro
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    lwp_step HT HG HF
    lwp_expr_simp
    lwp_step HT HG HF
    lwp_expr_simp
    lwp_step HT HG HF
    lwp_expr_simp
    icases oblFuels_add 4 5 _ $$ HF with ⟨HF, -⟩
    iapply acquire_mine lc i G γ dq₁ dq₂ ℓ m R E hE C Φ curr c gu κu hgu $$ ITK GMEt GMEo HΦ
      AL CF HG HF [Kgu] Agu Kk Of PtrCurr0 HR [HU2] HT
    · iapply Par.kids_congr _ $$ Kgu
      intro z
      simp
    · iunfold finallyI
      iexact HU2
  · -- The lock is taken: wait in the container.
    sorry

end Acquire

/-! ## Temporal guarantees

The guarantees keep the trace content of the invariants: the values of `next` and `curr`, and
the `finallyI` of the unlock obligation of ticket `c + 1`. Rocq writes the inferred guarantee
out with a `trSpec_true` for every ghost conjunct (to match `into_guar` syntactically); here the
ghost conjuncts are dropped and the guarantees are proved with the rules of `GuaranteeRules`. -/

section Guarantee
variable {GF : BundledGFunctors}

/-- `l ↦{q} v` as a trace specification. -/
abbrev ptsSpec (l : Loc) (q : Qp) (v : Val) : TrSpec Exp State GF :=
  TrSpec.state (pointstoSat l (.own q) v)

/-- The holder will increment `curr`. -/
abbrev releasedTrSpec (curr : Loc) (c : Int) : TrSpec Exp State GF :=
  ◇ₛ (ptsSpec curr q34 (vz (c + 1)) ∧ₛ TrSpec.true)

/-- The holder part of the alive lock invariant: free, or ticket `c + 1` will be released. -/
def holderTrSpec (curr : Loc) (c n : Int) : TrSpec Exp State GF :=
  (⌜c = n⌝ₛ ∧ₛ ptsSpec curr q34 (vz c) ∧ₛ TrSpec.true) ∨ₛ (⌜c < n⌝ₛ ∧ₛ releasedTrSpec curr c)

/-- The guarantee of the alive branch of the lock invariant (Rocq `lock_inv_alive_trSpec`). -/
@[lantana_alias lock_inv_alive_trSpec]
def lockInvAliveTrSpec (next curr : Loc) : TrSpec Exp State GF :=
  ∃ₛ (n : Int) (c : Int), ptsSpec next 1 (vz n) ∧ₛ ptsSpec curr q14 (vz c) ∧ₛ
    ⌜0 ≤ c ∧ c ≤ n⌝ₛ ∧ₛ holderTrSpec curr c n

/-- The guarantee of the lock invariant: its left disjunct (a deleted lock) is ghost state
(Rocq `lock_inv_trSpec`). -/
@[lantana_alias lock_inv_trSpec]
def lockInvTrSpec (next curr : Loc) : TrSpec Exp State GF :=
  TrSpec.true ∨ₛ lockInvAliveTrSpec next curr

/-- The guarantee of the token's invariant: nobody holds the lock (ghost state), or its holder
will increment `curr` (Rocq `lock_token_inv_trSpec`). -/
@[lantana_alias lock_token_inv_trSpec]
def lockTokenInvTrSpec (curr : Loc) : TrSpec Exp State GF :=
  ∃ₛ c : Int, TrSpec.true ∨ₛ (ptsSpec curr q34 (vz c) ∧ₛ releasedTrSpec curr c)

/-- The guarantee of `isFairLock`, vacuous on traces since the lock can be deleted (Rocq
`fair_lock_trSpec`); see `guar_isFairLockAlive`. -/
@[lantana_alias fair_lock_trSpec]
def fairLockTrSpec (tl : Val) : TrSpec Exp State GF :=
  ∃ₛ (next : Loc) (curr : Loc), ⌜tl = vLock next curr⌝ₛ ∧ₛ □ₛ lockInvTrSpec next curr ∧ₛ
    □ₛ lockTokenInvTrSpec curr

/-- The guarantee of a lock that cannot be deleted (Rocq `alive_fair_lock_trSpec`). -/
@[lantana_alias alive_fair_lock_trSpec]
def aliveFairLockTrSpec (tl : Val) : TrSpec Exp State GF :=
  fairLockTrSpec tl ∧ₛ
    ∃ₛ (next : Loc) (curr : Loc), ⌜tl = vLock next curr⌝ₛ ∧ₛ □ₛ lockInvAliveTrSpec next curr

variable [ModelGS GF] [HeapGS GF] [TicketLockG GF]

omit [TicketLockG GF] in
/-- Dropping the left resource of a separating conjunction. -/
theorem guar_sep_drop {P Q : IProp GF} {G : TrSpec Exp State GF} (h : ⊢ Q ⊨ₜ G) :
    ⊢@{IProp GF} iprop(P ∗ Q) ⊨ₜ G := by
  refine h.trans ?_
  iintro #HG
  iapply guar_mono $$ [] HG
  imodintro
  iintro ⟨-, HQ⟩
  iexact HQ

omit [TicketLockG GF] in
/-- Dropping the right resource of a separating conjunction. -/
theorem guar_sep_drop_r {P Q : IProp GF} {G : TrSpec Exp State GF} (h : ⊢ P ⊨ₜ G) :
    ⊢@{IProp GF} iprop(P ∗ Q) ⊨ₜ G := by
  refine h.trans ?_
  iintro #HG
  iapply guar_mono $$ [] HG
  imodintro
  iintro ⟨HP, -⟩
  iexact HP

omit [TicketLockG GF] in
/-- A pure fact, read as a weaker one. -/
theorem guar_pure_weaken {φ ψ : Prop} (h : φ → ψ) :
    ⊢@{IProp GF} iprop(⌜φ⌝) ⊨ₜ (⌜ψ⌝ₛ : TrSpec Exp State GF) :=
  (guar_pure φ).trans (guar_weaken (fun _ => BI.pure_mono h))

omit [TicketLockG GF] in
theorem guar_released (curr : Loc) (c : Int) (R : IProp GF) :
    ⊢@{IProp GF} released curr c R ⊨ₜ (ptsSpec curr q34 (vz (c + 1)) ∧ₛ TrSpec.true) := by
  unfold released
  iapply guar_sep
  · iapply (GuarOf.guar_of (P := curr ↦{.own q34} some (vz (c + 1))))
  · iapply guar_true

omit [TicketLockG GF] in
theorem guar_finally_released (κ : Oid) (q : Qp) (curr : Loc) (c : Int) (R : IProp GF) :
    ⊢@{IProp GF} finallyI Nev κ q (released curr c R) ⊨ₜ releasedTrSpec curr c := by
  unfold finallyI
  exact guar_untilI_valid (guar_true (P := iprop(True))) (guar_released curr c R)

theorem guar_holderSt (γt γo γc : GName) (curr : Loc) (R : IProp GF) (c n : Int) :
    ⊢@{IProp GF} holderSt γt γo γc curr R c n ⊨ₜ holderTrSpec curr c n := by
  unfold holderSt holderTrSpec
  iapply guar_or
  · iapply guar_sep
    · iapply guar_pure
    iapply guar_sep
    · iapply (GuarOf.guar_of (P := curr ↦{.own q34} some (vz c)))
    · iapply guar_true
  · iapply guar_sep
    · iapply guar_pure
    iapply guar_ex_ghost
    iintro %ℓ
    iapply guar_ex_ghost
    iintro %κ
    iapply guar_sep_drop
    iapply guar_sep_drop
    iapply guar_sep_drop
    iapply guar_sep_drop_r
    iapply guar_finally_released

theorem guar_lockInvAlive (γt γo γc : GName) (next curr : Loc) (R : IProp GF) :
    ⊢@{IProp GF} lockInvAlive γt γo γc next curr R ⊨ₜ lockInvAliveTrSpec next curr := by
  unfold lockInvAlive lockInvAliveTrSpec
  iapply guar_ex
  iintro %n
  iapply guar_ex
  iintro %c
  iapply guar_ex_ghost
  iintro %tickets
  iapply guar_ex_ghost
  iintro %obls
  iapply guar_sep
  · iapply (GuarOf.guar_of (P := next ↦ some (vz n)))
  iapply guar_sep
  · iapply (GuarOf.guar_of (P := curr ↦{.own q14} some (vz c)))
  iapply guar_sep_drop
  iapply guar_sep_drop
  iapply guar_sep
  · iapply guar_pure_weaken (by exact fun h => ⟨h.2.2.1, h.2.2.2⟩)
  iapply guar_sep_drop
  iapply guar_holderSt

theorem guar_lockInv (γt γo γc γa : GName) (next curr : Loc) (R : IProp GF) :
    ⊢@{IProp GF} lockInv γt γo γc γa next curr R ⊨ₜ lockInvTrSpec next curr := by
  unfold lockInv lockInvTrSpec
  iapply guar_or
  · iapply guar_true
  · iapply guar_lockInvAlive

theorem guar_lockTokenInv (γo γk : GName) (curr : Loc) (R : IProp GF) :
    ⊢@{IProp GF} lockTokenInv γo γk curr R ⊨ₜ lockTokenInvTrSpec curr := by
  unfold lockTokenInv lockTokenInvTrSpec
  iapply guar_ex
  iintro %c
  iapply guar_or
  · iapply guar_true
  iapply guar_ex_ghost
  iintro %κ
  iapply guar_sep_drop
  iapply guar_sep
  · iapply (GuarOf.guar_of (P := curr ↦{.own q34} some (vz c)))
  iapply guar_sep_drop
  iapply guar_finally_released

@[lantana_alias guar_is_fair_lock]
theorem guar_isFairLock (tl : Val) (γ : TicketLockName) (R : IProp GF) :
    ⊢@{IProp GF} isFairLock tl γ R ⊨ₜ fairLockTrSpec tl := by
  unfold isFairLock fairLockTrSpec
  iapply guar_ex
  iintro %next
  iapply guar_ex
  iintro %curr
  iapply guar_sep
  · iapply guar_pure
  iapply guar_sep
  · iapply guar_alwaysI_valid (guar_lockInv γ.γt γ.γo γ.γc γ.γa next curr R)
  · iapply guar_alwaysI_valid (guar_lockTokenInv γ.γo γ.γk curr R)

/-- Clients see the lock's guarantee, not its invariant. -/
@[lantana_alias into_guar_is_fair_lock]
instance intoGuar_isFairLock (tl : Val) (γ : TicketLockName) (R : IProp GF) :
    IntoGuar (Expr := Exp) (State := State) (isFairLock tl γ R) (fairLockTrSpec tl) :=
  ⟨guar_isFairLock tl γ R⟩

@[lantana_alias guar_is_fair_lock_alive]
theorem guar_isFairLockAlive (tl : Val) (γ : TicketLockName) (R : IProp GF) :
    ⊢@{IProp GF} isFairLockAlive tl γ R ⊨ₜ aliveFairLockTrSpec tl := by
  unfold isFairLockAlive aliveFairLockTrSpec
  iapply guar_sep
  · iapply guar_isFairLock
  iapply guar_ex
  iintro %next
  iapply guar_ex
  iintro %curr
  iapply guar_sep
  · iapply guar_pure
  · iapply guar_alwaysIAs_valid (guar_lockInvAlive γ.γt γ.γo γ.γc next curr R)

@[lantana_alias into_guar_is_fair_lock_alive]
instance intoGuar_isFairLockAlive (tl : Val) (γ : TicketLockName) (R : IProp GF) :
    IntoGuar (Expr := Exp) (State := State) (isFairLockAlive tl γ R) (aliveFairLockTrSpec tl) :=
  ⟨guar_isFairLockAlive tl γ R⟩

/-- A persistent alive token (as the queue keeps) rules out deletion, hence the left disjunct
of `lockInv`: the lock invariant is registered under its alive branch (Rocq
`is_fair_lock_register_alive`). -/
@[lantana_alias is_fair_lock_register_alive]
theorem isFairLock_register_alive (E : CoPset) (tl : Val) (γ : TicketLockName) (R : IProp GF)
    (hE : ↑Ninv ⊆ E) :
    isFairLock tl γ R ⊢ (γ ↪LOCK_AL{.discard}) -∗ |={E}=>m isFairLockAlive tl γ R := by
  iintro #H #AL
  unfold isFairLock
  icases H with ⟨%next, %curr, %htl, #I, #K⟩
  imod alwaysI_register (Expr := Exp) (State := State) (E := E) (N := Ninv)
    (P := lockInv γ.γt γ.γo γ.γc γ.γa next curr R)
    (V := lockInvAlive γ.γt γ.γo γ.γc next curr R) hE $$ [] [] with #IA
  · iapply alwaysI_inv $$ I
  · imodintro
    iintro H
    iunfold lockInv at H
    icases H with (H | H)
    · iexfalso
      iapply ownAlive_full_false $$ AL H
    · iexact H
  imodintro
  unfold isFairLockAlive isFairLock
  isplitl []
  · iexists next, curr
    isplitr
    · ipureintro
      exact htl
    iframe I K
  · iexists next, curr
    isplitr
    · ipureintro
      exact htl
    iexact IA

end Guarantee

/-! ## Progress of the lock, at the level of traces -/

section Trace

/-- `l ↦ v` in the current state of the trace (Rocq `tr_pointsto`). -/
@[lantana_alias tr_pointsto]
def trPointsTo (l : Loc) (v : Val) : TrProp Exp State :=
  TrProp.state (pointstoSat l (DFrac.own 1) v)

/-- A location holds one value at a time. -/
theorem state_pointsto_agree {l : Loc} {dq₁ dq₂ : DFrac} {v₁ v₂ : Val} {τ : Trace Exp State}
    (h₁ : TrProp.state (pointstoSat l dq₁ v₁) τ) (h₂ : TrProp.state (pointstoSat l dq₂ v₂) τ) :
    v₁ = v₂ := by
  simp only [TrProp.state, pointstoSat] at h₁ h₂
  exact Option.some.inj (Option.some.inj (h₁.symm.trans h₂))

/-- Release progress of the ticket lock `(next, curr)`: whenever a ticket is taken but not
served out (`curr ↦ c`, `next ↦ n`, `c < n`), `curr` is eventually incremented. So every holder
of the lock eventually releases it (Rocq `release_progress`). -/
@[lantana_alias release_progress]
def releaseProgress (next curr : Loc) : TrProp Exp State :=
  □ₜ (∀ₜ (n : Int) (c : Int), trPointsTo next (vz n) →ₜ trPointsTo curr (vz c) →ₜ ⌜c < n⌝ₜ →ₜ
    ◇ₜ trPointsTo curr (vz (c + 1)))

@[lantana_alias lock_inv_alive_trSpec_release_progress]
theorem lockInvAliveTrSpec_release_progress {GF : BundledGFunctors} (next curr : Loc) :
    (□ₛ lockInvAliveTrSpec (GF := GF) next curr).external ⊆ releaseProgress next curr := by
  intro τ h m hm n c hn hc hlt
  obtain ⟨n', c', hn', hc', -, hcase⟩ := h m hm
  obtain rfl : n = n' := by simpa [vz] using state_pointsto_agree (dq₁ := .own 1) (dq₂ := .own 1) hn hn'
  obtain rfl : c = c' := by simpa [vz] using state_pointsto_agree (dq₁ := .own 1) (dq₂ := .own q14) hc hc'
  rcases hcase with ⟨h, -⟩ | ⟨-, m', hm', ⟨hpts, -⟩, -⟩
  · exact absurd (show c = n from h) (by have : c < n := hlt; omega)
  · exact ⟨m', hm', hpts, fun _ _ _ => trivial⟩

@[lantana_alias alive_fair_lock_release_progress]
theorem aliveFairLock_release_progress {GF : BundledGFunctors} (tl : Val)
    (τ : Trace Exp State) (h : (aliveFairLockTrSpec (GF := GF) tl).external τ) :
    ∃ next curr : Loc, tl = vLock next curr ∧ releaseProgress next curr τ := by
  obtain ⟨-, next, curr, htl, hal⟩ := h
  exact ⟨next, curr, htl, lockInvAliveTrSpec_release_progress (GF := GF) next curr τ hal⟩

/-- `next` never decreases. Only the next ticket carries a `finallyI` (the releasing thread
allocates its obligation), so starvation freedom also needs this: the code ensures it, the
guarantee does not record it (see Rocq `ticket_lock_mono.v`) (Rocq `next_monotone`). -/
@[lantana_alias next_monotone]
def nextMonotone (next : Loc) : TrProp Exp State :=
  □ₜ (∀ₜ n : Int, trPointsTo next (vz n) →ₜ
    □ₜ (∃ₜ n' : Int, trPointsTo next (vz n') ∧ₜ ⌜n ≤ n'⌝ₜ))

/-- Starvation freedom: every pending ticket `t` (`c < t ≤ n`) is eventually served (Rocq
`starvation_free`). -/
@[lantana_alias starvation_free]
def starvationFree (next curr : Loc) : TrProp Exp State :=
  □ₜ (∀ₜ (n : Int) (c : Int) (t : Int), trPointsTo next (vz n) →ₜ trPointsTo curr (vz c) →ₜ
    ⌜c < t ∧ t ≤ n⌝ₜ →ₜ ◇ₜ trPointsTo curr (vz t))

/-- By induction on `t - c₀`, from any time at which `curr ↦ c₀ < t ≤ next`. -/
theorem releaseProgress_served (next curr : Loc) (k : Nat) (τf : Nat → TraceState Exp State)
    (t : Int) (Hrp : releaseProgress next curr ⟨k, τf⟩) (Hmon : nextMonotone next ⟨k, τf⟩) :
    ∀ (d m₀ : Nat) (c₀ : Int), (t - c₀).toNat = d → k ≤ m₀ →
      trPointsTo curr (vz c₀) ⟨m₀, τf⟩ → c₀ < t →
      (∃ n₀ : Int, trPointsTo next (vz n₀) ⟨m₀, τf⟩ ∧ t ≤ n₀) →
      ∃ m', m₀ ≤ m' ∧ trPointsTo curr (vz t) ⟨m', τf⟩ := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d IH =>
    intro m₀ c₀ hd hm₀ hc₀ hlt ⟨n₀, hn₀, htn₀⟩
    obtain ⟨m₁, hm₁, hc₁, -⟩ := Hrp m₀ hm₀ n₀ c₀ hn₀ hc₀ (by simp only [TrProp.pure]; omega)
    dsimp only at hm₁
    by_cases he : c₀ + 1 = t
    · subst he
      exact ⟨m₁, hm₁, hc₁⟩
    obtain ⟨n₁, hn₁, hle⟩ := Hmon m₀ hm₀ n₀ hn₀ m₁ hm₁
    simp only [TrProp.pure] at hle
    obtain ⟨m', hm', ht'⟩ := IH (t - (c₀ + 1)).toNat (by omega) m₁ (c₀ + 1) rfl (by omega) hc₁
      (by omega) ⟨n₁, hn₁, by omega⟩
    exact ⟨m', by omega, ht'⟩

@[lantana_alias release_progress_starvation_free]
theorem releaseProgress_starvationFree (next curr : Loc) (τ : Trace Exp State)
    (Hrp : releaseProgress next curr τ) (Hmon : nextMonotone next τ) :
    starvationFree next curr τ := by
  obtain ⟨k, τf⟩ := τ
  intro m hm n c t hn hc ht
  simp only [TrProp.pure] at ht
  obtain ⟨m', hm', ht'⟩ := releaseProgress_served next curr k τf t Hrp Hmon _ m c rfl hm hc
    ht.1 ⟨n, hn, ht.2⟩
  exact ⟨m', hm', ht', fun _ _ _ => trivial⟩

end Trace

end Lantana.Examples.TicketLock
