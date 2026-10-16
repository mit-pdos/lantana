/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.Instances.Lib.GhostMap
public import Lantana.Examples.Lib
public import Lantana.Examples.LockLevel

/-! # A starvation-free ticket lock

Rocq `examples/ticket_lock2.v`. Each ticket comes with an unlock obligation, allocated by its
acquiring thread, so that every pending ticket is eventually served
(`fairLock_starvationFree`).

TODO: complete the docstring.
-/

@[expose] public noncomputable section

namespace Lantana.Examples.TicketLock2

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open Iris.Std (get? insert delete)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The program -/

/-- `λ _, (ref 0, ref 0)`: the next ticket and the ticket being served. -/
@[lantana_alias ticket_lock2.TicketLock.init]
def init : Val := hl_val(λ _, (ref(#0), ref(#0)))

/-- Take a ticket, and spin until it is served. -/
@[lantana_alias ticket_lock2.TicketLock.acquire]
def acquire : Val :=
  hl_val(λ lnc,
    let next := fst(lnc);
    let curr := snd(lnc);
    let myTicket := faa(next, #1);
    (rec loop _ := if !curr = myTicket then #() else loop #()) #())

/-- Serve the next ticket. -/
@[lantana_alias ticket_lock2.TicketLock.release]
def release : Val := hl_val(λ lnc, let curr := snd(lnc); curr ← !curr + #1)

/-- The spin loop of `acquire`, waiting for the ticket `my` to be served. -/
abbrev spin (curr : Loc) (my : Int) : Val :=
  hl_val(rec loop _ := if !#curr = #my then #() else loop #())

/-! ## Ghost state -/

/-- The cameras of the lock (Rocq `ticket_lockG`): the obligations and the acknowledgements of
the tickets, and the level of the lock. -/
@[lantana_alias ticket_lock2.ticket_lockG]
class TicketLock2G (GF : BundledGFunctors) where
  [ticketG : GhostMapG GF Int Oid IntMap]
  [ackG : GhostMapG GF Int Bool IntMap]
  [levelG : LockLevelG GF]

attribute [reducible, instance] TicketLock2G.ticketG TicketLock2G.ackG TicketLock2G.levelG

#lantana_ignore ticket_lock2.«ticket_lockΣ»
  "Subsumed by the `BundledGFunctors` worlds (`Examples.ExGF`)."
#lantana_ignore ticket_lock2.«subG_ticket_lockΣ»
  "Subsumed by the `BundledGFunctors` worlds (`Examples.ExGF`)."

/-- The ghost names of a lock. -/
@[lantana_alias ticket_lock2.ticketlock_γ]
structure TicketLockName where
  /-- The obligations of the tickets. -/
  γt : GName
  /-- The acknowledgements of the tickets. -/
  γa : GName
  /-- The level of the lock. -/
  γc : GName

attribute [lantana_alias ticket_lock2.TicketLockName] TicketLockName.mk
attribute [lantana_alias ticket_lock2.ticketlock_γt] TicketLockName.γt
attribute [lantana_alias ticket_lock2.ticketlock_γa] TicketLockName.γa
attribute [lantana_alias ticket_lock2.ticketlock_γc] TicketLockName.γc

/-- The namespaces of the lock, of its invariant and of the unlock obligations. -/
def N : Namespace := nroot.@"ticket_lock"
def Ninv : Namespace := N.@"inv"
def Nev : Namespace := N.@"eventually"

@[lantana_alias ticket_lock2.N_subseteq_1]
theorem Nev_subseteq : (↑Nev : CoPset) ⊆ ⊤ \ ↑Ninv := by
  intro p hp
  refine Iris.Std.LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun h' => ?_⟩
  exact ndot_ne_disjoint N (by decide) p ⟨hp, h'⟩

#lantana_ignore ticket_lock2.N_disj_1 "Used only for `N_subseteq_1` (`Nev_subseteq`)."

/-- The layer of the obligation of the ticket `t` of a lock at level `ℓ`. -/
abbrev tkLayer (ℓ : Layer) (t : Int) : Layer := ℓ +ₕ Ordinals.Ordinal.ofNat t.toNat

/-- The value of an integer. -/
abbrev vInt (n : Int) : Val := hl_val(#n)

/-- Half of a points-to. -/
abbrev half : DFrac := .own (1 : Qp).half

/-! ## The invariant -/

section Invariant
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLock2G GF]

/-- The ticket `t`, whose obligation is `κ`: its registration, the witness of `κ` at the layer
`ℓ + t` for a level `ℓ` the lock has had; and `κ` is discharged if `t` has been served, or `t`
is pending and half of the finally of `κ` says that it will be served. -/
def ticketEntry (γt γc : GName) (curr : Loc) (R : IProp GF) (c n t : Int) (κ : Oid) :
    IProp GF :=
  iprop((∃ ℓ : Layer, (γt ↪◯MAP[t]{.discard} κ) ∗ Wit.layer κ (tkLayer ℓ t) ∗
      lockLevelLb γc ℓ) ∗
    ((⌜0 ≤ t ∧ t ≤ c⌝ ∧ Obl.discharged κ) ∨
      (⌜c + 1 ≤ t ∧ t ≤ n⌝ ∧ finallyI Nev κ (1 : Qp).half iprop(curr ↦{half} some (vInt t) ∗ R))))

/-- The acknowledgement of the ticket `t`: served tickets are acknowledged, the next one is
being served, and the later ones are not acknowledged (the other half is with their thread). -/
def ackEntry (γa : GName) (c n t : Int) : IProp GF :=
  iprop((⌜0 ≤ t ∧ t ≤ c⌝ ∧ (γa ↪◯MAP[t]{.discard} true)) ∨ ⌜t = c + 1⌝ ∨
    (⌜c + 1 < t ∧ t ≤ n⌝ ∧ (γa ↪◯MAP[t]{half} false)))

/-- The invariant of the lock (Rocq `lock_inv`): `next ↦ n`, half of `curr ↦ c`; the tickets
`0 … n` with their obligations and acknowledgements; and the lock is free with `R` and the other
half of `curr`, or the next ticket `c + 1` is not acknowledged yet (and the lock is free), or it
has been taken by its thread. -/
@[lantana_alias ticket_lock2.lock_inv]
def lockInv (γt γa γc : GName) (next curr : Loc) (R : IProp GF) : IProp GF :=
  iprop(∃ (n c : Int) (tickets : IntMap Oid) (acks : IntMap Bool),
    next ↦ some (vInt n) ∗ curr ↦{half} some (vInt c) ∗
    ((γt ↪●MAP tickets) ∗ (γa ↪●MAP acks)) ∗
    ⌜∀ t, (get? tickets t).isSome ↔ (get? acks t).isSome⌝ ∗
    ⌜0 ≤ c ∧ c ≤ n⌝ ∗
    ⌜∀ t, (get? tickets t).isSome ↔ (0 ≤ t ∧ t ≤ n)⌝ ∗
    bigSepM (M := IntMap) (fun t κ => ticketEntry γt γc curr R c n t κ) tickets ∗
    bigSepM (M := IntMap) (fun t (_ : Bool) => ackEntry γa c n t) acks ∗
    ((⌜c = n⌝ ∧ (curr ↦{half} some (vInt c) ∗ R)) ∨
      (⌜c < n⌝ ∧ (((γa ↪◯MAP[c + 1]{half} false) ∗ curr ↦{half} some (vInt c) ∗ R) ∨
        (γa ↪◯MAP[c + 1]{.discard} true)))))

/-- The holder of the lock serving `u` (Rocq `lock_token`): the other half of `curr`, the
registration of its unlock obligation `κu` at `u + 1`, and half of its finally. -/
@[lantana_alias ticket_lock2.lock_token]
def lockToken (tl : Val) (γ : TicketLockName) (κu : Oid) (R : IProp GF) : IProp GF :=
  iprop(∃ (next curr : Loc) (u : Int), ⌜tl = hl_val((#next, #curr))⌝ ∧
    (curr ↦{half} some (vInt u) ∗ (γ.γt ↪◯MAP[u + 1]{.discard} κu) ∗
      finallyI Nev κu (1 : Qp).half iprop(curr ↦{half} some (vInt (u + 1)) ∗ R)))

#lantana_ignore ticket_lock2.lock_token_def "`lockToken` is not sealed."
#lantana_ignore ticket_lock2.lock_token_aux "`lockToken` is not sealed."
#lantana_ignore ticket_lock2.lock_token_unseal "`lockToken` is not sealed."

/-- The lock `tl` protecting `R` (Rocq `is_fair_lock`). -/
@[lantana_alias ticket_lock2.is_fair_lock]
def isFairLock (tl : Val) (γ : TicketLockName) (R : IProp GF) : IProp GF :=
  iprop(∃ next curr : Loc, ⌜tl = hl_val((#next, #curr))⌝ ∧
    alwaysI Ninv (lockInv γ.γt γ.γa γ.γc next curr R))

/-- The fraction `dq` of the level `ℓ` of the lock (Rocq `own_fair_lock_level`, notation
`γ ↪LOCK{dq} ℓ`). -/
@[lantana_alias ticket_lock2.own_fair_lock_level]
def ownFairLockLevel (γ : TicketLockName) (ℓ : Layer) (dq : DFrac) : IProp GF :=
  lockLevel γ.γc dq ℓ

@[lantana_alias ticket_lock2.is_fair_lock_persistent]
instance isFairLock_persistent (tl : Val) (γ : TicketLockName) (R : IProp GF) :
    Persistent (isFairLock tl γ R) := by
  unfold isFairLock; infer_instance

omit [ModelGS GF] [HeapGS GF] in
@[lantana_alias ticket_lock2.lock_reconfig]
theorem lock_reconfig (γ : TicketLockName) {ℓ₁ ℓ₂ : Layer} (h : ℓ₁ ≤ ℓ₂) :
    ownFairLockLevel (GF := GF) γ ℓ₁ (.own 1) ⊢ |==> ownFairLockLevel γ ℓ₂ (.own 1) :=
  lockLevel_update γ.γc h

omit [ModelGS GF] [HeapGS GF] in
@[lantana_alias ticket_lock2.lock_config_persist]
theorem lock_config_persist (γ : TicketLockName) (dq : DFrac) (ℓ : Layer) :
    ownFairLockLevel (GF := GF) γ ℓ dq ⊢ |==> ownFairLockLevel γ ℓ .discard :=
  lockLevel_persist γ.γc dq ℓ

/-- `ticketEntry` unfolded (for `icases`, which does not unfold definitions). -/
theorem ticketEntry_iff (γt γc : GName) (curr : Loc) (R : IProp GF) (c n t : Int) (κ : Oid) :
    ticketEntry γt γc curr R c n t κ ⊣⊢
      (∃ ℓ : Layer, (γt ↪◯MAP[t]{.discard} κ) ∗ Wit.layer κ (tkLayer ℓ t) ∗
        lockLevelLb γc ℓ) ∗
      ((⌜0 ≤ t ∧ t ≤ c⌝ ∧ Obl.discharged κ) ∨
        (⌜c + 1 ≤ t ∧ t ≤ n⌝ ∧
          finallyI Nev κ (1 : Qp).half iprop(curr ↦{half} some (vInt t) ∗ R))) := by
  unfold ticketEntry; exact .rfl

omit [ModelGS GF] [HeapGS GF] in
/-- `ackEntry` unfolded. -/
theorem ackEntry_iff (γa : GName) (c n t : Int) :
    ackEntry (GF := GF) γa c n t ⊣⊢
      (⌜0 ≤ t ∧ t ≤ c⌝ ∧ (γa ↪◯MAP[t]{.discard} true)) ∨ ⌜t = c + 1⌝ ∨
        (⌜c + 1 < t ∧ t ≤ n⌝ ∧ (γa ↪◯MAP[t]{half} false)) := by
  unfold ackEntry; exact .rfl

/-- A ticket stays registered when more tickets are taken. -/
theorem ticketEntry_take (γt γc : GName) (curr : Loc) (R : IProp GF) {c n n' t : Int}
    (κ : Oid) (h : n ≤ n') :
    ticketEntry γt γc curr R c n t κ ⊢ ticketEntry γt γc curr R c n' t κ := by
  unfold ticketEntry
  iintro ⟨H1, (⟨%ht, H2⟩ | ⟨%ht, H2⟩)⟩
  · iframe H1
    ileft
    isplit
    · ipureintro
      exact ht
    · iexact H2
  · iframe H1
    iright
    isplit
    · ipureintro
      omega
    · iexact H2

omit [ModelGS GF] [HeapGS GF] in
/-- An acknowledgement stays when more tickets are taken. -/
theorem ackEntry_take (γa : GName) {c n n' t : Int} (h : n ≤ n') :
    ackEntry (GF := GF) γa c n t ⊢ ackEntry γa c n' t := by
  unfold ackEntry
  iintro (⟨%ht, #H⟩ | %ht | ⟨%ht, H⟩)
  · ileft
    isplit
    · ipureintro
      exact ht
    · iexact H
  · iright
    ileft
    ipureintro
    exact ht
  · iright
    iright
    isplit
    · ipureintro
      omega
    · iexact H

/-- A ticket other than the next one stays registered when the next one is served. -/
theorem ticketEntry_serve (γt γc : GName) (curr : Loc) (R : IProp GF) {c n t : Int}
    (κ : Oid) (ht : t ≠ c + 1) :
    ticketEntry γt γc curr R c n t κ ⊢ ticketEntry γt γc curr R (c + 1) n t κ := by
  unfold ticketEntry
  iintro ⟨H1, (⟨%ht', H2⟩ | ⟨%ht', H2⟩)⟩
  · iframe H1
    ileft
    isplit
    · ipureintro
      omega
    · iexact H2
  · iframe H1
    iright
    isplit
    · ipureintro
      omega
    · iexact H2

omit [ModelGS GF] [HeapGS GF] in
/-- When the next ticket `c + 1` has been acknowledged and is served, the acknowledgements of
the tickets other than `c + 2` stay. -/
theorem ackEntry_serve (γa : GName) {c n t : Int} (hc : 0 ≤ c) (ht : t ≠ c + 2) :
    (γa ↪◯MAP[c + 1]{.discard} true) ⊢ ackEntry (GF := GF) γa c n t -∗ ackEntry γa (c + 1) n t := by
  unfold ackEntry
  iintro #Hc (⟨%ht', #H⟩ | %ht' | ⟨%ht', H⟩)
  · ileft
    isplit
    · ipureintro
      omega
    · iexact H
  · ileft
    subst ht'
    isplit
    · ipureintro
      omega
    · iexact Hc
  · iright
    iright
    isplit
    · ipureintro
      omega
    · iexact H

end Invariant

/-! ## Specifications -/

section Specs
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLock2G GF]

@[lantana_alias ticket_lock2.TicketLock_init_spec]
theorem init_spec : ∃ m : Measure, ∀ (lc : Fuel) (ℓ : Layer) (i : ThreadId) (G : Oids)
    (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&init) #()) ∗ thKids i G ∗ oblFuels G m }}}
        hl(v(&init) #()) @ i
      l{{{ (tl : Val) (γ : TicketLockName), RET tl; threadExpr i C hl(v(&tl)) ∗ £ₒ lc ∗
        thKids i G ∗ ownFairLockLevel γ ℓ (.own 1) ∗
        (∀ (E : CoPset) (R : IProp GF), R -∗ |={E}=>m isFairLock tl γ R) }}} := by
  refine ⟨4, fun lc ℓ i G C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF⟩ HΦ
  unfold init
  lwp_step HT HG HF
  lwp_expr_simp
  -- `curr` first (right to left), then `next`.
  icases oblFuels_add 1 2 G $$ HF with ⟨HF1, HF⟩
  lwp_bind hl(ref(#0)) HT
  iapply lwp_alloc (o := 0) (G := G) (R := ∅) $$ [HT HG HF1]
  · iframe HT
    iapply stepPre_nil $$ HG HF1
  iintro %curr ⟨HT, ⟨-, HG, -⟩, Hcurr⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  icases oblFuels_add 1 1 G $$ HF with ⟨HF1, HF⟩
  lwp_bind hl(ref(#0)) HT
  iapply lwp_alloc (o := 0) (G := G) (R := ∅) $$ [HT HG HF1]
  · iframe HT
    iapply stepPre_nil $$ HG HF1
  iintro %next ⟨HT, ⟨-, HG, -⟩, Hnext⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF with Hlc : lc
  -- The ghost state: ticket `0`, served, with a discharged obligation.
  imod Obl.new_discharged ⊤ (tkLayer ℓ 0) with ⟨%κ, #Dκ, #Wκ⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Int) (V := Oid) (H := IntMap) with ⟨%γt, GMt⟩
  imod ghost_map_insert_persist 0 κ (Iris.Std.LawfulPartialMap.get?_empty _) $$ GMt
    with ⟨GMt, #Mt⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Int) (V := Bool) (H := IntMap) with ⟨%γa, GMa⟩
  imod ghost_map_insert_persist 0 true (Iris.Std.LawfulPartialMap.get?_empty _) $$ GMa
    with ⟨GMa, #Ma⟩
  imod lockLevel_alloc (GF := GF) ℓ with ⟨%γc, CF⟩
  ihave #CFl := lockLevel_lb γc _ ℓ $$ CF
  icases (pointsTo_halves curr _).mp $$ Hcurr with ⟨Hc1, Hc2⟩
  iapply lwp_value'
  iapply HΦ $$ %_ %⟨γt, γa, γc⟩
  iframe HT Hlc HG
  isplitl [CF]
  · unfold ownFairLockLevel
    iexact CF
  iintro %E %R HR
  imod alwaysI_alloc (E := E) (N := Ninv) (P := lockInv γt γa γc next curr R)
    $$ [Hnext Hc1 Hc2 GMt GMa HR] with #HA
  · inext
    unfold lockInv
    iexists 0, 0, insert ∅ 0 κ, insert ∅ 0 true
    iframe Hnext Hc1 GMt GMa
    isplitr
    · ipureintro
      intro t
      simp only [Iris.Std.LawfulPartialMap.get?_insert, Iris.Std.LawfulPartialMap.get?_empty]
      split <;> simp
    isplitr
    · ipureintro
      omega
    isplitr
    · ipureintro
      intro t
      simp only [Iris.Std.LawfulPartialMap.get?_insert, Iris.Std.LawfulPartialMap.get?_empty]
      split
      · subst_vars
        simp
      · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
        omega
    isplitr
    · iapply (BigSepM.bigSepM_insert (Iris.Std.LawfulPartialMap.get?_empty _)).mpr
      isplitl
      · unfold ticketEntry
        isplitl
        · iexists ℓ
          iframe Mt Wκ CFl
        · ileft
          isplit
          · ipureintro
            omega
          · iexact Dκ
      · iapply BigSepM.bigSepM_empty.mpr
        iempintro
    isplitr
    · iapply (BigSepM.bigSepM_insert (Iris.Std.LawfulPartialMap.get?_empty _)).mpr
      isplitl
      · unfold ackEntry
        ileft
        isplit
        · ipureintro
          omega
        · iexact Ma
      · iapply BigSepM.bigSepM_empty.mpr
        iempintro
    ileft
    isplit
    · ipureintro
      rfl
    · iframe
  imodintro
  unfold isFairLock
  iexists next, curr
  isplit
  · ipureintro
    rfl
  · iexact HA

/-- The spin loop of `acquire` for the ticket `my`, by induction on the witness fuel of the
obligation `κp` of the ticket `my` (the unlock obligation of the previous holder): each
iteration in which `my` is not served observes `κp`, whose credit buys the fuel of the next
iteration. When `my` is served, the thread acknowledges its ticket `my + 1` and takes `R`. -/
theorem acquire_spin (i : ThreadId) (C : List ECtxItem) (G : Oids) (next curr : Loc)
    (γ : TicketLockName) (R : IProp GF) (my : Int) (κp κu : Oid) (ℓw : Layer)
    (F : OidMap (Layer × Measure))
    (hF : ([∗map] f ↦ lm ∈ F, Obl.fuel (GF := GF) f lm.1 lm.2) ⊢ oblFuels G 4)
    (lc : Fuel) (Φ : Val → IProp GF) (α : Fuel) :
    alwaysI Ninv (lockInv γ.γt γ.γa γ.γc next curr R) ⊢
      (γ.γt ↪◯MAP[my]{.discard} κp) -∗ Wit.layer κp ℓw -∗
      (γ.γt ↪◯MAP[my + 1]{.discard} κu) -∗ (γ.γa ↪◯MAP[my + 1]{half} false) -∗
      Wit.fuels κp ℓw α F -∗
      threadExpr i C hl(v(&(spin curr my)) #()) -∗ thKids i G -∗ oblFuels G 4 -∗
      (threadExpr i C hl(#()) -∗ £ₒ lc -∗ thKids i G -∗ curr ↦{half} some (vInt my) -∗ R -∗
        Φ hl_val(#())) -∗
      lWP hl(v(&(spin curr my)) #()) @ i {{ Φ }} := by
  induction α using WellFounded.induction Ordinals.Ordinal.lt_wf with
  | h α IH =>
  iintro #Hinv #Mtp #Wp #Mtu Ma WF HT HG HF HΦ
  lwp_step HT HG HF with Hc : 1
  lwp_expr_simp
  sorry

end Specs

end Lantana.Examples.TicketLock2
