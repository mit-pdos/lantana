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
(`fairLock_starvationFree`). The lock is not deletable; it is independent of the deletable
ticket lock of `Examples.TicketLock`.

Ghost state (`TicketLock2G`): a ghost map `γt` from tickets to their obligations, a ghost map
`γa` from tickets to acknowledgements, and the level `γc` of the lock (`Examples.LockLevel`,
Rocq `auth_mra (ord.le)`, notation `γ ↪LOCK{dq} ℓ`: `ownFairLockLevel γ ℓ dq`). The invariant
`lockInv` holds `next ↦ n`, half of `curr ↦ c` and, for each ticket `t ≤ n`, its registered
obligation `κ` with a witness at the layer `ℓ + t` (`tkLayer`) for a level `ℓ` the lock has had;
`κ` is discharged if `t ≤ c`, else half of `finallyI Nev κ (curr ↦ t ∗ R)` is there. The thread
of ticket `t` (whose `faa` returned `t - 1`) owns the other half; the acknowledgements make sure
that only it takes `R` when `curr` reaches `t - 1`.

* `init_spec` (measure `4`): the cells, ticket `0` with a discharged obligation, and the lock,
  whose invariant is allocated later for any `R` (Rocq: same).
* `acquire_spec` (measure `1` at the layer `ℓ + aleph`, lowered to `ℓ + ω`): `faa` takes the
  ticket `my`, allocates the unlock obligation `κu` at `ℓ + (my + 1)` and registers it; the spin
  loop (`acquire_spin`) is a witness induction on the obligation `κp` of the ticket `my` (the
  previous holder's), at `ℓ0 + my < ℓ + (my + 1)`: each unsuccessful iteration observes `κp`, and
  its credit gives `50` units of fuel at `ℓ + (my + 1)` to every child. The thread returns with
  `κu` (fuel `μ` at `ℓ`), the lock token and `R`.
* `release_spec` (measure `100`): the store to `curr` discharges `κu` with `curr ↦ u + 1 ∗ R`
  (`finallyI_discharge`, one later credit); the next ticket, if any, finds the lock free.

Guarantees (`GuarOf`, inferred): `lockInvTrSpec` (Rocq `lock_inv_trSpec`), `fairLockTrSpec`,
`lockTokenTrSpec`; at the level of traces, `starvationFree` (whenever `next ↦ n` and `curr ↦ c`,
each `t` with `c < t ≤ n` is eventually served) and `lockTokenTr`.

Adaptations. Rocq's layer `ℵ` (`ord.large`) of the acquiring fuel has no counterpart among the
layers `Ordinal.{0}`; `aleph := succ ω` is used, as the proof only needs a layer above `ω`.
Tickets are `Int`s and the maps `IntMap`s; Rocq's `dom tickets = dom acks` and
`t ∈ dom tickets ↔ 0 ≤ t ≤ n` are stated with `get?`. The entries of the big separating
conjunctions are definitions (`ticketEntry`, `ackEntry`, with `_iff` lemmas and `GuarOf`
instances), so that an entry taken out can be put back. The invariant's `κp` (the obligation the
thread waits for) is read during `faa` (Rocq: in a second opening of the invariant); the spin loop
is a separate lemma, by well-founded induction on the witness fuel (Rocq: `iInduction` inside
`acquire`). `lockToken` is not sealed. Aliases are prefixed with `ticket_lock2.`.

Everything here is proved.
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

/-- A layer above `ω`, for the waiting of `acquire`: Rocq's layer `ℵ` (`ord.large`, above the
ranks of all small well-founded relations) has no counterpart among the layers `Ordinal.{0}`;
the proof only needs a layer above `ω`. -/
abbrev aleph : Layer := Ordinals.Ordinal.succ ω

theorem omega_lt_aleph (ℓ : Layer) : ℓ +ₕ ω < ℓ +ₕ aleph :=
  Ordinals.Ordinal.nadd_lt_nadd_left (Ordinals.Ordinal.lt_succ ω) ℓ

theorem lt_tkLayer (ℓ : Layer) {t : Int} (ht : 0 < t) : ℓ < tkLayer ℓ t := by
  have h := Ordinals.Ordinal.nadd_lt_nadd_left (a := ℓ)
    (Ordinals.Ordinal.ofNat_lt_ofNat_iff.mpr (show 0 < t.toNat by omega))
  rwa [Ordinals.Ordinal.ofNat_zero, Ordinals.Ordinal.nadd_zero] at h

theorem tkLayer_lt_tkLayer {ℓ ℓ' : Layer} {t t' : Int} (hℓ : ℓ ≤ ℓ') (ht : 0 ≤ t)
    (htt : t < t') : tkLayer ℓ t < tkLayer ℓ' t' :=
  Ordinals.Ordinal.lt_of_le_of_lt
    (Ordinals.Ordinal.nadd_le_nadd hℓ (Ordinals.Ordinal.le_refl _))
    (Ordinals.Ordinal.nadd_lt_nadd_left
      (Ordinals.Ordinal.ofNat_lt_ofNat_iff.mpr (by omega)) ℓ')

theorem tkLayer_lt_omega (ℓ : Layer) (t : Int) : tkLayer ℓ t < ℓ +ₕ ω :=
  Ordinals.Ordinal.nadd_lt_nadd_left (Ordinals.Ordinal.ofNat_lt_omega _) ℓ

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
abbrev ownFairLockLevel (γ : TicketLockName) (ℓ : Layer) (dq : DFrac) : IProp GF :=
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
the tickets other than `c + 1 + 1` stay. -/
theorem ackEntry_serve (γa : GName) {c n t : Int} (hc : 0 ≤ c) (ht : t ≠ c + 1 + 1) :
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
  -- The load of `curr`, in the invariant; it observes `κp`.
  lwp_bind hl(!#curr) HT
  ihave Hacc := alwaysI_acc (E := ⊤) (N := Ninv) (P := lockInv γ.γt γ.γa γ.γc next curr R)
    (fun _ _ => CoPset.mem_full) $$ Hinv
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨Hi, Hclose⟩
  iapply lwp_credit_later $$ Hc
  inext
  iunfold lockInv at Hi
  icases Hi with ⟨%n, %c, %tickets, %acks, Hnext, Hcurr, ⟨GMt, GMa⟩, %hdom, %hc, %hdomt, HMt,
    HMa, Hlast⟩
  icases oblFuels_add 1 2 G $$ HF with ⟨HF1, HF⟩
  iapply lwp_load (o := 0) (C := _ ++ C) (G := G) (R := {κp}) $$ [HT HG HF1 Hcurr]
  · iframe HT Hcurr
    iapply stepPre_wit $$ HG HF1 Wp
  iintro ⟨HT, ⟨-, HG, HW⟩, Hcurr⟩
  ihave %LUa := ghost_map_lookup $$ GMa Ma
  by_cases hmy : c = my
  · -- My turn: acknowledge the ticket `my + 1` and take `R`.
    subst hmy
    ihave %LUt := ghost_map_lookup $$ GMt Mtu
    have hcn : c + 1 ≤ n := ((hdomt (c + 1)).mp (by simp [LUt])).2
    icases Hlast with (⟨%hcn', -⟩ | ⟨%hcn', (⟨Ma2, Hcurr2, HR⟩ | #Ha)⟩)
    · exact absurd hcn' (by omega)
    rotate_left
    · iexfalso
      ihave %h := ghost_map_elem_agree $$ [Ma Ha]
      · iframe Ma
        iexact Ha
      simp at h
    ihave Mfull := (ghostMapElem_halves _ _ _).mpr $$ [Ma Ma2]
    · iframe
    imod ghost_map_update true $$ GMa Mfull with ⟨GMa, Mfull⟩
    imod ghost_map_elem_persist $$ Mfull with #Ma'
    imod Hclose $$ [Hnext Hcurr GMt GMa HMt HMa] with -
    · inext
      iunfold lockInv
      iexists n, c, tickets, insert acks (c + 1) true
      iframe Hnext Hcurr GMt GMa HMt
      isplitr
      · ipureintro
        intro t
        rw [hdom t, Iris.Std.LawfulPartialMap.get?_insert]
        split
        · subst_vars
          simp [LUa]
        · rfl
      isplitr
      · ipureintro
        exact hc
      isplitr
      · ipureintro
        exact hdomt
      isplitl [HMa]
      · iapply BigSepM.bigSepM_insert_delete.mpr
        iapply (BigSepM.bigSepM_delete LUa).mp $$ HMa
      iright
      isplit
      · ipureintro
        omega
      · iright
        iexact Ma'
    imodintro
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    lwp_step HT HG HF
    simp only [beq_self_eq_true]
    lwp_step HT HG HF with Hlc : lc
    iapply lwp_value'
    iapply HΦ $$ HT Hlc HG Hcurr2 HR
  · -- Not my turn: `κp` is not discharged, and its credit pays the next iteration.
    icases witCreds_singleton κp $$ HW with (Hcr | #Hd)
    rotate_left
    · iexfalso
      ihave %LUp := ghost_map_lookup $$ GMt Mtp
      icases (BigSepM.bigSepM_delete LUp).mp $$ HMt with ⟨Hp, -⟩
      icases (ticketEntry_iff _ _ _ _ _ _ _ _).mp $$ Hp with ⟨-, (⟨%hp, -⟩ | ⟨%hp, Hu⟩)⟩
      · -- `my` has been served before: its successor `my + 1` would be acknowledged.
        icases (BigSepM.bigSepM_delete LUa).mp $$ HMa with ⟨Ha, -⟩
        icases (ackEntry_iff _ _ _ _).mp $$ Ha with (⟨%ha, #Ht⟩ | %ha | ⟨%ha, -⟩)
        · ihave %h := ghost_map_elem_agree $$ [Ma Ht]
          · iframe Ma
            iexact Ht
          simp at h
        · exact absurd ha (by omega)
        · exact absurd ha.1 (by omega)
      · iunfold finallyI at Hu
        iapply untilI_discharged_false $$ Hu Hd
    imod Hclose $$ [Hnext Hcurr GMt GMa HMt HMa Hlast] with -
    · inext
      iunfold lockInv
      iexists n, c, tickets, acks
      iframe Hnext Hcurr GMt GMa HMt HMa Hlast
      ipureintro
      exact ⟨hdom, hc, hdomt⟩
    imodintro
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    imod Wit.fuels_decr κp ℓw α F $$ WF Hcr with ⟨%α₀, %hlt, WF, Fs⟩
    ihave HF' := hF $$ Fs
    lwp_step HT HG HF
    rw [show (vInt c == vInt my) = false by simp [hmy]]
    lwp_step HT HG HF
    iapply IH α₀ hlt $$ Hinv Mtp Wp Mtu Ma WF HT HG HF' HΦ

/-- Acquiring: the thread takes the ticket `my` and spins until it is served. Its unlock
obligation `κu`, a new child at the layer `ℓ + (my + 1)` registered at the ticket `my + 1`,
pays for the spinning together with the fuel of the other children (lowered from `ℓ + ℵ` to
`ℓ + ω`), and comes back with fuel `μ` at the level `ℓ` for the critical section. -/
@[lantana_alias ticket_lock2.TicketLock_acquire_spec]
theorem acquire_spec : ∃ m : Measure, ∀ (lc : Fuel) (μ : Measure) (i : ThreadId) (G : Oids)
    (tl : Val) (γ : TicketLockName) (dq : DFrac) (ℓ : Layer) (R : IProp GF)
    (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&acquire) v(&tl)) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g (ℓ +ₕ aleph) m) ∗ ownFairLockLevel γ ℓ dq ∗
          isFairLock tl γ R }}}
        hl(v(&acquire) v(&tl)) @ i
      l{{{ (κu : Oid), RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ ⌜κu ∉ G⌝ ∗
        thKids i (G.insert κu) ∗ oblKids κu ∅ ∗ Obl.fuel κu ℓ μ ∗ ownFairLockLevel γ ℓ dq ∗
        lockToken tl γ κu R ∗ R }}} := by
  refine ⟨1, fun lc μ i G tl γ dq ℓ R C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, CF, #Hfl⟩ HΦ
  -- The fuel of the children, at the layer `ℓ + ω`: `100` for the steps, `1` for the loop.
  imod Obl.fuel_extend_set G (omega_lt_aleph ℓ) ((100 : Measure) + 1) $$ HF with HF
  icases (Obl.fuel_add_set G _ _ _).mp $$ HF with ⟨HF, HFw⟩
  ihave HF := oblFuels_init G 100 _ $$ HF
  unfold isFairLock
  icases Hfl with ⟨%next, %curr, %htl, #Hinv⟩
  subst htl
  unfold acquire
  lwp_step HT HG HF with Hc : 1
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- The ticket: `faa` on `next`, in the invariant; the unlock obligation follows the step.
  lwp_bind hl(faa(#next, #1)) HT
  icases oblFuels_add 1 92 G $$ HF with ⟨HF1, HF⟩
  ihave Hacc := alwaysI_acc (E := ⊤) (N := Ninv) (P := lockInv γ.γt γ.γa γ.γc next curr R)
    (fun _ _ => CoPset.mem_full) $$ Hinv
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨Hi, Hclose⟩
  iapply lwp_credit_later $$ Hc
  inext
  iunfold lockInv at Hi
  icases Hi with ⟨%n, %c, %tickets, %acks, Hnext, Hcurr, ⟨GMt, GMa⟩, %hdom, %hc, %hdomt, HMt,
    HMa, Hlast⟩
  iapply lwp_faa (o := 0) (C := _ ++ C) (G := G) (R := ∅) $$ [HT HG HF1 Hnext]
  · iframe HT Hnext
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, Hnext⟩
  -- The obligation `κp` of the ticket `n`, which this thread waits for.
  obtain ⟨κp, hκp⟩ := Option.isSome_iff_exists.mp ((hdomt n).mpr ⟨by omega, by omega⟩)
  icases (BigSepM.bigSepM_delete hκp).mp $$ HMt with ⟨Hp, HMt⟩
  icases (ticketEntry_iff _ _ _ _ _ _ _ _).mp $$ Hp with ⟨⟨%ℓ0, #Mtp, #Wp, #CFp⟩, Hp⟩
  ihave HMt : bigSepM (M := IntMap) (fun t κ => ticketEntry γ.γt γ.γc curr R c n t κ) tickets
    $$ [Hp HMt]
  · iapply (BigSepM.bigSepM_delete hκp).mpr
    iframe HMt
    iapply (ticketEntry_iff _ _ _ _ _ _ _ _).mpr
    iframe Hp
    iexists ℓ0
    iframe Mtp Wp CFp
  icases lockLevel_lb_valid _ _ _ _ $$ CF CFp with ⟨CF, %hℓ0⟩
  icases lockLevel_get_lb _ _ _ $$ CF with ⟨CF, #CFl⟩
  -- The unlock obligation `κu` of the ticket `n + 1`.
  imod untilI_alloc (E := ⊤ \ ↑Ninv) (.thread i) G (tkLayer ℓ (n + 1))
    (((50 : Measure) + 50 * ▽) + 1) $$ [] HG with ⟨%κu, %hκu, HG, Kκu, Fκu, #Wκu, A⟩
  · iapply parLe_thread
  imod A $$ %(⊤ \ ↑Ninv) %Nev %iprop(True) %iprop(curr ↦{half} some (vInt (n + 1)) ∗ R) []
    with U
  · inext
    ipureintro
    trivial
  icases untilI_frac_split (q₁ := (1 : Qp).half) (q₂ := (1 : Qp).half) (Qp.half_add_half 1).symm
    $$ U with ⟨U1, U2⟩
  icases (Obl.fuel_add κu _ _ _).mp $$ Fκu with ⟨Fκu, Qκu⟩
  imod Obl.fuel_extend κu (lt_tkLayer ℓ (t := n + 1) (by omega)) μ $$ Qκu with Qκu
  have hnt : get? tickets (n + 1) = none := by
    cases h : get? tickets (n + 1) with
    | none => rfl
    | some _ =>
      have := ((hdomt (n + 1)).mp (by simp [h])).2
      omega
  have hna : get? acks (n + 1) = none := by
    cases h : get? acks (n + 1) with
    | none => rfl
    | some _ =>
      have := ((hdomt (n + 1)).mp ((hdom (n + 1)).mpr (by simp [h]))).2
      omega
  imod ghost_map_insert_persist (n + 1) κu hnt $$ GMt with ⟨GMt, #Mtu⟩
  imod ghost_map_insert (n + 1) false hna $$ GMa with ⟨GMa, Ma⟩
  icases (ghostMapElem_halves _ _ _).mp $$ Ma with ⟨Ma1, Ma2⟩
  imod Hclose $$ [Hnext Hcurr GMt GMa HMt HMa Hlast U2 Ma2] with -
  · inext
    iunfold lockInv
    iexists n + 1, c, insert tickets (n + 1) κu, insert acks (n + 1) false
    iframe Hnext Hcurr GMt GMa
    isplitr
    · ipureintro
      intro t
      rw [Iris.Std.LawfulPartialMap.get?_insert, Iris.Std.LawfulPartialMap.get?_insert]
      split
      · simp
      · exact hdom t
    isplitr
    · ipureintro
      omega
    isplitr
    · ipureintro
      intro t
      rw [Iris.Std.LawfulPartialMap.get?_insert]
      split
      · subst_vars
        simp only [Option.isSome_some, true_iff]
        omega
      · rw [hdomt t]
        omega
    isplitl [HMt U2]
    · iapply (BigSepM.bigSepM_insert hnt).mpr
      isplitl [U2]
      · iapply (ticketEntry_iff _ _ _ _ _ _ _ _).mpr
        isplitr
        · iexists ℓ
          iframe Mtu Wκu CFl
        · iright
          isplit
          · ipureintro
            omega
          · iunfold finallyI
            iexact U2
      · iapply BigSepM.bigSepM_mono (fun _ => ticketEntry_take _ _ _ _ _ (by omega)) $$ HMt
    icases Hlast with (⟨%hcn, Hcurr2, HR⟩ | ⟨%hcn, Hl⟩)
    · -- The lock was free: the new ticket is the next one.
      isplitl [HMa]
      · iapply (BigSepM.bigSepM_insert hna).mpr
        isplitr
        · iapply (ackEntry_iff _ _ _ _).mpr
          iright
          ileft
          ipureintro
          omega
        · iapply BigSepM.bigSepM_mono (fun _ => ackEntry_take _ (by omega)) $$ HMa
      iright
      isplit
      · ipureintro
        omega
      · ileft
        subst hcn
        iframe
    · isplitl [HMa Ma2]
      · iapply (BigSepM.bigSepM_insert hna).mpr
        isplitl [Ma2]
        · iapply (ackEntry_iff _ _ _ _).mpr
          iright
          iright
          isplit
          · ipureintro
            omega
          · iexact Ma2
        · iapply BigSepM.bigSepM_mono (fun _ => ackEntry_take _ (by omega)) $$ HMa
      iright
      isplit
      · ipureintro
        omega
      · iexact Hl
  imodintro
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  -- The fuel of the steps: `50` from the old children and from `κu`.
  icases (Obl.fuel_add κu _ _ _).mp $$ Fκu with ⟨Fκu, Fκw⟩
  icases oblFuels_add 42 50 G $$ HF with ⟨-, HF⟩
  ihave HF := oblFuels_add_obl G κu _ _ $$ Fκu HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  -- The witness induction on `κp` (at `ℓ0 + n < ℓ + (n + 1)`): `50` per credit for the children.
  imod Obl.fuel_extend_set G (tkLayer_lt_omega ℓ (n + 1)) (50 * ▽) $$ HFw with HFw
  ihave HFw := (bigSepS_insert_oids hκu).mpr $$ [HFw Fκw]
  · iframe
  icases Wit.fuels_init κp (tkLayer ℓ0 n) $$ Wp with ⟨%α, WF⟩
  imod Wit.fuels_add_map κp (tkLayer ℓ0 n) α ∅ (G.insert κu) (tkLayer ℓ (n + 1)) 50
    (tkLayer_lt_tkLayer hℓ0 (by omega) (by omega)) $$ WF HFw with WF
  have hF : ([∗map] f ↦ lm ∈ ((∅ : OidMap (Layer × Measure)) ∪
      (Iris.Std.FiniteMap.ofSet (tkLayer ℓ (n + 1), (50 : Measure)) (G.insert κu) :
        OidMap (Layer × Measure))), Obl.fuel (GF := GF) f lm.1 lm.2) ⊢
      oblFuels (G.insert κu) 4 := by
    rw [OidMap.empty_union]
    refine (BigSepM.bigSepM_ofSet
      (fun f (lm : Layer × Measure) => Obl.fuel (GF := GF) f lm.1 lm.2) (G.insert κu)
      _).1.trans ?_
    refine (oblFuels_init _ 50 _).trans ?_
    exact (oblFuels_add 4 46 _).trans sep_elim_left
  icases oblFuels_add 4 43 _ $$ HF with ⟨HF, -⟩
  iapply acquire_spin i C (G.insert κu) next curr γ R n κp κu (tkLayer ℓ0 n) _ hF lc Φ α
    $$ Hinv Mtp Wp Mtu Ma1 WF HT HG HF [HΦ Kκu Qκu CF U1]
  iintro HT Hlc HG Hcurr2 HR
  iapply HΦ $$ %κu
  iframe HT Hlc HG Kκu Qκu CF HR
  isplitr
  · ipureintro
    exact hκu
  unfold lockToken
  iexists next, curr, n
  isplit
  · ipureintro
    rfl
  · iunfold finallyI
    iframe Hcurr2 Mtu U1

/-- Releasing: the holder increments `curr` (its half and the invariant's), which serves the
next ticket: its unlock obligation `κu` is discharged with `curr ↦ u + 1` and `R` (a later
credit for the finally), and the next ticket's thread, if any, finds the lock free with its
acknowledgement pending. -/
@[lantana_alias ticket_lock2.TicketLock_release_spec]
theorem release_spec : ∃ m : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids) (tl : Val)
    (γ : TicketLockName) (R : IProp GF) (κu : Oid) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&release) v(&tl)) ∗ thKids i G ∗ oblFuels G m ∗
          ⌜κu ∈ G⌝ ∗ oblKids κu ∅ ∗ lockToken tl γ κu R ∗ R ∗ isFairLock tl γ R }}}
        hl(v(&release) v(&tl)) @ i
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i (G.erase κu) }}} := by
  refine ⟨100, fun lc i G tl γ R κu C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hκu, Kκu, Htok, HR, #Hfl⟩ HΦ
  unfold lockToken
  icases Htok with ⟨%next, %curr, %u, %htl, Hcu, #Mtu, Uu⟩
  subst htl
  unfold isFairLock
  icases Hfl with ⟨%next', %curr', %htl', #Hinv⟩
  obtain ⟨rfl, rfl⟩ : next = next' ∧ curr = curr' := by
    simpa only [Val.pair.injEq, Val.lit.injEq, BaseLit.loc.injEq] using htl'
  unfold release
  lwp_step HT HG HF with Hc : Ordinals.Ordinal.ofNat (1 + 1)
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- The load of `curr`, with the holder's half.
  lwp_bind hl(!#curr) HT
  icases oblFuels_add 1 95 G $$ HF with ⟨HF1, HF⟩
  iapply lwp_load (o := 0) (C := _ ++ C) (G := G) (R := ∅) $$ [HT HG HF1 Hcu]
  · iframe HT Hcu
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, Hcu⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  -- The store, in the invariant; the discharge of `κu` follows the step.
  lwp_bind hl(#curr ← v(&(vInt (u + 1)))) HT
  icases oblFuels_add 1 93 G $$ HF with ⟨HF1, -⟩
  ihave Hacc := alwaysI_acc (E := ⊤) (N := Ninv) (P := lockInv γ.γt γ.γa γ.γc next curr R)
    (fun _ _ => CoPset.mem_full) $$ Hinv
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨Hi, Hclose⟩
  icases (tlc_split_nat 1 1).mp $$ Hc with ⟨Hc1, Hc2⟩
  iapply lwp_credit_later_nat $$ Hc1
  inext
  iunfold lockInv at Hi
  icases Hi with ⟨%n, %c, %tickets, %acks, Hnext, Hcurr, ⟨GMt, GMa⟩, %hdom, %hc, %hdomt, HMt,
    HMa, Hlast⟩
  icombine Hcurr Hcu gives %hcu
  obtain rfl : c = u := by simpa using hcu.2
  ihave Hfull := (pointsTo_halves curr _).mpr $$ [Hcurr Hcu]
  · iframe
  iapply lwp_store (o := lc) (C := _ ++ C) (G := G) (R := ∅) $$ [HT HG HF1 Hfull]
  · iframe HT Hfull
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨Hlc, HG, -⟩, Hfull⟩
  icases (pointsTo_halves curr _).mp $$ Hfull with ⟨Hcurr, Hcu⟩
  -- The ticket `c + 1` is the holder's: its obligation `κu` is pending.
  ihave %LUt := ghost_map_lookup $$ GMt Mtu
  icases (BigSepM.bigSepM_delete LUt).mp $$ HMt with ⟨Hu, HMt⟩
  icases (ticketEntry_iff _ _ _ _ _ _ _ _).mp $$ Hu with ⟨Hu1, (⟨%hu, -⟩ | ⟨%hu, Uu2⟩)⟩
  · exact absurd hu.2 (by omega)
  -- The lock is taken: the acknowledgement of `c + 1` is there.
  icases Hlast with (⟨%hcn, -⟩ | ⟨%hcn, (⟨-, Hcurr', -⟩ | #Ha)⟩)
  · exact absurd hcn (by omega)
  · iexfalso
    icombine Hcurr Hcurr' gives %h
    simp only [Option.some.injEq, Val.lit.injEq, BaseLit.int.injEq] at h
    exact absurd h.2 (by omega)
  ihave U : finallyI Nev κu 1 iprop(curr ↦{half} some (vInt (c + 1)) ∗ R) $$ [Uu Uu2]
  · iunfold finallyI at Uu Uu2
    iunfold finallyI
    iapply untilI_frac_add (q := 1) (Qp.half_add_half 1).symm $$ Uu Uu2
  imod finallyI_discharge (E := ⊤ \ ↑Ninv) (.thread i) G Nev_subseteq hκu $$ Hc2 HG Kκu U
    [Hcu HR] with ⟨⟨Hcu, HR⟩, HG, #Dκu⟩
  · iframe
  have hdel : ∀ {t : Int} {κ : Oid}, get? (delete tickets (c + 1)) t = some κ → t ≠ c + 1 := by
    intro t κ h ht
    subst ht
    simp [Iris.Std.LawfulPartialMap.get?_delete_eq] at h
  imod Hclose $$ [Hnext Hcurr GMt GMa HMt HMa Hu1 Hcu HR] with -
  · inext
    iunfold lockInv
    iexists n, c + 1, tickets, acks
    iframe Hnext Hcurr GMt GMa
    isplitr
    · ipureintro
      exact hdom
    isplitr
    · ipureintro
      omega
    isplitr
    · ipureintro
      exact hdomt
    isplitl [HMt Hu1]
    · iapply (BigSepM.bigSepM_delete LUt).mpr
      isplitl [Hu1]
      · iapply (ticketEntry_iff _ _ _ _ _ _ _ _).mpr
        iframe Hu1
        ileft
        isplit
        · ipureintro
          omega
        · iexact Dκu
      · iapply BigSepM.bigSepM_mono (fun h => ticketEntry_serve _ _ _ _ _ (hdel h)) $$ HMt
    by_cases hcn1 : c + 1 = n
    · -- No ticket is pending: the lock is free.
      isplitl [HMa]
      · iapply BigSepM.bigSepM_impl $$ HMa
        imodintro
        iintro %t %a %hta Ht
        have := (hdomt t).mp ((hdom t).mpr (by simp [hta]))
        iapply ackEntry_serve _ hc.1 (by omega) $$ Ha Ht
      ileft
      isplit
      · ipureintro
        exact hcn1
      · iframe
    · -- The next ticket `c + 2` is pending: the lock is free for it.
      obtain ⟨a, LUa⟩ := Option.isSome_iff_exists.mp
        ((hdom (c + 1 + 1)).mp ((hdomt (c + 1 + 1)).mpr (by omega)))
      icases (BigSepM.bigSepM_delete LUa).mp $$ HMa with ⟨Ha2, HMa⟩
      icases (ackEntry_iff _ _ _ _).mp $$ Ha2 with (⟨%ha, -⟩ | %ha | ⟨%ha, Ma2⟩)
      · exact absurd ha.2 (by omega)
      · exact absurd ha (by omega)
      isplitl [HMa]
      · iapply (BigSepM.bigSepM_delete LUa).mpr
        isplitr
        · iapply (ackEntry_iff _ _ _ _).mpr
          iright
          ileft
          ipureintro
          rfl
        · iapply BigSepM.bigSepM_impl $$ HMa
          imodintro
          iintro %t %a' %hta Ht
          have hne : t ≠ c + 1 + 1 := by
            intro ht
            subst ht
            simp [Iris.Std.LawfulPartialMap.get?_delete_eq] at hta
          iapply ackEntry_serve _ hc.1 hne $$ Ha Ht
      iright
      isplit
      · ipureintro
        omega
      · ileft
        iframe
  imodintro
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  iapply lwp_value'
  iapply HΦ
  iframe

end Specs

/-! ## Temporal guarantees

The guarantees are inferred (`GuarOf`): `TrSpec.true` for the ghost state, `R` and the
obligations; the pending tickets `c + 1 ≤ t ≤ n` carry `◇ (curr ↦ t)`. -/

section Guarantee
variable {GF : BundledGFunctors}

/-- What a ticket guarantees. -/
def ticketEntryTrSpec (curr : Loc) (c n t : Int) : TrSpec Exp State GF :=
  (TrSpec.true ∧ₛ TrSpec.true ∧ₛ TrSpec.true) ∧ₛ
    ((⌜0 ≤ t ∧ t ≤ c⌝ₛ ∧ₛ TrSpec.true) ∨ₛ
      (⌜c + 1 ≤ t ∧ t ≤ n⌝ₛ ∧ₛ
        ◇ₛ (TrSpec.state (pointstoSat curr half (vInt t)) ∧ₛ TrSpec.true)))

/-- What an acknowledgement guarantees. -/
def ackEntryTrSpec (c n t : Int) : TrSpec Exp State GF :=
  (⌜0 ≤ t ∧ t ≤ c⌝ₛ ∧ₛ TrSpec.true) ∨ₛ ⌜t = c + 1⌝ₛ ∨ₛ (⌜c + 1 < t ∧ t ≤ n⌝ₛ ∧ₛ TrSpec.true)

/-- The guarantee of the invariant, as inferred (Rocq `lock_inv_trSpec`). -/
@[lantana_alias ticket_lock2.lock_inv_trSpec]
def lockInvTrSpec (next curr : Loc) : TrSpec Exp State GF :=
  ∃ₛ (n : Int) (c : Int) (tickets : IntMap Oid) (acks : IntMap Bool),
    TrSpec.state (pointstoSat next (.own 1) (vInt n)) ∧ₛ
    TrSpec.state (pointstoSat curr half (vInt c)) ∧ₛ (TrSpec.true ∧ₛ TrSpec.true) ∧ₛ
    ⌜∀ t, (get? tickets t).isSome ↔ (get? acks t).isSome⌝ₛ ∧ₛ ⌜0 ≤ c ∧ c ≤ n⌝ₛ ∧ₛ
    ⌜∀ t, (get? tickets t).isSome ↔ (0 ≤ t ∧ t ≤ n)⌝ₛ ∧ₛ
    (∀ₛ (t : Int) (κ : Oid), ⌜get? tickets t = some κ⌝ₛ →ₛ ticketEntryTrSpec curr c n t) ∧ₛ
    (∀ₛ (t : Int) (a : Bool), ⌜get? acks t = some a⌝ₛ →ₛ ackEntryTrSpec c n t) ∧ₛ
    ((⌜c = n⌝ₛ ∧ₛ (TrSpec.state (pointstoSat curr half (vInt c)) ∧ₛ TrSpec.true)) ∨ₛ
      (⌜c < n⌝ₛ ∧ₛ ((TrSpec.true ∧ₛ TrSpec.state (pointstoSat curr half (vInt c)) ∧ₛ
        TrSpec.true) ∨ₛ TrSpec.true)))

/-- The guarantee of a lock (Rocq `fair_lock_trSpec`). -/
@[lantana_alias ticket_lock2.fair_lock_trSpec]
def fairLockTrSpec (tl : Val) : TrSpec Exp State GF :=
  ∃ₛ (next : Loc) (curr : Loc), ⌜tl = hl_val((#next, #curr))⌝ₛ ∧ₛ □ₛ lockInvTrSpec next curr

/-- The guarantee of a lock token: the holder releases the lock (Rocq `lock_token_trSpec`). -/
@[lantana_alias ticket_lock2.lock_token_trSpec]
def lockTokenTrSpec (tl : Val) : TrSpec Exp State GF :=
  ∃ₛ (next : Loc) (curr : Loc) (u : Int), ⌜tl = hl_val((#next, #curr))⌝ₛ ∧ₛ
    (TrSpec.state (pointstoSat curr half (vInt u)) ∧ₛ TrSpec.true ∧ₛ
      ◇ₛ (TrSpec.state (pointstoSat curr half (vInt (u + 1))) ∧ₛ TrSpec.true))

variable [ModelGS GF] [HeapGS GF] [TicketLock2G GF]

instance guarOf_ticketEntry (γt γc : GName) (curr : Loc) (R : IProp GF) (c n t : Int)
    (κ : Oid) : GuarOf (ticketEntry γt γc curr R c n t κ) (ticketEntryTrSpec curr c n t) := by
  unfold ticketEntry ticketEntryTrSpec; exact ⟨GuarOf.guar_of⟩

instance guarOf_ackEntry (γa : GName) (c n t : Int) :
    GuarOf (ackEntry (GF := GF) γa c n t) (ackEntryTrSpec c n t) := by
  unfold ackEntry ackEntryTrSpec; exact ⟨GuarOf.guar_of⟩

instance guarOf_lockInv (γt γa γc : GName) (next curr : Loc) (R : IProp GF) :
    GuarOf (lockInv γt γa γc next curr R) (lockInvTrSpec next curr) := by
  unfold lockInv lockInvTrSpec; exact ⟨GuarOf.guar_of⟩

/-- Clients see the lock's guarantee, not its invariant. -/
@[lantana_alias ticket_lock2.into_guar_is_fair_lock]
instance guarOf_isFairLock (tl : Val) (γ : TicketLockName) (R : IProp GF) :
    GuarOf (isFairLock tl γ R) (fairLockTrSpec tl) := by
  unfold isFairLock fairLockTrSpec; exact ⟨GuarOf.guar_of⟩

@[lantana_alias ticket_lock2.guar_is_fair_lock]
theorem guar_isFairLock (tl : Val) (γ : TicketLockName) (R : IProp GF) :
    ⊢@{IProp GF} isFairLock tl γ R ⊨ₜ fairLockTrSpec tl :=
  GuarOf.guar_of

@[lantana_alias ticket_lock2.into_guar_lock_token]
instance guarOf_lockToken (tl : Val) (γ : TicketLockName) (κu : Oid) (R : IProp GF) :
    GuarOf (lockToken tl γ κu R) (lockTokenTrSpec tl) := by
  unfold lockToken lockTokenTrSpec; exact ⟨GuarOf.guar_of⟩

@[lantana_alias ticket_lock2.guar_lock_token]
theorem guar_lockToken (tl : Val) (γ : TicketLockName) (κu : Oid) (R : IProp GF) :
    ⊢@{IProp GF} lockToken tl γ κu R ⊨ₜ lockTokenTrSpec tl :=
  GuarOf.guar_of

end Guarantee

/-! ## Starvation freedom, at the level of traces -/

section Traces
variable {GF : BundledGFunctors}

/-- `l ↦ v` in the current state of the trace (Rocq `tr_pointsto`). -/
@[lantana_alias ticket_lock2.tr_pointsto]
abbrev trPointsTo (l : Loc) (v : Val) : TrProp Exp State :=
  TrProp.state (pointstoSat l (.own 1) v)

/-- Starvation freedom of the ticket lock `(next, curr)` (Rocq `starvation_free`): whenever
`next ↦ n` and `curr ↦ c`, every ticket `t` with `c < t ≤ n` is eventually served. -/
@[lantana_alias ticket_lock2.starvation_free]
def starvationFree (next curr : Loc) : TrProp Exp State :=
  □ₜ (∀ₜ (n : Int) (c : Int) (t : Int), trPointsTo next (vInt n) →ₜ
    trPointsTo curr (vInt c) →ₜ ⌜c < t ∧ t ≤ n⌝ₜ →ₜ ◇ₜ trPointsTo curr (vInt t))

/-- Two readings of one location agree. -/
theorem pointstoSat_agree {l : Loc} {dq₁ dq₂ : DFrac} {v₁ v₂ : Val} {σ : State}
    {tp : List Exp} (h₁ : pointstoSat l dq₁ v₁ σ tp) (h₂ : pointstoSat l dq₂ v₂ σ tp) :
    v₁ = v₂ := by
  simp only [pointstoSat] at h₁ h₂
  rw [h₁] at h₂
  simpa using h₂

/-- From the invariant's reading: the atoms fix `n` and `c`, the pure facts give the ticket `t`
its obligation, whose branch for pending tickets is the finally (Rocq
`lock_inv_trSpec_starvation_free`). -/
@[lantana_alias ticket_lock2.lock_inv_trSpec_starvation_free]
theorem lockInvTrSpec_starvationFree (next curr : Loc) :
    (□ₛ lockInvTrSpec (GF := GF) next curr).external ⊆ starvationFree next curr := by
  intro τ h m hm n c t hn hc ht
  obtain ⟨n', c', tickets, acks, hn', hc', -, -, hb, hdomt, htk, -⟩ := h m hm
  have ht : c < t ∧ t ≤ n := ht
  have hb : 0 ≤ c' ∧ c' ≤ n' := hb
  have hdomt : ∀ t, (get? tickets t).isSome ↔ (0 ≤ t ∧ t ≤ n') := hdomt
  obtain rfl : n' = n := by
    simpa [vInt] using pointstoSat_agree (dq₁ := .own 1) (dq₂ := .own 1) hn' hn
  obtain rfl : c' = c := by
    simpa [vInt] using pointstoSat_agree (dq₁ := half) (dq₂ := .own 1) hc' hc
  obtain ⟨κ, hκ⟩ := Option.isSome_iff_exists.mp ((hdomt t).mpr ⟨by omega, ht.2⟩)
  rcases (htk t κ hκ).2 with ⟨ht', -⟩ | ⟨-, m', hm', ⟨hfin, -⟩, -⟩
  · have ht' : 0 ≤ t ∧ t ≤ c' := ht'
    exact absurd ht'.2 (by omega)
  · exact ⟨m', hm', hfin, fun _ _ _ => trivial⟩

/-- The trace property of a fair lock: starvation freedom of its two cells (Rocq
`fair_lock_sf`). -/
@[lantana_alias ticket_lock2.fair_lock_sf]
def fairLockSf (tl : Val) : TrProp Exp State :=
  ∃ₜ (next : Loc) (curr : Loc), ⌜tl = hl_val((#next, #curr))⌝ₜ ∧ₜ starvationFree next curr

@[lantana_alias ticket_lock2.fair_lock_starvation_free]
theorem fairLock_starvationFree (tl : Val) :
    (fairLockTrSpec (GF := GF) tl).external ⊆ fairLockSf tl := by
  rintro τ ⟨next, curr, htl, h⟩
  exact ⟨next, curr, htl, lockInvTrSpec_starvationFree next curr τ h⟩

/-- The holder of a lock token (serving the ticket `u`) eventually releases the lock (Rocq
`lock_token_tr`). -/
@[lantana_alias ticket_lock2.lock_token_tr]
def lockTokenTr (tl : Val) : TrProp Exp State :=
  ∃ₜ (next : Loc) (curr : Loc) (u : Int), ⌜tl = hl_val((#next, #curr))⌝ₜ ∧ₜ
    trPointsTo curr (vInt u) ∧ₜ ◇ₜ trPointsTo curr (vInt (u + 1))

@[lantana_alias ticket_lock2.lock_token_releases]
theorem lockToken_releases (tl : Val) :
    (lockTokenTrSpec (GF := GF) tl).external ⊆ lockTokenTr tl := by
  rintro τ ⟨next, curr, u, htl, hu, -, m, hm, ⟨hfin, -⟩, -⟩
  exact ⟨next, curr, u, htl, hu, m, hm, hfin, fun _ _ _ => trivial⟩

end Traces

/-! ## Starvation freedom as a guarantee -/

section CastGuarantee
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLock2G GF]

/-- The lock's guarantee, cast to its trace property (Rocq `is_fair_lock_starvation_free`). -/
@[lantana_alias ticket_lock2.is_fair_lock_starvation_free]
theorem isFairLock_starvationFree (tl : Val) (γ : TicketLockName) (R : IProp GF) :
    ⊢@{IProp GF} isFairLock tl γ R ⊨ₜ
      (fairLockTrSpec tl).cast (fairLockSf tl) (fairLock_starvationFree tl) :=
  (guar_isFairLock tl γ R).trans (guar_cast _ _)

end CastGuarantee

end Lantana.Examples.TicketLock2
