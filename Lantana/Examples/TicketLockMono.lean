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

/-! ## Specifications

The specifications of `TicketLock`, for this lock. -/

section Specs
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLockMonoG GF]

/-- Opening the mono cell. -/
theorem nextGe_acc {E : CoPset} (γm : GName) (next : Loc) (v : Int) (hN : ↑Nmono ⊆ E) :
    nextGe γm next v ⊢@{IProp GF}
      |={E, E \ ↑Nmono}=> ▷ monoInv γm next ∗ (▷ monoInv γm next ={E \ ↑Nmono, E}=∗ True) := by
  unfold nextGe
  exact alwaysIGuar_acc hN

@[lantana_alias ticket_lock_mono.TicketLock_init_spec]
theorem init_spec : ∃ μ : Measure, ∀ (lc : Fuel) (ℓ : Layer) (i : ThreadId) (G : Oids)
    (E : CoPset) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&TicketLock.init) #()) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) }}}
        hl(v(&TicketLock.init) #()) @ i; E
      l{{{ (tl : Val) (γ : TicketLockName), RET tl; threadExpr i C hl(&tl) ∗ £ₒ lc ∗
        thKids i G ∗ (γ ↪LOCK_AL) ∗ (γ ↪LOCK_CF ℓ) ∗
        (∀ (E₁ : CoPset) (R : IProp GF), R -∗ |={E₁}=>m isFairLock tl γ R) }}} := by
  refine ⟨10, fun lc ℓ i G E C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF⟩ HΦ
  ihave HF := oblFuels_init G 10 0 $$ HF
  unfold TicketLock.init
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
  imod iOwn_alloc (E := TicketLock.TicketLockG.configG) (●AM[(· ≤ ·)] ℓ) AuthMra.auth_valid
    with ⟨%γc, Hc⟩
  imod MonoZ.own_alloc (GF := GF) 0 (by omega) with ⟨%γm, Auth, #Lb⟩
  icases (pointsTo_halves next _).mp $$ Hnext with ⟨Hnext, Hnext0⟩
  icases (TicketLock.pointsTo_quarters curr _).mp $$ Hcurr with ⟨Hcurr, Hcurr34⟩
  iapply lwp_value'
  iapply HΦ $$ %(vLock next curr) %(⟨⟨γt, γo, γk, γc, γa⟩, γm⟩ : TicketLockName)
  iframe HT Hlc HG
  isplitl [Ha]
  · unfold TicketLock.ownAlive
    iexact Ha
  isplitl [Hc]
  · unfold TicketLock.ownLayer
    iexact Hc
  iintro %E₁ %R HR
  -- The mono cell, registered for `0`.
  imod nextGe_alloc E₁ γm next 0 $$ Lb [Hnext0 Auth] with #NG
  · inext
    iunfold monoInv
    iexists 0
    iframe Auth
    ileft
    iexact Hnext0
  imod alwaysI_alloc (E := E₁) (N := Ninv) (P := lockInv γt γo γc γa γm next curr R) $$
    [Hnext Hcurr Hcurr34 Ht Ho HR] with #HI
  · inext
    unfold lockInv lockInvAlive
    iright
    iexists 0, 0, ({[0 := none]} : TMap TicketInfo), ({[0 := some κu]} : TMap (Option Oid))
    iframe Hnext NG Hcurr Ht Ho
    isplitr
    · ipureintro
      refine ⟨fun t => ?_, fun t => ?_, by omega, by omega⟩ <;>
        · rw [LawfulPartialMap.get?_singleton]
          grind
    isplitl []
    · iapply BigSepM.bigSepM_singleton.mpr
      unfold TicketLock.ticketSt
      ileft
      iexists κu
      iframe Hte Hoe Dk
      ipureintro
      omega
    · unfold TicketLock.holderSt
      ileft
      iframe Hcurr34 HR
      ipureintro
      rfl
  imod alwaysI_alloc (E := E₁) (N := Ntk) (P := TicketLock.lockTokenInv γo γk curr R) $$ [Hk]
    with #HK
  · inext
    unfold TicketLock.lockTokenInv
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

@[lantana_alias ticket_lock_mono.TicketLock_release_spec]
theorem release_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids) (tl : Val)
    (γ : TicketLockName) (dq : DFrac) (R : IProp GF) (κu : Oid) (E : CoPset) (_ : ↑N ⊆ E)
    (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&TicketLock.release) v(&tl)) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ ⌜κu ∈ G⌝ ∗ oblKids κu ∅ ∗ TicketLock.lockToken γ κu ∗
          R ∗ (γ ↪LOCK_AL{dq}) ∗ isFairLock tl γ R }}}
        hl(v(&TicketLock.release) v(&tl)) @ i; E
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i (G.erase κu) ∗
        (γ ↪LOCK_AL{dq}) }}} := by
  refine ⟨10, fun lc i G tl γ dq R κu E hE C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hκu, Kku, LT, HR, AL, #IFL⟩ HΦ
  ihave HF := oblFuels_init G 10 0 $$ HF
  rw [TicketLock.lockToken_unfold]
  icases LT with ⟨%c, GV, #GMEtku, #GMEo⟩
  unfold isFairLock
  icases IFL with ⟨%next, %curr, %htl, #INV, #ITK⟩
  subst htl
  unfold TicketLock.release
  lwp_step HT HG HF with Hlc : lc +ₕ 1 +ₕ 1 +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc3⟩
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc2⟩
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc1⟩
  -- Exchange the token.
  ihave Hc1 := tlc_one_nat.mpr $$ Hc1
  imod TicketLock.lockToken_exchange E hE γ curr R κu c $$ ITK Hc1 GV GMEo with
    ⟨PtrCurr0, GEku⟩
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
    (P := lockInv γ.γt γ.γo γ.γc γ.γa γ.γm next curr R) (TicketLock.Ninv_subseteq hE) $$ INV
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨H, Hclose⟩
  iclear Hacc
  iapply lwp_credit_later $$ Hc2
  inext
  iunfold lockInv at H
  icases H with (Hdel | H)
  · iexfalso
    iapply TicketLock.ownAlive_full_false $$ AL Hdel
  iunfold lockInvAlive at H
  icases H with ⟨%n, %c', %tickets, %obls, PtrNext, #NG, PtrCurr, GMAt, GMAo,
    %⟨Domt, Domo, hc0, hcn⟩, HMt, Hc⟩
  ihave %h := pointsTo_agree (l := curr) $$ [PtrCurr PtrCurr0]
  · iframe
  obtain rfl : c = c' := by simpa [vz] using h.symm
  ihave PtrCurr := (TicketLock.pointsTo_quarters curr _).mpr $$ [PtrCurr PtrCurr0]
  · iframe
  ihave %hlt := ghostMapP_lookup $$ GMAt GMEtku
  have hc1 := (Domt (c + 1)).mp (by simp [hlt])
  iunfold TicketLock.holderSt at Hc
  icases Hc with (⟨%hcn', -⟩ | ⟨%hcn', %ℓ0, %κ, #CFl, #Wl, #GMEo1, HE, -⟩)
  · iexfalso
    ipureintro
    omega
  ihave %h := ghost_map_elem_agree _ _ _ _ (some κu) (some κ) $$ [GMEo GMEo1]
  · iframe GMEo GMEo1
  cases h
  iunfold finallyI at GEku HE
  ihave HU := untilI_frac_add (q := 1) (Qp.half_add_half 1).symm $$ GEku HE
  ihave HU := untilI_discharge (E := E \ ↑Ninv) (TicketLock.Nev_subseteq hE) $$ HU
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
  icases (TicketLock.pointsTo_quarters curr _).mp $$ PtrCurr with ⟨PtrCurr, PtrCurr34⟩
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
      iframe PtrNext NG GMAt GMAo
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
        iapply TicketLock.ticketSt_release γ.γt γ.γo γ.γc κu t hc0 ht $$ GMEtku GMEo Dku H
      · iunfold TicketLock.holderSt
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
    iunfold TicketLock.ticketSt at Ht2
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
    imod ALLOC $$ %(E \ ↑Ninv) %Nev %iprop(True) %(TicketLock.released curr (c + 1) R) []
      with HU1
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
      iframe PtrNext NG GMAt GMAo
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
        · iunfold TicketLock.ticketSt
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
        iapply TicketLock.ticketSt_release γ.γt γ.γo γ.γc κu t hc0 ht $$ GMEtku GMEo Dku H
      · iunfold TicketLock.holderSt
        iright
        isplitr
        · ipureintro
          omega
        iexists ℓ1, κu1
        iunfold finallyI
        iframe CFl1 Wlku1 GMEo2 HU2
        ileft
        iunfold TicketLock.nextOwner
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

@[lantana_alias ticket_lock_mono.TicketLock_delete_spec]
theorem delete_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids) (tl : Val)
    (γ : TicketLockName) (R : IProp GF) (κu : Oid) (E : CoPset) (_ : ↑N ⊆ E)
    (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&TicketLock.delete) v(&tl)) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ ⌜κu ∈ G⌝ ∗ oblKids κu ∅ ∗ TicketLock.lockToken γ κu ∗
          R ∗ (γ ↪LOCK_AL) ∗ isFairLock tl γ R }}}
        hl(v(&TicketLock.delete) v(&tl)) @ i; E
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i (G.erase κu) ∗ R }}} := by
  refine ⟨20, fun lc i G tl γ R κu E hE C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hκu, Kku, LT, HR, AL, #IFL⟩ HΦ
  ihave HF := oblFuels_init G 20 0 $$ HF
  rw [TicketLock.lockToken_unfold]
  icases LT with ⟨%c, GV, #GMEtku, #GMEo⟩
  unfold isFairLock
  icases IFL with ⟨%next, %curr, %htl, #INV, #ITK⟩
  subst htl
  unfold TicketLock.delete
  lwp_step HT HG HF with Hlc : lc +ₕ 1 +ₕ 1 +ₕ 1 +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc4⟩
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc3⟩
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc2⟩
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc1⟩
  -- Exchange the token.
  ihave Hc1 := tlc_one_nat.mpr $$ Hc1
  imod TicketLock.lockToken_exchange E hE γ curr R κu c $$ ITK Hc1 GV GMEo with
    ⟨PtrCurr0, GEku⟩
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
    (P := lockInv γ.γt γ.γo γ.γc γ.γa γ.γm next curr R) (TicketLock.Ninv_subseteq hE) $$ INV
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨H, Hclose⟩
  iclear Hacc
  iapply lwp_credit_later $$ Hc2
  inext
  iunfold lockInv at H
  icases H with (Hdel | H)
  · iexfalso
    iapply TicketLock.ownAlive_full_false $$ AL Hdel
  iunfold lockInvAlive at H
  icases H with ⟨%n, %c', %tickets, %obls, PtrNext, #NG, PtrCurr, GMAt, GMAo,
    %⟨Domt, Domo, hc0, hcn⟩, HMt, Hc⟩
  ihave %h := pointsTo_agree (l := curr) $$ [PtrCurr PtrCurr0]
  · iframe
  obtain rfl : c = c' := by simpa [vz] using h.symm
  ihave PtrCurr := (TicketLock.pointsTo_quarters curr _).mpr $$ [PtrCurr PtrCurr0]
  · iframe
  ihave %hlt := ghostMapP_lookup $$ GMAt GMEtku
  have hc1 := (Domt (c + 1)).mp (by simp [hlt])
  iunfold TicketLock.holderSt at Hc
  icases Hc with (⟨%hcn', -⟩ | ⟨%hcn', %ℓ0, %κ, #CFl, #Wl, #GMEo1, HE, -⟩)
  · iexfalso
    ipureintro
    omega
  ihave %h := ghost_map_elem_agree _ _ _ _ (some κu) (some κ) $$ [GMEo GMEo1]
  · iframe GMEo GMEo1
  cases h
  iunfold finallyI at GEku HE
  ihave HU := untilI_frac_add (q := 1) (Qp.half_add_half 1).symm $$ GEku HE
  ihave HU := untilI_discharge (E := E \ ↑Ninv) (TicketLock.Nev_subseteq hE) $$ HU
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
  icases (TicketLock.pointsTo_quarters curr _).mp $$ PtrCurr with ⟨PtrCurr, PtrCurr34⟩
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
    unfold TicketLock.ownAlive
    iexact AL
  imodintro
  ihave PtrCurr := (TicketLock.pointsTo_quarters curr _).mpr $$ [PtrCurr PtrCurr34]
  · iframe
  ihave HF := oblFuels_remove_obl κu G _ $$ HF
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(free(#next)) HT
  -- The mono cell, open for the step, keeps half of `next`'s freed points-to.
  ihave Hacc := nextGe_acc (E := E) γ.γm next n (nclose_subseteq' _ hE) $$ NG
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨HJ, CloseJ⟩
  iclear Hacc
  iapply lwp_credit_later $$ Hc4
  inext
  iunfold monoInv at HJ
  icases HJ with ⟨%w, Auth, (PtrNext0 | Fr)⟩
  rotate_left
  · iexfalso
    ihave %h := pointsTo_agree (l := next) $$ [PtrNext Fr]
    · iframe
    simp at h
  ihave %h := pointsTo_agree (l := next) $$ [PtrNext PtrNext0]
  · iframe
  have hw : w = n := by simpa [vz] using h
  subst w
  ihave PtrNext := (pointsTo_halves next _).mpr $$ [PtrNext PtrNext0]
  · iframe
  icases oblFuels_add 1 7 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_free (o := 0) (G := G.erase κu) (R := ∅) $$ [HT HG HF1 PtrNext]
  · iframe HT PtrNext
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, Fr⟩
  icases (pointsTo_halves next _).mp $$ Fr with ⟨Fr, -⟩
  imod CloseJ $$ [Auth Fr] with -
  · inext
    iunfold monoInv
    iexists n
    iframe Auth
    iright
    iexact Fr
  imodintro
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

/-! ## Acquire

`TicketLock.acquire_end` and `TicketLock.acquire_mine`, which do not open the lock invariant,
are reused, with the definitions of the loop (`loopV`, `acqPost`, the fuel maps); the loop, which
opens the invariant, and `acquire_spec` are those of `TicketLock` with the mono cell. -/

section Acquire
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLockMonoG GF]
open Lantana.Examples.TicketLock (loopV acqPost lockTokenInv layerLb embedMap witMap
  bigSepM_embedMap bigSepM_witMap holderSt holderSt_mono_n nextOwner ticketSt ticketSt_obl
  ticketSt_waiting ownAlive_full_false tickets_update tickets_insert dom_insert_same
  dom_insert_succ ownLayer_lb ownLayer_lb_le acquire_end acquire_mine released Ninv_subseteq
  Ntk_subseteq lockToken)

/-- The loop of `acquire` for the ticket `my + 1`, `ν` tickets after the holder of ticket
`prev + 1`, whose unlock obligation is `κ` at layer `ℓ₀`. The thread waits in the container
`gu` (at the lock's layer `ℓ`); the outer induction is on `ν` (`embedFuels`), the inner one on
`κ`'s witness (`Wit.fuels`), started with the fuel `50 * ▽` of the children `G`. -/
def AcqLoopSpec (lc : Fuel) (i : ThreadId) (G : Oids) (γ : TicketLockName) (dq₁ dq₂ : DFrac)
    (ℓ : Layer) (m : Measure) (R : IProp GF) (E : CoPset) (C : List ECtxItem)
    (Φ : Val → IProp GF) (next curr : Loc) (my : Int) (ν : Nat) : Prop :=
  ∀ (prev : Int) (κ : Oid) (ℓ₀ : Layer) (gu : Oid), ν = (my - prev).toNat → prev < my →
    ℓ₀ ≤ ℓ → gu ∉ G →
    ⊢@{IProp GF} alwaysI (Expr := Exp) (State := State) Ninv
        (lockInv γ.γt γ.γo γ.γc γ.γa γ.γm next curr R) -∗
      alwaysI (Expr := Exp) (State := State) Ntk (lockTokenInv γ.γo γ.γk curr R) -∗
      layerLb γ.γc ℓ -∗ layerLb γ.γc ℓ₀ -∗ Wit.layer κ ℓ₀ -∗
      (γ.γo ↪◯MAP[prev + 1]{.discard} some κ) -∗ Wit.layer gu ℓ -∗
      acqPost Φ i C lc G γ dq₁ dq₂ ℓ m R -∗ (γ ↪LOCK_AL{dq₁}) -∗ (γ ↪LOCK_CF{dq₂} ℓ) -∗
      embedFuels Nat.lt_wfRel.wf ν (embedMap G ℓ) -∗
      ([∗set] g ∈ G, Obl.fuel g ℓ.succ (50 * ▽)) -∗ Obl.assigned gu 1 -∗
      (γ.γt ↪◯PMAP[my + 1]{.own (1 : Qp).half} (some (gu, ℓ, m) : TicketInfo)) -∗
      thKids i (G.insert gu) -∗ oblFuels (G.insert gu) 4 -∗
      threadExpr i C hl(v(&(loopV curr my)) #()) -∗
      lWP hl(v(&(loopV curr my)) #()) @ i; E {{ Φ }}

/-- An iteration of the loop of `acquire`, by witness induction on the holder's unlock
obligation `κ` (Rocq: the inner `iInduction α`). -/
theorem acquire_loop_inner (lc : Fuel) (i : ThreadId) (G : Oids) (γ : TicketLockName)
    (dq₁ dq₂ : DFrac) (ℓ : Layer) (m : Measure) (R : IProp GF) (E : CoPset) (hE : ↑N ⊆ E)
    (C : List ECtxItem) (Φ : Val → IProp GF) (next curr : Loc) (my : Int) (ν : Nat)
    (prev : Int) (κ : Oid) (ℓ₀ : Layer) (hν : ν = (my - prev).toNat) (hprev : prev < my)
    (IH : ∀ ν' < ν, AcqLoopSpec lc i G γ dq₁ dq₂ ℓ m R E C Φ next curr my ν') :
    ∀ (α : Fuel) (gu : Oid), gu ∉ G →
    ⊢@{IProp GF} alwaysI (Expr := Exp) (State := State) Ninv
        (lockInv γ.γt γ.γo γ.γc γ.γa γ.γm next curr R) -∗
      alwaysI (Expr := Exp) (State := State) Ntk (lockTokenInv γ.γo γ.γk curr R) -∗
      layerLb γ.γc ℓ -∗ layerLb γ.γc ℓ₀ -∗ Wit.layer κ ℓ₀ -∗
      (γ.γo ↪◯MAP[prev + 1]{.discard} some κ) -∗ Wit.layer gu ℓ -∗
      acqPost Φ i C lc G γ dq₁ dq₂ ℓ m R -∗ (γ ↪LOCK_AL{dq₁}) -∗ (γ ↪LOCK_CF{dq₂} ℓ) -∗
      embedFuels Nat.lt_wfRel.wf ν (embedMap G ℓ) -∗ Wit.fuels κ ℓ₀ α (witMap G ℓ) -∗
      Obl.assigned gu 1 -∗
      (γ.γt ↪◯PMAP[my + 1]{.own (1 : Qp).half} (some (gu, ℓ, m) : TicketInfo)) -∗
      thKids i (G.insert gu) -∗ oblFuels (G.insert gu) 4 -∗
      threadExpr i C hl(v(&(loopV curr my)) #()) -∗
      lWP hl(v(&(loopV curr my)) #()) @ i; E {{ Φ }} := by
  intro α
  induction α using WellFounded.induction Ordinals.Ordinal.lt_wf with
  | h α IHα =>
  intro gu hgu
  iintro #INV #ITK #CFl #CFl0 #Wl0 #GMEo0 #Wgu HΦ AL CF EFs WFs Agu GMEt0 HG HF HT
  lwp_step HT HG HF with Hc : 1
  lwp_expr_simp
  lwp_bind hl(!#curr) HT
  -- The atomic load, in the lock invariant: it observes the holder's unlock obligation.
  ihave Hacc := alwaysI_acc (E := E) (N := Ninv)
    (P := lockInv γ.γt γ.γo γ.γc γ.γa γ.γm next curr R) (Ninv_subseteq hE) $$ INV
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
  icases H with ⟨%n, %c, %tickets, %obls, PtrNext, #NG, PtrCurr, GMAt, GMAo,
    %⟨Domt, Domo, hc0, hcn⟩,
    HMt, Hc⟩
  icases oblFuels_add 1 2 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_load (o := 0) (G := G.insert gu) (R := {κ}) $$ [HT HG HF1 PtrCurr]
  · iframe HT PtrCurr
    iapply stepPre_wit _ _ κ ℓ₀ $$ HG HF1 Wl0
  iintro ⟨HT, ⟨-, HG, HW⟩, PtrCurr⟩
  ihave Wc := witCreds_singleton κ $$ HW
  ihave %hlt := ghostMapP_lookup $$ GMAt GMEt0
  have hmy := (Domt (my + 1)).mp (by simp [hlt])
  by_cases hc : c = my
  · -- My turn.
    obtain rfl : my = c := hc.symm
    iunfold holderSt at Hc
    icases Hc with (⟨%h, -⟩ | ⟨%hcn', %ℓ₁, %κu, #CFl1, #Wl1, #GMEo1, HE0, (Hn | #GMEt1)⟩)
    · iexfalso
      ipureintro
      omega
    · iunfold nextOwner at Hn
      icases Hn with ⟨%g, %μ, GMEt1, HE, Gg, Kk, Of, PtrCurr0, HR⟩
      icases ghostMapP_elem_combine_halves _ _ _ _ $$ [GMEt0 GMEt1] with ⟨GMEt, %h⟩
      · iframe
      obtain ⟨rfl, rfl, rfl⟩ : gu = g ∧ ℓ = ℓ₁ ∧ m = μ := by
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
      imod ghostMapP_update (none : TicketInfo) $$ GMAt GMEt with ⟨GMAt, GMEt⟩
      imod ghostMapP_elem_persist $$ GMEt with #GMEt
      imod Hclose $$ [PtrNext PtrCurr GMAt GMAo HMt HE0] with -
      · inext
        iunfold lockInv
        iright
        iunfold lockInvAlive
        iexists n, my, insert tickets (my + 1) (none : TicketInfo), obls
        iframe PtrNext NG PtrCurr GMAt GMAo
        isplitr
        · ipureintro
          exact ⟨dom_insert_same Domt hmy _, Domo, hc0, hcn⟩
        isplitl [HMt]
        · iapply tickets_update _ _ _ hlt _ $$ HMt
        · iunfold holderSt
          iright
          isplitr
          · ipureintro
            exact hcn'
          iexists ℓ, κu
          iframe CFl1 Wl1 GMEo1 HE0
          iright
          iexact GMEt
      imodintro
      ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
      lwp_expr_simp
      iapply acquire_end lc i G γ dq₁ dq₂ ℓ m R E hE C Φ curr my gu κu hgu $$ ITK GMEt GMEo1 HΦ
        AL CF HG HF Gg Agu Kk Of PtrCurr0 HR HE HT
    · iexfalso
      ihave %h := ghostMapP_elem_agree _ _ _ _ (none : TicketInfo) (some (gu, ℓ, m)) $$ [GMEt0]
      · iframe GMEt1 GMEt0
      simp at h
  · -- Not my turn: renew the container.
    icases (BigSepM.bigSepM_delete hlt).mp $$ HMt with ⟨Ht, HMt⟩
    iunfold ticketSt at Ht
    icases Ht with (⟨%κ', %h, #H1, -⟩ | %h | ⟨%g, %ℓ', %μ, %h, GMEt1, GMEo1, -, Kg, -⟩)
    · iexfalso
      ihave %h := ghostMapP_elem_agree _ _ _ _ (none : TicketInfo) (some (gu, ℓ, m)) $$ [GMEt0]
      · iframe H1 GMEt0
      simp at h
    · iexfalso
      ipureintro
      omega
    icases ghostMapP_elem_combine_halves _ _ _ _ $$ [GMEt0 GMEt1] with ⟨GMEt, %h'⟩
    · iframe
    obtain ⟨rfl, rfl, rfl⟩ : gu = g ∧ ℓ = ℓ' ∧ m = μ := by
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      exact ⟨h'.1.symm, h'.2.1.symm, h'.2.2.symm⟩
    imod Obl.discharge_leaf (E \ ↑Ninv) (.thread i) (G.insert gu) gu (by simp) $$ HG Kg Agu
      with ⟨HG, -⟩
    have hGgu : ∀ z, z ∈ (G.insert gu).erase gu ↔ z ∈ G := by
      intro z
      simp only [Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.mem_insert]
      grind
    ihave HG := Par.kids_congr hGgu $$ HG
    ihave HF := oblFuels_remove_obl gu _ _ $$ HF
    ihave HF := oblFuels_subset (B := G) _ (fun z hz => (hGgu z).mpr hz) $$ HF
    imod Obl.new (E \ ↑Ninv) (.thread i) G ℓ (2 + 4) $$ [] HG with
      ⟨%gu', %hgu', HG, Kgu', Agu', Fgu', #Wgu'⟩
    · iapply parLe_thread
    icases (Obl.fuel_add gu' ℓ 2 4).mp $$ Fgu' with ⟨F2, F4⟩
    ihave HF := oblFuels_add_obl G gu' ℓ 2 $$ F2 HF
    imod ghostMapP_update (some (gu', ℓ, m) : TicketInfo) $$ GMAt GMEt with ⟨GMAt, GMEt⟩
    icases ghostMapP_elem_halves $$ GMEt with ⟨GMEt, GMEt0⟩
    have hDomt' := dom_insert_same Domt hmy (some (gu', ℓ, m) : TicketInfo)
    have hne : (vz c == vz my) = false := by simpa [vz] using hc
    icases Wc with (Wc | #Dκ)
    · -- A credit of `κ`: the next iteration, by witness induction.
      imod Hclose $$ [PtrNext PtrCurr GMAt GMAo HMt Hc GMEt GMEo1 Kgu'] with -
      · inext
        iunfold lockInv
        iright
        iunfold lockInvAlive
        iexists n, c, insert tickets (my + 1) (some (gu', ℓ, m) : TicketInfo), obls
        iframe PtrNext NG PtrCurr GMAt GMAo Hc
        isplitr
        · ipureintro
          exact ⟨hDomt', Domo, hc0, hcn⟩
        iapply BigSepM.bigSepM_insert_delete.mpr
        iframe HMt
        iunfold ticketSt
        iright
        iright
        iexists gu', ℓ, m
        iframe GMEt GMEo1 CFl Kgu' Wgu'
        ipureintro
        omega
      imodintro
      ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
      lwp_expr_simp
      lwp_step HT HG HF
      rw [hne]
      lwp_step HT HG HF
      lwp_expr_simp
      imod Wit.fuels_decr κ ℓ₀ α _ $$ WFs Wc with ⟨%α₀, %hα, WFs, Fs⟩
      ihave Fs := (bigSepM_witMap G ℓ).mp $$ Fs
      ihave Fs := oblFuels_init G 50 ℓ.succ $$ Fs
      icases oblFuels_add_nat 4 46 50 G rfl $$ Fs with ⟨Fs, -⟩
      ihave HF4 := oblFuels_add_obl G gu' ℓ 4 $$ F4 Fs
      iapply IHα α₀ hα gu' hgu' $$ INV ITK CFl CFl0 Wl0 GMEo0 Wgu' HΦ AL CF EFs WFs Agu' GMEt0 HG
        HF4 HT
    · -- `κ` is discharged: the holder has changed, by the outer induction.
      iunfold holderSt at Hc
      icases Hc with (⟨%h2, -⟩ | ⟨%hcn', %ℓ₁, %κ₁, #CFl1, #Wl1, #GMEo1', HE1, Hn1⟩)
      · iexfalso
        ipureintro
        omega
      by_cases hpc' : prev = c
      · -- The same holder: its `finallyI` on `κ` is still in the invariant.
        iexfalso
        subst hpc'
        ihave %h := ghost_map_elem_agree _ _ _ _ (some κ₁) (some κ) $$ [GMEo1']
        · iframe GMEo1' GMEo0
        cases h
        iunfold finallyI at HE1
        iapply untilI_discharged_false $$ HE1 Dκ
      ihave %hlo := ghost_map_lookup $$ GMAo GMEo0
      have hp := (Domo (prev + 1)).mp (by simp [hlo])
      obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp ((Domt (prev + 1)).mpr hp)
      have hv'' : get? (PartialMap.delete tickets (my + 1)) (prev + 1) = some v' := by
        rw [LawfulPartialMap.get?_delete]
        split
        next h => exact absurd h (by omega)
        next => exact hv'
      icases (BigSepM.bigSepM_lookup_acc hv'').mp $$ HMt with ⟨Ht, HMt⟩
      icases ticketSt_obl _ _ _ c n (prev + 1) κ $$ Ht GMEo0 with ⟨%hle, Ht⟩
      ihave HMt := HMt $$ Ht
      have hpc : prev < c := by omega
      imod Hclose $$ [PtrNext PtrCurr GMAt GMAo HMt HE1 Hn1 GMEt GMEo1 Kgu'] with -
      · inext
        iunfold lockInv
        iright
        iunfold lockInvAlive
        iexists n, c, insert tickets (my + 1) (some (gu', ℓ, m) : TicketInfo), obls
        iframe PtrNext NG PtrCurr GMAt GMAo
        isplitr
        · ipureintro
          exact ⟨hDomt', Domo, hc0, hcn⟩
        isplitl [HMt GMEt GMEo1 Kgu']
        · iapply BigSepM.bigSepM_insert_delete.mpr
          iframe HMt
          iunfold ticketSt
          iright
          iright
          iexists gu', ℓ, m
          iframe GMEt GMEo1 CFl Kgu' Wgu'
          ipureintro
          omega
        · iunfold holderSt
          iright
          isplitr
          · ipureintro
            exact hcn'
          iexists ℓ₁, κ₁
          iframe CFl1 Wl1 GMEo1' HE1 Hn1
      imodintro
      ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
      lwp_expr_simp
      lwp_step HT HG HF
      rw [hne]
      lwp_step HT HG HF
      lwp_expr_simp
      have hν' : (my - c).toNat < ν := by omega
      imod embedFuels_decr Nat.lt_wfRel.wf _ hν' $$ EFs with ⟨EFs, Fs⟩
      ihave Fs := (bigSepM_embedMap G ℓ).mp $$ Fs
      icases (Obl.fuel_add_set G ℓ.succ 50 (50 * ▽)).mp $$ Fs with ⟨Fs, Fsloop⟩
      ihave Fs := oblFuels_init G 50 ℓ.succ $$ Fs
      icases oblFuels_add_nat 4 46 50 G rfl $$ Fs with ⟨Fs, -⟩
      ihave HF4 := oblFuels_add_obl G gu' ℓ 4 $$ F4 Fs
      icases ownLayer_lb_le γ dq₂ ℓ ℓ₁ $$ CF CFl1 with ⟨%hℓ₁, CF⟩
      iapply IH _ hν' c κ₁ ℓ₁ gu' rfl (by omega) hℓ₁ hgu' $$ INV ITK CFl CFl1 Wl1 GMEo1' Wgu'
        HΦ AL CF EFs Fsloop Agu' GMEt0 HG HF4 HT

/-- The loop of `acquire`, by embedded well-founded induction on the number of tickets ahead
(Rocq: the outer `iInduction ν`). -/
theorem acquire_loop (lc : Fuel) (i : ThreadId) (G : Oids) (γ : TicketLockName)
    (dq₁ dq₂ : DFrac) (ℓ : Layer) (m : Measure) (R : IProp GF) (E : CoPset) (hE : ↑N ⊆ E)
    (C : List ECtxItem) (Φ : Val → IProp GF) (next curr : Loc) (my : Int) (ν : Nat) :
    AcqLoopSpec lc i G γ dq₁ dq₂ ℓ m R E C Φ next curr my ν := by
  induction ν using Nat.strongRecOn with
  | _ ν IH =>
    intro prev κ ℓ₀ gu hν hprev hℓ₀ hgu
    iintro #INV #ITK #CFl #CFl0 #Wl0 #GMEo0 #Wgu HΦ AL CF EFs Fsloop Agu GMEt0 HG HF HT
    icases Wit.fuels_init κ ℓ₀ $$ Wl0 with ⟨%α, WFs⟩
    imod Wit.fuels_add_map κ ℓ₀ α ∅ G ℓ.succ 50 (Ordinals.Ordinal.lt_succ_iff.mpr hℓ₀) $$
      WFs Fsloop with WFs
    iapply acquire_loop_inner lc i G γ dq₁ dq₂ ℓ m R E hE C Φ next curr my ν prev κ ℓ₀ hν hprev
      IH α gu hgu $$ INV ITK CFl CFl0 Wl0 GMEo0 Wgu HΦ AL CF EFs WFs Agu GMEt0 HG HF HT

@[lantana_alias ticket_lock_mono.TicketLock_acquire_spec]
theorem acquire_spec : ∃ μ : Measure, ∀ (lc : Fuel) (m : Measure) (i : ThreadId) (G : Oids)
    (tl : Val) (γ : TicketLockName) (dq₁ dq₂ : DFrac) (ℓ : Layer) (R : IProp GF) (E : CoPset)
    (_ : ↑N ⊆ E) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&TicketLock.acquire) v(&tl)) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g ℓ.succ μ) ∗ (γ ↪LOCK_AL{dq₁}) ∗ (γ ↪LOCK_CF{dq₂} ℓ) ∗
          isFairLock tl γ R }}}
        hl(v(&TicketLock.acquire) v(&tl)) @ i; E
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
  unfold TicketLock.acquire
  lwp_step HT HG HF with Hc : 1 +ₕ 1
  icases tlc_split.mp $$ Hc with ⟨Hc, Hc'⟩
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
    (P := lockInv γ.γt γ.γo γ.γc γ.γa γ.γm next curr R) (Ninv_subseteq hE) $$ INV
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
  icases H with ⟨%n, %c, %tickets, %obls, PtrNext, #NG, PtrCurr, GMAt, GMAo,
    %⟨Domt, Domo, hc0, hcn⟩, HMt, Hc⟩
  -- The mono cell, open for the step, holds the other half of `next`.
  ihave Hacc := TicketLockMono.nextGe_acc (E := E \ ↑Ninv) γ.γm next n (Nmono_subseteq hE) $$ NG
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨HJ, CloseJ⟩
  iclear Hacc
  iapply lwp_credit_later $$ Hc'
  inext
  iunfold monoInv at HJ
  icases HJ with ⟨%w, Auth, (PtrNext0 | Fr)⟩
  rotate_left
  · iexfalso
    ihave %h := pointsTo_agree (l := next) $$ [PtrNext Fr]
    · iframe
    simp at h
  ihave %h := pointsTo_agree (l := next) $$ [PtrNext PtrNext0]
  · iframe
  have hw : w = n := by simpa [vz] using h
  subst w
  ihave PtrNext := (pointsTo_halves next _).mpr $$ [PtrNext PtrNext0]
  · iframe
  icases oblFuels_add 1 12 G $$ HF with ⟨HF1, HF⟩
  iapply lwp_faa (o := 0) (G := G) (R := ∅) $$ [HT HG HF1 PtrNext]
  · iframe HT PtrNext
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, PtrNext⟩
  icases (pointsTo_halves next _).mp $$ PtrNext with ⟨PtrNext, PtrNext0⟩
  -- `next` has increased: close the cell and register it for `n + 1`.
  imod MonoZ.own_update γ.γm n (n + 1) (by omega) $$ Auth with ⟨Auth, #Lb⟩
  imod CloseJ $$ [Auth PtrNext0] with -
  · inext
    iunfold monoInv
    iexists n + 1
    iframe Auth
    ileft
    iexact PtrNext0
  imodintro
  imod nextGe_register (E \ ↑Ninv) γ.γm next (n + 1) n (Nmono_subseteq hE) $$ NG Lb with #NG1
  iclear NG Lb
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
      iframe PtrNext NG1 PtrCurr GMAt GMAo
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
    obtain ⟨hft, Domt'⟩ := dom_insert_succ Domt (by omega) (some (gu, ℓ, m) : TicketInfo)
    obtain ⟨hfo, Domo'⟩ := dom_insert_succ Domo (by omega) (none : Option Oid)
    imod ghostMapP_insert (n + 1) (some (gu, ℓ, m) : TicketInfo) hft $$ GMAt with ⟨GMAt, GMEt⟩
    icases ghostMapP_elem_halves $$ GMEt with ⟨GMEt, GMEt0⟩
    imod ghost_map_insert (n + 1) (none : Option Oid) hfo $$ GMAo with ⟨GMAo, GMEo⟩
    imod Hclose $$ [PtrNext PtrCurr GMAt GMAo HMt Hc GMEt GMEo Kgu] with -
    · inext
      iunfold lockInv
      iright
      iunfold lockInvAlive
      iexists n + 1, c, insert tickets (n + 1) (some (gu, ℓ, m) : TicketInfo),
        insert obls (n + 1) (none : Option Oid)
      iframe PtrNext NG1 PtrCurr GMAt GMAo
      isplitr
      · ipureintro
        exact ⟨Domt', Domo', hc0, by omega⟩
      isplitl [HMt GMEt GMEo Kgu]
      · iapply tickets_insert γ.γt γ.γo γ.γc tickets _ hft $$ HMt
        iunfold ticketSt
        iright
        iright
        iexists gu, ℓ, m
        iframe GMEt GMEo CFl Kgu Wgu
        ipureintro
        omega
      · iapply holderSt_mono_n γ.γt γ.γo γ.γc curr R hcn'
        iunfold holderSt
        iright
        isplitr
        · ipureintro
          exact hcn'
        iexact Hc
    imodintro
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    lwp_step HT HG HF with Hc1 : 1
    lwp_expr_simp
    lwp_step HT HG HF
    lwp_expr_simp
    lwp_step HT HG HF
    lwp_expr_simp
    icases oblFuels_add 4 5 _ $$ HF with ⟨HF, -⟩
    -- My turn, or wait: the first check, in the lock invariant.
    iapply fupd_lwp
    ihave Hacc := alwaysI_acc (E := E) (N := Ninv)
      (P := lockInv γ.γt γ.γo γ.γc γ.γa γ.γm next curr R) (Ninv_subseteq hE) $$ INV
    imod Hacc with ⟨H, Hclose⟩
    ihave Hc1 := tlc_one_nat.mpr $$ Hc1
    imod lc_fupd_elim_later $$ Hc1 H with H
    iunfold lockInv at H
    icases H with (Hdel | H)
    · iexfalso
      iapply ownAlive_full_false $$ AL Hdel
    iunfold lockInvAlive at H
    icases H with ⟨%n', %c', %tickets', %obls', PtrNext, #NG, PtrCurr, GMAt, GMAo,
      %⟨Domt₁, Domo₁, hc0', hcn''⟩, HMt, Hc⟩
    ihave %hlt := ghostMapP_lookup $$ GMAt GMEt0
    have hmy := (Domt₁ (n + 1)).mp (by simp [hlt])
    icases (BigSepM.bigSepM_lookup_acc hlt).mp $$ HMt with ⟨Ht, HMt⟩
    icases ticketSt_waiting _ _ _ c' n' (n + 1) _ $$ Ht GMEt0 with ⟨%hle, Ht, GMEt0⟩
    ihave HMt := HMt $$ Ht
    iunfold holderSt at Hc
    icases Hc with (⟨%h, -⟩ | ⟨%hcn2, %ℓ₀, %κ, #CFl0, #Wl0, #GMEo0, HE0, Hn⟩)
    · iexfalso
      ipureintro
      omega
    by_cases hmine : n = c'
    · -- My turn.
      obtain rfl := hmine
      icases Hn with (Hn | #GMEt1)
      rotate_left
      · iexfalso
        ihave %h := ghostMapP_elem_agree _ _ _ _ (none : TicketInfo) (some (gu, ℓ, m)) $$
          [GMEt0]
        · iframe GMEt1 GMEt0
        simp at h
      iunfold nextOwner at Hn
      icases Hn with ⟨%g, %μ, GMEt1, HE, Gg, Kk, Of, PtrCurr0, HR⟩
      icases ghostMapP_elem_combine_halves _ _ _ _ $$ [GMEt0 GMEt1] with ⟨GMEt, %h⟩
      · iframe
      obtain ⟨rfl, rfl, rfl⟩ : gu = g ∧ ℓ = ℓ₀ ∧ m = μ := by
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
      imod ghostMapP_update (none : TicketInfo) $$ GMAt GMEt with ⟨GMAt, GMEt⟩
      imod ghostMapP_elem_persist $$ GMEt with #GMEt
      imod Hclose $$ [PtrNext PtrCurr GMAt GMAo HMt HE0] with -
      · inext
        iunfold lockInv
        iright
        iunfold lockInvAlive
        iexists n', n, insert tickets' (n + 1) (none : TicketInfo), obls'
        iframe PtrNext NG PtrCurr GMAt GMAo
        isplitr
        · ipureintro
          exact ⟨dom_insert_same Domt₁ ⟨by omega, hmy.2⟩ _, Domo₁, hc0', hcn''⟩
        isplitl [HMt]
        · iapply tickets_update _ _ _ hlt _ $$ HMt
        · iunfold holderSt
          iright
          isplitr
          · ipureintro
            exact hcn2
          iexists ℓ, κ
          iframe CFl0 Wl0 GMEo0 HE0
          iright
          iexact GMEt
      imodintro
      iapply acquire_mine lc i G γ dq₁ dq₂ ℓ m R E hE C Φ curr n gu κ hgu $$ ITK GMEt GMEo0 HΦ
        AL CF HG HF Gg Agu Kk Of PtrCurr0 HR HE HT
    · -- Not my turn: the loop.
      have hlt' : c' < n := by omega
      imod Hclose $$ [PtrNext PtrCurr GMAt GMAo HMt HE0 Hn] with -
      · inext
        iunfold lockInv
        iright
        iunfold lockInvAlive
        iexists n', c', tickets', obls'
        iframe PtrNext NG PtrCurr GMAt GMAo HMt
        isplitr
        · ipureintro
          exact ⟨Domt₁, Domo₁, hc0', hcn''⟩
        iunfold holderSt
        iright
        isplitr
        · ipureintro
          exact hcn2
        iexists ℓ₀, κ
        iframe CFl0 Wl0 GMEo0 HE0 Hn
      imodintro
      icases ownLayer_lb_le γ dq₂ ℓ ℓ₀ $$ CF CFl0 with ⟨%hℓ₀, CF⟩
      icases (Obl.fuel_add_set G ℓ.succ _ _).mp $$ Fsloop with ⟨Fs1, Fs2⟩
      imod embedFuels_add_map Nat.lt_wfRel.wf (n - c').toNat ∅ G ℓ.succ (50 + 50 * ▽) $$
        [] Fs1 with EFs
      · iapply embedFuels_init
      iapply acquire_loop lc i G γ dq₁ dq₂ ℓ m R E hE C Φ next curr n ((n - c').toNat) c' κ ℓ₀
        gu rfl hlt' hℓ₀ hgu $$ INV ITK CFl CFl0 Wl0 GMEo0 Wgu HΦ AL CF EFs Fs2 Agu GMEt0 HG HF HT


end Acquire

end Lantana.Examples.TicketLockMono
