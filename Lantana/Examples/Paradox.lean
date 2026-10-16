/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Examples.World

/-! # The no-credit rule is unsound

Rocq `examples/paradox.v`. The class `LwpNoLc` assumes, for HeapLang, a rule for one pure step
that pays no fuel and gives no later credits, yet yields a witness credit for each observed
obligation that is not discharged (`lwp_pure_step_no_lc`; compare `lwp_pure_step`: no thread
token, no children with their fuel, no `ALC`/`£`). With it, two threads running
`rec loop _ := loop ()` prove "eventually `False`" (`loop_paradox`), and a fair run of the loops
refutes the rule (`no_lc_absurd`).

Thread `0` holds the commitment `untilI N1 z 1 True False`, which it never keeps, and steps by
the assumed rule, observing in every step the current obligation `ck` of thread `1` as a
witness: a witness credit decreases its witness fuel (`Wit.fuels_ind`, well-founded); once `ck`
is discharged, thread `0` reads the next obligation and ten later credits from the invariant
`px` and continues by Löb induction (`px_loop1_spec`). Thread `1` pays its steps honestly with
the fuel of `ck`; in each iteration it allocates the next obligation `ck1`, registers it with
ten later credits in the invariant at the next index, and discharges `ck` (`px_loop2_spec`).
The invariant `pxInv` keeps, per index `a`, the obligation `k` registered there, its witness,
and either the ten credits or a lower bound of thread `0`'s counter past `a` (the credits have
been taken), and either half of the until on `k` or its discharge with the next entry.

The assumed rule is a hypothesis of the theorems (the class, assumed for every instance of the
ghost state of the closed world `ExGF`), never an axiom. Statement adaptations: thread ids are
list positions (Rocq `i`, `j` are `0`, `1`); the counters are two mono-nat ghost names (Rocq: one
`gmap positive mono_nat` camera with fresh keys); the hypothesis is over `ExGF` only (Rocq: over
every `Σ` with `heapGS Σ`), which makes the theorems stronger.
-/

@[expose] public noncomputable section

namespace Lantana.Examples.Paradox

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open Iris.Std (get? insert)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The assumed rule -/

/-- The no-credit rule (Rocq `lantanaGS_no_lc`): one pure step that pays no fuel and gives no
later credits, yet yields a witness credit for each obligation of `R` that is not discharged. -/
@[lantana_alias lantanaGS_no_lc]
class LwpNoLc (GF : BundledGFunctors) [ModelGS GF] [HeapGS GF] : Prop where
  lwp_pure_step_no_lc (s : Stuckness) (i : ThreadId) (E E' : CoPset) (e₁ e₂ : Exp) (φ : Prop)
    (Φ : Val → IProp GF) : PureExec φ 1 e₁ e₂ → φ →
    (|={E,E'}=> ∃ R : Oids, witLayers R ∗
      (witCreds R -∗ |={E',E}=> |={E}=>m lWP e₂ @ s; i; E {{ Φ }})) ⊢
      lWP e₁ @ s; i; E {{ Φ }}

attribute [lantana_alias lwp_pure_step_no_lc] LwpNoLc.lwp_pure_step_no_lc

/-! ## The program -/

/-- `rec loop _ := loop ()`. -/
@[lantana_alias paradox.loop]
def loop : Val := hl_val(rec loop _ := loop #())

/-! ## The ghost state: counters and a ghost map of obligations -/

/-- Finite maps from indices. -/
abbrev IdxMap : Type → Type := OidMap

/-- The cameras of the paradox (Rocq `mcntsG`): mono-nat counters and a ghost map from indices
to obligations. -/
@[lantana_alias mcntsG]
class ParadoxG (GF : BundledGFunctors) where
  [cntG : MonoNatG GF]
  [mapG : GhostMapG GF Nat Oid IdxMap]

attribute [reducible, instance] ParadoxG.cntG ParadoxG.mapG

instance : ParadoxG ExGF where

section Counters
variable {GF : BundledGFunctors} [ParadoxG GF]

/-- The fraction `q` of the authority of the counter `γ`, at `n`. -/
@[lantana_alias cnt_auth]
def cntAuth (γ : GName) (n : Nat) (q : Qp) : IProp GF := MonoNat.auth_own γ (.own q) ⟨n⟩

/-- The counter `γ` is at least `n`. -/
@[lantana_alias cnt_lb]
def cntLb (γ : GName) (n : Nat) : IProp GF := MonoNat.lb_own γ ⟨n⟩

@[lantana_alias cnt_lb_persistent]
instance cntLb_persistent (γ : GName) (n : Nat) : Persistent (cntLb (GF := GF) γ n) := by
  unfold cntLb; infer_instance

@[lantana_alias cnt_auth_timeless]
instance cntAuth_timeless (γ : GName) (n : Nat) (q : Qp) : Timeless (cntAuth (GF := GF) γ n q) := by
  unfold cntAuth; infer_instance

@[lantana_alias cnt_lb_timeless]
instance cntLb_timeless (γ : GName) (n : Nat) : Timeless (cntLb (GF := GF) γ n) := by
  unfold cntLb; infer_instance

/-- The authority is two halves. -/
theorem cntAuth_halves (γ : GName) (n : Nat) :
    cntAuth (GF := GF) γ n 1 ⊣⊢ cntAuth γ n (1 : Qp).half ∗ cntAuth γ n (1 : Qp).half := by
  have h := (inferInstance : Fractional (PROP := IProp GF)
    (fun q : Qp => MonoNat.auth_own γ (.own q) (⟨n⟩ : MaxNat))).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

@[lantana_alias get_cnt_lb]
theorem cntAuth_lb (γ : GName) {m n : Nat} (q : Qp) (h : m ≤ n) :
    cntAuth (GF := GF) γ n q ⊢ cntLb γ m := by
  unfold cntAuth cntLb
  iintro H
  ihave H := MonoNat.lb_own_get γ _ _ $$ H
  iapply MonoNat.lb_own_le γ ⟨n⟩ ⟨m⟩ h $$ H

@[lantana_alias cnt_auth_op_valid]
theorem cntAuth_agree (γ : GName) (n₁ n₂ : Nat) (q₁ q₂ : Qp) :
    cntAuth (GF := GF) γ n₁ q₁ ⊢ cntAuth γ n₂ q₂ -∗ ⌜n₁ = n₂⌝ := by
  unfold cntAuth
  iintro H₁ H₂
  ihave %h := MonoNat.auth_own_agree γ _ _ _ _ $$ H₁ H₂
  ipureintro
  exact congrArg MaxNat.toNat h.2

@[lantana_alias cnt_auth_lb_valid]
theorem cntAuth_lb_valid (γ : GName) (n m : Nat) (q : Qp) :
    cntAuth (GF := GF) γ n q ⊢ cntLb γ m -∗ ⌜m ≤ n⌝ := by
  unfold cntAuth cntLb
  iintro H₁ H₂
  ihave %h := MonoNat.auth_lb_own_valid γ _ _ _ $$ H₁ H₂
  ipureintro
  exact h.2

@[lantana_alias cnt_auth_update]
theorem cntAuth_update (γ : GName) {n m : Nat} (h : n ≤ m) :
    cntAuth (GF := GF) γ n 1 ⊢ |==> (cntAuth γ m 1 ∗ cntLb γ m) := by
  unfold cntAuth cntLb
  iintro H
  iapply MonoNat.own_update γ ⟨n⟩ ⟨m⟩ h $$ H

@[lantana_alias alloc_cnt_auth]
theorem cntAuth_alloc (n : Nat) : ⊢@{IProp GF} |==> ∃ γ : GName, cntAuth γ n 1 := by
  unfold cntAuth
  imod MonoNat.own_alloc (GF := GF) ⟨n⟩ with ⟨%γ, H, -⟩
  imodintro
  iexists γ
  iexact H

end Counters

/-! ## The invariant -/

/-- The namespaces of the invariant, of the untils of thread `1` and of thread `0`'s
commitment. -/
def N : Namespace := nroot.@"paradox_inv"
def Nu : Namespace := nroot.@"paradox_until"
def N1 : Namespace := nroot.@"paradox_false"

/-- The untils' namespace is outside the invariant's. -/
theorem Nu_subseteq : (↑Nu : CoPset) ⊆ ⊤ \ ↑N := by
  intro p hp
  refine Iris.Std.LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun h' => ?_⟩
  exact ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩

section Invariant
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [ParadoxG GF]

/-- The index `a` is registered with the obligation `k` (Rocq `a ↪[rm]□ k`). -/
abbrev mapElem (rm : GName) (a : Nat) (k : Oid) : IProp GF := rm ↪◯MAP[a]{.discard} k

/-- What the discharge of the obligation of index `a` gives: thread `1`'s counter is past `a`,
and the next index is registered. -/
def nextQ (rm cj : GName) (a : Nat) : IProp GF :=
  iprop(cntLb cj (a + 1) ∗ ∃ k' : Oid, mapElem rm (a + 1) k')

instance nextQ_persistent (rm cj : GName) (a : Nat) : Persistent (nextQ (GF := GF) rm cj a) := by
  unfold nextQ; infer_instance

/-- The entry of index `a`, registered with `k`: ten later credits for thread `0` or its counter
past `a`, the registration, thread `1`'s counter at `a`, the witness of `k`; and half of the
until on `k`, or its discharge with the next registration. -/
def pxEntry (rm ci cj : GName) (a : Nat) (k : Oid) : IProp GF :=
  iprop(((£ₙ 10 ∨ cntLb ci a) ∗ mapElem rm a k ∗ cntLb cj a ∗ Wit.layer k 0) ∗
    (finallyI Nu k (1 : Qp).half (nextQ rm cj a) ∨ (Obl.discharged k ∗ nextQ rm cj a)))

/-- The invariant of the paradox (Rocq `px_inv`). -/
@[lantana_alias px_inv]
def pxInv (rm ci cj : GName) : IProp GF :=
  iprop(∃ (n : Nat) (os : IdxMap Oid), (cntAuth cj n (1 : Qp).half ∗ rm ↪●MAP os) ∗
    bigSepM (M := IdxMap) (fun a k => pxEntry rm ci cj a k) os)

/-- Rocq `px`. -/
@[lantana_alias px]
def px (rm ci cj : GName) : IProp GF := inv N (pxInv rm ci cj)

@[lantana_alias px_persistent]
instance px_persistent (rm ci cj : GName) : Persistent (px (GF := GF) rm ci cj) := by
  unfold px; infer_instance

/-- An index past thread `1`'s counter is not registered. -/
theorem pxInv_fresh (rm ci cj : GName) (n : Nat) (q : Qp) (os : IdxMap Oid) :
    bigSepM (M := IdxMap) (fun a k => pxEntry (GF := GF) rm ci cj a k) os ⊢
      cntAuth cj n q -∗ ⌜get? os (n + 1) = none⌝ := by
  iintro HM Ca
  rcases h : get? os (n + 1) with _ | k
  · ipureintro
    rfl
  · unfold pxEntry
    icases (BigSepM.bigSepM_delete h).mp $$ HM with ⟨⟨⟨-, -, #Hlb, -⟩, -⟩, -⟩
    ihave %hle := cntAuth_lb_valid cj n (n + 1) q $$ Ca Hlb
    exact absurd hle (by omega)

end Invariant

/-! ## The two loops -/

section Specs
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [ParadoxG GF]

/-- Thread `1` pays its steps with the fuel of its obligation `ck` of index `n`; in each
iteration it registers the next obligation, with ten later credits, and discharges `ck`. -/
@[lantana_alias px_loop2_spec]
theorem px_loop2_spec : ∀ (j n : Nat) (rm ci cj : GName) (ck : Oid) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr j C hl(v(&loop) #()) ∗ thKids j {ck} ∗ oblKids ck ∅ ∗
          finallyI Nu ck (1 : Qp).half (nextQ rm cj n) ∗ Obl.fuel ck 0 10 ∗ px rm ci cj ∗
          cntAuth cj n (1 : Qp).half ∗ mapElem rm n ck }}}
        hl(v(&loop) #()) @ j
      l{{{ RET hl_val(#()); threadExpr j C hl(#()) ∗
        liftTerm j (fun _ _ => iprop(True)) hl_val(#()) }}} := by
  intro j n rm ci cj ck C
  iintro %Φ !> ⟨HT, HG, Kck, Uck, Gf, #Hpx, Caj, #Mn⟩ HΦ
  unfold finallyI
  iloeb as IH generalizing! %n %ck
  ihave HF := oblFuels_init {ck} 10 0 $$ [Gf]
  · iapply BigSepS.bigSepS_singleton.mpr
    iexact Gf
  unfold loop
  lwp_step HT HG HF with Hlc : Ordinals.Ordinal.ofNat (1 + (10 + (1 + 1)))
  lwp_expr_simp
  icases (tlc_split_nat 1 _).mp $$ Hlc with ⟨Hc1, Hlc⟩
  iapply lwp_credit_later_nat $$ Hc1
  inext
  icases (tlc_split_nat 10 _).mp $$ Hlc with ⟨Hc10, Hlc⟩
  icases (tlc_split_nat 1 1).mp $$ Hlc with ⟨Hc2, Hc3⟩
  -- The next obligation `ck1`, with its until, is allocated before the invariant is opened.
  imod untilI_alloc (E := ⊤) (.thread j) {ck} 0 10 $$ [] HG with
    ⟨%ck1, %hck1, HG, Kck1, Of1, #Wl1, A⟩
  · iapply parLe_thread
  imod A $$ %⊤ %Nu %iprop(True) %(nextQ rm cj (n + 1)) [] with Unew
  · inext
    ipureintro
    trivial
  icases untilI_frac_split (q₁ := (1 : Qp).half) (q₂ := (1 : Qp).half) (Qp.half_add_half 1).symm
    $$ Unew with ⟨Unew, Unew1⟩
  ihave Hupd : |={⊤}=>m (thKids j {ck1} ∗ cntAuth cj (n + 1) (1 : Qp).half ∗
      mapElem rm (n + 1) ck1) $$ [Hc2 Hc3 Hc10 HG Kck Uck Caj Unew1]
  · unfold px
    ihave Hacc := inv_acc (E := ⊤) (N := N) (P := pxInv rm ci cj)
      (fun _ _ => CoPset.mem_full) $$ Hpx
    ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
    imod Hacc with ⟨Hi, Hclose⟩
    iapply lc_mupd_add_later $$ Hc2
    inext
    unfold pxInv
    icases Hi with ⟨%m, %os, ⟨Ca, GMA⟩, HM⟩
    ihave %hm := cntAuth_agree cj n m _ _ $$ Caj Ca
    subst hm
    ihave %hfresh := pxInv_fresh rm ci cj n _ os $$ HM Caj
    ihave %hlu := ghost_map_lookup $$ GMA Mn
    icases (BigSepM.bigSepM_delete hlu).mp $$ HM with ⟨Hn, HM⟩
    unfold pxEntry finallyI
    icases Hn with ⟨Hn, (Uck1 | ⟨#Hd, -⟩)⟩
    rotate_left
    · iexfalso
      iapply untilI_discharged_false $$ Uck Hd
    ihave Uck := untilI_frac_add (q := 1) (Qp.half_add_half 1).symm $$ Uck Uck1
    ihave Caj := (cntAuth_halves cj n).mpr $$ [Caj Ca]
    · iframe
    imod cntAuth_update cj (Nat.le_succ n) $$ Caj with ⟨Caj, #Hlb1⟩
    icases (cntAuth_halves cj (n + 1)).mp $$ Caj with ⟨Caj, Ca⟩
    imod ghost_map_insert_persist (n + 1) ck1 hfresh $$ GMA with ⟨GMA, #Mn1⟩
    have hdis : (£ₙ 1 : IProp GF) ⊢ thKids j (({ck} : Oids).insert ck1) -∗ oblKids ck ∅ -∗
        untilI Nu ck 1 iprop(True) (nextQ rm cj n) -∗ nextQ rm cj n -∗
        |={⊤ \ ↑N}=>m nextQ rm cj n ∗ thKids j ((({ck} : Oids).insert ck1).erase ck) ∗
          Obl.discharged ck :=
      finallyI_discharge (.thread j) _ Nu_subseteq (by simp)
    imod hdis $$ Hc3 HG Kck Uck [] with ⟨#HQ, HG, #Hd⟩
    · unfold nextQ
      iframe Hlb1
      iexists ck1
      iexact Mn1
    ihave HG := Par.kids_congr (B := {ck1}) ?_ $$ HG
    · intro z
      simp at hck1 ⊢
      grind
    imod Hclose $$ [Ca GMA HM Hn Hc10 Unew1] with -
    · inext
      iexists n + 1, insert os (n + 1) ck1
      iframe Ca GMA
      iapply (BigSepM.bigSepM_insert hfresh).mpr
      isplitl [Hc10 Unew1]
      · iframe Unew1 Mn1 Hlb1 Wl1
        ileft
        iexact Hc10
      · iapply (BigSepM.bigSepM_delete hlu).mpr
        iframe HM
        iframe Hn
        iright
        iframe Hd HQ
    imodintro
    iframe HG Caj Mn1
  imod Hupd with ⟨HG, Caj, #Mn1⟩
  iapply IH $$ %(n + 1) %ck1 HT HG Kck1 Unew Of1 Caj HΦ Mn1

end Specs

end Lantana.Examples.Paradox
