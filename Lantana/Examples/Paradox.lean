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
ghost state of the closed world `ExGF`, whose slots 21–22 hold the counters and the ghost map),
never an axiom. Statement adaptations: thread ids are list positions (Rocq `i`, `j` are `0`, `1`);
the counters are two mono-nat ghost names (Rocq: one `gmap positive mono_nat` camera with fresh
keys); the hypothesis is over `ExGF` only (Rocq: over every `Σ` with `heapGS Σ`), which makes the
theorems stronger. Proof adaptations: the witness induction of thread `0` is `Wit.fuels_ind` with
no fuels (Rocq: `iInduction` on the ordinal of `wit_fuels_init`); the later credits strip the
later of the invariant (and of the Löb hypothesis) with `lc_fupd_add_later`/`lc_mupd_add_later`;
the specs are stated with an arbitrary caller context `C`, as in Rocq. Rocq's derived forms of the
rule and their tactics (`lwp_pure_step_no_lc_alt`, `tac_lwp_pure_no_lc`, `lwp_pure_no_lc`) are not
needed: the rule is applied once, directly.
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
theorem cntAuth_alloc (n : Nat) :
    ⊢@{IProp GF} |==> ∃ γ : GName, cntAuth γ n 1 ∗ cntLb γ n := by
  unfold cntAuth cntLb
  iapply MonoNat.own_alloc (GF := GF) ⟨n⟩

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

omit [ModelGS GF] [HeapGS GF] in
/-- `nextQ` unfolded (for `icases`, which does not unfold definitions). -/
theorem nextQ_iff (rm cj : GName) (a : Nat) :
    nextQ (GF := GF) rm cj a ⊣⊢ cntLb cj (a + 1) ∗ ∃ k' : Oid, mapElem rm (a + 1) k' := by
  unfold nextQ; exact .rfl

/-- `pxEntry` unfolded: a big separating conjunction over the entries keeps them folded, so that
an entry taken out with `bigSepM_delete` can be put back. -/
theorem pxEntry_iff (rm ci cj : GName) (a : Nat) (k : Oid) :
    pxEntry (GF := GF) rm ci cj a k ⊣⊢
      ((£ₙ 10 ∨ cntLb ci a) ∗ mapElem rm a k ∗ cntLb cj a ∗ Wit.layer k 0) ∗
        (finallyI Nu k (1 : Qp).half (nextQ rm cj a) ∨ (Obl.discharged k ∗ nextQ rm cj a)) := by
  unfold pxEntry; exact .rfl

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

/-- Thread `0` steps by the assumed rule, observing thread `1`'s obligation `ck` of index `n`;
its later credits come from the invariant (`px`). -/
@[lantana_alias px_loop1_spec]
theorem px_loop1_spec [LwpNoLc GF] : ∀ (i : ThreadId) (z : Oid) (rm ci cj : GName)
    (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&loop) #()) ∗ thKids i {z} ∗
          untilI N1 z 1 iprop(True) iprop(False) ∗ £ₙ 10 ∗ px rm ci cj ∗
          ∃ n : Nat, cntAuth ci n 1 ∗ cntLb cj n ∗ ∃ ck : Oid, Wit.layer ck 0 ∗ mapElem rm n ck }}}
        hl(v(&loop) #()) @ i
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗
        liftTerm i (fun _ _ => iprop(True)) hl_val(#()) }}} := by
  intro i z rm ci cj C
  iintro %Φ !> ⟨HT, HG, HU, Hlc, #Hpx, %n, Hca, #Hlb, %ck, #Wck, #Mn⟩ -
  unfold px
  iloeb as IH generalizing! %n %ck
  icases Wit.fuels_init ck 0 $$ Wck with ⟨%α, #Wf⟩
  imod Wit.fuels_ind ck 0 α ∅ iprop(threadExpr i C hl(v(&loop) #()) -∗ thKids i {z} -∗
      untilI N1 z 1 iprop(True) iprop(False) -∗ £ₙ 10 -∗ cntAuth ci n 1 -∗
      lWP hl(v(&loop) #()) @ i {{ Φ }}) $$ [] with HP
  · isplitl []
    · imodintro
      iintro HInd
      imodintro
      iintro HT HG HU Hlc Hca
      -- The step pays nothing and observes `ck`.
      iapply LwpNoLc.lwp_pure_step_no_lc (e₁ := hl(v(&loop) #())) _ i ⊤ ⊤ _ True Φ
        instPureExecBeta trivial
      imodintro
      iexists {ck}
      isplitl []
      · unfold witLayers
        iapply BigSepS.bigSepS_singleton.mpr
        iexists 0
        iexact Wck
      iintro Hwc
      unfold loop
      lwp_expr_simp
      icases witCreds_singleton ck $$ Hwc with (Hc | #Hd)
      · -- A credit of `ck`: witness induction.
        imod HInd $$ Hc with ⟨-, HP⟩
        imodintro
        imodintro
        iapply HP $$ HT HG HU Hlc Hca
      · -- `ck` is discharged: the next index, and its credits, from the invariant.
        imod inv_acc (E := ⊤) (N := N) (P := pxInv rm ci cj) (fun _ _ => CoPset.mem_full)
          $$ Hpx with ⟨Hi, Hclose⟩
        icases (tlc_split_nat 1 9).mp $$ Hlc with ⟨Hc1, -⟩
        iapply lc_fupd_add_later $$ Hc1
        inext
        unfold pxInv
        icases Hi with ⟨%m, %os, ⟨Ca, GMA⟩, HM⟩
        ihave %hlu := ghost_map_lookup $$ GMA Mn
        icases (BigSepM.bigSepM_delete hlu).mp $$ HM with ⟨Hn, HM⟩
        icases (pxEntry_iff rm ci cj n ck).mp $$ Hn with ⟨Hn, (HF | ⟨-, #HQ⟩)⟩
        · iexfalso
          unfold finallyI
          iapply untilI_discharged_false $$ HF Hd
        icases (nextQ_iff rm cj n).mp $$ HQ with ⟨#Hlbj1, %ck1, #Mn1⟩
        ihave HM : bigSepM (M := IdxMap) (fun a k => pxEntry rm ci cj a k) os $$ [Hn HM]
        · iapply (BigSepM.bigSepM_delete hlu).mpr
          iframe HM
          iapply (pxEntry_iff rm ci cj n ck).mpr
          iframe Hn
          iright
          iframe Hd HQ
        ihave %hlu1 := ghost_map_lookup $$ GMA Mn1
        icases (BigSepM.bigSepM_delete hlu1).mp $$ HM with ⟨Hn1, HM⟩
        icases (pxEntry_iff rm ci cj (n + 1) ck1).mp $$ Hn1 with
          ⟨⟨(Hc10 | #Hlbi), -, -, #Wck1⟩, HnU1⟩
        rotate_left
        · ihave %hle := cntAuth_lb_valid ci n (n + 1) 1 $$ Hca Hlbi
          exact absurd hle (by omega)
        imod cntAuth_update ci (Nat.le_succ n) $$ Hca with ⟨Hca, #Hlbi1⟩
        imod Hclose $$ [Ca GMA HM HnU1] with -
        · inext
          iexists m, os
          iframe Ca GMA
          iapply (BigSepM.bigSepM_delete hlu1).mpr
          iframe HM
          iapply (pxEntry_iff rm ci cj (n + 1) ck1).mpr
          iframe HnU1 Mn1 Hlbj1 Wck1
          iright
          iexact Hlbi1
        imodintro
        imodintro
        iapply IH $$ %(n + 1) %ck1 HT HG HU Hc10 Hca Hlbj1 Wck1 Mn1
    · iexact Wf
  iapply HP $$ HT HG HU Hlc Hca

/-- The ghost state and the invariant, and thread `1`'s first obligation `ck` at index `0`,
registered with its witness and half of its until. -/
@[lantana_alias px_init]
theorem px_init (E : CoPset) (j : ThreadId) :
    (thKids j ∅ : IProp GF) ⊢ |={E}=>m ∃ (ck : Oid) (rm ci cj : GName) (n : Nat),
      thKids j {ck} ∗ oblKids ck ∅ ∗ Obl.fuel ck 0 10 ∗
      finallyI Nu ck (1 : Qp).half (nextQ rm cj n) ∗ Wit.layer ck 0 ∗ px rm ci cj ∗
      cntAuth ci n 1 ∗ cntAuth cj n (1 : Qp).half ∗ cntLb cj n ∗ mapElem rm n ck := by
  iintro HG
  imod cntAuth_alloc (GF := GF) 0 with ⟨%ci, Cai, #Cli⟩
  imod cntAuth_alloc (GF := GF) 0 with ⟨%cj, Caj, #Clj⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Oid) (H := IdxMap) with ⟨%rm, GM⟩
  imod untilI_alloc (E := E) (.thread j) ∅ 0 10 $$ [] HG with ⟨%ck, -, HG, Kck, Gf, #Wl, A⟩
  · iapply parLe_thread
  imod A $$ %E %Nu %iprop(True) %(nextQ rm cj 0) [] with HF
  · inext
    ipureintro
    trivial
  imod ghost_map_insert_persist 0 ck (Iris.Std.LawfulPartialMap.get?_empty _) $$ GM
    with ⟨GM, #Me⟩
  icases untilI_frac_split (q₁ := (1 : Qp).half) (q₂ := (1 : Qp).half) (Qp.half_add_half 1).symm
    $$ HF with ⟨HF, HF0⟩
  icases (cntAuth_halves cj 0).mp $$ Caj with ⟨Caj, Caj0⟩
  imod inv_alloc N E (pxInv rm ci cj) $$ [Caj0 GM HF0] with #Hpx
  · inext
    unfold pxInv
    iexists 0, insert (∅ : IdxMap Oid) 0 ck
    iframe Caj0 GM
    iapply (BigSepM.bigSepM_insert (Iris.Std.LawfulPartialMap.get?_empty _)).mpr
    isplitl
    · iapply (pxEntry_iff rm ci cj 0 ck).mpr
      iframe Me Clj Wl
      isplitr
      · iright
        iexact Cli
      · ileft
        unfold finallyI
        iexact HF0
    · iapply BigSepM.bigSepM_empty.mpr
      iempintro
  imodintro
  iexists ck, rm, ci, cj, 0
  unfold finallyI
  iframe Kck Gf HF Wl Cai Caj Clj Me
  isplitl [HG]
  · iapply Par.kids_congr _ $$ HG
    intro z
    simp
  · unfold px
    iexact Hpx

/-- The resources after the allocations (Rocq `Φ_P`): thread `0`'s commitment to `False`,
half of the until on thread `1`'s first obligation, and the rest. -/
def mainRes : IProp GF :=
  iprop(∃ (z ck : Oid) (rm ci cj : GName) (n : Nat),
    untilI N1 z 1 iprop(True) iprop(False) ∗
    finallyI Nu ck (1 : Qp).half (nextQ rm cj n) ∗
    (£ₙ 10 ∗ px rm ci cj ∗ cntAuth ci n 1 ∗ cntAuth cj n (1 : Qp).half ∗ cntLb cj n ∗
      mapElem rm n ck ∗ Wit.layer ck 0 ∗ thKids 0 {z} ∗ thKids 1 {ck} ∗ oblKids ck ∅ ∗
      Obl.fuel ck 0 10))

/-- The postcondition of both threads. -/
abbrev post : ThreadId → Val → IProp GF := fun _ _ => iprop(True)

/-- From the tokens of the two threads, ten later credits and their empty sets of children:
the resources, and the `lWP`s of the threads from them (Rocq `px_loop_pre`). -/
@[lantana_alias px_loop_pre]
theorem px_loop_pre [LwpNoLc GF] :
    threadExpr (GF := GF) 0 [] hl(v(&loop) #()) ⊢ threadExpr 1 [] hl(v(&loop) #()) -∗ £ₙ 10 -∗
      thKids 0 ∅ -∗ thKids 1 ∅ -∗
      |={⊤}=>m mainRes ∗
        (mainRes -∗ |={⊤}=>m lWP hl(v(&loop) #()) @ 0; ⊤ {{ liftTerm 0 post }} ∗
          lWP hl(v(&loop) #()) @ 1; ⊤ {{ liftTerm 1 post }}) := by
  iintro HT0 HT1 Hlc HG0 HG1
  imod untilI_alloc (E := ⊤) (.thread 0) ∅ 1 0 $$ [] HG0 with ⟨%z, -, HG0, -, -, -, A⟩
  · iapply parLe_thread
  imod A $$ %⊤ %N1 %iprop(True) %iprop(False) [] with HFz
  · inext
    ipureintro
    trivial
  imod px_init ⊤ 1 $$ HG1 with
    ⟨%ck, %rm, %ci, %cj, %n, HG1, Kck, Gf, HFck, #Wl, #Hpx, Cai, Caj, #Clj, #Me⟩
  imodintro
  isplitl [HFz HFck Hlc Cai Caj HG0 HG1 Kck Gf]
  · unfold mainRes
    iexists z, ck, rm, ci, cj, n
    iframe HFz HFck Hlc Hpx Cai Caj Clj Me Wl HG1 Kck Gf
    iapply Par.kids_congr _ $$ HG0
    intro z
    simp
  iintro HP
  unfold mainRes
  icases HP with ⟨%z, %ck, %rm, %ci, %cj, %n, HFz, HFck, Hlc, #Hpx, Cai, Caj, #Clj, #Me, #Wl,
    HG0, HG1, Kck, Gf⟩
  imodintro
  isplitl [HT0 HG0 HFz Hlc Cai]
  · iapply px_loop1_spec 0 z rm ci cj [] $$ [HT0 HG0 HFz Hlc Cai]
    · iframe HT0 HG0 HFz Hlc Hpx
      iexists n
      iframe Cai Clj
      iexists ck
      iframe Wl Me
    · iintro ⟨-, H⟩
      unfold liftTerm
      iexact H
  · iapply px_loop2_spec 1 n rm ci cj ck [] $$ [HT1 HG1 Kck HFck Gf Caj]
    · iframe HT1 HG1 Kck HFck Gf Hpx Caj Me
    · iintro ⟨-, H⟩
      unfold liftTerm
      iexact H

end Specs

/-! ## Adequacy: "eventually `False`" -/

section Guarantee
variable {GF : BundledGFunctors}

/-- Eventually `False` (and eventually `True`) (Rocq `R_main`). -/
def rMain : TrProp Exp State := ◇ₜ ⌜False⌝ₜ ∧ₜ ◇ₜ ⌜True⌝ₜ

/-- What the resources guarantee (Rocq `G_main`, inferred): thread `0`'s `True 𝒰 False`, and
thread `1`'s first until, read with `True` on the right. -/
def gMain : TrSpec Exp State GF :=
  (⌜True⌝ₛ 𝒰ₛ ⌜False⌝ₛ) ∧ₛ (⌜True⌝ₛ 𝒰ₛ TrSpec.true) ∧ₛ TrSpec.true

@[lantana_alias paradox.G_main_impl]
theorem gMain_impl : (gMain (GF := GF)).external ⊆ rMain :=
  fun _ ⟨h₁, h₂, _⟩ => ⟨h₁, h₂⟩

variable [ModelGS GF] [HeapGS GF] [ParadoxG GF]

@[lantana_alias paradox.guar_Φ_P]
theorem guar_mainRes : ⊢@{IProp GF} mainRes ⊨ₜ gMain := by
  unfold mainRes gMain
  exact IntoGuar.into_guar

end Guarantee

section Adequacy

/-- The initial pool: the two loops, threads `0` and `1`. -/
abbrev tp0 : ThreadPool Exp := [hl(v(&loop) #()), hl(v(&loop) #())]

/-- The initial state: the empty heap. -/
abbrev σ0 : State := ⟨∅⟩

/-- **The paradox**: with the no-credit rule, in every fair behavior from the initial
configuration, eventually `False`. -/
@[lantana_alias loop_paradox]
theorem loop_paradox (hnolc : ∀ [ModelGS ExGF] [HeapGS ExGF], LwpNoLc ExGF)
    (τ : Trace Exp State) (hbeh : IsBehavior τ) (hfair : fairScheduling τ) (hpos : τ.pos = 0)
    (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) : rMain τ := by
  refine lwp_adequacy_temporal (GF := ExGF) σ0 tp0 0 gMain rMain gMain_impl τ hbeh hfair hpos
    hinit ?_
  intro _ _
  refine ⟨Ordinals.Ordinal.ofNat 10, ?_⟩
  imod heapState_init σ0 tp0 with ⟨%hs, Hσ, -, HT⟩
  letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
  haveI : LwpNoLc ExGF := hnolc
  imodintro
  iexists instStateInterp, (fun _ _ => iprop(True)), post
  isplitl [Hσ]
  · iexact Hσ
  iintro Hc HG
  rw [show List.range (List.length tp0) = [0, 1] from rfl]
  icases BigSepL.bigSepL_cons.mp $$ HG with ⟨HG0, HG⟩
  ihave HG1 := BigSepL.bigSepL_singleton.mp $$ HG
  icases BigSepL.bigSepL_cons.mp $$ HT with ⟨HT0, HT⟩
  ihave HT1 := BigSepL.bigSepL_singleton.mp $$ HT
  imod px_loop_pre $$ HT0 HT1 Hc HG0 HG1 with ⟨HP, Hwp⟩
  imodintro
  iexists mainRes
  isplitr
  · iapply guar_mainRes
  iframe HP
  iintro HP
  imod Hwp $$ HP with ⟨W0, W1⟩
  imodintro
  iapply BigSepL.bigSepL_cons.mpr
  iframe W0
  iapply BigSepL.bigSepL_singleton.mpr
  iexact W1

/-! ## The fair run of the two loops -/

/-- `loop ()` steps to itself. -/
@[lantana_alias paradox.loop_prim_step]
theorem loop_primStep (σ : State) :
    primStep (hl(v(&loop) #()) : Exp) σ hl(v(&loop) #()) σ [] :=
  EctxLanguage.primStep_of_baseStep (.betaS _ _ _ _ _ σ rfl)

/-- Thread `0` is scheduled at even positions, thread `1` at odd ones. -/
def sched (m : Nat) : Nat := if m % 2 = 0 then 0 else 1

/-- The run of the two loops: every step takes `loop ()` to `loop ()`. -/
@[lantana_alias paradox.loop_run]
def loopRun : Trace Exp State := ⟨0, fun m => ⟨(tp0, σ0), sched m⟩⟩

/-- Each thread is scheduled at the current position or at the next one. -/
theorem sched_eventually (m j : Nat) (hj : j < 2) : ∃ m', m ≤ m' ∧ sched m' = j := by
  by_cases h : sched m = j
  · exact ⟨m, Nat.le_refl m, h⟩
  · refine ⟨m + 1, Nat.le_succ m, ?_⟩
    unfold sched at h ⊢
    split at h <;> split <;> omega

/-- Both threads run the loop. -/
theorem tp0_getElem? {j : Nat} (hj : j < 2) : tp0[j]? = some hl(v(&loop) #()) := by
  rcases j with _ | _ | j
  · rfl
  · rfl
  · omega

@[lantana_alias paradox.loop_run_behavior]
theorem loopRun_behavior : IsBehavior loopRun := by
  intro m _
  left
  have hlt : sched m < 2 := by
    unfold sched
    split <;> decide
  have h := ThreadStep.step (i := sched m) (tp := tp0) (σ := σ0) (tp0_getElem? hlt)
    (loop_primStep σ0)
  have hset : tp0.set (sched m) hl(v(&loop) #()) = tp0 := by
    unfold sched
    split <;> rfl
  rw [List.append_nil, hset] at h
  exact h

@[lantana_alias paradox.loop_run_fair]
theorem loopRun_fair : fairScheduling loopRun := by
  intro m _ j
  by_cases hj : j < 2
  · right
    obtain ⟨m', hm', ht⟩ := sched_eventually m j hj
    exact ⟨⟨hl(v(&loop) #()), tp0_getElem? hj, rfl⟩, m', hm', ht, fun _ _ _ => trivial⟩
  · left
    left
    exact List.getElem?_eq_none (Nat.not_lt.mp hj)

/-- **The no-credit rule is unsound**: assuming it, `loop_paradox` gives "eventually `False`" on
the fair run of the loops. -/
@[lantana_alias no_lc_absurd]
theorem no_lc_absurd (hnolc : ∀ [ModelGS ExGF] [HeapGS ExGF], LwpNoLc ExGF) : False := by
  obtain ⟨⟨_, _, hF, _⟩, _⟩ := loop_paradox hnolc loopRun loopRun_behavior loopRun_fair rfl rfl
  exact hF

end Adequacy

end Lantana.Examples.Paradox
