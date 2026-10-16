/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Examples.Flag
public import Lantana.Examples.Handoff
public import Lantana.Examples.World

/-! # A client of the handoff

Rocq `examples/handoff_client.v`, the program `handoffMain` of the paper (§5.2): the main
thread allocates a cell `b`, forks a receiver on it, creates a flag `x`, sends the task
`set x` to the receiver and waits on the flag.

The layers: `set` runs at `0`, the task is below the handoff's layer `1`, the flag's obligation
`k` is at `1` (in a container `g0` at `1`, from which `send` moves it into the receiver's
inbox), and the main thread's commitments `kl` (to return `1`) and `kc` (to create a flag and a
handoff) are at `2`, above the flag's layer for the `wait`.

Unlike Rocq, which forks with `lwp_fork_step` to create the receiver's inbox in the receiver,
the inbox `gj` is created below the main thread just before the fork (with the fuel for the fork
step, its move and the receiver), the handoff is initialized with it, and `lwp_fork` moves it to
the receiver. The measure is `20 + μ_init + μ_send + μ_wait` for `kl` and `kc`; the container
gets `2 + (μ_init + μ_send)` and the inbox `1 + (1 + μ_receive)`.

`handoffClient_adequacy` is the end-to-end statement, from `lwp_adequacy_temporal` in the
closed world `ExGF` (with `HandoffG ExGF` from its ghost-variable slot);
`handoffClient_safety_adequacy` the safety statement, from `lwp_adequacy_safety`.

Everything here is proved; the end-to-end corollaries depend only on the standard axioms
(checked in `LantanaTest.Examples`).
-/

@[expose] public noncomputable section

namespace Lantana.Examples.HandoffClient

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.Flag (flagTk isFlag isFlagTr flagTrSpec v1)
open Lantana.Examples.Handoff (HandoffG HandoffName isHandoff isTask taskAt handoffInvTrSpec
  handoffTr vNone)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The program -/

/-- `λ _, let b := ref none; fork (receive b); let x := init (); send b set x;
let v := wait x; v`. -/
@[lantana_alias handoff_client.main]
def main : Val :=
  hl_val(λ _,
    let b := ref(none());
    fork(v(&Handoff.receive) b);
    let x := v(&Flag.init) #();
    v(&Handoff.send) b v(&Flag.set) x;
    let r := v(&Flag.wait) x;
    r)

/-- The namespaces of the main thread's commitments: to return, to create a flag and a
handoff. -/
def Nl : Namespace := nroot.@"return"
def Nc : Namespace := nroot.@"handoff_client_flag"

/-! ## The specification -/

section Spec
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [HandoffG GF]

/-- The main proof. Besides returning, the main thread commits to creating a flag and a
handoff cell. The layers: `set` at `0`, the task below `1`, the flag's obligation at `1` (in a
container at `1`), the return obligation and the commitment at `2`. -/
@[lantana_alias handoff_client.main_spec]
theorem main_spec : ∃ μ : Measure, ∀ (i : ThreadId) (kl kc : Oid),
    ⊢@{IProp GF} l{{{ threadExpr i [] hl(v(&main) #()) ∗ thKids i {kl, kc} ∗
          ([∗set] g ∈ ({kl, kc} : Oids), Obl.fuel g 2 μ) ∗ ⌜kl ≠ kc⌝ ∗ oblKids kl ∅ ∗
          oblKids kc ∅ ∗ finallyI Nl kl 1 (exits v1 @ i) ∗
          finallyI Nc kc 1 iprop((∃ (x : Loc) (k : Oid) (ℓ : Layer), isFlag x k ℓ) ∗
            (∃ (b : Loc) (γ : HandoffName) (ℓ : Layer), isHandoff b γ ℓ)) }}}
        hl(v(&main) #()) @ i
      l{{{ (v : Val), RET v; threadExpr i [] hl(&v) ∗
        liftTerm i (fun _ v => iprop(⌜v = v1⌝)) v }}} := by
  obtain ⟨μfi, hfi⟩ := Flag.init_spec (GF := GF)
  obtain ⟨μfs, hfs⟩ := Flag.set_spec (GF := GF)
  obtain ⟨μfw, hfw⟩ := Flag.wait_spec (GF := GF)
  obtain ⟨μhs, hhs⟩ := Handoff.send_spec (GF := GF)
  obtain ⟨μhr, hhr⟩ := Handoff.receive_spec (GF := GF)
  refine ⟨20 + μfi + μhs + μfw, fun i kl kc => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hne, Hkl, Hkc, HFl, HFc⟩ HΦ
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Hfw⟩
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Hhs⟩
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Hfi⟩
  ihave HF := oblFuels_init _ _ _ $$ HF
  unfold main
  lwp_step HT HG HF with Hlc : 1 +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hc1, Hc2⟩
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_bind hl(allocn(#1, v(none()))) HT
  icases oblFuels_add 1 17 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_alloc (o := 0) (C := _) (G := {kl, kc}) (R := ∅) $$ [HT HG HF1]
  · iframe HT
    iapply stepPre_nil $$ HG HF1
  iintro %b ⟨HT, ⟨-, HG, -⟩, Hb⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- The receiver's inbox, at layer `0`: an obligation of this thread until the fork moves it to
  -- the receiver. It pays the fork step, its move, and the receiver's steps.
  imod Obl.new ⊤ (.thread i) {kl, kc} 0 (((1 : Nat) : Measure) + (1 + μhr)) $$ [] HG with
    ⟨%gj, %hgj, HG, Kgj, Agj, Fgj, #Wgj⟩
  · iapply parLe_thread
  rw [show (hl_val(none()) : Val) = vNone from rfl]
  icases (pointsTo_halves b _).mp $$ Hb with ⟨Hb, Hb0⟩
  imod Handoff.isHandoff_initialize ⊤ b 1 gj $$ Hb0 Kgj Wgj with ⟨%γ, #Hh, Gv⟩
  icases (Obl.fuel_add gj _ _ _).mp $$ Fgj with ⟨F1, Fgj⟩
  icases (Obl.fuel_add gj _ _ _).mp $$ Fgj with ⟨Fmv, Fhr⟩
  icases oblFuels_add 1 14 _ $$ HF with ⟨HF1, HF⟩
  ihave HF1 := oblFuels_add_obl _ gj 0 _ $$ F1 HF1
  lwp_bind hl(fork(v(&Handoff.receive) #b)) HT
  have hsub : ({gj} : Oids) ⊆ ({kl, kc} : Oids).insert gj := fun z hz => by
    rw [Iris.Std.LawfulSet.mem_singleton] at hz
    subst hz
    exact Std.ExtTreeSet.mem_insert_self
  iapply lwp_fork (o := 0) (G := ({kl, kc} : Oids).insert gj) (R := ∅) {gj}
    iprop(Obl.assigned gj 1 ∗ Obl.fuel gj 0 μhr ∗ (γ.γd ↪VAR{.own (1 : Qp).half} gj))
    hl(v(&Handoff.receive) #b) hsub $$ [] [HT HG HF1 Fmv Agj Fhr Gv]
  · -- The forked thread receives, and terminates when it has run a task.
    iintro %j %Φ' !> ⟨HTj, HGj, Agj, Fhr, Gv⟩ HΦ'
    iapply lwp_mupd
    iapply hhr 0 j b gj γ 1 [] $$ [HTj HGj Fhr Agj Gv]
    · iframe HTj HGj Agj Gv
      isplitl [Fhr]
      · iapply BigSepS.bigSepS_singleton.mpr
        iexact Fhr
      · iexact Hh
    iintro %v ⟨-, -, HGj⟩
    imod Th.terminate ⊤ j $$ HGj with #Hd
    imodintro
    iapply HΦ'
    unfold liftTerm
    isplitl
    · iexact Hd
    · ipureintro
      trivial
  · iframe HT Agj Fhr Gv
    isplitl [HG HF1]
    · iapply stepPre_nil $$ HG HF1
    · unfold oblFuels
      iapply BigSepS.bigSepS_singleton.mpr
      iexists _
      iexact Fmv
  iintro ⟨HT, -, HG, -⟩
  ihave HG := Par.kids_congr (B := {kl, kc}) ?_ $$ HG
  · intro z
    simp at hgj ⊢
    grind
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(v(&Flag.init) #()) HT
  -- A container for the flag's obligation, at the flag's layer `1`: the obligation is handed
  -- off from it.
  imod Obl.new ⊤ (.thread i) {kl, kc} 1 (((2 : Nat) : Measure) + (μfi + μhs)) $$ [] HG with
    ⟨%g0, %hg0, HG, Kg0, Ag0, Fg0, #Wg0⟩
  · iapply parLe_thread
  icases (Obl.fuel_add g0 _ _ _).mp $$ Fg0 with ⟨F0, Fg0⟩
  icases (Obl.fuel_add g0 _ _ _).mp $$ Fg0 with ⟨F0fi, F0hs⟩
  imod Obl.fuel_layer_mono_set _ (ℓ₁ := 0) μfi (Ordinals.Ordinal.zero_le _) $$ Hfi with Hfi
  imod Obl.fuel_layer_mono g0 (ℓ₁ := 0) μfi (Ordinals.Ordinal.zero_le _) $$ F0fi with F0fi
  iapply hfi 0 i (({kl, kc} : Oids).insert g0) (.obl g0) ∅ 1 1 _ $$ [HT HG Hfi F0fi Kg0]
  · iframe HT HG Kg0
    isplitl [Hfi F0fi]
    · iapply (bigSepS_insert_oids hg0).mpr
      iframe
    · iapply parLe_obl (ℓq := 1) g0 (Ordinals.Ordinal.le_refl _) $$ Wg0
  iintro %x %k ⟨HT, -, HG, -, Kg0, Hkk, Fk, Htk, #Hflag⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  -- Keep the commitment: the flag and the handoff exist.
  ihave Hc1 := tlc_one_nat.mpr $$ Hc1
  imod finallyI_discharge (E := ⊤) (.thread i) (({kl, kc} : Oids).insert g0)
    (fun _ _ => CoPset.mem_full) (by simp) $$ Hc1 HG Hkc HFc [] with ⟨-, HG, -⟩
  · isplitl
    · iexists x, k, 1
      iexact Hflag
    · iexists b, γ, 1
      iexact Hh
  ihave HG := Par.kids_congr (B := ({kl} : Oids).insert g0) ?_ $$ HG
  · intro z
    simp at hg0 ⊢
    grind
  ihave HF := oblFuels_subset _ (B := {kl}) (fun z hz => by simp_all) $$ HF
  icases oblFuels_add 2 10 _ $$ HF with ⟨HF2, HF⟩
  ihave HF2 := oblFuels_add_obl _ g0 1 _ $$ F0 HF2
  lwp_step HT HG HF2
  lwp_step HT HG HF2
  lwp_expr_simp
  -- Send the task `set x`, with the flag's obligation `k`, from the container `g0`.
  lwp_bind hl(v(&Handoff.send) #b v(&Flag.set) #x) HT
  ihave Hhs := BigSepS.bigSepS_subseteq (Y := ({kl} : Oids)) (fun z hz => by simp_all) $$ Hhs
  imod Obl.fuel_layer_mono_set {kl} (ℓ₁ := 0) μhs (Ordinals.Ordinal.zero_le _) $$ Hhs with Hhs
  imod Obl.fuel_layer_mono g0 (ℓ₁ := 0) μhs (Ordinals.Ordinal.zero_le _) $$ F0hs with F0hs
  have hg0' : g0 ∉ ({kl} : Oids) := fun h => hg0 (by simp_all)
  iapply hhs 0 i b Flag.set hl_val(#x) (({kl} : Oids).insert g0) (.obl g0) {k} {k} γ 1 _
    $$ [HT HG Hhs F0hs Kg0 Fk Hb Htk Hkk]
  · iframe HT HG Hb
    isplitl [Hhs F0hs]
    · iapply (bigSepS_insert_oids hg0').mpr
      iframe
    isplitl [Kg0]
    · iapply Par.kids_congr _ $$ Kg0
      intro z
      simp
    isplitr
    · ipureintro
      exact fun _ h => h
    isplitl [Fk]
    · iapply BigSepS.bigSepS_singleton.mpr
      iexact Fk
    isplitl
    · -- The task: `set x` at layer `0`, with the flag's token and the obligation's children.
      unfold isTask
      iexists 0, iprop(flagTk x k ∗ oblKids k ∅)
      isplit
      · ipureintro
        exact Ordinals.Ordinal.zero_lt_one
      iframe Htk Hkk
      iexists μfs
      unfold taskAt
      iintro %lc' %i' %G' %p' %K'' %C' %Φ'' !> ⟨HT', HG', HF', HK', %hK', Htk', Hkk'⟩ HΦ''
      iapply hfs lc' i' x G' p' K'' k 1 C' $$ [HT' HG' HF' HK' Hkk' Htk']
      · iframe
        isplitl
        · ipureintro
          exact hK' _ (Iris.Std.LawfulSet.mem_singleton.mpr rfl)
        · iexact Hflag
      iintro ⟨HT', Hlc', HG', HK', -⟩
      iapply HΦ''
      iframe
      iapply Par.kids_congr _ $$ HK'
      intro z
      simp only [Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.mem_diff_iff,
        Iris.Std.LawfulSet.mem_singleton]
      grind
    · iexact Hh
  iintro ⟨HT, -, HG, Kg0⟩
  -- The container is empty: discharge it.
  imod Obl.discharge_leaf ⊤ (.thread i) _ g0 Std.ExtTreeSet.mem_insert_self $$ HG [Kg0] Ag0
    with ⟨HG, -⟩
  · iapply Par.kids_congr _ $$ Kg0
    intro z
    simp
  ihave HG := Par.kids_congr (B := {kl}) ?_ $$ HG
  · intro z
    simp at hg0' ⊢
    grind
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  unfold Handoff.vUnit
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- Wait for the flag, at layer `2` above the flag's layer `1`.
  lwp_bind hl(v(&Flag.wait) #x) HT
  ihave Hfw := BigSepS.bigSepS_subseteq (Y := ({kl} : Oids)) (fun z hz => by simp_all) $$ Hfw
  imod Obl.fuel_layer_mono_set {kl} (ℓ₁ := Ordinals.Ordinal.succ 1) (ℓ₂ := 2) μfw
    (Ordinals.Ordinal.le_of_eq rfl) $$ Hfw with Hfw
  iapply hfw 0 i x {kl} k 1 _ $$ [HT HG Hfw]
  · iframe HT HG Hfw
    iexact Hflag
  iintro ⟨HT, -, HG, -⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  unfold v1
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  rw [show (hl(#1) : Exp) = .val hl_val(#1) from rfl]
  iapply lwp_value_mupd'.mpr
  ihave Hc2 := tlc_one_nat.mpr $$ Hc2
  imod threadExpr_terminate_finally i ⊤ hl_val(#1) kl Nl (fun _ _ => CoPset.mem_full)
    $$ HT Hc2 HG Hkl HFl with ⟨HT, #Hd⟩
  imodintro
  iapply HΦ
  iframe HT
  unfold liftTerm
  isplitl
  · iexact Hd
  · ipureintro
    rfl

/-- What the main thread `i` commits to: a flag and a handoff exist. -/
abbrev flagAndHandoff : IProp GF :=
  iprop((∃ (x : Loc) (k : Oid) (ℓ : Layer), isFlag x k ℓ) ∗
    (∃ (b : Loc) (γ : HandoffName) (ℓ : Layer), isHandoff b γ ℓ))

/-- The commitments of the main thread `i` and its resources (Rocq `Φ_P`). -/
def mainRes (i : ThreadId) (μ : Measure) : IProp GF :=
  iprop(∃ kl kc : Oid, finallyI Nl kl 1 (exits v1 @ i) ∗ finallyI Nc kc 1 flagAndHandoff ∗
    (thKids i {kl, kc} ∗ oblKids kl ∅ ∗ oblKids kc ∅ ∗ ⌜kl ≠ kc⌝ ∗
      [∗set] g ∈ ({kl, kc} : Oids), Obl.fuel g 2 μ))

/-- The postcondition of the main thread. -/
abbrev mainPost : ThreadId → Val → IProp GF := fun _ v => iprop(⌜v = v1⌝)

/-- From the main thread's token and its empty set of children: its commitments, and its
`lWP` from them. -/
@[lantana_alias handoff_client.main_pre]
theorem main_pre (i : ThreadId) :
    threadExpr (GF := GF) i [] hl(v(&main) #()) ⊢ thKids i ∅ -∗
      |={⊤}=>m ∃ μ : Measure, mainRes i μ ∗
        (mainRes i μ -∗ |={⊤}=>m lWP hl(v(&main) #()) @ i; ⊤ {{ liftTerm i mainPost }}) := by
  obtain ⟨μ, hmain⟩ := main_spec (GF := GF)
  iintro HT HG
  imod untilI_alloc (E := ⊤) (.thread i) ∅ 2 μ $$ [] HG with
    ⟨%kl, -, HG, Hkl, Fkl, -, Akl⟩
  · iapply parLe_thread
  imod Akl $$ %⊤ %Nl %iprop(True) %(exits v1 @ i) [] with Ul
  · inext
    ipureintro
    trivial
  imod untilI_alloc (E := ⊤) (.thread i) _ 2 μ $$ [] HG with
    ⟨%kc, %hkc, HG, Hkc, Fkc, -, Akc⟩
  · iapply parLe_thread
  imod Akc $$ %⊤ %Nc %iprop(True) %(flagAndHandoff (GF := GF)) [] with Uc
  · inext
    ipureintro
    trivial
  have hne : kl ≠ kc := by
    rintro rfl
    exact hkc Std.ExtTreeSet.mem_insert_self
  imodintro
  iexists μ
  isplitl [Ul Uc HG Hkl Hkc Fkl Fkc]
  · unfold mainRes finallyI
    iexists kl, kc
    iframe Ul Uc Hkl Hkc
    isplitl [HG]
    · iapply Par.kids_congr _ $$ HG
      intro z
      simp
      grind
    isplitr
    · ipureintro
      exact hne
    iapply (bigSepS_pair hne).mpr
    iframe
  iintro HP
  unfold mainRes
  icases HP with ⟨%kl, %kc, HFl, HFc, HG, Hkl, Hkc, %hne, HF⟩
  imodintro
  iapply hmain i kl kc $$ [HT HG HF Hkl Hkc HFl HFc]
  · iframe
    ipureintro
    exact hne
  iintro %v ⟨-, Hd⟩
  iexact Hd

end Spec

/-! ## Traces and the guarantee -/

section Guarantee
variable {GF : BundledGFunctors}

/-- The main thread `i` returns `1`, and a flag gets created that is `0` until it is `1`, and
then `1`; in particular, the receiver thread runs the task `set x` (Rocq `R_main`). -/
def rMain (i : ThreadId) : TrProp Exp State :=
  ◇ₜ TrProp.state (threadExprSat i [] (.val v1)) ∧ₜ ◇ₜ (∃ₜ x : Loc, isFlagTr x)

/-- Moreover, a handoff cell gets created that from then on always holds `NONE` or a task
(Rocq `R_handoff`). -/
def rHandoff : TrProp Exp State := ◇ₜ (∃ₜ b : Loc, handoffTr b)

/-- What the commitments guarantee (Rocq `G_main`). -/
def gMain (i : ThreadId) : TrSpec Exp State GF :=
  ◇ₛ TrSpec.state (threadExprSat i [] (.val v1)) ∧ₛ
    ◇ₛ ((∃ₛ x : Loc, flagTrSpec x) ∧ₛ (∃ₛ b : Loc, □ₛ handoffInvTrSpec b)) ∧ₛ TrSpec.true

@[lantana_alias handoff_client.G_main_impl]
theorem gMain_impl (i : ThreadId) :
    (gMain (GF := GF) i).external ⊆ (rMain i ∧ₜ rHandoff) := by
  intro τ ⟨hr, ⟨m, hm, ⟨⟨x, hx⟩, ⟨b, hb⟩⟩, hbef⟩, _⟩
  exact ⟨⟨hr, m, hm, ⟨x, Flag.flagTrSpec_impl x _ hx⟩, hbef⟩,
    m, hm, ⟨b, Handoff.handoffInvTrSpec_ext b _ hb⟩, hbef⟩

variable [ModelGS GF] [HeapGS GF] [HandoffG GF]

@[lantana_alias handoff_client.guar_Φ_P]
theorem guar_mainRes (i : ThreadId) (μ : Measure) :
    ⊢@{IProp GF} mainRes i μ ⊨ₜ gMain i := by
  haveI : GuarOf (Expr := Exp) (State := State)
      iprop(∃ (x : Loc) (k : Oid) (ℓ : Layer), isFlag (GF := GF) x k ℓ)
      (∃ₛ x : Loc, flagTrSpec x) := ⟨Flag.guar_exFlag⟩
  haveI : GuarOf (Expr := Exp) (State := State)
      iprop(∃ (b : Loc) (γ : HandoffName) (ℓ : Layer), isHandoff (GF := GF) b γ ℓ)
      (∃ₛ b : Loc, □ₛ handoffInvTrSpec b) := ⟨Handoff.guar_exHandoff⟩
  unfold mainRes gMain finallyI
  iapply guar_ex_ghost
  iintro %kl
  iapply guar_ex_ghost
  iintro %kc
  iapply guar_sep
  · iapply (GuarOf.guar_of (P := untilI (Expr := Exp) (State := State) Nl kl 1 iprop(True)
      (exits v1 @ i)))
  iapply guar_sep
  · iapply (GuarOf.guar_of (P := untilI (Expr := Exp) (State := State) Nc kc 1 iprop(True)
      (flagAndHandoff (GF := GF))))
  iapply guar_true

end Guarantee

/-! ## Adequacy -/

section Adequacy

instance : HandoffG ExGF := {}

/-- The initial pool: the main thread `0`. -/
abbrev tp0 : ThreadPool Exp := [hl(v(&main) #())]

/-- The initial state: the empty heap. -/
abbrev σ0 : State := ⟨∅⟩

/-- In every fair behavior from the initial configuration, the main thread returns `1`, a flag
gets created that is `0` until it is `1` and then `1`, and a handoff cell gets created that
from then on always holds `NONE` or a task. -/
@[lantana_alias handoff_client_adequacy]
theorem handoffClient_adequacy (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    rMain 0 τ ∧ rHandoff τ := by
  refine lwp_adequacy_temporal (GF := ExGF) σ0 tp0 0 (gMain 0) (rMain 0 ∧ₜ rHandoff)
    (gMain_impl 0) τ hbeh hfair hpos hinit ?_
  intro _ _
  refine ⟨2, ?_⟩
  imod heapState_init σ0 tp0 with ⟨%hs, Hσ, -, HT⟩
  letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
  imodintro
  iexists instStateInterp, (fun _ _ => iprop(True)), mainPost
  isplitl [Hσ]
  · iexact Hσ
  iintro Hc HG
  rw [show List.range (List.length tp0) = [0] from rfl]
  ihave HG := BigSepL.bigSepL_singleton.mp $$ HG
  ihave HT := BigSepL.bigSepL_singleton.mp $$ HT
  imod main_pre 0 $$ HT HG with ⟨%μ, HP, Hwp⟩
  imodintro
  iexists mainRes 0 μ
  isplitr
  · iapply guar_mainRes
  iframe HP
  iintro HP
  imod Hwp $$ HP with Hwp
  imodintro
  iapply BigSepL.bigSepL_singleton.mpr
  iexact Hwp

/-- Safety: in every fair behavior from the initial configuration, the scheduled thread is never
stuck, and once the main thread has returned, its value is `1`. -/
@[lantana_alias handoff_client_safety_adequacy]
theorem handoffClient_safety_adequacy (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    safetyIris 0 (fun _ v => v = v1) τ := by
  refine lwp_adequacy_safety (GF := ExGF) σ0 tp0 0 0 _ τ hbeh hfair hpos hinit (by decide) ?_
  intro _ _
  refine ⟨2, ?_⟩
  imod heapState_init σ0 tp0 with ⟨%hs, Hσ, -, HT⟩
  letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
  imodintro
  iexists instStateInterp, (fun _ _ => iprop(True)), mainPost
  isplit
  · ipureintro
    exact fun _ => .rfl
  isplitl [Hσ]
  · iexact Hσ
  iintro Hc HG
  rw [show List.range (List.length tp0) = [0] from rfl]
  ihave HG := BigSepL.bigSepL_singleton.mp $$ HG
  ihave HT := BigSepL.bigSepL_singleton.mp $$ HT
  imod main_pre 0 $$ HT HG with ⟨%μ, HP, Hwp⟩
  imod Hwp $$ HP with Hwp
  imodintro
  iapply BigSepL.bigSepL_singleton.mpr
  iexact Hwp

/-- Liveness and safety together, over the same fair behaviors. -/
@[lantana_alias handoff_client_liveness_safety]
theorem handoffClient_liveness_safety (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    (rMain 0 τ ∧ rHandoff τ) ∧ safetyIris 0 (fun _ v => v = v1) τ :=
  ⟨handoffClient_adequacy τ hbeh hfair hpos hinit,
    handoffClient_safety_adequacy τ hbeh hfair hpos hinit⟩

end Adequacy

end Lantana.Examples.HandoffClient
