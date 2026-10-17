/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Examples.Flag
public import Lantana.Examples.World

/-! # A flag set by a forked thread

Rocq `examples/flag_fork.v`, the program `main` of the paper (§2): the main thread creates a
flag, forks a thread that sets it, waits for it and returns `42`.

The main thread holds two obligations at layer `1`: `kr`, with the commitment
`finallyI Nr kr 1 (exits 42 @ i)` to return `42`, and `kc`, with the commitment to create a flag.
It creates the flag's obligation `k` at layer `0` below itself (`Flag.init_thread_spec`),
discharges `kc` at once with the flag, and moves `k` to the forked thread, which sets the flag
(`Flag.set_thread_spec`) and terminates. The main thread then waits with the fuel of `kr` at
layer `1` (the layer above the flag's, which is why `kr` is at layer `1`), and discharges `kr` with
its final value (`threadExpr_terminate_finally`). The measure is `10 + μ_init + μ_wait` for `kr`
and `kc`, and the flag's obligation gets `3 + (1 + μ_set)`: three steps of the main thread until
the fork, one unit for its move, and the forked thread.

`main_adequacy` is the end-to-end statement (Rocq `main_adequacy`), from the adequacy theorem
`lwp_adequacy_temporal` in the closed world `ExGF`: HeapLang's ghost state is allocated with
`heapState_init`, the state interpretation is HeapLang's and forked threads have the
postcondition `True`. The guarantee `gMain` of the commitments `mainRes` is inferred
(`IntoGuar`, from the flag's instance `Flag.guarOf_isFlag`): the flag's location is
trace-visible (the target is a `TrSpec.ex` over `Loc`), its obligation, its layer and the names
of the commitments are ghost.
`main_safety_adequacy` is the safety statement from `lwp_adequacy_safety`.

Everything here is proved; the end-to-end corollaries depend only on the standard axioms
(checked in `LantanaTest.Examples`).
-/

@[expose] public noncomputable section

namespace Lantana.Examples.FlagFork

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.Flag (flagTk isFlag isFlagTr flagTrSpec v1)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The program -/

/-- `λ _, let x := init (); fork (set x); wait x; 42`. -/
@[lantana_alias FlagFork.main]
def main : Val :=
  hl_val(λ _,
    let x := v(&Flag.init) #();
    fork(v(&Flag.set) x);
    v(&Flag.wait) x;
    #42)

/-- The value `42`. -/
def v42 : Val := hl_val(#42)

/-- The namespaces of the two commitments of the main thread: to return, to create a flag. -/
def Nr : Namespace := nroot.@"flag_fork_ret"
def Nc : Namespace := nroot.@"flag_fork_flag"

/-! ## The specification -/

section Spec
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]

/-- The main proof. Besides returning, the main thread commits to creating a flag. -/
@[lantana_alias FlagFork_main_spec]
theorem main_spec : ∃ μ : Measure, ∀ (i : ThreadId) (kr kc : Oid),
    ⊢@{IProp GF} l{{{ threadExpr i [] hl(v(&main) #()) ∗ thKids i {kr, kc} ∗
          ([∗set] g ∈ ({kr, kc} : Oids), Obl.fuel g 1 μ) ∗ ⌜kr ≠ kc⌝ ∗ oblKids kr ∅ ∗
          oblKids kc ∅ ∗ finallyI Nr kr 1 (exits v42 @ i) ∗
          finallyI Nc kc 1 iprop(∃ (x : Loc) (k : Oid) (ℓ : Layer), isFlag x k ℓ) }}}
        hl(v(&main) #()) @ i
      l{{{ (v : Val), RET v; threadExpr i [] hl(&v) ∗ ⌜v = v42⌝ ∗
        liftTerm i (fun _ _ => iprop(True)) v }}} := by
  obtain ⟨μfi, hfi⟩ := Flag.init_thread_spec (GF := GF)
  obtain ⟨μfs, hfs⟩ := Flag.set_thread_spec (GF := GF)
  obtain ⟨μfw, hfw⟩ := Flag.wait_spec (GF := GF)
  refine ⟨10 + μfi + μfw, fun i kr kc => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hne, Hkr, Hkc, HFr, HFc⟩ HΦ
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Hfw⟩
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Hfi⟩
  ihave HF := oblFuels_init _ _ _ $$ HF
  unfold main
  lwp_step HT HG HF with Hlc : 1 +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hc1, Hc2⟩
  lwp_expr_simp
  lwp_bind hl(v(&Flag.init) #()) HT
  imod Obl.fuel_layer_mono_set _ (ℓ₁ := 0) μfi (Ordinals.Ordinal.zero_le _) $$ Hfi with Hfi
  -- The flag's obligation `k` pays the steps until the fork, its move to the forked thread,
  -- and the forked thread.
  iapply hfi 0 i {kr, kc} 0 (((3 : Nat) : Measure) + (1 + μfs)) _ $$ [HT HG Hfi]
  · iframe
  iintro %x %k ⟨HT, -, %hk, HG, Hkk, Hf, Htk, #Hflag⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  -- Keep the commitment: the flag exists.
  ihave Hc1 := tlc_one_nat.mpr $$ Hc1
  imod finallyI_discharge (E := ⊤) (.thread i) (({kr, kc} : Oids).insert k)
    (fun _ _ => CoPset.mem_full) (by simp) $$ Hc1 HG Hkc HFc [] with ⟨-, HG, -⟩
  · iexists x, k, 0
    iexact Hflag
  ihave HG := Par.kids_congr (B := ({kr} : Oids).insert k) ?_ $$ HG
  · intro z
    simp at hk ⊢
    grind
  ihave HF := oblFuels_subset _ (B := {kr}) (fun z hz => by simp at hz ⊢; simp [hz]) $$ HF
  icases (Obl.fuel_add k _ _ _).mp $$ Hf with ⟨Hf, Hfr⟩
  icases (Obl.fuel_add k _ _ _).mp $$ Hfr with ⟨Hmv, Hfj⟩
  icases oblFuels_add 3 6 _ $$ HF with ⟨Hf₃, HF⟩
  ihave Hf₃ := oblFuels_add_obl _ k 0 _ $$ Hf Hf₃
  lwp_step HT HG Hf₃
  lwp_step HT HG Hf₃
  lwp_expr_simp
  lwp_bind hl(fork(v(&Flag.set) #x)) HT
  have hsub : ({k} : Oids) ⊆ ({kr} : Oids).insert k := fun z hz => by
    rw [Iris.Std.LawfulSet.mem_singleton] at hz
    subst hz
    exact Std.ExtTreeSet.mem_insert_self
  iapply lwp_fork (o := 0) (G := ({kr} : Oids).insert k) (R := ∅) {k}
    iprop(oblKids k ∅ ∗ Obl.fuel k 0 μfs ∗ flagTk x k)
    hl(v(&Flag.set) #x) hsub $$ [] [HT HG Hf₃ Hmv Hkk Hfj Htk]
  · -- The forked thread sets the flag and terminates.
    iintro %j %Φ' !> ⟨HTj, HGj, Hkk, Hfj, Htk⟩ HΦ'
    iapply lwp_mupd
    iapply hfs 0 j x {k} k 0 [] $$ [HTj HGj Hkk Htk Hfj]
    · iframe HTj HGj Hkk Htk
      isplitl [Hfj]
      · iapply BigSepS.bigSepS_singleton.mpr
        iexact Hfj
      isplitl
      · ipureintro
        exact Iris.Std.LawfulSet.mem_singleton.mpr rfl
      · iexact Hflag
    iintro ⟨-, -, HGj, -⟩
    imod Th.terminate ⊤ j $$ [HGj] with #Hdone
    · iapply Par.kids_congr _ $$ HGj
      intro z
      simp only [Std.ExtTreeSet.mem_erase, Iris.Std.LawfulSet.mem_singleton,
        Std.ExtTreeSet.not_mem_empty]
      grind
    imodintro
    iapply HΦ'
    unfold liftTerm
    isplitl
    · iexact Hdone
    · ipureintro
      trivial
  · iframe HT Hkk Hfj Htk
    isplitl [HG Hf₃]
    · iapply stepPre_nil $$ HG Hf₃
    · unfold oblFuels
      iapply BigSepS.bigSepS_singleton.mpr
      iexists _
      iexact Hmv
  iintro ⟨HT, -, HG, -⟩
  ihave HG := Par.kids_congr (B := {kr}) ?_ $$ HG
  · intro z
    simp at hk ⊢
    grind
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(v(&Flag.wait) #x) HT
  ihave Hfw := BigSepS.bigSepS_subseteq (Y := ({kr} : Oids))
    (fun z hz => by simp at hz ⊢; simp [hz]) $$ Hfw
  imod Obl.fuel_layer_mono_set {kr} (ℓ₁ := Ordinals.Ordinal.succ 0) μfw
    (Ordinals.Ordinal.le_of_eq Ordinals.Ordinal.one_eq_succ_zero.symm) $$ Hfw with Hfw
  iapply hfw 0 i x {kr} k 0 _ $$ [HT HG Hfw]
  · iframe
    iexact Hflag
  iintro ⟨HT, -, HG, -⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  unfold v1
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- The return value discharges the commitment to return, and the thread terminates.
  rw [show (hl(#42) : Exp) = .val v42 from rfl]
  iapply lwp_value_mupd'.mpr
  ihave Hc2 := tlc_one_nat.mpr $$ Hc2
  imod threadExpr_terminate_finally i ⊤ v42 kr Nr (fun _ _ => CoPset.mem_full)
    $$ HT Hc2 HG Hkr HFr with ⟨HT, #Hd⟩
  imodintro
  iapply HΦ
  iframe HT
  isplitr
  · ipureintro
    rfl
  unfold liftTerm
  isplitl
  · iexact Hd
  · ipureintro
    trivial

/-- The commitments of the main thread `i` and its resources (Rocq `Φ_P`). -/
def mainRes (i : ThreadId) (μ : Measure) : IProp GF :=
  iprop(∃ kr kc : Oid, finallyI Nr kr 1 (exits v42 @ i) ∗
    finallyI Nc kc 1 iprop(∃ (x : Loc) (k : Oid) (ℓ : Layer), isFlag x k ℓ) ∗
    (thKids i {kr, kc} ∗ oblKids kr ∅ ∗ oblKids kc ∅ ∗ ⌜kr ≠ kc⌝ ∗
      [∗set] g ∈ ({kr, kc} : Oids), Obl.fuel g 1 μ))

/-- The postcondition of the main thread. -/
abbrev mainPost : ThreadId → Val → IProp GF := fun _ v => iprop(⌜v = v42⌝)

/-- From the main thread's token and its empty set of children: its commitments, and its
`lWP` from them. -/
@[lantana_alias flag_fork.main_pre]
theorem main_pre (i : ThreadId) :
    threadExpr (GF := GF) i [] hl(v(&main) #()) ⊢ thKids i ∅ -∗
      |={⊤}=>m ∃ μ : Measure, mainRes i μ ∗
        (mainRes i μ -∗ |={⊤}=>m lWP hl(v(&main) #()) @ i; ⊤ {{ liftTerm i mainPost }}) := by
  obtain ⟨μ, hmain⟩ := main_spec (GF := GF)
  iintro HT HG
  imod untilI_alloc (E := ⊤) (.thread i) ∅ 1 μ $$ [] HG with
    ⟨%kr, -, HG, Hkr, Fkr, -, Akr⟩
  · iapply parLe_thread
  imod Akr $$ %⊤ %Nr %iprop(True) %(exits v42 @ i) [] with Ur
  · inext
    ipureintro
    trivial
  imod untilI_alloc (E := ⊤) (.thread i) _ 1 μ $$ [] HG with
    ⟨%kc, %hkc, HG, Hkc, Fkc, -, Akc⟩
  · iapply parLe_thread
  imod Akc $$ %⊤ %Nc %iprop(True) %iprop(∃ (x : Loc) (k : Oid) (ℓ : Layer), isFlag x k ℓ) []
    with Uc
  · inext
    ipureintro
    trivial
  have hne : kr ≠ kc := by
    rintro rfl
    exact hkc Std.ExtTreeSet.mem_insert_self
  imodintro
  iexists μ
  isplitl [Ur Uc HG Hkr Hkc Fkr Fkc]
  · unfold mainRes finallyI
    iexists kr, kc
    iframe Ur Uc Hkr Hkc
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
  icases HP with ⟨%kr, %kc, HFr, HFc, HG, Hkr, Hkc, %hne, HF⟩
  imodintro
  iapply hmain i kr kc $$ [HT HG HF Hkr Hkc HFr HFc]
  · iframe
    ipureintro
    exact hne
  iintro %v ⟨-, %hv, Hd⟩
  unfold liftTerm
  icases Hd with ⟨Hd, -⟩
  iframe Hd
  ipureintro
  exact hv

end Spec

/-! ## Traces and the guarantee -/

section Guarantee
variable {GF : BundledGFunctors}

/-- The main thread `i` returns `42`, and a flag gets created that is `0` until it is `1`, and
then `1` (Rocq `R_main`). -/
def rMain (i : ThreadId) : TrProp Exp State :=
  ◇ₜ TrProp.state (threadExprSat i [] (.val v42)) ∧ₜ ◇ₜ (∃ₜ x : Loc, isFlagTr x)

/-- What the commitments guarantee: eventually the main thread has exited with `42`, and
eventually a flag exists; the ghost names and the resources do not show (Rocq `G_main`). -/
def gMain (i : ThreadId) : TrSpec Exp State GF :=
  ◇ₛ TrSpec.state (threadExprSat i [] (.val v42)) ∧ₛ ◇ₛ (∃ₛ x : Loc, flagTrSpec x) ∧ₛ
    TrSpec.true

@[lantana_alias flag_fork.G_main_impl]
theorem gMain_impl (i : ThreadId) : (gMain (GF := GF) i).external ⊆ rMain i := by
  intro τ ⟨hr, ⟨m, hm, ⟨x, hx⟩, hb⟩, _⟩
  exact ⟨hr, m, hm, ⟨x, Flag.flagTrSpec_impl x _ hx⟩, hb⟩

variable [ModelGS GF] [HeapGS GF]

@[lantana_alias flag_fork.guar_Φ_P]
theorem guar_mainRes (i : ThreadId) (μ : Measure) :
    ⊢@{IProp GF} mainRes i μ ⊨ₜ gMain i := by
  unfold mainRes gMain
  exact IntoGuar.into_guar

end Guarantee

/-! ## Adequacy -/

section Adequacy

/-- The initial pool: the main thread `0`. -/
abbrev tp0 : ThreadPool Exp := [hl(v(&main) #())]

/-- The initial state: the empty heap. -/
abbrev σ0 : State := ⟨∅⟩

/-- In every fair behavior from the initial configuration, the main thread returns `42`, and a
flag gets created that is `0` until it is `1`, and then `1`. -/
@[lantana_alias flag_fork.main_adequacy]
theorem main_adequacy (τ : Trace Exp State) (hbeh : IsBehavior τ) (hfair : fairScheduling τ)
    (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) : rMain 0 τ := by
  refine lwp_adequacy_temporal (GF := ExGF) σ0 tp0 0 (gMain 0) (rMain 0) (gMain_impl 0) τ hbeh
    hfair hpos hinit ?_
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
stuck, and once the main thread has returned, its value is `42`. -/
@[lantana_alias flag_fork.main_safety_adequacy]
theorem main_safety_adequacy (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    safetyIris 0 (fun _ v => v = v42) τ := by
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
@[lantana_alias flag_fork.main_liveness_safety]
theorem main_liveness_safety (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    rMain 0 τ ∧ safetyIris 0 (fun _ v => v = v42) τ :=
  ⟨main_adequacy τ hbeh hfair hpos hinit, main_safety_adequacy τ hbeh hfair hpos hinit⟩

end Adequacy

end Lantana.Examples.FlagFork
