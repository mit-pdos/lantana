/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Examples.Flag
public import Lantana.Examples.World

/-! # A client of the flag: one thread sets it, another waits for it

Rocq `examples/flag_client.v`: the flag is at a fixed location `xLoc`, which holds `0` in the
initial state; the writer (thread `0`) sets it and the reader (thread `1`) waits for it.

`flagClient_pre` creates the flag at thread `0` (`Flag.isFlag_init`, its obligation `k` at layer
`0`) and the threads' commitments to return: `kl₁` at layer `0` for the writer, `kl₂` at layer
`1` for the reader (whose `wait` needs fuel above the flag's layer). Each thread discharges its
commitment with its final value (`threadExpr_terminate_finally`). The measures are `4 + μ_set`
(writer) and `10 + μ_wait` (reader).

`flagClient_adequacy` is the end-to-end statement, from `lwp_adequacy_temporal` in the closed
world `ExGF` (the points-to of the flag comes from the initial heap through `heapState_init`);
`flagClient_safety_adequacy` the safety statement, from `lwp_adequacy_safety`, once per thread.
The guarantee `gClient` of the resources `clientRes` is inferred (`IntoGuar`), from the
flag's instances `Flag.guarOf_isFlag` and `Flag.guarOf_flagTk`; the names are ghost.

Everything here is proved; the end-to-end corollaries depend only on the standard axioms
(checked in `LantanaTest.Examples`).
-/

@[expose] public noncomputable section

namespace Lantana.Examples.FlagClient

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.Flag (flagTk isFlag isFlagTr flagTrSpec pointsToSpec pointsToTr v0 v1)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The program -/

/-- The flag's location, fixed. -/
@[lantana_alias X_loc]
def xLoc : Loc := ⟨0⟩

/-- The flag. -/
@[lantana_alias X]
def X : Val := hl_val(#xLoc)

/-- `λ _, let v := set X; v`. -/
@[lantana_alias writer]
def writer : Val := hl_val(λ _, let v := v(&Flag.set) v(&X); v)

/-- `λ _, let v := wait X; v`. -/
@[lantana_alias reader]
def reader : Val := hl_val(λ _, let v := v(&Flag.wait) v(&X); v)

/-- The unit value. -/
def vUnit : Val := hl_val(#())

/-- The namespace of the threads' commitments to return. -/
def Nl : Namespace := nroot.@"writer_return"

/-! ## The specifications -/

section Specs
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]

/-- The writer sets the flag, discharging its obligation `k`, and returns. -/
@[lantana_alias writer_spec]
theorem writer_spec : ∃ μ : Measure, ∀ (i : ThreadId) (k kl : Oid),
    ⊢@{IProp GF} l{{{ threadExpr i [] hl(v(&writer) #()) ∗ thKids i {k, kl} ∗
          ([∗set] g ∈ ({k, kl} : Oids), Obl.fuel g 0 μ) ∗ ⌜k ≠ kl⌝ ∗ oblKids k ∅ ∗
          oblKids kl ∅ ∗ flagTk xLoc k ∗ finallyI Nl kl 1 (exits vUnit @ i) ∗
          isFlag xLoc k 0 }}}
        hl(v(&writer) #()) @ i
      l{{{ RET vUnit; threadExpr i [] hl(#()) ∗ liftTerm i (fun _ _ => iprop(True)) vUnit }}} := by
  obtain ⟨μs, hfs⟩ := Flag.set_thread_spec (GF := GF)
  refine ⟨4 + μs, fun i k kl => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hne, Hk, Hkl, Htk, HFl, #Hflag⟩ HΦ
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Hfs⟩
  ihave HF := oblFuels_init _ _ _ $$ HF
  unfold writer X
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(v(&Flag.set) #xLoc) HT
  iapply hfs 1 i xLoc {k, kl} k 0 _ $$ [HT HG Hfs Hk Htk]
  · iframe
    isplitl
    · ipureintro
      simp
    · iexact Hflag
  iintro ⟨HT, Hc, HG, -⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  ihave HG := Par.kids_congr (B := {kl}) ?_ $$ HG
  · intro z
    simp
    grind
  ihave HF := oblFuels_subset _ (B := {kl}) (fun z hz => by simp at hz ⊢; simp [hz]) $$ HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  rw [show (hl(#()) : Exp) = .val vUnit from rfl]
  iapply lwp_value_mupd'.mpr
  ihave Hc := tlc_one_nat.mpr $$ Hc
  imod threadExpr_terminate_finally i ⊤ vUnit kl Nl (fun _ _ => CoPset.mem_full)
    $$ HT Hc HG Hkl HFl with ⟨HT, #Hd⟩
  imodintro
  iapply HΦ
  iframe HT
  unfold liftTerm
  isplitl
  · iexact Hd
  · ipureintro
    trivial

/-- The reader waits for the flag and returns `1`; its obligation is at layer `1`, above the
flag's. -/
@[lantana_alias reader_spec]
theorem reader_spec : ∃ μ : Measure, ∀ (i : ThreadId) (k kl : Oid),
    ⊢@{IProp GF} l{{{ threadExpr i [] hl(v(&reader) #()) ∗ thKids i {kl} ∗
          Obl.fuel kl 1 μ ∗ oblKids kl ∅ ∗ finallyI Nl kl 1 (exits v1 @ i) ∗
          isFlag xLoc k 0 }}}
        hl(v(&reader) #()) @ i
      l{{{ RET v1; threadExpr i [] hl(#1) ∗ liftTerm i (fun _ _ => iprop(True)) v1 }}} := by
  obtain ⟨μw, hfw⟩ := Flag.wait_spec (GF := GF)
  refine ⟨10 + μw, fun i k kl => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, Hkl, HFl, #Hflag⟩ HΦ
  icases (Obl.fuel_add _ _ _ _).mp $$ HF with ⟨HF, Hfw⟩
  ihave HF : oblFuels {kl} 10 $$ [HF]
  · unfold oblFuels
    iapply BigSepS.bigSepS_singleton.mpr
    iexists _
    iexact HF
  unfold reader X
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(v(&Flag.wait) #xLoc) HT
  ihave Hfw := (Obl.fuel_layer_eq kl μw Ordinals.Ordinal.one_eq_succ_zero).mp $$ Hfw
  iapply hfw 1 i xLoc {kl} k 0 _ $$ [HT HG Hfw]
  · iframe HT HG
    isplitl [Hfw]
    · iapply BigSepS.bigSepS_singleton.mpr
      iexact Hfw
    · iexact Hflag
  iintro ⟨HT, Hc, HG, -⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  unfold v1
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  rw [show (hl(#1) : Exp) = .val hl_val(#1) from rfl]
  iapply lwp_value_mupd'.mpr
  ihave Hc := tlc_one_nat.mpr $$ Hc
  imod threadExpr_terminate_finally i ⊤ hl_val(#1) kl Nl (fun _ _ => CoPset.mem_full)
    $$ HT Hc HG Hkl HFl with ⟨HT, #Hd⟩
  imodintro
  iapply HΦ
  iframe HT
  unfold liftTerm
  isplitl
  · iexact Hd
  · ipureintro
    trivial

/-- The commitments of the writer (thread `0`) and the reader (thread `1`), and their resources
(Rocq `Φ_P`). -/
def clientRes (μ₁ μ₂ : Measure) : IProp GF :=
  iprop(∃ k kl₁ kl₂ : Oid, ⌜k ≠ kl₁⌝ ∗ isFlag xLoc k 0 ∗ flagTk xLoc k ∗
    finallyI Nl kl₁ 1 (exits vUnit @ 0) ∗ finallyI Nl kl₂ 1 (exits v1 @ 1) ∗
    (thKids 0 {k, kl₁} ∗ oblKids k ∅ ∗ oblKids kl₁ ∅ ∗ thKids 1 {kl₂} ∗ oblKids kl₂ ∅ ∗
      ([∗set] g ∈ ({k, kl₁} : Oids), Obl.fuel g 0 μ₁) ∗ Obl.fuel kl₂ 1 μ₂))

/-- The return values: `()` for the writer (thread `0`), `1` for the reader. -/
def clientVal : ThreadId → Val → Prop
  | 0, v => v = vUnit
  | _, v => v = v1

/-- The postconditions of the threads. -/
abbrev clientPost : ThreadId → Val → IProp GF := fun j v => iprop(⌜clientVal j v⌝)

/-- From the threads' tokens, the flag's location and the threads' empty sets of children: the
flag, the commitments, and the `lWP`s from them. -/
@[lantana_alias flag_client_pre]
theorem flagClient_pre :
    threadExpr (GF := GF) 0 [] hl(v(&writer) #()) ⊢ threadExpr 1 [] hl(v(&reader) #()) -∗
      xLoc ↦ some v0 -∗ thKids 0 ∅ -∗ thKids 1 ∅ -∗
      |={⊤}=>m ∃ μ₁ μ₂ : Measure, clientRes μ₁ μ₂ ∗
        (clientRes μ₁ μ₂ -∗ |={⊤}=>m
          lWP hl(v(&writer) #()) @ 0; ⊤ {{ liftTerm 0 clientPost }} ∗
          lWP hl(v(&reader) #()) @ 1; ⊤ {{ liftTerm 1 clientPost }}) := by
  obtain ⟨μ₁, hw⟩ := writer_spec (GF := GF)
  obtain ⟨μ₂, hr⟩ := reader_spec (GF := GF)
  iintro HT0 HT1 Hl HG0 HG1
  imod Flag.isFlag_init ⊤ xLoc (.thread 0) ∅ 0 μ₁ $$ [] Hl HG0 with
    ⟨%k, -, HG0, Hk, Fk, Htk, #Hflag⟩
  · iapply parLe_thread
  imod untilI_alloc (E := ⊤) (.thread 0) _ 0 μ₁ $$ [] HG0 with
    ⟨%kl₁, %hkl₁, HG0, Hkl₁, Fkl₁, -, A₁⟩
  · iapply parLe_thread
  imod A₁ $$ %⊤ %Nl %iprop(True) %(exits vUnit @ 0) [] with U₁
  · inext
    ipureintro
    trivial
  imod untilI_alloc (E := ⊤) (.thread 1) ∅ 1 μ₂ $$ [] HG1 with
    ⟨%kl₂, -, HG1, Hkl₂, Fkl₂, -, A₂⟩
  · iapply parLe_thread
  imod A₂ $$ %⊤ %Nl %iprop(True) %(exits v1 @ 1) [] with U₂
  · inext
    ipureintro
    trivial
  have hne : k ≠ kl₁ := by
    rintro rfl
    exact hkl₁ Std.ExtTreeSet.mem_insert_self
  imodintro
  iexists μ₁, μ₂
  isplitl [Htk U₁ U₂ HG0 Hk Hkl₁ HG1 Hkl₂ Fk Fkl₁ Fkl₂]
  · unfold clientRes finallyI
    iexists k, kl₁, kl₂
    isplitr
    · ipureintro
      exact hne
    isplitr
    · iexact Hflag
    iframe Htk U₁ U₂ Hk Hkl₁ Hkl₂ Fkl₂
    isplitl [HG0]
    · iapply Par.kids_congr _ $$ HG0
      intro z
      simp
      grind
    isplitl [HG1]
    · iapply Par.kids_congr _ $$ HG1
      intro z
      simp
    iapply (bigSepS_pair hne).mpr
    iframe
  iintro HP
  unfold clientRes
  icases HP with
    ⟨%k, %kl₁, %kl₂, %hne, #Hflag, Htk, HF₁, HF₂, HG0, Hk, Hkl₁, HG1, Hkl₂, Fs, Fkl₂⟩
  imodintro
  isplitl [HT0 HG0 Hk Hkl₁ Htk HF₁ Fs]
  · iapply hw 0 k kl₁ $$ [HT0 HG0 Fs Hk Hkl₁ Htk HF₁]
    · iframe
      isplitl
      · ipureintro
        exact hne
      · iexact Hflag
    iintro ⟨-, Hd⟩
    unfold liftTerm
    icases Hd with ⟨Hd, -⟩
    iframe Hd
    ipureintro
    rfl
  · iapply hr 1 k kl₂ $$ [HT1 HG1 Fkl₂ Hkl₂ HF₂]
    · iframe
      iexact Hflag
    iintro ⟨-, Hd⟩
    unfold liftTerm
    icases Hd with ⟨Hd, -⟩
    iframe Hd
    ipureintro
    rfl

end Specs

/-! ## Traces and the guarantee -/

section Guarantee
variable {GF : BundledGFunctors}

/-- The flag is `0` until it is `1`, and then `1`; it is `0` until it is `1`; the writer
returns `()` and the reader returns `1` (Rocq `R_main`). -/
def rClient : TrProp Exp State :=
  isFlagTr xLoc ∧ₜ (pointsToTr xLoc v0 𝒰ₜ pointsToTr xLoc v1) ∧ₜ
    ◇ₜ TrProp.state (threadExprSat 0 [] (.val vUnit)) ∧ₜ
    ◇ₜ TrProp.state (threadExprSat 1 [] (.val v1))

/-- What the resources guarantee: nothing for the pure and ghost parts; the names do not show
(Rocq `G_client`). -/
def gClient : TrSpec Exp State GF :=
  TrSpec.true ∧ₛ flagTrSpec xLoc ∧ₛ (pointsToSpec xLoc v0 𝒰ₛ pointsToSpec xLoc v1) ∧ₛ
    ◇ₛ TrSpec.state (threadExprSat 0 [] (.val vUnit)) ∧ₛ
    ◇ₛ TrSpec.state (threadExprSat 1 [] (.val v1)) ∧ₛ TrSpec.true

@[lantana_alias G_client_impl]
theorem gClient_impl : (gClient (GF := GF)).external ⊆ rClient := by
  intro τ ⟨_, hflag, hu, hf₁, hf₂, _⟩
  exact ⟨Flag.flagTrSpec_impl xLoc τ hflag, hu, hf₁, hf₂⟩

variable [ModelGS GF] [HeapGS GF]

@[lantana_alias flag_client.guar_Φ_P]
theorem guar_clientRes (μ₁ μ₂ : Measure) : ⊢@{IProp GF} clientRes μ₁ μ₂ ⊨ₜ gClient := by
  unfold clientRes gClient
  exact IntoGuar.into_guar

end Guarantee

/-! ## Adequacy -/

section Adequacy

/-- The initial pool: the writer (thread `0`) and the reader (thread `1`). -/
abbrev tp0 : ThreadPool Exp := [hl(v(&writer) #()), hl(v(&reader) #())]

/-- The initial state: the flag is `0`. -/
abbrev σ0 : State := ⟨Iris.Std.insert (M := HeapF) ∅ xLoc (some v0)⟩

/-- The initial resources of the threads, and their `lWP`s (the common part of the adequacy
proofs). -/
theorem flagClient_init [ModelGS ExGF] [TemporalGS Exp State ExGF] (hs : HeapStateGS ExGF) :
    letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
    bigSepM (M := HeapF) (fun l v => l ↦ v) σ0.heap ∗
      ([∗list] j ↦ e ∈ tp0, threadExpr j [] e) ⊢
      ([∗list] j ∈ List.range tp0.length, thKids j ∅) -∗
      |={⊤}=>m ∃ μ₁ μ₂ : Measure, clientRes μ₁ μ₂ ∗
        (clientRes μ₁ μ₂ -∗
          |={⊤}=>m [∗list] j ↦ e ∈ tp0, lWP e @ j; ⊤ {{ liftTerm j clientPost }}) := by
  letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
  iintro ⟨Hl, HT⟩ HG
  rw [show List.range (List.length tp0) = [0, 1] from rfl]
  icases BigSepL.bigSepL_cons.mp $$ HG with ⟨HG0, HG⟩
  ihave HG1 := BigSepL.bigSepL_singleton.mp $$ HG
  icases BigSepL.bigSepL_cons.mp $$ HT with ⟨HT0, HT⟩
  ihave HT1 := BigSepL.bigSepL_singleton.mp $$ HT
  icases (BigSepM.bigSepM_insert (Iris.Std.LawfulPartialMap.get?_empty _)).mp $$ Hl with ⟨Hl, -⟩
  imod flagClient_pre $$ HT0 HT1 Hl HG0 HG1 with ⟨%μ₁, %μ₂, HP, Hwp⟩
  imodintro
  iexists μ₁, μ₂
  iframe HP
  iintro HP
  imod Hwp $$ HP with ⟨W0, W1⟩
  imodintro
  iapply BigSepL.bigSepL_cons.mpr
  iframe W0
  iapply BigSepL.bigSepL_singleton.mpr
  iexact W1

/-- In every fair behavior from the initial configuration, the flag is `0` until it is `1`, and
then `1`, the writer returns `()` and the reader returns `1`. -/
@[lantana_alias flag_client_adequacy]
theorem flagClient_adequacy (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    rClient τ := by
  refine lwp_adequacy_temporal (GF := ExGF) σ0 tp0 0 gClient rClient gClient_impl τ hbeh hfair
    hpos hinit ?_
  intro _ _
  refine ⟨4, ?_⟩
  imod heapState_init σ0 tp0 with ⟨%hs, Hσ, Hl, HT⟩
  letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
  imodintro
  iexists instStateInterp, (fun _ _ => iprop(True)), clientPost
  isplitl [Hσ]
  · iexact Hσ
  iintro - HG
  imod flagClient_init hs $$ [Hl HT] HG with ⟨%μ₁, %μ₂, HP, Hwp⟩
  · iframe
  imodintro
  iexists clientRes μ₁ μ₂
  isplitr
  · iapply guar_clientRes
  iframe

/-- Safety for one thread `j`, for any property `Φ` implied by its return value. -/
theorem flagClient_safety_of (j : ThreadId) (hj : j < tp0.length) (Φ : ThreadId → Val → Prop)
    (hΦ : ∀ v, clientVal j v → Φ j v) (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    safetyIris j Φ τ := by
  refine lwp_adequacy_safety (GF := ExGF) σ0 tp0 0 j Φ τ hbeh hfair hpos hinit hj ?_
  intro _ _
  refine ⟨4, ?_⟩
  imod heapState_init σ0 tp0 with ⟨%hs, Hσ, Hl, HT⟩
  letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
  imodintro
  iexists instStateInterp, (fun _ _ => iprop(True)), clientPost
  isplit
  · ipureintro
    exact fun v => pure_mono (hΦ v)
  isplitl [Hσ]
  · iexact Hσ
  iintro - HG
  imod flagClient_init hs $$ [Hl HT] HG with ⟨%μ₁, %μ₂, HP, Hwp⟩
  · iframe
  iapply Hwp $$ HP

/-- Safety: in every fair behavior from the initial configuration, the scheduled thread is never
stuck, and once the writer (resp. the reader) has returned, its value is `()` (resp. `1`). -/
@[lantana_alias flag_client_safety_adequacy]
theorem flagClient_safety_adequacy (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    safetyIris 0 (fun _ v => v = vUnit) τ ∧ safetyIris 1 (fun _ v => v = v1) τ :=
  ⟨flagClient_safety_of 0 (by decide) _ (fun _ h => h) τ hbeh hfair hpos hinit,
    flagClient_safety_of 1 (by decide) _ (fun _ h => h) τ hbeh hfair hpos hinit⟩

/-- Liveness and safety together, over the same fair behaviors. -/
@[lantana_alias flag_client_liveness_safety]
theorem flagClient_liveness_safety (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    rClient τ ∧ (safetyIris 0 (fun _ v => v = vUnit) τ ∧ safetyIris 1 (fun _ v => v = v1) τ) :=
  ⟨flagClient_adequacy τ hbeh hfair hpos hinit,
    flagClient_safety_adequacy τ hbeh hfair hpos hinit⟩

end Adequacy

end Lantana.Examples.FlagClient
