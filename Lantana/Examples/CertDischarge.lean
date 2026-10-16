/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Examples.Flag
public import Lantana.Examples.World

/-! # A discharge in the pre-step modality, with nested structures

Rocq `examples/cert_discharge.v`, a test of the adequacy proof: the commitment
`◇ (x ↦ 1 ∗ alwaysI Na (y ↦ 7) ∗ ◇ (x ↦ 2))` (the `finallyI` on `kq` with the right formula
`cdQ x y kf`) is discharged in the pre-step modality of `x ← #2`, which destroys `x ↦ 1`; the
always on `y ↦ 7` is allocated in the same modality, and the nested commitment `◇ (x ↦ 2)` (on
`kf`) is discharged after the store, before the thread terminates. Adequacy records the nested
always and until at the discharge position.

`cert_discharge_adequacy` is the end-to-end statement, from `lwp_adequacy_temporal` in the
closed world `ExGF` (as `FlagFork.main_adequacy`): the initial heap holds `x ↦ 0` and `y ↦ 7`,
whose points-tos come from `heapState_init`; the main thread allocates both obligations in
`main_pre`. At the level of traces (`rMain`): eventually `x` holds `1` while `y` holds `7` from
then on and `x` later holds `2`, and eventually `x` holds `2`. `cert_discharge_safety_adequacy`
is the safety statement.

Statement adaptations: thread ids are list positions, so the main thread is `0`; locations
`x = ⟨0⟩`, `y = ⟨1⟩`. The guarantee of a `finallyI` is inferred as `⌜True⌝ₛ 𝒰ₛ G`, which is
`◇ₛ G` by definition.
-/

@[expose] public noncomputable section

namespace Lantana.Examples.CertDischarge

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.Flag (pointsToSpec pointsToTr)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The program -/

/-- `λ x y, x ← 1; x ← 2; ()`. -/
@[lantana_alias CertDischarge.main]
def main : Val := hl_val(λ x y, x ← #1; x ← #2; #())

/-- The values stored. -/
def v0 : Val := hl_val(#0)
def v1 : Val := hl_val(#1)
def v2 : Val := hl_val(#2)
def v7 : Val := hl_val(#7)

/-- The namespaces of the two commitments and of the always. -/
def Nq : Namespace := nroot.@"cert_discharge_q"
def Nf : Namespace := nroot.@"cert_discharge_f"
def Na : Namespace := nroot.@"cert_discharge_always"

/-! ## The specification -/

section Spec
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]

/-- The right formula of the first commitment: the state at the discharge, a trace-visible
invariant allocated in the same pre-step modality, and the second commitment. -/
@[lantana_alias cd_Q]
def cdQ (x y : Loc) (kf : Oid) : IProp GF :=
  iprop(x ↦ some v1 ∗ alwaysI Na iprop(y ↦ some v7) ∗ finallyI Nf kf 1 iprop(x ↦ some v2))

/-- What `cdQ` guarantees. -/
def cdQSpec (x y : Loc) : TrSpec Exp State GF :=
  pointsToSpec x v1 ∧ₛ □ₛ pointsToSpec y v7 ∧ₛ ◇ₛ pointsToSpec x v2

instance guarOf_cdQ (x y : Loc) (kf : Oid) : GuarOf (cdQ (GF := GF) x y kf) (cdQSpec x y) := by
  unfold cdQ cdQSpec finallyI; exact ⟨GuarOf.guar_of⟩

@[lantana_alias guar_cd_Q]
theorem guar_cdQ (x y : Loc) (kf : Oid) : ⊢@{IProp GF} cdQ x y kf ⊨ₜ cdQSpec x y :=
  GuarOf.guar_of

/-- The main proof: `kq` is discharged in the pre-step modality of the second store, `kf` after
it. -/
@[lantana_alias cert_discharge.main_spec]
theorem main_spec : ∃ μ : Measure, ∀ (i : ThreadId) (kq kf : Oid) (x y : Loc),
    ⊢@{IProp GF} l{{{ threadExpr i [] hl(v(&main) #x #y) ∗ thKids i {kq, kf} ∗
          ([∗set] g ∈ ({kq, kf} : Oids), Obl.fuel g 0 μ) ∗ ⌜kq ≠ kf⌝ ∗ oblKids kq ∅ ∗
          oblKids kf ∅ ∗ x ↦ some v0 ∗ y ↦ some v7 ∗
          finallyI Nq kq 1 (cdQ x y kf) ∗ finallyI Nf kf 1 iprop(x ↦ some v2) }}}
        hl(v(&main) #x #y) @ i
      l{{{ RET hl_val(#()); threadExpr i [] hl(#()) ∗
        liftTerm i (fun _ _ => iprop(True)) hl_val(#()) }}} := by
  refine ⟨10, fun i kq kf x y => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hne, Hkq, Hkf, Hx, Hy, HQ, HFf⟩ HΦ
  ihave HF := oblFuels_init _ 10 0 $$ HF
  unfold main
  lwp_step HT HG HF with Hlc : 1 +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hc1, Hc2⟩
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- `x ← #1`
  lwp_bind hl(#x ← #1) HT
  icases oblFuels_add 1 6 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_store (o := 0) (G := {kq, kf}) (R := ∅) x v0 hl_val(#1)
    $$ [HT HG HF1 Hx]
  · iframe HT Hx
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, Hx⟩
  rw [show (hl_val(#1) : Val) = v1 from rfl]
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- `x ← #2`: the discharge of `kq` happens in the pre-step modality of this store.
  lwp_bind hl(#x ← #2) HT
  imod alwaysI_alloc (E := ⊤) (N := Na) (P := iprop(y ↦ some v7)) $$ [Hy] with #HA
  · inext
    iexact Hy
  ihave Hc1 := tlc_one_nat.mpr $$ Hc1
  imod finallyI_discharge (E := ⊤) (.thread i) {kq, kf} (fun _ _ => CoPset.mem_full) (by simp)
    $$ Hc1 HG Hkq HQ [Hx HFf] with ⟨HQ, HG, -⟩
  · unfold cdQ
    iframe Hx HFf
    iexact HA
  ihave HG := Par.kids_congr (B := {kf}) ?_ $$ HG
  · intro z
    simp
    grind
  ihave HF := oblFuels_subset _ (B := {kf}) (fun z hz => by simp_all) $$ HF
  unfold cdQ
  icases HQ with ⟨Hx, -, HFf⟩
  icases oblFuels_add 1 3 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_store (o := 0) (G := {kf}) (R := ∅) x v1 hl_val(#2) $$ [HT HG HF1 Hx]
  · iframe HT Hx
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, Hx⟩
  rw [show (hl_val(#2) : Val) = v2 from rfl]
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- The nested commitment, then termination.
  iapply lwp_value_mupd'.mpr
  ihave Hc2 := tlc_one_nat.mpr $$ Hc2
  imod finallyI_discharge (E := ⊤) (.thread i) {kf} (fun _ _ => CoPset.mem_full) (by simp)
    $$ Hc2 HG Hkf HFf Hx with ⟨-, HG, -⟩
  imod Th.terminate ⊤ i $$ [HG] with #Hd
  · iapply Par.kids_congr _ $$ HG
    intro z
    simp
  imodintro
  iapply HΦ
  iframe HT
  unfold liftTerm
  isplitl
  · iexact Hd
  · ipureintro
    trivial

/-- The commitments of the main thread `i`, the initial heap and the resources (Rocq `Φ_P`). -/
def mainRes (x y : Loc) (i : ThreadId) (μ : Measure) : IProp GF :=
  iprop(∃ kq kf : Oid, finallyI Nq kq 1 (cdQ x y kf) ∗ finallyI Nf kf 1 iprop(x ↦ some v2) ∗
    x ↦ some v0 ∗ y ↦ some v7 ∗
    (thKids i {kq, kf} ∗ oblKids kq ∅ ∗ oblKids kf ∅ ∗ ⌜kq ≠ kf⌝ ∗
      [∗set] g ∈ ({kq, kf} : Oids), Obl.fuel g 0 μ))

/-- The postcondition of the main thread. -/
abbrev mainPost : ThreadId → Val → IProp GF := fun _ v => iprop(⌜v = hl_val(#())⌝)

/-- From the main thread's token, the initial heap and the thread's empty set of children: the
commitments, and the `lWP` of the thread from them. The obligation `kf` is allocated first, as
the right formula of `kq` mentions it. -/
@[lantana_alias cert_discharge.main_pre]
theorem main_pre (i : ThreadId) (x y : Loc) :
    threadExpr (GF := GF) i [] hl(v(&main) #x #y) ⊢ x ↦ some v0 -∗ y ↦ some v7 -∗
      thKids i ∅ -∗
      |={⊤}=>m ∃ μ : Measure, mainRes x y i μ ∗
        (mainRes x y i μ -∗
          |={⊤}=>m lWP hl(v(&main) #x #y) @ i; ⊤ {{ liftTerm i mainPost }}) := by
  obtain ⟨μ, hmain⟩ := main_spec (GF := GF)
  iintro HT Hx Hy HG
  imod untilI_alloc (E := ⊤) (.thread i) ∅ 0 μ $$ [] HG with
    ⟨%kf, -, HG, Hkf, Fkf, -, Akf⟩
  · iapply parLe_thread
  imod Akf $$ %⊤ %Nf %iprop(True) %iprop(x ↦ some v2) [] with Uf
  · inext
    ipureintro
    trivial
  imod untilI_alloc (E := ⊤) (.thread i) _ 0 μ $$ [] HG with
    ⟨%kq, %hkq, HG, Hkq, Fkq, -, Akq⟩
  · iapply parLe_thread
  imod Akq $$ %⊤ %Nq %iprop(True) %(cdQ x y kf) [] with Uq
  · inext
    ipureintro
    trivial
  have hne : kq ≠ kf := by
    rintro rfl
    exact hkq Std.ExtTreeSet.mem_insert_self
  imodintro
  iexists μ
  isplitl [Uq Uf Hx Hy HG Hkq Hkf Fkq Fkf]
  · unfold mainRes finallyI
    iexists kq, kf
    iframe Uq Uf Hx Hy Hkq Hkf
    isplitl [HG]
    · iapply Par.kids_congr _ $$ HG
      intro z
      simp
    isplitr
    · ipureintro
      exact hne
    iapply (bigSepS_pair hne).mpr
    iframe
  iintro HP
  unfold mainRes
  icases HP with ⟨%kq, %kf, HQ, HFf, Hx, Hy, HG, Hkq, Hkf, %hne, HF⟩
  imodintro
  iapply hmain i kq kf x y $$ [HT HG HF Hkq Hkf Hx Hy HQ HFf]
  · iframe
    ipureintro
    exact hne
  iintro ⟨-, Hd⟩
  unfold liftTerm
  icases Hd with ⟨Hd, -⟩
  iframe Hd
  ipureintro
  rfl

end Spec

/-! ## Traces and the guarantee -/

section Guarantee
variable {GF : BundledGFunctors}

/-- At the level of traces (Rocq `R_main`): eventually `x` holds `1` while `y` holds `7` from
then on and `x` later holds `2`; and eventually `x` holds `2`. -/
def rMain (x y : Loc) : TrProp Exp State :=
  ◇ₜ (pointsToTr x v1 ∧ₜ □ₜ pointsToTr y v7 ∧ₜ ◇ₜ pointsToTr x v2) ∧ₜ ◇ₜ pointsToTr x v2

/-- What the resources guarantee; the first commitment's right formula keeps its nested
structures (Rocq `G_main`). -/
def gMain (x y : Loc) : TrSpec Exp State GF :=
  ◇ₛ cdQSpec x y ∧ₛ ◇ₛ pointsToSpec x v2 ∧ₛ pointsToSpec x v0 ∧ₛ pointsToSpec y v7 ∧ₛ
    TrSpec.true

@[lantana_alias cert_discharge.G_main_impl]
theorem gMain_impl (x y : Loc) : (gMain (GF := GF) x y).external ⊆ rMain x y :=
  fun _ ⟨h₁, h₂, _⟩ => ⟨h₁, h₂⟩

variable [ModelGS GF] [HeapGS GF]

@[lantana_alias cert_discharge.guar_Φ_P]
theorem guar_mainRes (x y : Loc) (i : ThreadId) (μ : Measure) :
    ⊢@{IProp GF} mainRes x y i μ ⊨ₜ gMain x y := by
  unfold mainRes gMain finallyI
  iapply guar_ex_ghost
  iintro %kq
  iapply guar_ex_ghost
  iintro %kf
  iapply guar_sep
  · iapply (GuarOf.guar_of (P := untilI (Expr := Exp) (State := State) Nq kq 1 iprop(True)
      (cdQ (GF := GF) x y kf)))
  iapply guar_sep
  · iapply (GuarOf.guar_of (P := untilI (Expr := Exp) (State := State) Nf kf 1 iprop(True)
      iprop(x ↦ some v2)))
  iapply guar_sep
  · iapply (GuarOf.guar_of (P := iprop(x ↦ some v0 : IProp GF)))
  iapply guar_sep
  · iapply (GuarOf.guar_of (P := iprop(y ↦ some v7 : IProp GF)))
  iapply guar_true

end Guarantee

/-! ## Adequacy -/

section Adequacy

/-- The locations `x` and `y`. -/
abbrev x0 : Loc := ⟨0⟩
abbrev y0 : Loc := ⟨1⟩

/-- The initial pool: the main thread `0`. -/
abbrev tp0 : ThreadPool Exp := [hl(v(&main) #x0 #y0)]

/-- The initial state: `x` holds `0` and `y` holds `7`. -/
abbrev σ0 : State :=
  ⟨Iris.Std.insert (Iris.Std.insert (∅ : HeapF (Option Val)) y0 (some v7)) x0 (some v0)⟩

/-- The points-tos of the initial heap. -/
theorem heap0_pointsTo {GF : BundledGFunctors} [HeapStateGS GF] :
    bigSepM (M := HeapF) (fun l v => l ↦ v) σ0.heap ⊢@{IProp GF}
      x0 ↦ some v0 ∗ y0 ↦ some v7 := by
  refine (BigSepM.bigSepM_insert ?_).mp.trans (sep_mono_right ?_)
  · rw [Iris.Std.LawfulPartialMap.get?_insert, Iris.Std.get?_empty]
    decide
  · refine (BigSepM.bigSepM_insert ?_).mp.trans sep_elim_left
    exact Iris.Std.get?_empty _

/-- In every fair behavior from the initial configuration, eventually `x` holds `1` while `y`
holds `7` from then on and `x` later holds `2`, and eventually `x` holds `2`. -/
@[lantana_alias cert_discharge_adequacy]
theorem certDischarge_adequacy (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    rMain x0 y0 τ := by
  refine lwp_adequacy_temporal (GF := ExGF) σ0 tp0 0 (gMain x0 y0) (rMain x0 y0)
    (gMain_impl x0 y0) τ hbeh hfair hpos hinit ?_
  intro _ _
  refine ⟨2, ?_⟩
  imod heapState_init σ0 tp0 with ⟨%hs, Hσ, Hh, HT⟩
  letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
  imodintro
  iexists instStateInterp, (fun _ _ => iprop(True)), mainPost
  isplitl [Hσ]
  · iexact Hσ
  iintro Hc HG
  rw [show List.range (List.length tp0) = [0] from rfl]
  ihave HG := BigSepL.bigSepL_singleton.mp $$ HG
  ihave HT := BigSepL.bigSepL_singleton.mp $$ HT
  icases heap0_pointsTo $$ Hh with ⟨Hx, Hy⟩
  imod main_pre 0 x0 y0 $$ HT Hx Hy HG with ⟨%μ, HP, Hwp⟩
  imodintro
  iexists mainRes x0 y0 0 μ
  isplitr
  · iapply guar_mainRes
  iframe HP
  iintro HP
  imod Hwp $$ HP with Hwp
  imodintro
  iapply BigSepL.bigSepL_singleton.mpr
  iexact Hwp

/-- Safety: in every fair behavior from the initial configuration, the scheduled thread is never
stuck, and once the main thread has returned, its value is `()`. -/
@[lantana_alias cert_discharge_safety_adequacy]
theorem certDischarge_safety_adequacy (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    safetyIris 0 (fun _ v => v = hl_val(#())) τ := by
  refine lwp_adequacy_safety (GF := ExGF) σ0 tp0 0 0 _ τ hbeh hfair hpos hinit (by decide) ?_
  intro _ _
  refine ⟨2, ?_⟩
  imod heapState_init σ0 tp0 with ⟨%hs, Hσ, Hh, HT⟩
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
  icases heap0_pointsTo $$ Hh with ⟨Hx, Hy⟩
  imod main_pre 0 x0 y0 $$ HT Hx Hy HG with ⟨%μ, HP, Hwp⟩
  imod Hwp $$ HP with Hwp
  imodintro
  iapply BigSepL.bigSepL_singleton.mpr
  iexact Hwp

/-- Liveness and safety together, over the same fair behaviors. -/
@[lantana_alias cert_discharge_liveness_safety]
theorem certDischarge_liveness_safety (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    rMain x0 y0 τ ∧ safetyIris 0 (fun _ v => v = hl_val(#())) τ :=
  ⟨certDischarge_adequacy τ hbeh hfair hpos hinit,
    certDischarge_safety_adequacy τ hbeh hfair hpos hinit⟩

end Adequacy

end Lantana.Examples.CertDischarge
