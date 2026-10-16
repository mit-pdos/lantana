/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TemporalFormulaRun
public import Lantana.Trace.FairScheduling
public import Lantana.Trace.Adequacy.Alloc
public import Lantana.Trace.Adequacy.RunStep

/-! # Adequacy (Theorem 1)

Rocq `lantana/trace/adequacy_temporal.v`: `lWP` is a running system with the one-step
property, so if the initial resources guarantee `G`, every fair behavior from the initial
configuration satisfies the trace reading of `G`.

The running system of `lWP` (`sysLwp`) is the registry state and the running threads; its
one-step property (`sysStep_lwp`) is the check of the registry (`regCheck`) followed by one step
of the run (`run_step`, in `Lantana.Trace.Adequacy.RunStep`). From a position `n`
(`lwp_adequacy_internal`), the user's model update gives a resource `P` that guarantees `G`
(whose record at `n` is eliminated after the first step against the bundle of the check at `n`)
and the `lWP`s of the threads. The theorem allocates the ghost state at its names (D32,
`adequacy_alloc_names`), and reads the internal reading off by satisfiability (`TrSpec.adeq`).

The ghost state is allocated inside the proof, so the premise quantifies over its instances; the
user then chooses the state interpretation (after allocating the language's ghost state), the
fork postcondition and the per-thread postconditions.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode Ordinals
open Lantana.Model
open scoped Lantana.TrSpec Lantana.TrProp

/-- The ghost state a world must provide before the temporal layer is allocated: the model's
(Rocq `mupdGpreS`), the history's (`histGpreS`) and the registry's (`tregGpreS`). -/
class TemporalGpreS (Expr State : Type) (GF : BundledGFunctors) where
  [modelG : ModelGpreS GF]
  [histG : MonoListG GF (HistEntry Expr State)]
  [regG : RegGpreS Expr State GF]

attribute [reducible, instance] TemporalGpreS.modelG TemporalGpreS.histG TemporalGpreS.regG

section Lwp

variable {Expr State Val : Type} [Language Expr State Val] {GF : BundledGFunctors}
  [ModelGS GF] [L : LantanaGS Expr State Val GF]

/-- The running system of `lWP` (Rocq `sys_lwp`): the registry state and the running threads
of the pool, for some postconditions. -/
@[lantana_alias sys_lwp]
def sysLwp (_ : Nat) (_ : State) (tp : ThreadPool Expr) : IProp GF :=
  iprop(regState (Expr := Expr) (State := State) ∗
    ∃ Ψ : ThreadId → Val → IProp GF, threadsRun tp Ψ)

/-- The history and temporal interpretation of the registry. -/
theorem historyTInterp_reg (h : List (HistEntry Expr State)) (n : Nat) (σ : State)
    (tp : ThreadPool Expr) :
    historyTInterp (GF := GF) h n σ tp ⊣⊢
      historyInterp h n σ tp ∗ regState (Expr := Expr) (State := State) :=
  .rfl

/-- **The one-step property of `lWP`** (Rocq `sys_step_lwp`): the check of the registry gives
the bundle, then one step of the run. -/
@[lantana_alias sys_step_lwp]
theorem sysStep_lwp :
    ⊢ sysStep (sysLwp (Expr := Expr) (State := State) (Val := Val) (GF := GF)) := by
  rw [sysStep_eq]
  unfold sysStepPre
  iintro !> %c %h %n %σ %tp %g %v %Ω %W %τf %γ %⟨hbeh, hcnt, hLb, hh⟩ ⟨HI, MI, HS⟩
  unfold sysLwp
  icases HS with ⟨HR, %Ψ, HT⟩
  imod regCheck n h σ tp g v Ω W $$ HR HI MI with ⟨HR, HI, MI, %l, #B⟩
  have hb : bundle (Expr := Expr) (State := State) (GF := GF) l n ⊢ bundlePre recordTrI l n := by
    rw [bundle_eq]
  ihave #B' := hb $$ B
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  iexists l
  isplitl []
  · iexact B'
  inext
  imod Hclose with -
  imodintro
  ihave HH := (historyTInterp_reg h n σ tp).mpr $$ [HI HR]
  · iframe HI HR
  imod run_step c hbeh hcnt hLb hh $$ [HH MI HT] with H
  · iframe HH MI HT
  imodintro
  iapply ALC_wand $$ [] H
  iintro H
  unfold runStepPost
  imod H with ⟨%σ', %tp', %Ψ', %g', %v', %Ω', %W', %⟨h₁, h₂, h₃, h₄, h₅, -⟩, Hc, HH, MI, HT⟩
  icases (historyTInterp_reg _ _ _ _).mp $$ HH with ⟨HI, HR⟩
  imodintro
  iexists σ', tp', g', v', Ω', W'
  isplitr
  · ipureintro
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  iframe Hc HI MI HR
  iexists Ψ'
  iexact HT

/-- The program logic from position `n` (Rocq `lwp_adequacy_internal`): the user's model
update gives a resource `P` guaranteeing `G` and the `lWP`s of the threads; the record of `G`
at `n` is eliminated after the first step, against the bundle of the check at `n`. -/
@[lantana_alias lwp_adequacy_internal]
theorem lwp_adequacy_internal {h : List (HistEntry Expr State)} {n : Nat} {σ : State}
    {tp : ThreadPool Expr} (Ψ : ThreadId → Val → IProp GF) {g : List MEvent} {v : Nat}
    {Ω : Obls} {W : Witnesses} {τf : Nat → TraceState Expr State} {γ : Nat → ThreadId → Nat}
    (G : TrSpec Expr State GF) (hbeh : IsBehavior (⟨n, τf⟩ : Trace Expr State))
    (hcnt : BehFscnt ⟨n, τf⟩ γ) (hLb : owitInvLb (fairMeasure (γ n)) Ω W)
    (hh : histTrace h τf) :
    historyTInterp h n σ tp ∗ modelInterp g v Ω W n tp.length ∗
      (|={⊤}=>m ∃ P : IProp GF, (P ⊨ₜ G) ∗ P ∗
        (P -∗ |={⊤}=>m [∗list] j ↦ e ∈ tp, lWP e @ j; ⊤ {{ liftTerm j Ψ }})) ⊢
      |={⊤,∅}=> ALC iprop(|={∅,⊤}=> G.internal ⟨n, τf⟩) := by
  have hγ := owitInvLbMonoFair_fairMeasure (γ n)
  have hrun : (|={⊤}=>m [∗list] j ↦ e ∈ tp, lWP e @ j; ⊤ {{ liftTerm j Ψ }}) ⊢
      |={⊤}=>m threadsRun (GF := GF) tp Ψ :=
    (mupd_mono (lwps_threadsRun tp Ψ)).trans mupd_trans
  ihave #ST := sysStep_lwp (Expr := Expr) (State := State) (Val := Val) (GF := GF)
  iintro ⟨HH, MI, HW⟩
  imod mupd_modelInterp_steps (fairMeasure (γ n)) hγ ⊤ ⊤ h n σ tp g v Ω W _ hLb $$ HW HH MI
    with ⟨⟨%P, #HG, HP, HW⟩, HH, %g₁, %v₁, %Ω₁, %W₁, %⟨-, hLb₁⟩, MI⟩
  icases (historyTInterp_reg _ _ _ _).mp $$ HH with ⟨HI, HR⟩
  icases persistent_entails_left (wand_elim (guar_elim P G h n σ tp _ _ Ω₁ W₁)) $$
    [HI MI HP] with ⟨⟨-, HI, MI, HP⟩, #TF⟩
  · isplitl []
    · iexact HG
    · iframe HI MI HP
  ispecialize HW $$ HP
  ihave HW := hrun $$ HW
  ihave HH := (historyTInterp_reg h n σ tp).mpr $$ [HI HR]
  · iframe HI HR
  imod mupd_modelInterp_steps (fairMeasure (γ n)) hγ ⊤ ⊤ h n σ tp _ _ Ω₁ W₁ _ hLb₁ $$ HW HH MI
    with ⟨HT, HH, %g₂, %v₂, %Ω₂, %W₂, %⟨-, hLb₂⟩, MI⟩
  icases (historyTInterp_reg _ _ _ _).mp $$ HH with ⟨HI, HR⟩
  -- the check at `n`
  imod regCheck n h σ tp _ _ Ω₂ W₂ $$ HR HI MI with ⟨HR, HI, MI, %l, #B⟩
  ihave HH := (historyTInterp_reg h n σ tp).mpr $$ [HI HR]
  · iframe HI HR
  imod run_step 0 hbeh hcnt hLb₂ hh $$ [HH MI HT] with H
  · iframe HH MI HT
  imodintro
  iapply ALC_wand $$ [] H
  iintro H
  unfold runStepPost
  imod H with ⟨%σ', %tp', %Ψ', %g', %v', %Ω', %W', %⟨-, h₂, h₃, h₄, -⟩, -, HH, MI, HT⟩
  icases (historyTInterp_reg _ _ _ _).mp $$ HH with ⟨HI, HR⟩
  imodintro
  have hf : IsBehavior (⟨n, τf⟩ : Trace Expr State) ∧ BehFscnt ⟨n + 1, τf⟩ γ ∧
      owitInvLb (fairMeasure (γ (n + 1))) Ω' W' ∧ histTrace (h ++ [(σ', tp')]) τf :=
    ⟨hbeh, h₂, h₃, h₄⟩
  iapply record_elim G (Sys := sysLwp (Expr := Expr) (State := State) (Val := Val) (GF := GF))
    $$ TF ST %hf B
  iframe HI MI
  unfold sysLwp
  iframe HR
  iexists Ψ'
  iexact HT

end Lwp

/-- **Theorem 1 (adequacy).** Let `G` be a trace specification and `R` a trace property implied
by its trace reading. If, for every allocation of the temporal ghost state, the user can
produce (under a fancy update, from some amount `c` of later credits and the initial threads'
empty sets of children) a resource `P` that guarantees `G` together with `lWP`s for the
initial threads, then every fair behavior from the initial configuration satisfies `R`. -/
@[lantana_alias lwp_adequacy_temporal]
theorem lwp_adequacy_temporal {Expr State Val : Type} [Language Expr State Val]
    {GF : BundledGFunctors} [TemporalGpreS Expr State GF]
    (σ : State) (tp : ThreadPool Expr) (i : ThreadId) (G : TrSpec Expr State GF)
    (R : TrProp Expr State) (hGR : G.external ⊆ R) (τ : Trace Expr State)
    (hbeh : IsBehavior τ) (hfair : fairScheduling τ) (hpos : τ.pos = 0)
    (hinit : τ.seq 0 = ⟨(tp, σ), i⟩)
    (hwp : ∀ [ModelGS GF] [TemporalGS Expr State GF],
      ∃ c : Fuel, ⊢@{IProp GF} |={⊤}=>
        ∃ (SI : StateInterp Expr State GF) (forkPost : ThreadId → Val → IProp GF)
          (Ψ : ThreadId → Val → IProp GF),
          let _ : LantanaGS Expr State Val GF :=
            { toTemporalGS := inferInstance, toStateInterp := SI, forkPost := forkPost }
          iprop(stateInterp σ tp ∗
            (£ₒ c -∗ ([∗list] j ∈ List.range tp.length, thKids j ∅) -∗
              |={⊤}=>m ∃ P : IProp GF, (P ⊨ₜ G) ∗ P ∗
                (P -∗ |={⊤}=>m [∗list] j ↦ e ∈ tp, lWP e @ j; ⊤ {{ liftTerm j Ψ }})))) :
    R τ := by
  apply hGR
  obtain ⟨n, τf⟩ := τ
  simp only at hpos hinit
  subst hpos
  obtain ⟨γc, hγc⟩ := fairScheduling_behFscnt hfair
  obtain ⟨γ, hγ⟩ := iPropSat.sat_alloc (adequacy_alloc_names (GF := GF) σ tp)
  letI : ModelGS GF := ModelGS.ofNames γ.1
  letI : TemporalGS Expr State GF := TemporalGS.ofNames γ.2
  obtain ⟨c, hc⟩ := hwp
  have hh₀ : histTrace [(σ, tp)] τf := by
    intro n' σ' tp' hn'
    cases n' with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hn'
      obtain ⟨rfl, rfl⟩ := hn'
      exact ⟨i, hinit⟩
    | succ n' => simp at hn'
  have hLb₀ : owitInvLb (fairMeasure (γc 0)) ∅ ∅ := mapForall2_empty
  refine G.adeq iprop(emp) ⟨0, τf⟩ ?_
  refine SatFUpd.fupd (S := iPropSatLcAtFrame (GF := GF) iprop(emp)) (E₁ := ∅) (E₂ := ⊤) ?_
  refine sat_ALC (S := iPropSatLcAtFrame (GF := GF) iprop(emp) ∅) (A := Ordinal.{1}) ?_
  refine SatFUpd.fupd (S := iPropSatLcAtFrame (GF := GF) iprop(emp)) (E₁ := ⊤) (E₂ := ∅) ?_
  refine iPropSatLcAtFrame_sat.mpr (iPropSat.sat_bupd (iPropSat.mono ?_ hγ))
  iintro ⟨⟨%x, Hsup⟩, Hw, HE, HM, Hk, Hhist, HR⟩
  imod supply_alloc c $$ Hsup with ⟨Hsup, Hc⟩
  imodintro
  isplitl [Hsup]
  · iexists _
    iexact Hsup
  iframe Hw HE
  isplitl []
  · itrivial
  ihave H := hc
  imod H with ⟨%SI, %fp, %Ψ, H⟩
  letI : LantanaGS Expr State Val GF :=
    { toTemporalGS := inferInstance, toStateInterp := SI, forkPost := fp }
  icases H with ⟨Hs, Hwp⟩
  imod Hhist $$ %SI Hs with HH
  have hTI : regAuth (Expr := Expr) (State := State) (GF := GF) [] ⊢
      regState (Expr := Expr) (State := State) (GF := GF) :=
    regStateWith_init _
  ihave HTI := hTI $$ HR
  ispecialize Hwp $$ Hc Hk
  ihave HHT := (historyTInterp_reg [(σ, tp)] 0 σ tp).mpr $$ [HH HTI]
  · iframe HH HTI
  iapply lwp_adequacy_internal Ψ G hbeh hγc hLb₀ hh₀
  iframe HHT HM Hwp

end Lantana
