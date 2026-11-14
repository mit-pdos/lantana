/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Trace.Adequacy.RunStep
public import Lantana.Trace.Adequacy.Temporal

/-! # Adequacy: safety

Rocq `lantana/trace/adequacy_safety.v`: Iris-style safety on fair behaviors, read off the run
directly (no guarantees): no thread of the pool is ever stuck, and a terminated thread `j` of
the initial pool satisfies its postcondition. (Rocq asks it of the scheduled thread; traces here
carry no thread label, and the statement for every thread is the stronger one.) Lantana-Lean
derives it from the single-step simulation `run_step`, which also exposes the pure facts of the
step that safety needs, instead of duplicating that proof: the step-indexed reading
`safetyIrisTrI` (an `always` of a pure predicate) is a Löb induction whose body is one
`run_step` (`threadsRun_safety`), and satisfiability reads it off (`safetyIrisTrI_trProp`).

The temporal layer is interpreted by the registry state (`regTemporalInterp`), initialised from
the empty registry of the allocation (`regStateWith_init`); the proof of `threadsRun_safety` is
generic in the interpretation.

Adaptation: Rocq requires the postcondition of `j` to be given (`Ψs !! j = Some Q`), i.e. `j`
to be an initial thread; here the postconditions are a function, so `j < tp.length` is a
hypothesis (a thread forked later gets `forkPost`, about which nothing is assumed).
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode Ordinals
open Iris.ProgramLogic (toVal Language EvContext)
open Lantana.Model
open scoped Lantana.TrProp

variable {Expr State Obs Val Ectx : Type} [Language Expr State Obs Val] [EvContext Expr Ectx]

/-- If thread `j` has terminated with the value `v`, then `Φ j v` (Rocq `if_term_val`). -/
@[lantana_alias if_term_val]
def Cfg.ifTermVal (j : ThreadId) (Φ : ThreadId → Val → Prop) (ρ : Cfg Expr State) : Prop :=
  ∀ e v, ρ.1[j]? = some e → toVal e = some v → Φ j v

/-- The safety facts at the current position: no thread of the pool is stuck and a terminated
thread `j` satisfies `Φ j`. -/
def safeNow (j : ThreadId) (Φ : ThreadId → Val → Prop) : TrProp (Cfg Expr State) :=
  TrProp.atomic Cfg.notStuck ∧ₜ TrProp.atomic (Cfg.ifTermVal (Val := Val) j Φ)

/-- Iris-style safety: always, no thread of the pool is stuck and a terminated thread `j`
satisfies `Φ j` (Rocq `safety_iris`). -/
@[lantana_alias safety_iris]
def safetyIris (j : ThreadId) (Φ : ThreadId → Val → Prop) : TrProp (Cfg Expr State) :=
  □ₜ (TrProp.atomic Cfg.notStuck ∧ₜ TrProp.atomic (Cfg.ifTermVal (Val := Val) j Φ))

section SafetyTrI

variable {GF : BundledGFunctors} [ModelGS GF]

/-- The step-indexed reading of safety (Rocq `safety_iris_trI`, with the one-formula
`TrIProp.always`: Rocq's second formula is only used with `True`). -/
@[lantana_alias safety_iris_trI]
def safetyIrisTrI (j : ThreadId) (Φ : ThreadId → Val → Prop) : TrIProp Expr State GF :=
  TrIProp.always fun τ => iprop(⌜safeNow (Expr := Expr) (State := State) j Φ τ⌝)

/-- Satisfiability of the step-indexed reading gives safety (Rocq `safety_iris_trI_trProp`). -/
@[lantana_alias safety_iris_trI_trProp]
theorem safetyIrisTrI_trProp (F : IProp GF) (j : ThreadId) (Φ : ThreadId → Val → Prop)
    (τ : Trace (Cfg Expr State)) (hs : (iPropSatLcAtFrame F ⊤).sat (safetyIrisTrI j Φ τ)) :
    safetyIris j Φ τ :=
  TrIProp.always_tr_always F _ (safeNow j Φ) (fun _ h => (iPropSatLcAtFrame F ⊤).elim h) τ hs

end SafetyTrI

section SafetyRun

variable [Crash Expr State Obs Val] {GF : BundledGFunctors} [ModelGS GF]
  [L : LantanaGS Expr State Obs Val GF] [TemporalInterp Expr State GF]

/-- The running threads are safe (Rocq `lwp_fix_safety_iris_trI`): by Löb induction, each
position is one `run_step`, which gives that no thread of the pool is stuck; the postcondition of
`j` holds whenever `j` is a value, and does not change across steps. -/
@[lantana_alias lwp_fix_safety_iris_trI]
theorem threadsRun_safety (τf : Nat → Cfg Expr State) (sched : Nat → ThreadId)
    (γ : Nat → ThreadId → Nat) (j : ThreadId) (Φ : ThreadId → Val → Prop) :
    ⊢ ∀ (h : List (HistEntry Expr State)) (n : Nat) (σ : State) (tp : ThreadPool Expr)
      (Ψ : ThreadId → Val → IProp GF) (g : List MEvent) (v : Nat) (Ω : Obls) (W : Witnesses),
      ⌜Schedule sched ⟨0, τf⟩ ∧ SchedCounters sched γ ⟨0, τf⟩ ∧
        owitInvLb (fairMeasure (γ n)) Ω W ∧ histTrace h τf ∧ j < tp.length ∧
        ∀ v, Ψ j v ⊢ ⌜Φ j v⌝⌝ -∗
      historyTInterp h n σ tp ∗ modelInterp g v Ω W n tp.length (Cfg.crashed (tp, σ)) ∗
        threadsRun tp Ψ -∗
      safetyIrisTrI j Φ ⟨n, τf⟩ := by
  iloeb as IH
  iintro %h %n %σ %tp %Ψ %g %v %Ω %W %⟨hsch, hcnt, hLb, hh, hj, hΨ⟩ ⟨HH, HM, HT⟩
  icases persistent_entails_left (threadsRun_ifTermVal hΨ) $$ HT with ⟨HT, %hval⟩
  icases persistent_entails_left (historyTInterp_wf h n σ tp) $$ HH with ⟨HH, %⟨-, hlast⟩⟩
  have hnow := hh n σ tp hlast
  have hunf : TrIProp.alwaysPre (fun τ => iprop(⌜safeNow (Expr := Expr) (State := State) j Φ τ⌝))
      (safetyIrisTrI (GF := GF) j Φ) ⟨n, τf⟩ ⊢ safetyIrisTrI j Φ ⟨n, τf⟩ :=
    (TrIProp.always_unfold _ _).mpr
  iapply hunf
  unfold TrIProp.alwaysPre TrIProp.defer
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose with -
  imodintro
  imod run_step 0 hsch hcnt hLb hh $$ [HH HM HT] with H
  · iframe HH HM HT
  imodintro
  iapply ALC_wand $$ [] H
  iintro H
  unfold runStepPost
  imod H with ⟨%σ', %tp', %Ψ', %g', %v', %Ω', %W',
    %⟨hLb', hh', -, hns, hle, hΨ'⟩, -, HH, HM, HT⟩
  have hsafe : safeNow (Expr := Expr) (State := State) j Φ ⟨n, τf⟩ := by
    unfold safeNow TrProp.and TrProp.atomic
    refine ⟨hns, ?_⟩
    simp only [Trace.now, hnow]
    exact hval
  have hfacts : Schedule sched ⟨0, τf⟩ ∧ SchedCounters sched γ ⟨0, τf⟩ ∧
      owitInvLb (fairMeasure (γ (n + 1))) Ω' W' ∧ histTrace (h ++ [(σ', tp')]) τf ∧
      j < tp'.length ∧ ∀ v, Ψ' j v ⊢ ⌜Φ j v⌝ :=
    ⟨hsch, hcnt, hLb', hh', Nat.lt_of_lt_of_le hj hle, by rw [hΨ' j hj]; exact hΨ⟩
  imodintro
  isplit
  · ipureintro
    exact hsafe
  · rw [show (⟨n, τf⟩ : Trace (Cfg Expr State)).next = ⟨n + 1, τf⟩ from rfl]
    iapply IH $$ %(h ++ [(σ', tp')]) %(n + 1) %σ' %tp' %Ψ' %g' %v' %Ω' %W' %hfacts
    iframe HH HM HT

end SafetyRun

/-- Safety adequacy (Rocq `lwp_adequacy_safety_iris`): if, in every world, the initial threads
can be given `lWP`s whose postcondition for the initial thread `j` implies `Φ j` (from the pieces
of the initial threads, as in `lwp_adequacy_temporal`), then every fair behavior from the initial
configuration is safe for `j`: no thread of the pool is ever stuck, and `j`, once terminated,
satisfies `Φ j`. -/
@[lantana_alias lwp_adequacy_safety_iris]
theorem lwp_adequacy_safety [Crash Expr State Obs Val] {GF : BundledGFunctors}
    [TemporalGpreS Expr State GF]
    (σ : State) (tp : ThreadPool Expr) (j : ThreadId) (Φ : ThreadId → Val → Prop)
    (τ : Trace (Cfg Expr State)) (hbeh : IsBehavior τ) (hfair : fairScheduling τ) (hpos : τ.pos = 0)
    (hinit : τ.seq 0 = (tp, σ)) (hj : j < tp.length)
    (hwp : ∀ [ModelGS GF] [TemporalGS Expr State GF],
      ∃ c : Fuel, ⊢@{IProp GF} |={⊤}=>
        ∃ (SI : StateInterp Expr State GF) (forkPost : ThreadId → Val → IProp GF)
          (Ψ : ThreadId → Val → IProp GF),
          let _ : LantanaGS Expr State Obs Val GF :=
            { toTemporalGS := inferInstance, toStateInterp := SI, forkPost := forkPost }
          iprop(⌜∀ v, Ψ j v ⊢ ⌜Φ j v⌝⌝ ∧ stateInterp σ tp ∗
            (£ₒ c -∗
              ([∗list] j ∈ List.range tp.length,
                (⌜¬Cfg.crashed (tp, σ) j⌝ -∗ thActive j ∗ thKids j ∅) ∗ thCarriers j ∅) -∗
              |={⊤}=>m [∗list] j ↦ e ∈ tp, lWP e @ j; ⊤ {{ liftTerm j Ψ }}))) :
    safetyIris j Φ τ := by
  obtain ⟨n, τf⟩ := τ
  simp only at hpos hinit
  subst hpos
  obtain ⟨sched, γc, hsch, hγc⟩ := exists_fair_schedule_schedCounters hbeh hfair
  obtain ⟨γ, hγ⟩ := iPropSat.sat_alloc (adequacy_alloc_names (GF := GF) σ tp (Cfg.crashed (tp, σ)))
  letI : ModelGS GF := ModelGS.ofNames γ.1
  letI : TemporalGS Expr State GF := TemporalGS.ofNames γ.2
  obtain ⟨c, hc⟩ := hwp
  have hh₀ : histTrace [(σ, tp)] τf := by
    intro n' σ' tp' hn'
    cases n' with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hn'
      obtain ⟨rfl, rfl⟩ := hn'
      exact hinit
    | succ n' => simp at hn'
  have hLb₀ : owitInvLb (fairMeasure (γc 0)) ∅ ∅ := mapForall2_empty
  refine safetyIrisTrI_trProp iprop(emp) j Φ ⟨0, τf⟩ (SatFUpd.fupd
    (S := iPropSatLcAtFrame (GF := GF) iprop(emp)) (E₁ := ⊤) (E₂ := ⊤) ?_)
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
  letI : LantanaGS Expr State Obs Val GF :=
    { toTemporalGS := inferInstance, toStateInterp := SI, forkPost := fp }
  icases H with ⟨%hΨ, Hs, Hwp⟩
  imod Hhist $$ %SI Hs with HH
  have hTI : regAuth (Expr := Expr) (State := State) (GF := GF) [] ⊢
      temporalInterp Expr State (GF := GF) := by
    rw [temporalInterp_reg]
    exact regStateWith_init _
  ihave HTI := hTI $$ HR
  ispecialize Hwp $$ Hc Hk
  have hrun : (|={⊤}=>m [∗list] j ↦ e ∈ tp, lWP e @ j; ⊤ {{ liftTerm j Ψ }}) ⊢
      |={⊤}=>m threadsRun (GF := GF) tp Ψ :=
    (mupd_mono (lwps_threadsRun tp Ψ)).trans mupd_trans
  ihave Hwp := hrun $$ Hwp
  ihave HHT : historyTInterp [(σ, tp)] 0 σ tp $$ [HH HTI]
  · unfold historyTInterp
    iframe HH HTI
  imod mupd_modelInterp_steps (fairMeasure (γc 0)) (owitInvLbMonoFair_fairMeasure _) ⊤ ⊤
    [(σ, tp)] 0 σ tp [(0, ∅)] 0 ∅ ∅ tp.length _ _ hLb₀ $$ Hwp HHT HM
    with ⟨HT, HHT, %g', %v', %Ω', %W', %⟨-, hLb'⟩, HM⟩
  have hfacts : Schedule sched ⟨0, τf⟩ ∧ SchedCounters sched γc ⟨0, τf⟩ ∧
      owitInvLb (fairMeasure (γc 0)) Ω' W' ∧ histTrace [(σ, tp)] τf ∧ j < tp.length ∧
      ∀ v, Ψ j v ⊢ ⌜Φ j v⌝ :=
    ⟨hsch, hγc, hLb', hh₀, hj, hΨ⟩
  imodintro
  iapply threadsRun_safety τf sched γc j Φ $$ %([(σ, tp)]) %0 %σ %tp %Ψ %_ %_ %Ω' %W' %hfacts
  iframe HHT HM HT

end Lantana
