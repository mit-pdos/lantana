/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

Based on Iris-Lean's `Iris.ProgramLogic.Lifting`, whose header reads:
  Copyright (c) The Iris-Lean Contributors
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Fernando Leal
Modified by the Lantana-Lean Contributors; the module documentation describes the changes.
-/
module

public import Lantana.ProgramLogic.WeakestPre

/-! # Lifting lemmas

Rocq `lantana/program_logic/lifting.v`, after Iris-Lean's `Iris.ProgramLogic.Lifting`: the rules
of the operational semantics as rules of `lWP`. Only `lwp_lift_step` sees the history and the
model updates around a step; the others are stated with the state interpretation and the
obligation interface. The shape a user of a step sees after the pre-step model update is

`∃ G, thKids i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗ ∀ e₂ σ₂ efs, ⌜primStep e₁ σ₁ e₂ σ₂ efs⌝ ={∅}=∗
  thKids i G -∗ witCreds R -∗ ([∗list] j ∈ List.range efs.length, thKids (len + j) ∅) -∗ ALC …`:

the step burns one unit of fuel of each child `G` of the thread, gives a credit to each witness
of `R` (`step_progress`), and gives every forked thread `len + j` an empty set of children
(`step_fork`).

There is no `state_interp_aux` (D17): `PureExecSI ς i` says that the token `ς` of thread `i`
and the state interpretation can be updated together along a pure step of `i`.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode Ordinals Ordinal
open Iris.ProgramLogic (toVal)

section Lifting

variable {Expr : Type} {State : Type} {Val : Type} {GF : BundledGFunctors}
variable [Λ : Language Expr State Val] [ModelGS GF]
variable [L : LantanaGS Expr State Val GF] [TemporalInterp Expr State GF]

/-- A pure step of thread `i` from `ctxApply K e₁` to `ctxApply K e₂` updates the token `ς i e₁`
and the state interpretation together (Rocq `PureExecSI`; `ς i e` is the thread-expression token
of HeapLang, which the state interpretation also knows). -/
@[lantana_alias PureExecSI]
class PureExecSI (ς : ThreadId → Expr → IProp GF) (i : ThreadId) : Prop where
  pureExecSI {K : Λ.Ctx} {e₁ e₂ : Expr} {σ : State} {tp : ThreadPool Expr} :
    Language.Context K → tp[i]? = some (ctxApply K e₁) → primStep e₁ σ e₂ σ [] →
      ς i e₁ ∗ stateInterp σ tp ⊢ |==> (ς i e₂ ∗ stateInterp σ (tp.set i (ctxApply K e₂)))

attribute [lantana_alias pure_exec_si] PureExecSI.pureExecSI

variable {s : Stuckness} {i : ThreadId} {E E₁ E₂ : CoPset} {e e₁ : Expr} {Φ : Val → IProp GF}

/-- The safety condition of the pure lifting lemmas (Rocq `if s is NotStuck then reducible e σ
else to_val e = None`): `e` is reducible for `NotStuck`, not a value for `MaybeStuck`. -/
def _root_.Iris.Stuckness.pureSafe : Stuckness → Expr → State → Prop
  | .NotStuck, e, σ => Language.Reducible e σ
  | .MaybeStuck, e, _ => toVal e = none

theorem _root_.Iris.Stuckness.pureSafe.toVal_eq_none {s : Stuckness} {e : Expr} {σ : State}
    (h : s.pureSafe e σ) : toVal e = none := by
  cases s
  · exact Language.Reducible.toVal_eq_none h
  · exact h

theorem _root_.Iris.Stuckness.pureSafe.maybeReducible {s : Stuckness} {e : Expr} {σ : State}
    (h : s.pureSafe e σ) : s.maybeReducible e σ := by
  cases s
  · exact h
  · trivial

theorem _root_.Iris.Stuckness.pureSafe_of_pureStep [Inhabited State] {s : Stuckness}
    {e₁ e₂ : Expr} (h : Language.PureStep e₁ e₂) (σ : State) : s.pureSafe e₁ σ := by
  cases s
  · exact h.safe σ
  · exact (h.safe default).toVal_eq_none

omit [ModelGS GF] in
/-- The forked threads `tc, …, tc + n - 1` of `step_fork`, from `0`. -/
theorem bigSepL_range'_sub {Ψ : Nat → IProp GF} (tc n : Nat) :
    ([∗list] j ∈ List.range' tc (tc + n - tc), Ψ j) ⊣⊢ [∗list] j ∈ List.range n, Ψ (tc + j) := by
  rw [Nat.add_sub_cancel_left, List.range'_eq_map_range, BigSepL.bigSepL_map]
  exact .rfl

/-- The length of the pool after a step. -/
theorem length_set_append {tp efs : List Expr} {j : ThreadId} {e' : Expr} :
    (tp.set j e' ++ efs).length = tp.length + efs.length := by
  simp

/-- `lwpStep` with the progress and fork rounds of the step applied (Rocq `lwp_step_step` and
`lwp_lift_step`). -/
@[lantana_alias lwp_lift_step, lantana_alias lwp_step_step]
theorem lwp_lift_step (he : toVal e₁ = none) :
    (∀ (K : Λ.Ctx) (h : List (HistEntry Expr State)) (n : Nat) (σ₁ : State)
        (tp : ThreadPool Expr),
      ⌜Language.Context K⌝ → ⌜tp[i]? = some (ctxApply K e₁)⌝ →
      historyTInterp h n σ₁ tp ={E,∅}=∗ |=[n, tp.length]=>m
        ⌜s.maybeReducible e₁ σ₁⌝ ∗
        ∃ G, thKids i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
          ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr), ⌜primStep e₁ σ₁ e₂ σ₂ efs⌝ ={∅}=∗
            thKids i G -∗ witCreds R -∗
            ([∗list] j ∈ List.range efs.length, thKids (tp.length + j) ∅) -∗
            ALC (mupdFancy ∅ E (n + 1) (tp.length + efs.length)
              iprop(historyTInterp (h ++ [(σ₂, tp.set i (ctxApply K e₂) ++ efs)]) (n + 1) σ₂
                  (tp.set i (ctxApply K e₂) ++ efs) ∗
                |={E}=>m (lWP e₂ @ s; i; E {{ Φ }} ∗
                  [∗list] j ↦ ef ∈ efs,
                    lWP ef @ s; (tp.length + j); ⊤ {{ liftTerm (tp.length + j) L.forkPost }}))))
      ⊢ lWP e₁ @ s; i; E {{ Φ }} := by
  iintro H
  rw [lwp_unfold.to_eq]
  simp only [lwpPre, he]
  unfold lwpStep
  iintro %K %h %n %σ₁ %tp %hK %hi Hσ
  imod H $$ %K %h %n %σ₁ %tp %hK %hi Hσ with H
  imodintro
  imod H with ⟨%hred, %G, HG, HF, %R, HR, H⟩
  imodintro
  isplitr
  · ipureintro
    exact hred
  iintro %e₂ %σ₂ %efs %hstep
  iapply step_progress n tp.length i G R $$ HG HF HR
  iintro HG HW
  imod H $$ %e₂ %σ₂ %efs %hstep with H
  imodintro
  iapply step_fork n (n + 1) tp.length (tp.length + efs.length) _ (Nat.le_succ n)
    (Nat.le_add_right _ _)
  iintro Hforks
  ihave Hforks := (bigSepL_range'_sub (Ψ := fun j => thKids j ∅) tp.length efs.length).mp $$
    Hforks
  ispecialize H $$ HG HW Hforks
  imodintro
  iapply ALC_wand $$ [] H
  iintro H
  unfold mupdFancy
  imod H with H
  imod H with H
  iapply fupd_mupdBase_elim
  imod H with ⟨Hσ, H⟩
  iapply mupd_elim (tp.length + efs.length) length_set_append $$ H Hσ

/-- `lwp_lift_step` over the state interpretation: the history and the interpretation of the
temporal layer are threaded, and no model update is taken around the step. -/
@[lantana_alias lwp_lift_step_si]
theorem lwp_lift_step_si (he : toVal e₁ = none) :
    (∀ (K : Λ.Ctx) (σ₁ : State) (tp : ThreadPool Expr),
      ⌜Language.Context K⌝ → ⌜tp[i]? = some (ctxApply K e₁)⌝ →
      stateInterp σ₁ tp ={E,∅}=∗
        ⌜s.maybeReducible e₁ σ₁⌝ ∗
        ∃ G, thKids i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
          ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr), ⌜primStep e₁ σ₁ e₂ σ₂ efs⌝ ={∅}=∗
            thKids i G -∗ witCreds R -∗
            ([∗list] j ∈ List.range efs.length, thKids (tp.length + j) ∅) -∗
            ALC iprop(|={∅,E}=> stateInterp σ₂ (tp.set i (ctxApply K e₂) ++ efs) ∗
              |={E}=>m (lWP e₂ @ s; i; E {{ Φ }} ∗
                [∗list] j ↦ ef ∈ efs,
                  lWP ef @ s; (tp.length + j); ⊤ {{ liftTerm (tp.length + j) L.forkPost }})))
      ⊢ lWP e₁ @ s; i; E {{ Φ }} := by
  iintro H
  iapply lwp_lift_step he
  iintro %K %h %n %σ₁ %tp %hK %hi Hσ
  iunfold historyTInterp, historyInterp at Hσ
  icases Hσ with ⟨⟨%hh, Ha, Hs⟩, HT⟩
  imod H $$ %K %σ₁ %tp %hK %hi Hs with ⟨%hred, %G, HG, HF, %R, HR, H⟩
  imodintro
  imodintro
  isplitr
  · ipureintro
    exact hred
  iexists G
  iframe HG HF
  iexists R
  iframe HR
  iintro %e₂ %σ₂ %efs %hstep
  imod H $$ %e₂ %σ₂ %efs %hstep with H
  imodintro
  iintro HG HW Hforks
  ispecialize H $$ HG HW Hforks
  iapply ALC_wand $$ [Ha HT] H
  iintro H
  unfold mupdFancy
  imodintro
  imodintro
  imod H with ⟨Hs, H⟩
  imod histAuth_append h [(σ₂, tp.set i (ctxApply K e₂) ++ efs)] $$ Ha with Ha
  imodintro
  iunfold historyTInterp, historyInterp
  iframe Hs Ha HT H
  ipureintro
  simp [hh.1]

@[lantana_alias lwp_lift_stuck]
theorem lwp_lift_stuck (he : toVal e = none) :
    (∀ (K : Λ.Ctx) (σ : State) (tp : ThreadPool Expr),
      ⌜Language.Context K⌝ → ⌜tp[i]? = some (ctxApply K e)⌝ →
      stateInterp σ tp ={E,∅}=∗ ⌜Language.Stuck e σ⌝)
      ⊢ lWP e @ i; E ?{{ Φ }} := by
  iintro H
  rw [lwp_unfold.to_eq]
  simp only [lwpPre, he]
  unfold lwpStep
  iintro %K %h %n %σ %tp %hK %hi Hσ
  iunfold historyTInterp, historyInterp at Hσ
  icases Hσ with ⟨⟨-, -, Hs⟩, -⟩
  imod H $$ %K %σ %tp %hK %hi Hs with %hstuck
  imodintro
  imodintro
  isplitr
  · ipureintro
    trivial
  iintro %e₂ %σ₂ %efs %hstep
  exact (hstuck.2 _ _ _ hstep).elim

/-! ## Derived lifting lemmas -/

/-- A pure step that forks no thread. -/
@[lantana_alias lwp_lift_pure_step_no_fork]
theorem lwp_lift_pure_step_no_fork [Inhabited State] {ς : ThreadId → Expr → IProp GF}
    [hς : PureExecSI ς i] (E' : CoPset)
    (hsafe : ∀ σ₁, s.pureSafe e₁ σ₁)
    (hstep : ∀ σ₁ e₂ σ₂ efs, primStep e₁ σ₁ e₂ σ₂ efs → σ₂ = σ₁ ∧ efs = []) :
    (|={E,E'}=> ς i e₁ ∗ ∃ G, thKids i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
      ∀ (σ : State) (e₂ : Expr), ⌜primStep e₁ σ e₂ σ []⌝ -∗ ς i e₂ -∗ thKids i G -∗ witCreds R -∗
        ALC iprop(|={E',E}=> |={E}=>m lWP e₂ @ s; i; E {{ Φ }}))
      ⊢ lWP e₁ @ s; i; E {{ Φ }} := by
  have hnv : toVal e₁ = none := Stuckness.pureSafe.toVal_eq_none (hsafe default)
  iintro H
  iapply lwp_lift_step_si hnv
  iintro %K %σ₁ %tp %hK %hi Hs
  imod H with ⟨Hc, %G, HG, HF, %R, HR, H⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact Stuckness.pureSafe.maybeReducible (hsafe σ₁)
  iexists G
  iframe HG HF
  iexists R
  iframe HR
  iintro %e₂ %σ₂ %efs %hst
  obtain ⟨rfl, rfl⟩ := hstep _ _ _ _ hst
  imod hς.pureExecSI hK hi hst $$ [Hc Hs] with ⟨Hc, Hs⟩
  · iframe
  imodintro
  iintro HG HW -
  ispecialize H $$ %_ %e₂ %hst Hc HG HW
  iapply ALC_wand $$ [Hclose Hs] H
  iintro H
  imod Hclose
  imod H with H
  imodintro
  rw [List.append_nil]
  iframe Hs
  imod H
  imodintro
  iframe H
  iempintro

@[lantana_alias lwp_lift_pure_stuck]
theorem lwp_lift_pure_stuck [Inhabited State] (hstuck : ∀ σ, Language.Stuck e σ) :
    iprop(True) ⊢ lWP e @ i; E ?{{ Φ }} := by
  iintro -
  iapply lwp_lift_stuck (hstuck default).1
  iintro %K %σ %tp %hK %hi -
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro -
  ipureintro
  exact hstuck σ

/-- An atomic step: the thread reaches a value. -/
@[lantana_alias lwp_lift_atomic_step]
theorem lwp_lift_atomic_step (he : toVal e₁ = none) :
    (∀ (K : Λ.Ctx) (σ₁ : State) (tp : ThreadPool Expr),
      ⌜Language.Context K⌝ → ⌜tp[i]? = some (ctxApply K e₁)⌝ →
      stateInterp σ₁ tp ={E₁,E₂}=∗
        ⌜s.maybeReducible e₁ σ₁⌝ ∗
        ∃ G, thKids i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
          ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr), ⌜primStep e₁ σ₁ e₂ σ₂ efs⌝ ={∅}=∗
            thKids i G -∗ witCreds R -∗
            ([∗list] j ∈ List.range efs.length, thKids (tp.length + j) ∅) -∗
            ALC iprop(|={E₂,E₁}=> stateInterp σ₂ (tp.set i (ctxApply K e₂) ++ efs) ∗
              |={E₁}=>m ((∃ v, ⌜toVal e₂ = some v⌝ ∗ Φ v) ∗
                [∗list] j ↦ ef ∈ efs,
                  lWP ef @ s; (tp.length + j); ⊤ {{ liftTerm (tp.length + j) L.forkPost }})))
      ⊢ lWP e₁ @ s; i; E₁ {{ Φ }} := by
  iintro H
  iapply lwp_lift_step_si he
  iintro %K %σ₁ %tp %hK %hi Hs
  imod H $$ %K %σ₁ %tp %hK %hi Hs with ⟨%hred, %G, HG, HF, %R, HR, H⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact hred
  iexists G
  iframe HG HF
  iexists R
  iframe HR
  iintro %e₂ %σ₂ %efs %hstep
  imod H $$ %e₂ %σ₂ %efs %hstep with H
  imodintro
  iintro HG HW Hforks
  ispecialize H $$ HG HW Hforks
  iapply ALC_wand $$ [Hclose] H
  iintro H
  imod Hclose
  imod H with ⟨Hs, H⟩
  imodintro
  iframe Hs
  imod H with ⟨⟨%v, %hv, HΦ⟩, Hefs⟩
  imodintro
  iframe Hefs
  iapply (lwp_value_mupd_of_toVal hv).mpr
  iapply mupd_intro $$ HΦ

/-- A pure deterministic step that forks no thread. -/
@[lantana_alias lwp_lift_pure_det_step_no_fork]
theorem lwp_lift_pure_det_step_no_fork [Inhabited State] {ς : ThreadId → Expr → IProp GF}
    [PureExecSI ς i] (E' : CoPset) {e₂ : Expr}
    (hsafe : ∀ σ₁, s.pureSafe e₁ σ₁)
    (hdet : ∀ σ₁ e₂' σ₂ efs, primStep e₁ σ₁ e₂' σ₂ efs → σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs = []) :
    (|={E,E'}=> ς i e₁ ∗ ∃ G, thKids i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
      (ς i e₂ -∗ thKids i G -∗ witCreds R -∗
        ALC iprop(|={E',E}=> |={E}=>m lWP e₂ @ s; i; E {{ Φ }})))
      ⊢ lWP e₁ @ s; i; E {{ Φ }} := by
  iintro H
  iapply lwp_lift_pure_step_no_fork (ς := ς) E' hsafe
    (fun _ _ _ _ h => ⟨(hdet _ _ _ _ h).1, (hdet _ _ _ _ h).2.2⟩)
  imod H with ⟨Hc, %G, HG, HF, %R, HR, H⟩
  imodintro
  iframe Hc
  iexists G
  iframe HG HF
  iexists R
  iframe HR
  iintro %σ %e₂' %hst Hc HG HW
  obtain ⟨-, rfl, -⟩ := hdet _ _ _ _ hst
  iapply H $$ Hc HG HW

/-- `n` pure steps, each of which takes one unit of fuel of the children `G` of the thread and
the witness layers `R`, and gives back their credits and `£ₒ o`. -/
@[lantana_alias lwp_pure_step]
theorem lwp_pure_step [Inhabited State] {ς : ThreadId → Expr → IProp GF} [PureExecSI ς i]
    (n : Nat) (o : Fuel) (E' : CoPset) {φ : Prop} {e₂ : Expr}
    [hex : Language.PureExec φ n e₁ e₂] (hφ : φ) :
    ς i e₁ ∗ Nat.repeat (fun P => iprop(|={E,E'}=>
        ∃ G, thKids i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
          (thKids i G -∗ witCreds R -∗ ALC iprop(£ₒ o ={E',E}=∗ |={E}=>m P)))) n
      iprop(ς i e₂ -∗ |={E}=>m lWP e₂ @ s; i; E {{ Φ }})
      ⊢ lWP e₁ @ s; i; E {{ Φ }} := by
  have hexec := hex.pureExec hφ
  induction hexec using Relation.Iterate.head_induction_on with
  | rfl =>
    simp only [Nat.repeat]
    iintro ⟨Hc, H⟩
    iapply mupd_lwp
    iapply H $$ Hc
  | @head n e₁ c hpure _ IH =>
    simp only [Nat.repeat]
    iintro ⟨Hc, H⟩
    iapply lwp_lift_pure_det_step_no_fork (ς := ς) E' (e₂ := c)
      (Stuckness.pureSafe_of_pureStep hpure) (fun _ _ _ _ h => hpure.det h)
    imod H with ⟨%G, HG, HF, %R, HR, H⟩
    imodintro
    iframe Hc
    iexists G
    iframe HG HF
    iexists R
    iframe HR
    iintro Hc HG HW
    ispecialize H $$ HG HW
    iapply (ALC_credits o).mpr
    iapply ALC_wand $$ [Hc] H
    iintro H Ho
    imod H $$ Ho with H
    imodintro
    imod H
    imodintro
    iapply IH
    iframe

/-! ## Several pure steps at once -/

instance witLayers_persistent (R : Oids) : Persistent (witLayers (GF := GF) R) := by
  unfold witLayers
  infer_instance

/-- `m + 1` units of fuel are `m` units and one unit. -/
theorem oblFuels_succ (G : Oids) (m : Nat) :
    oblFuels (GF := GF) G ((m + 1 : Nat) : Measure) ⊢ oblFuels G (m : Measure) ∗ oblFuels G 1 := by
  unfold oblFuels
  refine (BigSepS.bigSepS_mono fun _ => ?_).trans BigSepS.bigSepS_sep.mp
  iintro ⟨%ℓ, H⟩
  ihave H := (Obl.fuel_eq _ (ℓ := ℓ) (μ₂ := (m : Measure) + 1)
    (by rw [Measure.rep_nat_add, Measure.rep_add]; rfl)).mp $$ H
  icases (Obl.fuel_add _ ℓ _ _).mp $$ H with ⟨H1, H2⟩
  isplitl [H1]
  · iexists ℓ
    iexact H1
  · iexists ℓ
    iexact H2

/-- The credits of `m` steps and of one more step are the credits of `m + 1` steps. -/
theorem witCreds_succ (R : Oids) (m : Nat) :
    ([∗set] r ∈ R, Wit.cred (GF := GF) r (m : Fuel) ∨ Obl.discharged r) ∗ witCreds R ⊢
      [∗set] r ∈ R, Wit.cred r ((m + 1 : Nat) : Fuel) ∨ Obl.discharged r := by
  unfold witCreds
  refine BigSepS.bigSepS_sep.mpr.trans (BigSepS.bigSepS_mono fun _ => ?_)
  iintro ⟨H1 | #H1, H2 | #H2⟩
  · ileft
    rw [show ((m + 1 : Nat) : Fuel) = (m : Fuel) +ₕ 1 from (nadd_ofNat m 1).symm]
    iapply (Wit.cred_split _ _ _).mpr
    iframe
  · iright
    iexact H2
  · iright
    iexact H1
  · iright
    iexact H1

/-- The later credits of `m` steps and of one more step are those of `m + 1` steps. -/
theorem credits_succ (o : Fuel) (m : Nat) :
    £ₒ (o ×ⱼ (m : Fuel)) ∗ £ₒ o ⊢@{IProp GF} £ₒ (o ×ⱼ ((m + 1 : Nat) : Fuel)) := by
  rw [show ((m + 1 : Nat) : Fuel) = succ (m : Fuel) from rfl, jmul_succ]
  iintro ⟨H1, H2⟩
  iapply tlc_split.mpr
  iframe

/-- The iterated premise of `lwp_pure_step` from the fuel of `m + 1` steps. -/
private theorem pure_step_simple_aux (o : Fuel) (G R : Oids) (X : IProp GF) (m : Nat) :
    thKids i G ∗ oblFuels G ((m + 1 : Nat) : Measure) ∗ witLayers R ∗
      (thKids i G -∗ ([∗set] r ∈ R, Wit.cred r ((m + 1 : Nat) : Fuel) ∨ Obl.discharged r) -∗
        £ₒ (o ×ⱼ ((m + 1 : Nat) : Fuel)) -∗ X)
      ⊢ Nat.repeat (fun P => iprop(|={E,E}=>
          ∃ G, thKids i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
            (thKids i G -∗ witCreds R -∗ ALC iprop(£ₒ o ={E,E}=∗ |={E}=>m P)))) (m + 1) X := by
  induction m generalizing X with
  | zero =>
    simp only [Nat.repeat]
    rw [show ((0 + 1 : Nat) : Fuel) = 1 from rfl, jmul_one]
    iintro ⟨HG, HF, #HR, H⟩
    imodintro
    iexists G
    iframe HG HF
    iexists R
    iframe HR
    iintro HG HW
    imodintro
    iintro Ho
    imodintro
    imodintro
    iunfold witCreds at HW
    iapply H $$ HG HW Ho
  | succ m IH =>
    rw [show m + 1 + 1 = (m + 1) + 1 from rfl]
    simp only [Nat.repeat] at IH ⊢
    iintro ⟨HG, HF, #HR, H⟩
    icases oblFuels_succ G (m + 1) $$ HF with ⟨HF, HF1⟩
    imodintro
    iexists G
    iframe HG HF1
    iexists R
    iframe HR
    iintro HG HW1
    imodintro
    iintro Ho
    imodintro
    imodintro
    iapply IH
    iframe HG HF HR
    iintro HG HW Hom
    iapply H $$ HG [HW HW1] [Hom Ho]
    · iapply witCreds_succ R (m + 1)
      iframe
    · iapply credits_succ o (m + 1)
      iframe

/-- `n > 0` pure steps paid at once: `n` units of fuel of each child `G` of the thread, the
witness layers `R`; they give back `n` credits to each witness of `R` and `£ₒ (o ×ⱼ n)` (the
rules STEP-PURE, STEP-PURE-LC and STEP-PURE-WIT of the paper in one). -/
@[lantana_alias lwp_pure_step_simple]
theorem lwp_pure_step_simple [Inhabited State] {ς : ThreadId → Expr → IProp GF} [PureExecSI ς i]
    (n : Nat) (hn : 0 < n) (G R : Oids) (o : Fuel) {φ : Prop} {e₂ : Expr}
    [Language.PureExec φ n e₁ e₂] (hφ : φ) :
    ς i e₁ ∗ thKids i G ∗ oblFuels G (n : Measure) ∗ witLayers R ∗
      (ς i e₂ -∗ thKids i G -∗ ([∗set] r ∈ R, Wit.cred r (n : Fuel) ∨ Obl.discharged r) -∗
        £ₒ (o ×ⱼ (n : Fuel)) -∗ |={E}=>m lWP e₂ @ s; i; E {{ Φ }})
      ⊢ lWP e₁ @ s; i; E {{ Φ }} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  iintro ⟨Hc, HG, HF, HR, H⟩
  iapply lwp_pure_step (ς := ς) (m + 1) o E hφ
  iframe Hc
  iapply pure_step_simple_aux o G R _ m
  iframe HG HF HR
  iintro HG HW Ho Hc
  iapply H $$ Hc HG HW Ho

end Lifting

end Lantana
