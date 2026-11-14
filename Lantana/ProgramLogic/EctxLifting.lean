/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

Based on Iris-Lean's `Iris.ProgramLogic.EctxLifting`, whose header reads:
  Copyright (c) The Iris-Lean Contributors
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Fernando Leal
Modified by the Lantana-Lean Contributors; the module documentation describes the changes.
-/
module

public import Lantana.ProgramLogic.Lifting

/-! # Lifting lemmas for languages with evaluation contexts

Rocq `lantana/program_logic/ectx_lifting.v`, after Iris-Lean's `Iris.ProgramLogic.EctxLifting`:
the lifting lemmas of `Lantana.ProgramLogic.Lifting` with base steps and base reducibility, for
the language of an Iris-Lean `EctxLanguage`.  Every evaluation context is a context of that
language (`EctxLanguage.instContextFill`), so the lemmas quantify over `K : Ectx` without the
hypothesis `Language.Context (fill K)`.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode
open Iris.ProgramLogic (toVal BaseStep EctxLanguage)
open Iris.ProgramLogic.BaseStep (baseStep)
open Iris.ProgramLogic.EvContext (fill)

section EctxLifting

variable {Expr State Obs Val Ectx : Type} {GF : BundledGFunctors}
variable [Λ : EctxLanguage Expr Ectx State Obs Val] [ModelGS GF]
variable [L : LantanaGS Expr State Obs Val GF] [TemporalInterp Expr State GF]
variable {s : Stuckness} {i : ThreadId} {E E₁ E₂ : CoPset} {e e₁ : Expr} {Φ : Val → IProp GF}

/-- `lwp_bind` at an evaluation context. -/
theorem lwp_bind_fill (K : Ectx) :
    lWP e @ s; i; E {{ v, lWP (fill K ((v : Val) : Expr)) @ s; i; E {{ Φ }} }} ⊢
      lWP (fill K e) @ s; i; E {{ Φ }} :=
  lwp_bind (Expr := Expr) K

/-- A step of a base redex, over the state interpretation. -/
@[lantana_alias lwp_lift_base_step]
theorem lwp_lift_base_step (he : toVal e₁ = none) :
    (∀ (K : Ectx) (σ₁ : State) (tp : ThreadPool Expr), ⌜tp[i]? = some (fill K e₁)⌝ →
      stateInterp σ₁ tp ={E,∅}=∗
        ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
        ∃ G, thCarriers i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
          ∀ (obs : List Obs) (e₂ : Expr) (σ₂ : State) (efs : List Expr),
            ⌜baseStep (e₁, σ₁) obs (e₂, σ₂, efs)⌝ ={∅}=∗
            thCarriers i G -∗ witCreds R -∗
            ([∗list] j ∈ List.range efs.length,
              thActive (tp.length + j) ∗ thKids (tp.length + j) ∅ ∗ thCarriers (tp.length + j) ∅) -∗
            ALC iprop(|={∅,E}=> stateInterp σ₂ (tp.set i (fill K e₂) ++ efs) ∗
              |={E}=>m (lWP e₂ @ s; i; E {{ Φ }} ∗
                [∗list] j ↦ ef ∈ efs,
                  lWP ef @ s; (tp.length + j); ⊤ {{ liftTerm (tp.length + j) L.forkPost }})))
      ⊢ lWP e₁ @ s; i; E {{ Φ }} := by
  iintro H
  iapply lwp_lift_step_si he
  iintro %K %σ₁ %tp %hK %hi Hs
  imod H $$ %K %σ₁ %tp %hi Hs with ⟨%hred, H⟩
  imodintro
  isplitr
  · ipureintro
    cases s
    · exact EctxLanguage.primStep_reducible_of_baseStep_reducible hred
    · trivial
  icases H with ⟨%G, HG, HF, %R, HR, H⟩
  iexists G
  iframe HG HF
  iexists R
  iframe HR
  iintro %obs %e₂ %σ₂ %efs %hstep
  iapply H $$ %obs %e₂ %σ₂ %efs
    %(EctxLanguage.baseStep_of_primStep_of_baseStep_reducible hred hstep)

@[lantana_alias lwp_lift_base_stuck]
theorem lwp_lift_base_stuck (he : toVal e = none) (hsub : EctxLanguage.SubredexesAreValues e) :
    (∀ (K : Ectx) (σ : State) (tp : ThreadPool Expr), ⌜tp[i]? = some (fill K e)⌝ →
      stateInterp σ tp ={E,∅}=∗ ⌜BaseStep.Stuck (e, σ)⌝)
      ⊢ lWP e @ i; E ?{{ Φ }} := by
  iintro H
  iapply lwp_lift_stuck he
  iintro %K %σ %tp %hK %hi Hs
  imod H $$ %K %σ %tp %hi Hs with %hstuck
  imodintro
  ipureintro
  exact EctxLanguage.primStep_stuck_of_baseStep_stuck hstuck hsub

@[lantana_alias lwp_lift_pure_base_stuck]
theorem lwp_lift_pure_base_stuck (he : toVal e = none) (hsub : EctxLanguage.SubredexesAreValues e)
    (hstuck : ∀ σ, BaseStep.Stuck (e, σ)) : iprop(True) ⊢ lWP e @ i; E ?{{ Φ }} := by
  iintro -
  iapply lwp_lift_base_stuck he hsub
  iintro %K %σ %tp %hi -
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro -
  ipureintro
  exact hstuck σ

/-- An atomic step of a base redex: the thread reaches a value. -/
@[lantana_alias lwp_lift_atomic_base_step]
theorem lwp_lift_atomic_base_step (he : toVal e₁ = none) :
    (∀ (K : Ectx) (σ₁ : State) (tp : ThreadPool Expr), ⌜tp[i]? = some (fill K e₁)⌝ →
      stateInterp σ₁ tp ={E₁,E₂}=∗
        ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
        ∃ G, thCarriers i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
          ∀ (obs : List Obs) (e₂ : Expr) (σ₂ : State) (efs : List Expr),
            ⌜baseStep (e₁, σ₁) obs (e₂, σ₂, efs)⌝ ={∅}=∗
            thCarriers i G -∗ witCreds R -∗
            ([∗list] j ∈ List.range efs.length,
              thActive (tp.length + j) ∗ thKids (tp.length + j) ∅ ∗ thCarriers (tp.length + j) ∅) -∗
            ALC iprop(|={E₂,E₁}=> stateInterp σ₂ (tp.set i (fill K e₂) ++ efs) ∗
              |={E₁}=>m ((∃ v, ⌜toVal e₂ = some v⌝ ∗ Φ v) ∗
                [∗list] j ↦ ef ∈ efs,
                  lWP ef @ s; (tp.length + j); ⊤ {{ liftTerm (tp.length + j) L.forkPost }})))
      ⊢ lWP e₁ @ s; i; E₁ {{ Φ }} := by
  iintro H
  iapply lwp_lift_atomic_step he
  iintro %K %σ₁ %tp %hK %hi Hs
  imod H $$ %K %σ₁ %tp %hi Hs with ⟨%hred, H⟩
  imodintro
  isplitr
  · ipureintro
    cases s
    · exact EctxLanguage.primStep_reducible_of_baseStep_reducible hred
    · trivial
  icases H with ⟨%G, HG, HF, %R, HR, H⟩
  iexists G
  iframe HG HF
  iexists R
  iframe HR
  iintro %obs %e₂ %σ₂ %efs %hstep
  iapply H $$ %obs %e₂ %σ₂ %efs
    %(EctxLanguage.baseStep_of_primStep_of_baseStep_reducible hred hstep)

/-- An atomic step of a base redex that forks no thread. -/
@[lantana_alias lwp_lift_atomic_base_step_no_fork]
theorem lwp_lift_atomic_base_step_no_fork (he : toVal e₁ = none) :
    (∀ (K : Ectx) (σ₁ : State) (tp : ThreadPool Expr), ⌜tp[i]? = some (fill K e₁)⌝ →
      stateInterp σ₁ tp ={E₁,E₂}=∗
        ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
        ∃ G, thCarriers i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
          ∀ (obs : List Obs) (e₂ : Expr) (σ₂ : State) (efs : List Expr),
            ⌜baseStep (e₁, σ₁) obs (e₂, σ₂, efs)⌝ ={∅}=∗
            thCarriers i G -∗ witCreds R -∗
            ALC iprop(|={E₂,E₁}=> ⌜efs = []⌝ ∗ stateInterp σ₂ (tp.set i (fill K e₂)) ∗
              ∃ v, ⌜toVal e₂ = some v⌝ ∗ |={E₁}=>m Φ v))
      ⊢ lWP e₁ @ s; i; E₁ {{ Φ }} := by
  iintro H
  iapply lwp_lift_atomic_base_step he
  iintro %K %σ₁ %tp %hi Hs
  imod H $$ %K %σ₁ %tp %hi Hs with ⟨%hred, %G, HG, HF, %R, HR, H⟩
  imodintro
  isplitr
  · ipureintro
    exact hred
  iexists G
  iframe HG HF
  iexists R
  iframe HR
  iintro %obs %e₂ %σ₂ %efs %hstep
  imod H $$ %obs %e₂ %σ₂ %efs %hstep with H
  imodintro
  iintro HG HW -
  ispecialize H $$ HG HW
  iapply ALC_wand $$ [] H
  iintro H
  imod H with ⟨%hefs, Hs, %v, %hv, HΦ⟩
  subst hefs
  rw [List.append_nil]
  imodintro
  iframe Hs
  imod HΦ
  imodintro
  isplitl
  · iexists v
    iframe HΦ
    ipureintro
    exact hv
  · iempintro

/-- A pure deterministic base step that forks no thread. -/
@[lantana_alias lwp_lift_pure_det_base_step_no_fork]
theorem lwp_lift_pure_det_base_step_no_fork [Inhabited State] {ς : ThreadId → Expr → IProp GF}
    [PureExecSI ς i] (E' : CoPset) {e₂ : Expr} (he : toVal e₁ = none)
    (hsafe : ∀ σ₁, BaseStep.Reducible (e₁, σ₁))
    (hdet : ∀ σ₁ obs e₂' σ₂ efs, baseStep (e₁, σ₁) obs (e₂', σ₂, efs) →
      σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs = []) :
    (|={E,E'}=> ς i e₁ ∗ ∃ G, thCarriers i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
      (ς i e₂ -∗ thCarriers i G -∗ witCreds R -∗
        ALC iprop(|={E',E}=> |={E}=>m lWP e₂ @ s; i; E {{ Φ }})))
      ⊢ lWP e₁ @ s; i; E {{ Φ }} :=
  lwp_lift_pure_det_step_no_fork (ς := ς) E'
    (fun σ₁ => by
      cases s
      · exact EctxLanguage.primStep_reducible_of_baseStep_reducible (hsafe σ₁)
      · exact he)
    (fun σ₁ _ _ _ _ h =>
      hdet _ _ _ _ _ (EctxLanguage.baseStep_of_primStep_of_baseStep_reducible (hsafe σ₁) h))

end EctxLifting

end Lantana
