/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.ProgramLogic.EctxLanguage
public import Lantana.ProgramLogic.Lifting

/-! # Lifting lemmas for languages with evaluation contexts

Rocq `lantana/program_logic/ectx_lifting.v`, after Iris-Lean's `Iris.ProgramLogic.EctxLifting`:
the lifting lemmas of `Lantana.ProgramLogic.Lifting` stated with base steps and base
reducibility, for the language of an `EctxLanguage`. The contexts of that language are the
evaluation contexts `Ectx`, all of which are contexts (`instContextFill`): the lemmas quantify
over `K : Ectx` with `fill K`, without the hypothesis `Language.Context K`.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode
open Iris.ProgramLogic (toVal)
open EctxLanguage

section EctxLifting

variable {Expr : Type} {State : Type} {Val : Type} {Ectx : Type} {GF : BundledGFunctors}
variable [Λ : EctxLanguage Expr State Val Ectx] [ModelGS GF]
variable [L : LantanaGS Expr State Val GF] [TemporalInterp Expr State GF]
variable {s : Stuckness} {i : ThreadId} {E E₁ E₂ : CoPset} {e e₁ : Expr} {Φ : Val → IProp GF}

/-- `lwp_bind` at an evaluation context. -/
theorem lwp_bind_fill (K : Ectx) :
    lWP e @ s; i; E {{ fun v : Val => lWP (fill K (v : Expr)) @ s; i; E {{ Φ }} }} ⊢
      lWP (fill K e) @ s; i; E {{ Φ }} :=
  lwp_bind (Expr := Expr) K

/-- A step of a base redex, over the state interpretation. -/
@[lantana_alias lwp_lift_base_step]
theorem lwp_lift_base_step (he : toVal e₁ = none) :
    (∀ (K : Ectx) (σ₁ : State) (tp : ThreadPool Expr), ⌜tp[i]? = some (fill K e₁)⌝ →
      stateInterp σ₁ tp ={E,∅}=∗
        ⌜BaseReducible e₁ σ₁⌝ ∗
        ∃ G, thKids i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
          ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr), ⌜baseStep e₁ σ₁ e₂ σ₂ efs⌝ ={∅}=∗
            thKids i G -∗ witCreds R -∗
            ([∗list] j ∈ List.range efs.length, thKids (tp.length + j) ∅) -∗
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
    · exact reducible_of_baseReducible hred
    · trivial
  icases H with ⟨%G, HG, HF, %R, HR, H⟩
  iexists G
  iframe HG HF
  iexists R
  iframe HR
  iintro %e₂ %σ₂ %efs %hstep
  iapply H $$ %e₂ %σ₂ %efs %(baseStep_of_primStep_of_baseReducible hred hstep)

@[lantana_alias lwp_lift_base_stuck]
theorem lwp_lift_base_stuck (he : toVal e = none) (hsub : SubredexesAreValues e) :
    (∀ (K : Ectx) (σ : State) (tp : ThreadPool Expr), ⌜tp[i]? = some (fill K e)⌝ →
      stateInterp σ tp ={E,∅}=∗ ⌜BaseStuck e σ⌝)
      ⊢ lWP e @ i; E ?{{ Φ }} := by
  iintro H
  iapply lwp_lift_stuck he
  iintro %K %σ %tp %hK %hi Hs
  imod H $$ %K %σ %tp %hi Hs with %hstuck
  imodintro
  ipureintro
  exact stuck_of_baseStuck hstuck hsub

@[lantana_alias lwp_lift_pure_base_stuck]
theorem lwp_lift_pure_base_stuck (he : toVal e = none) (hsub : SubredexesAreValues e)
    (hstuck : ∀ σ, BaseStuck e σ) : iprop(True) ⊢ lWP e @ i; E ?{{ Φ }} := by
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
        ⌜BaseReducible e₁ σ₁⌝ ∗
        ∃ G, thKids i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
          ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr), ⌜baseStep e₁ σ₁ e₂ σ₂ efs⌝ ={∅}=∗
            thKids i G -∗ witCreds R -∗
            ([∗list] j ∈ List.range efs.length, thKids (tp.length + j) ∅) -∗
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
    · exact reducible_of_baseReducible hred
    · trivial
  icases H with ⟨%G, HG, HF, %R, HR, H⟩
  iexists G
  iframe HG HF
  iexists R
  iframe HR
  iintro %e₂ %σ₂ %efs %hstep
  iapply H $$ %e₂ %σ₂ %efs %(baseStep_of_primStep_of_baseReducible hred hstep)

/-- An atomic step of a base redex that forks no thread. -/
@[lantana_alias lwp_lift_atomic_base_step_no_fork]
theorem lwp_lift_atomic_base_step_no_fork (he : toVal e₁ = none) :
    (∀ (K : Ectx) (σ₁ : State) (tp : ThreadPool Expr), ⌜tp[i]? = some (fill K e₁)⌝ →
      stateInterp σ₁ tp ={E₁,E₂}=∗
        ⌜BaseReducible e₁ σ₁⌝ ∗
        ∃ G, thKids i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
          ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr), ⌜baseStep e₁ σ₁ e₂ σ₂ efs⌝ ={∅}=∗
            thKids i G -∗ witCreds R -∗
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
  iintro %e₂ %σ₂ %efs %hstep
  imod H $$ %e₂ %σ₂ %efs %hstep with H
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
    (hsafe : ∀ σ₁, BaseReducible e₁ σ₁)
    (hdet : ∀ σ₁ e₂' σ₂ efs, baseStep e₁ σ₁ e₂' σ₂ efs → σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs = []) :
    (|={E,E'}=> ς i e₁ ∗ ∃ G, thKids i G ∗ oblFuels G 1 ∗ ∃ R, witLayers R ∗
      (ς i e₂ -∗ thKids i G -∗ witCreds R -∗
        ALC iprop(|={E',E}=> |={E}=>m lWP e₂ @ s; i; E {{ Φ }})))
      ⊢ lWP e₁ @ s; i; E {{ Φ }} :=
  lwp_lift_pure_det_step_no_fork (ς := ς) E'
    (fun σ₁ => by
      cases s
      · exact reducible_of_baseReducible (hsafe σ₁)
      · exact he)
    (fun σ₁ _ _ _ h => hdet _ _ _ _ (baseStep_of_primStep_of_baseReducible (hsafe σ₁) h))

end EctxLifting

end Lantana
