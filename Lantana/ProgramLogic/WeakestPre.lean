/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

Based on Iris-Lean's `Iris.ProgramLogic.TotalWeakestPre` and `Iris.ProgramLogic.WeakestPre`,
whose headers read:
  Copyright (c) The Iris-Lean Contributors
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Marcelo Fornet, Zongyuan Liu (`TotalWeakestPre`); Fernando Leal (`WeakestPre`)
Modified by the Lantana-Lean Contributors; the module documentation describes the changes.
-/
module

public import Iris.BI.Lib.Fixpoint
public import Lantana.BaseLogic.LaterCredits
public import Lantana.ProgramLogic.OblForestRules
public import Lantana.ProgramLogic.Notation

/-! # The liveness weakest precondition `lWP`

Rocq `lantana/program_logic/weakestpre.v`: `lWP e @ s; i; E {{ Φ }}` is the least fixpoint of
one step of the program logic (`lwpStep`): a model update before the step, the progress and
physical rounds of the step, the allocation of later credits, a model update after it. The
structure follows Iris-Lean's total weakest precondition (`Iris.ProgramLogic.TotalWeakestPre`),
which is also a `bi_least_fixpoint`.

Thread ids are positions in the pool (D14): a step of thread `i` running `ctxApply K e₁` in the
pool `tp` leads to the pool `tp.set i (ctxApply K e₂) ++ efs`, and the forked threads get the ids
`tp.length, tp.length + 1, …`. The context `K` ranges over the contexts `Language.Ctx` of the
language (D31), which for HeapLang are syntactic: the thread-expression token then determines
`K`.

Induction (`lwp_ind_strong`, `lwp_ind`) needs no non-expansiveness of the predicate: it is
done on the predicate's closure under internal equality. The file also derives the rules of the
model updates `|=[n,tc]=>m P` and `|={E₁,E₂}=>m P` that the program logic uses (Rocq
`mupd.v`, `obl_forest_rules.v`), with their proof-mode instances.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode
open Iris.ProgramLogic (toVal)


/-- The ghost state of the program logic: the temporal layer, the state interpretation, and
the postcondition of forked threads (`True` for HeapLang). -/
@[lantana_alias lantanaGS]
class LantanaGS (Expr : Type) (State : Type) (Val : outParam Type) (GF : BundledGFunctors)
    [Language Expr State Val] extends TemporalGS Expr State GF, StateInterp Expr State GF where
  /-- The postcondition of a forked thread. -/
  forkPost : ThreadId → Val → IProp GF

section Lwp

variable {Expr : Type} {State : Type} {Val : Type} {GF : BundledGFunctors}
variable [Λ : Language Expr State Val] [ModelGS GF]
variable [L : LantanaGS Expr State Val GF] [TemporalInterp Expr State GF]

/-- One step of `lWP` for thread `i` running `ctxApply K e₁`, for every evaluation context `K` of
the language: a model update before the step (it may
discharge an until), the progress round `mprog` of `i` and the physical round `mphys` of the
step, the allocation of later credits `ALC`, and a model update after it; `ν e₂ len efs`
holds after a step to `e₂` that forks `efs` with ids from `len` (the old pool length). -/
@[lantana_alias lwp_step]
def lwpStep (s : Stuckness) (i : ThreadId) (E : CoPset) (e₁ : Expr)
    (ν : Expr → Nat → List Expr → IProp GF) : IProp GF :=
  iprop(∀ (K : Λ.Ctx) (h : List (HistEntry Expr State)) (n : Nat) (σ₁ : State)
    (tp : ThreadPool Expr),
    ⌜Language.Context K⌝ → ⌜tp[i]? = some (ctxApply K e₁)⌝ →
    historyTInterp h n σ₁ tp ={E,∅}=∗
    |=[n, tp.length]=>m
    ⌜s.maybeReducible e₁ σ₁⌝ ∗
    ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr), ⌜primStep e₁ σ₁ e₂ σ₂ efs⌝ -∗
      mprog n tp.length i
        (mphys n (n + 1) tp.length (tp.length + efs.length)
          (ALC (|=[n + 1, tp.length + efs.length]=>m |={∅,E}=>
            historyTInterp (h ++ [(σ₂, tp.set i (ctxApply K e₂) ++ efs)]) (n + 1) σ₂
              (tp.set i (ctxApply K e₂) ++ efs) ∗
            ν e₂ tp.length efs))))

@[lantana_alias lwp_step_mono]
theorem lwpStep_mono {s : Stuckness} {i : ThreadId} {E : CoPset} {e₁ : Expr}
    {ν₁ ν₂ : Expr → Nat → List Expr → IProp GF} :
    (∀ e₂ len efs, ν₁ e₂ len efs -∗ ν₂ e₂ len efs) ⊢
      lwpStep s i E e₁ ν₁ -∗ lwpStep s i E e₁ ν₂ := by
  unfold lwpStep
  iintro Hν H %K %h %n %σ₁ %tp %hK %hi Hσ
  imod H $$ %K %h %n %σ₁ %tp %hK %hi Hσ with H
  imodintro
  imod H with ⟨%hred, H⟩
  imodintro
  isplitr
  · ipureintro
    exact hred
  iintro %e₂ %σ₂ %efs %hstep
  ispecialize H $$ %e₂ %σ₂ %efs %hstep
  iapply mprog_wand $$ [Hν] H
  iintro H
  iapply mphys_wand $$ [Hν] H
  iintro H
  iapply ALC_wand $$ [Hν] H
  iintro H
  iapply mupdBase_wand $$ [Hν] H
  iintro H
  imod H with ⟨Hσ, H⟩
  imodintro
  iframe Hσ
  iapply Hν $$ H

theorem lwpStep_ne {s : Stuckness} {i : ThreadId} {E : CoPset} {e₁ : Expr} {n : SI}
    {ν₁ ν₂ : Expr → Nat → List Expr → IProp GF}
    (h : ∀ e₂ len efs, ν₁ e₂ len efs ≡{n}≡ ν₂ e₂ len efs) :
    lwpStep s i E e₁ ν₁ ≡{n}≡ lwpStep s i E e₁ ν₂ := by
  unfold lwpStep
  refine forall_ne fun K => forall_ne fun _ => forall_ne fun _ => forall_ne fun _ =>
    forall_ne fun tp => imp_ne.ne .rfl <| imp_ne.ne .rfl <| wand_ne.ne .rfl <| fupd_ne.ne <|
    (mupdBase_ne _ _).ne <| sep_ne.ne .rfl <| forall_ne fun e₂ => forall_ne fun _ =>
    forall_ne fun efs => wand_ne.ne .rfl <| (mprog_ne _ _ _).ne <| (mphys_ne _ _ _ _).ne <|
    ALC_ne.ne <| (mupdBase_ne _ _).ne <| fupd_ne.ne <| sep_ne.ne .rfl (h e₂ tp.length efs)

/-- The postcondition of a forked thread `j` with postcondition `Φ`: it has terminated. -/
@[lantana_alias lift_term]
def liftTerm (j : ThreadId) (Φ : ThreadId → Val → IProp GF) : Val → IProp GF :=
  fun v => iprop(Th.done j ∗ Φ j v)

/-- One unfolding of `lWP`: a value yields its postcondition under a model update; otherwise
one step, after which `lWP` continues and every forked thread `len + j` runs `ef` with the
postcondition `liftTerm (len + j) forkPost`. -/
@[lantana_alias lwp_pre]
def lwpPre (s : Stuckness)
    (lwp : ThreadId → CoPset → Expr → (Val → IProp GF) → IProp GF)
    (i : ThreadId) (E : CoPset) (e₁ : Expr) (Φ : Val → IProp GF) : IProp GF :=
  match toVal e₁ with
  | some v => iprop(|={E}=>m Φ v)
  | none =>
    lwpStep s i E e₁ fun e₂ len efs =>
      iprop(lwp i E e₂ Φ ∗
        [∗list] j ↦ ef ∈ efs, lwp (len + j) ⊤ ef (liftTerm (len + j) L.forkPost))

@[lantana_alias lwp_pre_mono]
theorem lwpPre_mono {s : Stuckness}
    {X Y : ThreadId → CoPset → Expr → (Val → IProp GF) → IProp GF} :
    □ (∀ i E e Φ, X i E e Φ -∗ Y i E e Φ) ⊢
      ∀ i E e Φ, lwpPre s X i E e Φ -∗ lwpPre s Y i E e Φ := by
  iintro #H %i %E %e %Φ Hpre
  unfold lwpPre
  cases toVal e with
  | some v => iexact Hpre
  | none =>
    iapply lwpStep_mono $$ [] Hpre
    iintro %e₂ %len %efs ⟨Hlwp, Hefs⟩
    isplitl [Hlwp]
    · iapply H $$ Hlwp
    · iapply BigSepL.bigSepL_impl $$ Hefs
      iintro !> %j %ef %_ Hef
      iapply H $$ Hef

namespace Internal

-- Catch-all discrete OFEs on the argument types, as in `Iris.ProgramLogic.TotalWeakestPre`.
local instance (priority := low) : OFE CoPset := OFE.ofDiscrete _
local instance (priority := low) : OFE Expr := OFE.ofDiscrete _
local instance (priority := low) : OFE Val := OFE.ofDiscrete _
local instance (priority := low) : OFE ThreadId := OFE.ofDiscrete _

/-- The arguments of `lWP`, uncurried. -/
abbrev Args := ThreadId × CoPset × Expr × (Val → IProp GF)

/-- `lwpPre` on the uncurried arguments. -/
@[lantana_alias lwp_pre']
abbrev pre' (s : Stuckness) (X : Args (Expr := Expr) (Val := Val) (GF := GF) → IProp GF) :
    Args (Expr := Expr) (Val := Val) (GF := GF) → IProp GF
  | (i, E, e, Φ) => lwpPre s (fun i E e Φ => X (i, E, e, Φ)) i E e Φ

@[lantana_alias lwp_pre_mono']
instance pre'_mono (s : Stuckness) :
    BIMonoPred (pre' (Expr := Expr) (Val := Val) (GF := GF) s) where
  mono_pred := by
    intro X Y _ _
    iintro #HXY %⟨i, E, e, Φ⟩ HX
    iapply lwpPre_mono $$ [] HX
    iintro !> %i %E %e %Φ H
    iapply HXY $$ H
  mono_pred_ne {X} _ := ⟨fun {n} => fun ⟨i₁, E₁, e₁, Φ₁⟩ ⟨i₂, E₂, e₂, Φ₂⟩ ⟨hi, hE, he, hΦ⟩ => by
    obtain rfl := show i₁ = i₂ from hi
    obtain rfl := show E₁ = E₂ from hE
    obtain rfl := show e₁ = e₂ from he
    simp only [pre', lwpPre]
    match toVal e₁ with
    | some v => exact (mupd_ne _ _).ne (hΦ v)
    | none =>
      refine lwpStep_ne fun e₂ _ _ => sep_ne.ne ?_ .rfl
      exact OFE.NonExpansive.ne (f := X) (x₁ := (i₁, E₁, e₂, Φ₁)) (x₂ := (i₁, E₁, e₂, Φ₂))
        ⟨.rfl, .rfl, .rfl, hΦ⟩⟩

/-- `lWP` as the least fixpoint. -/
@[lantana_alias lwp_fix]
def get (s : Stuckness) (i : ThreadId) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  bi_least_fixpoint (pre' s) (i, E, e, Φ)

theorem get_unfold {s : Stuckness} {i : ThreadId} {E : CoPset} {e : Expr}
    {Φ : Val → IProp GF} : get s i E e Φ ⊣⊢ lwpPre s (get s) i E e Φ :=
  equiv_iff.mp (least_fixpoint_unfold (pre' s))

omit [ModelGS GF] in
/-- Rewriting along an internal equality, with the equality in a separating conjunction. -/
private theorem internalEq_rewrite_sep {A : Type _} [OFE A] {a b : A} (Ψ : A → IProp GF)
    [OFE.NonExpansive Ψ] : iprop(a ≡ b) ∗ Ψ a ⊢ Ψ b :=
  sep_and.trans (internalEq.rewrite' Ψ and_elim_l and_elim_r)

/-- Induction on the least fixpoint for any `Ψ`: the induction is on its non-expansive
closure `fun x => ∀ y, x ≡ y → Ψ y`. -/
theorem get_ind_strong (s : Stuckness)
    (Ψ : ThreadId → CoPset → Expr → (Val → IProp GF) → IProp GF) :
    □ (∀ i e E Φ, lwpPre s (fun i E e Φ => iprop(Ψ i E e Φ ∧ get s i E e Φ)) i E e Φ -∗
        Ψ i E e Φ)
      ⊢ ∀ i e E Φ, get s i E e Φ -∗ Ψ i E e Φ := by
  let Ψ' : Args (Expr := Expr) (Val := Val) (GF := GF) → IProp GF :=
    fun x => iprop(∀ y : Args, x ≡ y → Ψ y.1 y.2.1 y.2.2.1 y.2.2.2)
  haveI hΨ' : OFE.NonExpansive Ψ' :=
    ⟨fun _ _ _ h => forall_ne fun y => imp_ne.ne ((internalEq.ne_l y).ne h) .rfl⟩
  letI : OFE.NonExpansive fun x => iprop(Ψ' x ∧ bi_least_fixpoint (pre' s) x) :=
    ⟨fun _ _ _ h => and_ne.ne (hΨ'.ne h) (OFE.NonExpansive.ne h)⟩
  unfold get
  iintro #IH %i %e %E %Φ H
  ihave H := least_fixpoint_ind (pre' s) Ψ' $$ [] %(i, E, e, Φ) H
  · iintro !> %x Hx %y Heq
    ihave Hy : pre' s (fun x => iprop(Ψ' x ∧ bi_least_fixpoint (pre' s) x)) y $$ [Hx Heq]
    · iapply internalEq_rewrite_sep (pre' s (fun x => iprop(Ψ' x ∧ bi_least_fixpoint (pre' s) x)))
      isplitl [Heq]
      · iexact Heq
      · iexact Hx
    obtain ⟨i, E, e, Φ⟩ := y
    iapply IH
    iapply lwpPre_mono $$ [] Hy
    iintro !> %i %E %e %Φ H
    isplit
    · icases H with ⟨H, -⟩
      iapply H $$ %(i, E, e, Φ)
      ipureintro
      rfl
    · icases H with ⟨-, H⟩
      iexact H
  iapply H $$ %(i, E, e, Φ)
  ipureintro
  rfl

theorem get_ne {s : Stuckness} {i : ThreadId} {E : CoPset} {e : Expr} :
    OFE.NonExpansive (get (Expr := Expr) (GF := GF) s i E e) :=
  ⟨fun _ _ _ h => by
    refine OFE.NonExpansive.ne (f := bi_least_fixpoint (pre' s)) ?_
    exact ⟨.rfl, .rfl, .rfl, h⟩⟩

end Internal

instance instLwp : Lwp (IProp GF) Expr Val Stuckness ThreadId where
  lwp := Internal.get

/-! ## The defining equations and induction -/

@[lantana_alias lwp_unfold]
theorem lwp_unfold {s : Stuckness} {i : ThreadId} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    lWP e @ s; i; E {{ Φ }} ⊣⊢ lwpPre s (Lwp.lwp (PROP := IProp GF) s) i E e Φ :=
  Internal.get_unfold

/-- Induction on `lWP`, with the fixpoint available in the hypothesis. -/
@[lantana_alias lwp_ind_strong]
theorem lwp_ind_strong (s : Stuckness)
    (Ψ : ThreadId → CoPset → Expr → (Val → IProp GF) → IProp GF) :
    □ (∀ i e E Φ,
        lwpPre s (fun i E e Φ => iprop(Ψ i E e Φ ∧ lWP e @ s; i; E {{ Φ }})) i E e Φ -∗ Ψ i E e Φ)
      ⊢ ∀ i e E Φ, lWP e @ s; i; E {{ Φ }} -∗ Ψ i E e Φ :=
  Internal.get_ind_strong s Ψ

/-- Induction on `lWP`. -/
@[lantana_alias lwp_ind]
theorem lwp_ind (s : Stuckness) (Ψ : ThreadId → CoPset → Expr → (Val → IProp GF) → IProp GF) :
    □ (∀ i e E Φ, lwpPre s Ψ i E e Φ -∗ Ψ i E e Φ)
      ⊢ ∀ i e E Φ, lWP e @ s; i; E {{ Φ }} -∗ Ψ i E e Φ := by
  iintro #IH
  iapply lwp_ind_strong s Ψ
  iintro !> %i %e %E %Φ H
  iapply IH
  iapply lwpPre_mono $$ [] H
  iintro !> %i %E %e %Φ H
  icases H with ⟨H, -⟩
  iexact H

@[lantana_alias lwp_ne]
instance lwp_ne {s : Stuckness} {i : ThreadId} {E : CoPset} {e : Expr} :
    OFE.NonExpansive (Lwp.lwp (PROP := IProp GF) (Val := Val) s i E e) :=
  Internal.get_ne

#lantana_ignore lwp_proper "Subsumed by the `NonExpansive` instance `lwp_ne`."
#lantana_ignore lwp_fix_ne "`lwp` is not sealed: `lwp_ne`."
#lantana_ignore lwp_fix_proper "`lwp` is not sealed: `lwp_ne`."
#lantana_ignore lwp_fix_unfold "`lwp` is not sealed: `lwp_unfold`."
#lantana_ignore lwp_fix_unfold_fix "`lwp` is not sealed: `lwp_unfold`."
#lantana_ignore lwp_unfold_fix "`lwp` is not sealed: `lwp_unfold`."
#lantana_ignore lwp_pre_lwp_pre' "`lwp` is not sealed: `pre'` is an `abbrev`."
#lantana_ignore lwp_step_ne "`lwpStep_ne`, a dist lemma (no `Proper`)."
#lantana_ignore lwp_step_proper "`lwpStep_ne`, a dist lemma (no `Proper`)."

/-! ## Structural rules -/

section Rules
variable {s s₁ s₂ : Stuckness} {i : ThreadId} {E E₁ E₂ : CoPset} {e : Expr}
  {Φ Ψ : Val → IProp GF} {P : IProp GF}

@[lantana_alias fupd_lwp]
theorem fupd_lwp : (|={E}=> lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }} := by
  simp only [(lwp_unfold (e := e)).to_eq, lwpPre]
  iintro H
  cases toVal e with
  | some v =>
    imod H
    iexact H
  | none =>
    unfold lwpStep
    iintro %K %h %n %σ₁ %tp %hK %hi Hσ
    imod H
    iapply H $$ %K %h %n %σ₁ %tp %hK %hi Hσ

@[lantana_alias sfmupd_lwp]
theorem mupd_lwp : (|={E}=>m lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }} := by
  simp only [(lwp_unfold (e := e)).to_eq, lwpPre]
  iintro H
  cases toVal e with
  | some v =>
    imod H
    iexact H
  | none =>
    unfold lwpStep mupd mupdFancy
    iintro %K %h %n %σ₁ %tp %hK %hi Hσ
    imod H $$ %h %n %σ₁ %tp Hσ with H
    imodintro
    imod H with H
    iapply fupd_mupdBase_elim
    imod H with ⟨Hσ, H⟩
    iapply H $$ %K %h %n %σ₁ %tp %hK %hi Hσ

@[lantana_alias lwp_value_sfmupd']
theorem lwp_value_mupd' {v : Val} : lWP (v : Expr) @ s; i; E {{ Φ }} ⊣⊢ |={E}=>m Φ v := by
  simp [(lwp_unfold (e := (v : Expr))).to_eq, lwpPre]

theorem _root_.Iris.Stuckness.maybeReducible_mono {s₁ s₂ : Stuckness} (hs : s₁ ≤ s₂) {e : Expr}
    {σ : State} (h : s₁.maybeReducible e σ) : s₂.maybeReducible e σ := by
  cases s₁ <;> cases s₂ <;> simp_all [Stuckness.maybeReducible, LE.le]

@[lantana_alias lwp_strong_mono_sfmupd]
theorem lwp_strong_mono_mupd (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    lWP e @ s₁; i; E₁ {{ Φ }} ⊢ (∀ v, Φ v ={E₂}=∗m Ψ v) -∗ lWP e @ s₂; i; E₂ {{ Ψ }} := by
  iintro H HΦ
  iapply lwp_ind_strong s₁ (fun i E₁ e Φ => iprop(∀ E₂ Ψ, ⌜E₁ ⊆ E₂⌝ -∗
      (∀ v, Φ v ={E₂}=∗m Ψ v) -∗ lWP e @ s₂; i; E₂ {{ Ψ }})) $$ [] %i %e %E₁ %Φ H %E₂ %Ψ %hE HΦ
  iintro !> %i %e %E₁ %Φ IH %E₂ %Ψ %hE HΦ
  rw [lwp_unfold.to_eq]
  unfold lwpPre
  cases toVal e with
  | some v =>
    imod mupd_mask_mono hE $$ IH with HΦv
    iapply HΦ $$ HΦv
  | none =>
    unfold lwpStep
    iintro %K %h %n %σ₁ %tp %hK %hi Hσ
    imod fupd_mask_subseteq hE with Hclose
    imod IH $$ %K %h %n %σ₁ %tp %hK %hi Hσ with IH
    imodintro
    imod IH with ⟨%hred, IH⟩
    imodintro
    isplitr
    · ipureintro
      exact Stuckness.maybeReducible_mono hs hred
    iintro %e₂ %σ₂ %efs %hstep
    ispecialize IH $$ %e₂ %σ₂ %efs %hstep
    iapply mprog_wand $$ [Hclose HΦ] IH
    iintro IH
    iapply mphys_wand $$ [Hclose HΦ] IH
    iintro IH
    iapply ALC_wand $$ [Hclose HΦ] IH
    iintro IH
    iapply mupdBase_wand $$ [Hclose HΦ] IH
    iintro IH
    imod IH with ⟨Hσ, ⟨IH, -⟩, Hefs⟩
    imod Hclose
    imodintro
    iframe Hσ
    isplitl [IH HΦ]
    · iapply IH $$ %E₂ %Ψ %hE HΦ
    · iapply BigSepL.bigSepL_impl $$ Hefs
      iintro !> %j %ef %_ ⟨Hef, -⟩
      iapply Hef $$ %⊤ %_ %(Std.LawfulSet.subset_refl)
      iintro %v Hv
      iapply mupd_intro $$ Hv

@[lantana_alias lwp_strong_mono]
theorem lwp_strong_mono (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    lWP e @ s₁; i; E₁ {{ Φ }} ⊢ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ lWP e @ s₂; i; E₂ {{ Ψ }} := by
  iintro H HΦ
  iapply lwp_strong_mono_mupd hs hE $$ H
  iintro %v Hv
  iapply fupd_mupd
  iapply HΦ $$ Hv

@[lantana_alias lwp_sfmupd]
theorem lwp_mupd : lWP e @ s; i; E {{ v, |={E}=>m Φ v }} ⊢ lWP e @ s; i; E {{ Φ }} := by
  iintro H
  iapply lwp_strong_mono_mupd (Std.IsPreorder.le_refl _) Std.LawfulSet.subset_refl $$ H
  iintro %v Hv
  iexact Hv

theorem lwp_value_mupd_of_toVal {v : Val} (he : toVal e = some v) :
    lWP e @ s; i; E {{ Φ }} ⊣⊢ |={E}=>m Φ v := by
  simp [(lwp_unfold (e := e)).to_eq, lwpPre, he]

@[lantana_alias lwp_value_sfmupd]
theorem lwp_value_mupd {v : Val} [h : Language.IntoVal e v] :
    lWP e @ s; i; E {{ Φ }} ⊣⊢ |={E}=>m Φ v := by
  obtain ⟨rfl⟩ := h
  exact lwp_value_mupd'

@[lantana_alias lwp_value']
theorem lwp_value' {v : Val} : Φ v ⊢ lWP (v : Expr) @ s; i; E {{ Φ }} :=
  mupd_intro.trans lwp_value_mupd'.mpr

@[lantana_alias lwp_value]
theorem lwp_value {v : Val} [Language.IntoVal e v] : Φ v ⊢ lWP e @ s; i; E {{ Φ }} :=
  mupd_intro.trans lwp_value_mupd.mpr

/-- `(tp.set i e ++ efs)[i]? = some e` when `i` is a thread of `tp`. -/
theorem getElem?_set_append {tp efs : List Expr} {i : ThreadId} {e e' : Expr}
    (hi : tp[i]? = some e) : (tp.set i e' ++ efs)[i]? = some e' := by
  have hlt : i < tp.length := (List.getElem?_eq_some_iff.mp hi).1
  rw [List.getElem?_append_left (by simpa using hlt)]
  simp [hlt]

/-- The value case of `lwp_atomic_mupd`. -/
private theorem lwp_atomic_value {e₂ : Expr} {v₂ : Val} (he₂ : toVal e₂ = some v₂)
    {h : List (HistEntry Expr State)} {n : Nat} {σ : State} {tp : ThreadPool Expr} {L : Nat}
    (hL : tp.length = L) {X : IProp GF} :
    lWP e₂ @ s; i; E₂ {{ v, |={E₂,E₁}=>m Φ v }} ⊢ historyTInterp h n σ tp -∗ X -∗
      |={E₂,∅}=> |=[n, L]=>m |={∅,E₁}=>
        (historyTInterp h n σ tp ∗ (lWP e₂ @ s; i; E₁ {{ Φ }} ∗ X)) := by
  iintro H Hσ HX
  ihave H := (lwp_value_mupd_of_toVal he₂).mp $$ H
  ihave H := mupd_trans $$ H
  imod mupd_elim L hL $$ H Hσ with H
  imodintro
  imod H with H
  imodintro
  imod H with ⟨Hσ, HΦ⟩
  imodintro
  iframe Hσ HX
  iapply (lwp_value_mupd_of_toVal he₂).mpr
  iapply mupd_intro $$ HΦ

@[lantana_alias lwp_atomic_sfmupd]
theorem lwp_atomic_mupd [hatom : Language.Atomic s.toAtomicity e] :
    (|={E₁,E₂}=>m lWP e @ s; i; E₂ {{ v, |={E₂,E₁}=>m Φ v }}) ⊢ lWP e @ s; i; E₁ {{ Φ }} := by
  simp only [(lwp_unfold (e := e)).to_eq, lwpPre]
  iintro H
  cases toVal e with
  | some v =>
    imod H
    imod H
    iexact H
  | none =>
    unfold lwpStep
    iintro %K %h %n %σ₁ %tp %hK %hi Hσ
    imod mupd_elim tp.length rfl $$ H Hσ with H
    imodintro
    imod H with H
    iapply fupd_mupdBase_elim
    imod H with ⟨Hσ, H⟩
    imod H $$ %K %h %n %σ₁ %tp %hK %hi Hσ with H
    imodintro
    imod H with ⟨%hred, H⟩
    imodintro
    isplitr
    · ipureintro
      exact hred
    iintro %e₂ %σ₂ %efs %hstep
    ispecialize H $$ %e₂ %σ₂ %efs %hstep
    iapply mprog_wand $$ [] H
    iintro H
    iapply mphys_wand $$ [] H
    iintro H
    iapply ALC_wand $$ [] H
    iintro H
    imod H with H
    iapply fupd_mupdBase_elim
    imod H with ⟨Hσ, H, Hefs⟩
    have hlen : (tp.set i (ctxApply K e₂) ++ efs).length = tp.length + efs.length := by simp
    have hat := hatom.atomic hstep
    cases s with
    | NotStuck =>
      cases he₂ : toVal e₂ with
      | some v₂ => iapply lwp_atomic_value he₂ hlen $$ H Hσ Hefs
      | none =>
        isimp only [(lwp_unfold (e := e₂)).to_eq, lwpPre, he₂, lwpStep] at H
        rw [← hlen]
        imod H $$ %K %_ %_ %_ %_ %hK %(getElem?_set_append hi) Hσ with H
        imodintro
        imod H with ⟨%hred₂, -⟩
        exact (Language.not_reducible_iff.mpr hat hred₂).elim
    | MaybeStuck =>
      obtain ⟨v₂, he₂⟩ := Option.isSome_iff_exists.mp hat
      iapply lwp_atomic_value he₂ hlen $$ H Hσ Hefs

@[lantana_alias lwp_bind]
theorem lwp_bind (K : Λ.Ctx) [hK : Language.Context K] :
    lWP e @ s; i; E {{ v, lWP (ctxApply K (↑v : Val)) @ s; i; E {{ Φ }} }} ⊢
      lWP (ctxApply K e) @ s; i; E {{ Φ }} := by
  iintro H
  iapply lwp_ind_strong s (fun i E e Ψ => iprop(∀ Φ,
      (∀ v, Ψ v -∗ lWP (ctxApply K (↑v : Val)) @ s; i; E {{ Φ }}) -∗
        lWP (ctxApply K e) @ s; i; E {{ Φ }}))
    $$ [] %i %e %E %_ H %Φ []
  · iintro !> %i %e %E %Ψ IH %Φ HΦ
    unfold lwpPre
    cases he : toVal e with
    | some v =>
      obtain rfl := Iris.ProgramLogic.ToVal.coe_of_toVal_eq_some he
      iapply mupd_lwp
      imod IH
      imodintro
      iapply HΦ $$ IH
    | none =>
      rw [(lwp_unfold (e := ctxApply K e)).to_eq]
      simp only [lwpPre, hK.toVal_eq_none_fill he]
      unfold lwpStep
      iintro %K₁ %h %n %σ₁ %tp %hK₁ %hi Hσ
      rw [← Language.ctxApply_comp] at hi
      imod IH $$ %(ctxComp K₁ K) %h %n %σ₁ %tp %(Language.Context.instComp K₁ K) %hi Hσ
        with IH
      isimp only [Language.ctxApply_comp] at IH
      imodintro
      imod IH with ⟨%hred, IH⟩
      imodintro
      isplitr
      · ipureintro
        cases s
        · exact Language.Context.reducible_fill K hred
        · trivial
      iintro %e₂ %σ₂ %efs %hstep
      obtain ⟨e₂', rfl, hstep'⟩ := hK.primStep_fill_inv he hstep
      ispecialize IH $$ %e₂' %σ₂ %efs %hstep'
      iapply mprog_wand $$ [HΦ] IH
      iintro IH
      iapply mphys_wand $$ [HΦ] IH
      iintro IH
      iapply ALC_wand $$ [HΦ] IH
      iintro IH
      iapply mupdBase_wand $$ [HΦ] IH
      iintro IH
      imod IH with ⟨Hσ, ⟨IH, -⟩, Hefs⟩
      imodintro
      iframe Hσ
      isplitl [IH HΦ]
      · iapply IH $$ %Φ HΦ
      · iapply BigSepL.bigSepL_mono_of_forall and_elim_r $$ Hefs
  · iintro %v Hv
    iexact Hv

@[lantana_alias lwp_bind_step]
theorem lwp_bind_step (K : Λ.Ctx) [Language.Context K] :
    lWP e @ s; i; E {{ v, |={E}=>m lWP (ctxApply K (↑v : Val)) @ s; i; E {{ Φ }} }} ⊢
      lWP (ctxApply K e) @ s; i; E {{ Φ }} := by
  iintro H
  iapply lwp_bind K
  iapply lwp_strong_mono (Std.IsPreorder.le_refl _) Std.LawfulSet.subset_refl $$ H
  iintro %v Hv
  imodintro
  iapply mupd_lwp $$ Hv

@[lantana_alias lwp_bind_sfmupd]
theorem lwp_bind_mupd (K : Λ.Ctx) [Language.Context K] :
    (|={E}=>m lWP e @ s; i; E {{ v, |={E}=>m lWP (ctxApply K (↑v : Val)) @ s; i; E {{ Φ }} }}) ⊢
      |={E}=>m lWP (ctxApply K e) @ s; i; E {{ Φ }} := by
  iintro H
  imod H
  imodintro
  iapply lwp_bind_step K $$ H

@[lantana_alias sfmupd_lwp_sfmupd]
theorem mupd_lwp_mupd :
    (|={E}=>m lWP e @ s; i; E {{ v, |={E}=>m Φ v }}) ⊢ |={E}=>m lWP e @ s; i; E {{ Φ }} := by
  iintro H
  imod H
  imodintro
  iapply lwp_mupd $$ H

/-! ## Derived rules -/

@[lantana_alias lwp_fupd]
theorem lwp_fupd : lWP e @ s; i; E {{ v, |={E}=> Φ v }} ⊢ lWP e @ s; i; E {{ Φ }} := by
  iintro H
  iapply lwp_strong_mono (Std.IsPreorder.le_refl _) Std.LawfulSet.subset_refl $$ H
  iintro %v Hv
  iexact Hv

@[lantana_alias lwp_atomic]
theorem lwp_atomic [Language.Atomic s.toAtomicity e] :
    (|={E₁,E₂}=> lWP e @ s; i; E₂ {{ v, |={E₂,E₁}=> Φ v }}) ⊢ lWP e @ s; i; E₁ {{ Φ }} := by
  iintro H
  iapply lwp_atomic_mupd
  iapply fupd_mupd
  imod H
  imodintro
  iapply lwp_strong_mono (Std.IsPreorder.le_refl _) Std.LawfulSet.subset_refl $$ H
  iintro %v Hv
  imodintro
  iapply fupd_mupd $$ Hv

@[lantana_alias lwp_step_sfmupd]
theorem lwp_step_mupd (_ : toVal e = none) (hE : E₂ ⊆ E₁) :
    (|={E₁,E₂}=>m |={E₂,E₁}=>m P) ∗ lWP e @ s; i; E₂ {{ v, P -∗ |={E₁}=>m Φ v }} ⊢
      lWP e @ s; i; E₁ {{ Φ }} := by
  iintro ⟨HP, H⟩
  iapply lwp_strong_mono_mupd (Std.IsPreorder.le_refl _) hE $$ H
  iintro %v H
  imod HP
  imod HP
  iapply H $$ HP

@[lantana_alias lwp_step_fupd]
theorem lwp_step_fupd (_ : toVal e = none) (hE : E₂ ⊆ E₁) :
    (|={E₁,E₂}=> |={E₂,E₁}=> P) ∗ lWP e @ s; i; E₂ {{ v, P ={E₁}=∗ Φ v }} ⊢
      lWP e @ s; i; E₁ {{ Φ }} := by
  iintro ⟨HP, H⟩
  iapply lwp_strong_mono (Std.IsPreorder.le_refl _) hE $$ H
  iintro %v H
  imod HP
  imod HP
  iapply H $$ HP

@[lantana_alias lwp_mono]
theorem lwp_mono (h : ∀ v, Φ v ⊢ Ψ v) : lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ Ψ }} := by
  iintro H
  iapply lwp_strong_mono (Std.IsPreorder.le_refl _) Std.LawfulSet.subset_refl $$ H
  iintro %v Hv
  imodintro
  iapply h $$ Hv

#lantana_ignore lwp_mono' "No `Proper` typeclass in Lean: `lwp_mono`."
#lantana_ignore lwp_flip_mono' "No `Proper` typeclass in Lean: `lwp_mono`."

@[lantana_alias lwp_stuck_mono, lantana_alias lwp_stuckness_mono]
theorem lwp_stuck_mono (hs : s₁ ≤ s₂) : lWP e @ s₁; i; E {{ Φ }} ⊢ lWP e @ s₂; i; E {{ Φ }} := by
  iintro H
  iapply lwp_strong_mono hs Std.LawfulSet.subset_refl $$ H
  iintro %v Hv
  iexact Hv

@[lantana_alias lwp_stuck_weaken]
theorem lwp_stuck_weaken : lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ i; E ?{{ Φ }} :=
  lwp_stuck_mono (by cases s <;> simp [LE.le])

@[lantana_alias lwp_mask_mono]
theorem lwp_mask_mono (hE : E₁ ⊆ E₂) : lWP e @ s; i; E₁ {{ Φ }} ⊢ lWP e @ s; i; E₂ {{ Φ }} := by
  iintro H
  iapply lwp_strong_mono (Std.IsPreorder.le_refl _) hE $$ H
  iintro %v Hv
  iexact Hv

@[lantana_alias lwp_frame_l]
theorem lwp_frame_l {R : IProp GF} :
    R ∗ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, R ∗ Φ v }} := by
  iintro ⟨HR, H⟩
  iapply lwp_strong_mono (Std.IsPreorder.le_refl _) Std.LawfulSet.subset_refl $$ H
  iintro %v Hv
  iframe

@[lantana_alias lwp_frame_r]
theorem lwp_frame_r {R : IProp GF} :
    lWP e @ s; i; E {{ Φ }} ∗ R ⊢ lWP e @ s; i; E {{ v, Φ v ∗ R }} := by
  iintro ⟨H, HR⟩
  iapply lwp_strong_mono (Std.IsPreorder.le_refl _) Std.LawfulSet.subset_refl $$ H
  iintro %v Hv
  iframe

@[lantana_alias lwp_frame_step_l]
theorem lwp_frame_step_l {R : IProp GF} (he : toVal e = none) (hE : E₂ ⊆ E₁) :
    (|={E₁,E₂}=> |={E₂,E₁}=> R) ∗ lWP e @ s; i; E₂ {{ Φ }} ⊢
      lWP e @ s; i; E₁ {{ v, R ∗ Φ v }} := by
  iintro ⟨HR, H⟩
  iapply lwp_step_fupd he hE
  isplitl [HR]
  · iexact HR
  iapply lwp_strong_mono (Std.IsPreorder.le_refl _) Std.LawfulSet.subset_refl $$ H
  iintro %v Hv
  imodintro
  iintro HR
  imodintro
  iframe

@[lantana_alias lwp_frame_step_r]
theorem lwp_frame_step_r {R : IProp GF} (he : toVal e = none) (hE : E₂ ⊆ E₁) :
    lWP e @ s; i; E₂ {{ Φ }} ∗ (|={E₁,E₂}=> |={E₂,E₁}=> R) ⊢
      lWP e @ s; i; E₁ {{ v, Φ v ∗ R }} := by
  iintro ⟨H, HR⟩
  iapply lwp_mono (fun _ => sep_comm.mp)
  iapply lwp_frame_step_l he hE
  iframe

@[lantana_alias lwp_frame_step_l']
theorem lwp_frame_step_l' {R : IProp GF} (he : toVal e = none) :
    R ∗ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, R ∗ Φ v }} := by
  iintro ⟨HR, H⟩
  iapply lwp_frame_step_l he Std.LawfulSet.subset_refl
  iframe

@[lantana_alias lwp_frame_step_r']
theorem lwp_frame_step_r' {R : IProp GF} (he : toVal e = none) :
    lWP e @ s; i; E {{ Φ }} ∗ R ⊢ lWP e @ s; i; E {{ v, Φ v ∗ R }} := by
  iintro ⟨H, HR⟩
  iapply lwp_frame_step_r he Std.LawfulSet.subset_refl
  iframe

@[lantana_alias lwp_wand]
theorem lwp_wand : lWP e @ s; i; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ lWP e @ s; i; E {{ Ψ }} := by
  iintro H HΦ
  iapply lwp_strong_mono (Std.IsPreorder.le_refl _) Std.LawfulSet.subset_refl $$ H
  iintro %v Hv
  imodintro
  iapply HΦ $$ Hv

@[lantana_alias lwp_wand_l]
theorem lwp_wand_l : (∀ v, Φ v -∗ Ψ v) ∗ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ Ψ }} := by
  iintro ⟨HΦ, H⟩
  iapply lwp_wand $$ H HΦ

@[lantana_alias lwp_wand_r]
theorem lwp_wand_r : lWP e @ s; i; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ lWP e @ s; i; E {{ Ψ }} := by
  iintro ⟨H, HΦ⟩
  iapply lwp_wand $$ H HΦ

@[lantana_alias lwp_frame_wand]
theorem lwp_frame_wand {R : IProp GF} :
    R ⊢ lWP e @ s; i; E {{ v, R -∗ Φ v }} -∗ lWP e @ s; i; E {{ Φ }} := by
  iintro HR H
  iapply lwp_wand $$ H
  iintro %v HΦ
  iapply HΦ $$ HR

/-! ## Later credits -/

/-- Spending one transfinite later credit strips a later in front of `lWP`. -/
@[lantana_alias lwp_lc_later_ord]
theorem lwp_credit_later : £ₒ 1 ⊢ ▷ lWP e @ s; i; E {{ Φ }} -∗ lWP e @ s; i; E {{ Φ }} := by
  iintro Hc H
  iapply fupd_lwp
  iapply lc_fupd_elim_later_ord $$ Hc H

@[lantana_alias lwp_lc_later]
theorem lwp_credit_later_nat : £ₙ 1 ⊢ ▷ lWP e @ s; i; E {{ Φ }} -∗ lWP e @ s; i; E {{ Φ }} :=
  lwp_credit_later

@[lantana_alias lwp_lc_laterN]
theorem lwp_credit_laterN (n : Nat) :
    £ₙ n ⊢ ▷^[n] lWP e @ s; i; E {{ Φ }} -∗ lWP e @ s; i; E {{ Φ }} := by
  iintro Hc H
  iapply fupd_lwp
  iapply lc_fupd_add_laterN n $$ Hc
  iapply laterN_mono n fupd_intro $$ H

end Rules

/-! ## Proof-mode instances -/

section ProofMode

variable {s : Stuckness} {i : ThreadId} {E E₁ E₂ : CoPset} {e : Expr}
  {Φ Ψ : Val → IProp GF} {P R : IProp GF}

@[lantana_alias frame_lwp]
instance frame_lwp {p : Bool} [H : ∀ v, FrameInstantiateExistDisabled p R (Φ v) (Ψ v)] :
    Frame p R (lWP e @ s; i; E {{ Φ }}) (lWP e @ s; i; E {{ Ψ }}) where
  frame := lwp_frame_l.trans (lwp_mono fun v => (H v).frame_instantiatiate_exist_disabled.frame)

@[lantana_alias is_except_0_lwp]
instance isExcept0_lwp : IsExcept0 (lWP e @ s; i; E {{ Φ }}) where
  is_except0 := (except0_mono fupd_intro).trans (BIFUpdate.except0.trans fupd_lwp)

@[lantana_alias elim_modal_fupd_lwp]
instance (priority := default + 10) elimModal_fupd_lwp {p io} :
    ElimModal True p io false iprop(|={E}=> P) P (lWP e @ s; i; E {{ Φ }})
      (lWP e @ s; i; E {{ Φ }}) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans (fupd_wand_right.trans fupd_lwp)

@[lantana_alias elim_modal_bupd_lwp]
instance elimModal_bupd_lwp {p io} :
    ElimModal True p io false iprop(|==> P) P (lWP e @ s; i; E {{ Φ }})
      (lWP e @ s; i; E {{ Φ }}) where
  elim_modal _ := (sep_mono_left (intuitionisticallyIf_mono
    (BIUpdateFUpdate.fupd_of_bupd (E := E)))).trans
      ((elimModal_fupd_lwp (p := p) (io := io)).elim_modal trivial)

@[lantana_alias elim_modal_sfmupd_lwp]
instance (priority := default + 10) elimModal_mupd_lwp {p io} :
    ElimModal True p io false (|={E}=>m P) P (lWP e @ s; i; E {{ Φ }})
      (lWP e @ s; i; E {{ Φ }}) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    mupd_frame_right.trans <| (mupd_mono wand_elim_right).trans mupd_lwp

/-- Error message for a non-mask-changing update at the wrong mask: for a non-atomic `e`,
first add a leading fancy update, then change its mask. -/
@[lantana_alias elim_modal_fupd_lwp_wrong_mask]
instance (priority := low) elimModal_fupd_lwp_wrongMask {p io} :
    ElimModal (PMError "Goal and eliminated modality must have the same mask.
Use `iapply fupd_lwp; imod (fupd_mask_subseteq E₂)` to adjust the mask of your goal to `E₂`")
      p io false iprop(|={E₂}=> P) iprop(False) (lWP e @ s; i; E₁ {{ Φ }}) iprop(False) where
  elim_modal := nofun

@[lantana_alias elim_modal_fupd_lwp_atomic]
instance elimModal_fupd_lwp_atomic {p io} :
    ElimModal (Language.Atomic s.toAtomicity e) p io false iprop(|={E₁,E₂}=> P) P
      (lWP e @ s; i; E₁ {{ Φ }}) (lWP e @ s; i; E₂ {{ v, |={E₂,E₁}=> Φ v }}) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans
    (fupd_wand_right.trans lwp_atomic)

@[lantana_alias elim_modal_sfmupd_lwp_atomic]
instance elimModal_mupd_lwp_atomic {p io} :
    ElimModal (Language.Atomic s.toAtomicity e) p io false (|={E₁,E₂}=>m P) P
      (lWP e @ s; i; E₁ {{ Φ }}) (lWP e @ s; i; E₂ {{ v, |={E₂,E₁}=>m Φ v }}) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    mupd_frame_right.trans <| (mupd_mono wand_elim_right).trans lwp_atomic_mupd

/-- Error message for a mask-changing update in front of a non-atomic expression. -/
@[lantana_alias elim_modal_fupd_lwp_atomic_wrong_mask]
instance (priority := low) elimModal_fupd_lwp_atomic_wrongMask {E₂' : CoPset} {p io} :
    ElimModal (PMError "Goal and eliminated modality must have the same mask.
Use `imod (fupd_mask_subseteq E₂)` to adjust the mask of your goal to `E₂`")
      p io false iprop(|={E₂,E₂'}=> P) iprop(False) (lWP e @ s; i; E₁ {{ Φ }}) iprop(False) where
  elim_modal := nofun

@[lantana_alias add_modal_fupd_lwp]
instance addModal_fupd_lwp : AddModal iprop(|={E}=> P) P (lWP e @ s; i; E {{ Φ }}) where
  add_modal := fupd_wand_right.trans fupd_lwp

@[lantana_alias add_modal_sfmupd_lwp]
instance addModal_mupd_lwp : AddModal (|={E}=>m P) P (lWP e @ s; i; E {{ Φ }}) where
  add_modal := mupd_frame_right.trans <| (mupd_mono wand_elim_right).trans mupd_lwp

@[lantana_alias elim_acc_lwp_atomic]
instance (priority := low) elimAcc_lwp_atomic {X : Type} (α β : X → IProp GF)
    (γ : X → Option (IProp GF)) :
    ElimAcc (Language.Atomic s.toAtomicity e) (fupd E₁ E₂) (fupd E₂ E₁) α β γ
      (lWP e @ s; i; E₁ {{ Φ }})
      (fun x => lWP e @ s; i; E₂ {{ v, |={E₂}=> β x ∗ (γ x -∗? Φ v) }}) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %atomic Hinner >⟨%x, Hα, Hclose⟩
    iapply lwp_wand $$ [Hinner Hα]
    · iapply Hinner $$ Hα
    · iintro %v >⟨Hβ, HΦ⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      imodintro
      cases (γ x) with
      | none => iexact HΦ
      | some P => iapply HΦ $$ Hclose

@[lantana_alias elim_acc_lwp_atomic_sfmupd]
instance (priority := low) elimAcc_lwp_atomic_mupd {X : Type} (α β : X → IProp GF)
    (γ : X → Option (IProp GF)) :
    ElimAcc (Language.Atomic s.toAtomicity e) (mupd (Expr := Expr) (State := State) E₁ E₂)
      (mupd (Expr := Expr) (State := State) E₂ E₁) α β γ
      (lWP e @ s; i; E₁ {{ Φ }})
      (fun x => lWP e @ s; i; E₂ {{ v, |={E₂}=>m β x ∗ (γ x -∗? Φ v) }}) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %atomic Hinner >⟨%x, Hα, Hclose⟩
    iapply lwp_wand $$ [Hinner Hα]
    · iapply Hinner $$ Hα
    · iintro %v >⟨Hβ, HΦ⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      imodintro
      cases (γ x) with
      | none => iexact HΦ
      | some P => iapply HΦ $$ Hclose

@[lantana_alias elim_acc_lwp_nonatomic]
instance elimAcc_lwp_nonatomic {X : Type} (α β : X → IProp GF) (γ : X → Option (IProp GF)) :
    ElimAcc True (fupd E E) (fupd E E) α β γ (lWP e @ s; i; E {{ Φ }})
      (fun x => lWP e @ s; i; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }}) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %_ Hinner >⟨%x, Hα, Hclose⟩
    iapply lwp_fupd
    iapply lwp_wand $$ [Hinner Hα]
    · iapply Hinner $$ Hα
    · iintro %v >⟨Hβ, HΦ⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      imodintro
      cases (γ x) with
      | none => iexact HΦ
      | some P => iapply HΦ $$ Hclose

@[lantana_alias elim_acc_lwp_nonatomic_sfmupd]
instance elimAcc_lwp_nonatomic_mupd {X : Type} (α β : X → IProp GF)
    (γ : X → Option (IProp GF)) :
    ElimAcc True (mupd (Expr := Expr) (State := State) E E)
      (mupd (Expr := Expr) (State := State) E E) α β γ (lWP e @ s; i; E {{ Φ }})
      (fun x => lWP e @ s; i; E {{ v, |={E}=>m β x ∗ (γ x -∗? Φ v) }}) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %_ Hinner >⟨%x, Hα, Hclose⟩
    iapply lwp_mupd
    iapply lwp_wand $$ [Hinner Hα]
    · iapply Hinner $$ Hα
    · iintro %v >⟨Hβ, HΦ⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      imodintro
      cases (γ x) with
      | none => iexact HΦ
      | some P => iapply HΦ $$ Hclose

end ProofMode

end Lwp

end Lantana
