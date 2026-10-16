/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.BI.Lib.Fixpoint
public import Lantana.BaseLogic.LaterCredits
public import Lantana.ProgramLogic.OblForest
public import Lantana.ProgramLogic.Notation

/-! # The liveness weakest precondition `lWP`

Rocq `lantana/program_logic/weakestpre.v`: `lWP e @ s; i; E {{ Φ }}` is the least fixpoint of
one step of the program logic (`lwpStep`): a model update before the step, the progress and
physical rounds of the step, the allocation of later credits, a model update after it. The
structure follows Iris-Lean's total weakest precondition (`Iris.ProgramLogic.TotalWeakestPre`),
which is also a `bi_least_fixpoint`.

Thread ids are positions in the pool (D14): a step of thread `i` running `K e₁` in the pool
`tp` leads to the pool `tp.set i (K e₂) ++ efs`, and the forked threads get the ids
`tp.length, tp.length + 1, …`.

**Skeleton (M1):** the definitions are real; the monotonicity proof and the rules are `sorry`.
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

/-! ## Derived rules of the model updates

The rules of `|=[n,tc]=>m P` (Rocq `base_logic/mupd.v`) and of `|={E₁,E₂}=>m P` (Rocq
`obl_forest_rules.v`) that the program logic uses, derived from the core rules of the
interface, with their proof-mode instances. -/

section MUpd

variable {Expr : Type} {State : Type} {GF : BundledGFunctors} [ModelGS GF]

section Base

variable {n tc : Nat} {P Q R : IProp GF}

@[lantana_alias mupd_wand_l]
theorem mupdBase_wand : (P -∗ Q) ⊢ (|=[n,tc]=>m P) -∗ |=[n,tc]=>m Q :=
  (wand_mono_right (mupdBase_intro n tc Q)).trans (mupdBase_bind n tc P Q)

@[lantana_alias mupd_mono]
theorem mupdBase_mono (h : P ⊢ Q) : (|=[n,tc]=>m P) ⊢ |=[n,tc]=>m Q :=
  wand_entails ((entails_wand h).trans mupdBase_wand)

@[lantana_alias mupd_trans]
theorem mupdBase_trans : (|=[n,tc]=>m |=[n,tc]=>m P) ⊢ |=[n,tc]=>m P :=
  wand_entails (wand_rfl.trans (mupdBase_bind n tc _ P))

@[lantana_alias mupd_frame_r]
theorem mupdBase_frame_right : (|=[n,tc]=>m P) ∗ R ⊢ |=[n,tc]=>m (P ∗ R) := by
  iintro ⟨HP, HR⟩
  iapply mupdBase_wand $$ [HR] HP
  iintro HP
  isplitl [HP]
  · iexact HP
  · iexact HR

@[lantana_alias mupd_fupd_l]
theorem fupd_mupdBase : (|={∅}=> P) ⊢ |=[n,tc]=>m P :=
  (fupd_mono (mupdBase_intro n tc P)).trans (fupd_mupdBase_elim n tc P)

instance fromModal_mupdBase {io} : FromModal io modality_id True (|=[n,tc]=>m P)
    (|=[n,tc]=>m P) P where
  from_modal _ := mupdBase_intro n tc P

instance elimModal_mupdBase {p io} :
    ElimModal True p io false (|=[n,tc]=>m P) P (|=[n,tc]=>m Q) (|=[n,tc]=>m Q) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    sep_comm.mp.trans <| wand_elim_left_trans (mupdBase_bind n tc P Q)

instance elimModal_fupd_mupdBase {p io} :
    ElimModal True p io false iprop(|={∅}=> P) P (|=[n,tc]=>m Q) (|=[n,tc]=>m Q) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    fupd_frame_right.trans <| (fupd_mono wand_elim_right).trans (fupd_mupdBase_elim n tc Q)

end Base

variable [TemporalGS Expr State GF] [StateInterp Expr State GF] [TemporalInterp Expr State GF]
variable {E E₁ E₂ E₃ : CoPset} {P Q R : IProp GF}

@[lantana_alias oblf.sfmupd_wand_l]
theorem mupd_wand : (P -∗ Q) ⊢ (|={E₁,E₂}=>m P) -∗ |={E₁,E₂}=>m Q :=
  (wand_mono_right (fupd_intro.trans (fupd_mupd E₂ E₂ Q))).trans (mupd_bind E₁ E₂ E₂ P Q)

@[lantana_alias oblf.sfmupd_intro]
theorem mupd_intro : P ⊢ |={E}=>m P :=
  fupd_intro.trans (fupd_mupd E E P)

@[lantana_alias oblf.sfmupd_mono]
theorem mupd_mono (h : P ⊢ Q) : (|={E₁,E₂}=>m P) ⊢ |={E₁,E₂}=>m Q :=
  wand_entails ((entails_wand h).trans mupd_wand)

@[lantana_alias oblf.sfmupd_trans]
theorem mupd_trans : (|={E₁,E₂}=>m |={E₂,E₃}=>m P) ⊢ |={E₁,E₃}=>m P :=
  wand_entails (wand_rfl.trans (mupd_bind E₁ E₂ E₃ _ P))

@[lantana_alias oblf.sfmupd_frame_r]
theorem mupd_frame_right : (|={E₁,E₂}=>m P) ∗ R ⊢ |={E₁,E₂}=>m (P ∗ R) := by
  iintro ⟨HP, HR⟩
  iapply mupd_wand $$ [HR] HP
  iintro HP
  isplitl [HP]
  · iexact HP
  · iexact HR

@[lantana_alias oblf.sfmupd_mask_mono]
theorem mupd_mask_mono (h : E₁ ⊆ E₂) : (|={E₁}=>m P) ⊢ |={E₂}=>m P := by
  iintro HP
  iapply mupd_bind E₂ E₁ E₂ iprop(|={E₁,E₂}=> emp) P $$ [HP]
  · iintro Hclose
    iapply mupd_bind E₁ E₁ E₂ P P $$ [Hclose] HP
    iintro HP
    iapply fupd_mupd
    imod Hclose with -
    imodintro
    iexact HP
  · iapply fupd_mupd
    iapply fupd_mask_subseteq h

instance fromModal_mupd {io} : FromModal io modality_id True (|={E}=>m P) (|={E}=>m P) P where
  from_modal _ := mupd_intro

instance elimModal_mupd {p io} :
    ElimModal True p io false (|={E₁,E₂}=>m P) P (|={E₁,E₃}=>m Q) (|={E₂,E₃}=>m Q) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    sep_comm.mp.trans <| wand_elim_left_trans (mupd_bind E₁ E₂ E₃ P Q)

instance elimModal_fupd_mupd {p io} :
    ElimModal True p io false iprop(|={E₁,E₂}=> P) P (|={E₁,E₃}=>m Q) (|={E₂,E₃}=>m Q) where
  elim_modal _ := (sep_mono_left (intuitionisticallyIf_elim.trans (fupd_mupd E₁ E₂ P))).trans <|
    sep_comm.mp.trans <| wand_elim_left_trans (mupd_bind E₁ E₂ E₃ P Q)

instance elimModal_bupd_mupd {p io} :
    ElimModal True p io false iprop(|==> P) P (|={E₁,E₂}=>m Q) (|={E₁,E₂}=>m Q) where
  elim_modal _ := (sep_mono_left (intuitionisticallyIf_elim.trans
      ((BIUpdateFUpdate.fupd_of_bupd (E := E₁)).trans (fupd_mupd E₁ E₁ P)))).trans <|
    sep_comm.mp.trans <| wand_elim_left_trans (mupd_bind E₁ E₁ E₂ P Q)

end MUpd

section Lwp

variable {Expr : Type} {State : Type} {Val : Type} {GF : BundledGFunctors}
variable [Λ : Language Expr State Val] [ModelGS GF]
variable [L : LantanaGS Expr State Val GF] [TemporalInterp Expr State GF]

/-- One step of `lWP` for thread `i` running `K e₁`: a model update before the step (it may
discharge an until), the progress round `mprog` of `i` and the physical round `mphys` of the
step, the allocation of later credits `ALC`, and a model update after it; `ν e₂ len efs`
holds after a step to `e₂` that forks `efs` with ids from `len` (the old pool length). -/
@[lantana_alias lwp_step]
def lwpStep (s : Stuckness) (i : ThreadId) (E : CoPset) (e₁ : Expr)
    (ν : Expr → Nat → List Expr → IProp GF) : IProp GF :=
  iprop(∀ (K : Expr → Expr) (h : List (HistEntry Expr State)) (n : Nat) (σ₁ : State)
    (tp : ThreadPool Expr),
    ⌜Language.Context K⌝ → ⌜tp[i]? = some (K e₁)⌝ →
    historyTInterp h n σ₁ tp ={E,∅}=∗
    |=[n, tp.length]=>m
    ⌜s.maybeReducible e₁ σ₁⌝ ∗
    ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr), ⌜primStep e₁ σ₁ e₂ σ₂ efs⌝ -∗
      mprog n tp.length i
        (mphys n (n + 1) tp.length (tp.length + efs.length)
          (ALC (|=[n + 1, tp.length + efs.length]=>m |={∅,E}=>
            historyTInterp (h ++ [(σ₂, tp.set i (K e₂) ++ efs)]) (n + 1) σ₂
              (tp.set i (K e₂) ++ efs) ∗
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

/-! ## Structural rules -/

section Rules
variable {s s₁ s₂ : Stuckness} {i : ThreadId} {E E₁ E₂ : CoPset} {e : Expr}
  {Φ Ψ : Val → IProp GF} {P : IProp GF}

@[lantana_alias fupd_lwp]
theorem fupd_lwp : (|={E}=> lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }} := sorry

@[lantana_alias sfmupd_lwp]
theorem mupd_lwp : (|={E}=>m lWP e @ s; i; E {{ Φ }}) ⊢ lWP e @ s; i; E {{ Φ }} := sorry

@[lantana_alias lwp_value_sfmupd']
theorem lwp_value_mupd' {v : Val} : lWP (v : Expr) @ s; i; E {{ Φ }} ⊣⊢ |={E}=>m Φ v := sorry

@[lantana_alias lwp_strong_mono]
theorem lwp_strong_mono (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    lWP e @ s₁; i; E₁ {{ Φ }} ⊢ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ lWP e @ s₂; i; E₂ {{ Ψ }} := sorry

@[lantana_alias lwp_strong_mono_sfmupd]
theorem lwp_strong_mono_mupd (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    lWP e @ s₁; i; E₁ {{ Φ }} ⊢ (∀ v, Φ v ={E₂}=∗m Ψ v) -∗ lWP e @ s₂; i; E₂ {{ Ψ }} := sorry

@[lantana_alias lwp_sfmupd]
theorem lwp_mupd : lWP e @ s; i; E {{ v, |={E}=>m Φ v }} ⊢ lWP e @ s; i; E {{ Φ }} := sorry

@[lantana_alias lwp_atomic_sfmupd]
theorem lwp_atomic_mupd [Language.Atomic s.toAtomicity e] :
    (|={E₁,E₂}=>m lWP e @ s; i; E₂ {{ v, |={E₂,E₁}=>m Φ v }}) ⊢ lWP e @ s; i; E₁ {{ Φ }} := sorry

@[lantana_alias lwp_bind]
theorem lwp_bind (K : Expr → Expr) [Language.Context K] :
    lWP e @ s; i; E {{ v, lWP (K (↑v : Val)) @ s; i; E {{ Φ }} }} ⊢ lWP (K e) @ s; i; E {{ Φ }} :=
  sorry

@[lantana_alias lwp_value']
theorem lwp_value' {v : Val} : Φ v ⊢ lWP (v : Expr) @ s; i; E {{ Φ }} := sorry

@[lantana_alias lwp_frame_l]
theorem lwp_frame_l {R : IProp GF} :
    R ∗ lWP e @ s; i; E {{ Φ }} ⊢ lWP e @ s; i; E {{ v, R ∗ Φ v }} := sorry

@[lantana_alias lwp_wand]
theorem lwp_wand : lWP e @ s; i; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ lWP e @ s; i; E {{ Ψ }} := sorry

/-- Spending one transfinite later credit strips a later in front of `lWP`. -/
@[lantana_alias lwp_lc_later_ord]
theorem lwp_credit_later : £ₒ 1 ⊢ ▷ lWP e @ s; i; E {{ Φ }} -∗ lWP e @ s; i; E {{ Φ }} := sorry

end Rules

end Lwp

end Lantana
