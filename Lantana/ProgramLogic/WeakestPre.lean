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

open Iris Iris.BI
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
instance pre'_mono (s : Stuckness) : BIMonoPred (pre' (Expr := Expr) (Val := Val) (GF := GF) s) :=
  sorry

/-- `lWP` as the least fixpoint. -/
@[lantana_alias lwp_fix]
def get (s : Stuckness) (i : ThreadId) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  bi_least_fixpoint (pre' s) (i, E, e, Φ)

end Internal

instance instLwp : Lwp (IProp GF) Expr Val Stuckness ThreadId where
  lwp := Internal.get

/-! ## The defining equations and induction -/

@[lantana_alias lwp_unfold]
theorem lwp_unfold {s : Stuckness} {i : ThreadId} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    lWP e @ s; i; E {{ Φ }} ⊣⊢ lwpPre s (Lwp.lwp (PROP := IProp GF) s) i E e Φ := sorry

/-- Induction on `lWP`, with the fixpoint available in the hypothesis. -/
@[lantana_alias lwp_ind_strong]
theorem lwp_ind_strong (s : Stuckness)
    (Ψ : ThreadId → CoPset → Expr → (Val → IProp GF) → IProp GF) :
    □ (∀ i e E Φ,
        lwpPre s (fun i E e Φ => iprop(Ψ i E e Φ ∧ lWP e @ s; i; E {{ Φ }})) i E e Φ -∗ Ψ i E e Φ)
      ⊢ ∀ i e E Φ, lWP e @ s; i; E {{ Φ }} -∗ Ψ i E e Φ := sorry

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
