/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Prelude.Ordinal
public import Lantana.BaseLogic.Satisfiable
public import Lantana.ProgramLogic.TemporalClass
public import Lantana.Trace.TracePropRules

/-! # Step-indexed trace predicates

Rocq `lantana/trace/triprop.v`: predicates `Trace → IProp GF` (the internal reading, which a run
establishes) and the two guarded fixpoints `TrIProp.always` and `TrIProp.until` (with a
decreasing fuel rank). Their bodies carry the **deferred shape** `defer` (D19): a check at the
current position (a fancy update with a later, where adequacy certifies the registered
invariants) followed by the step (a fancy update that allocates later credits); everything
about a position is established after the step from it.

**Skeleton (M1):** contractiveness and the reading lemmas are `sorry`.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open scoped Lantana.TrProp

/-- A step-indexed trace predicate. -/
@[lantana_alias trIProp]
abbrev TrIProp (Expr State : Type) (GF : BundledGFunctors) := Trace Expr State → IProp GF

namespace TrIProp

variable {Expr State : Type} {GF : BundledGFunctors}

@[lantana_alias trI_pure]
def pure (p : Prop) : TrIProp Expr State GF := fun _ => iprop(⌜p⌝)

@[lantana_alias trI_and]
def and (P Q : TrIProp Expr State GF) : TrIProp Expr State GF := fun τ => iprop(P τ ∧ Q τ)

@[lantana_alias trI_or]
def or (P Q : TrIProp Expr State GF) : TrIProp Expr State GF := fun τ => iprop(P τ ∨ Q τ)

/-- Implication with a *trace property* as antecedent: it is assumed at the level of traces. -/
@[lantana_alias trI_impl]
def imp (P : TrProp Expr State) (Q : TrIProp Expr State GF) : TrIProp Expr State GF :=
  fun τ => iprop(⌜P τ⌝ → Q τ)

@[lantana_alias trI_forall]
def all {A : Type _} (P : A → TrIProp Expr State GF) : TrIProp Expr State GF :=
  fun τ => iprop(∀ a, P a τ)

@[lantana_alias trI_exist]
def ex {A : Type _} (P : A → TrIProp Expr State GF) : TrIProp Expr State GF :=
  fun τ => iprop(∃ a, P a τ)

section Fixpoints
variable [ModelGS GF]

/-- The deferred shape: the check at the current position (a later under a fancy update), then
the step (a fancy update that allocates later credits). -/
def defer (P : IProp GF) : IProp GF :=
  iprop(|={⊤,∅}=> ▷ |={∅,⊤}=> |={⊤,∅}=> ALC iprop(|={∅,⊤}=> P))

theorem defer_mono {P Q : IProp GF} (h : P ⊢ Q) : defer P ⊢ defer Q := sorry
theorem defer_intro {P : IProp GF} : P ⊢ defer P := sorry
instance defer_ne : OFE.NonExpansive (defer (GF := GF)) := sorry

/-- One unfolding of `always`: `P` now, and `always P` at the next position, deferred. (Rocq's
`trI_always_pre` carries two formulas; the second is only used with `True`, so it is dropped.) -/
@[lantana_alias trI_always_pre]
def alwaysPre (P : TrIProp Expr State GF) (R : TrIProp Expr State GF) : TrIProp Expr State GF :=
  fun τ => defer iprop(P τ ∧ R τ.next)

@[lantana_alias trI_always_pre_contractive]
instance alwaysPre_contractive (P : TrIProp Expr State GF) : OFE.Contractive (alwaysPre P) := sorry

/-- `always P`: `P` holds at every position from the current one on (guarded fixpoint). -/
@[lantana_alias trI_always]
def always (P : TrIProp Expr State GF) : TrIProp Expr State GF := fixpoint (alwaysPre P)

@[lantana_alias trI_always_unfold]
theorem always_unfold (P : TrIProp Expr State GF) (τ : Trace Expr State) :
    always P τ ⊣⊢ alwaysPre P (always P) τ := sorry

/-- One unfolding of `strongUntil`: `Q` now, or `P` now and `until` at a smaller rank at the next
position, deferred. -/
@[lantana_alias trI_until_pre]
def untilPre (P Q : TrIProp Expr State GF) (R : Fuel → TrIProp Expr State GF)
    (a : Fuel) : TrIProp Expr State GF :=
  fun τ => defer iprop(Q τ ∨ (P τ ∧ ∃ a' : Fuel, ⌜a' < a⌝ ∧ R a' τ.next))

@[lantana_alias trI_until_pre_contractive]
instance untilPre_contractive (P Q : TrIProp Expr State GF) : OFE.Contractive (untilPre P Q) :=
  sorry

/-- `strongUntil P Q a`: `Q` eventually holds and `P` holds before, with a fuel rank `a` that
decreases at every step (guarded fixpoint). -/
@[lantana_alias trI_until]
def strongUntil (P Q : TrIProp Expr State GF) : Fuel → TrIProp Expr State GF :=
  fixpoint (untilPre P Q)

@[lantana_alias trI_until_unfold]
theorem until_unfold (P Q : TrIProp Expr State GF) (a : Fuel) (τ : Trace Expr State) :
    strongUntil P Q a τ ⊣⊢ untilPre P Q (strongUntil P Q) a τ := sorry

/-! ## Reading the fixpoints off a trace, by satisfiability -/

@[lantana_alias trI_always_tr_always]
theorem always_tr_always (F : IProp GF) (P : TrIProp Expr State GF) (R : TrProp Expr State)
    (h : ∀ τ, (iPropSatLcAtFrame F ⊤).sat (P τ) → R τ) (τ : Trace Expr State)
    (hs : (iPropSatLcAtFrame F ⊤).sat (always P τ)) : (□ₜ R) τ := sorry

@[lantana_alias trI_until_tr_until_gen]
theorem until_tr_until (F : IProp GF) (P Q : TrIProp Expr State GF) (R S : TrProp Expr State)
    (hP : ∀ τ, (iPropSatLcAtFrame F ⊤).sat (P τ) → R τ)
    (hQ : ∀ τ, (iPropSatLcAtFrame F ⊤).sat (Q τ) → S τ)
    (τ : Trace Expr State) (hs : (iPropSatLcAtFrame F ⊤).sat (ex (fun a => strongUntil P Q a) τ)) :
    (R 𝒰ₜ S) τ := sorry

/-! ## In-logic monotonicity (one step later) -/

@[lantana_alias trI_always_mono_i]
theorem always_mono_i (P P' : TrIProp Expr State GF) :
    ▷ □ (∀ τ, P τ -∗ P' τ) ⊢ ∀ τ, always P τ -∗ always P' τ := sorry

@[lantana_alias trI_until_mono_i]
theorem until_mono_i (P P' Q Q' : TrIProp Expr State GF) :
    ▷ □ (∀ τ, P τ -∗ P' τ) ⊢ ▷ □ (∀ τ, Q τ -∗ Q' τ) -∗
      ∀ a τ, strongUntil P Q a τ -∗ strongUntil P' Q' a τ := sorry

end Fixpoints

end TrIProp
end Lantana
