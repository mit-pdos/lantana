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

The reading lemmas (`always_tr_always`, `until_tr_until`) eliminate the deferred shape by
satisfiability (`sat_defer`); the in-logic monotonicity lemmas are by Löb induction.
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

theorem defer_mono {P Q : IProp GF} (h : P ⊢ Q) : defer P ⊢ defer Q :=
  fupd_mono <| later_mono <| fupd_mono <| fupd_mono <| ALC_mono <| fupd_mono h

/-- The argument of `defer` is only needed one step later. -/
theorem defer_intro_later {P : IProp GF} : ▷ P ⊢ defer P := by
  iintro HP
  unfold defer
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  iapply ALC_intro
  imod Hclose
  imodintro
  iexact HP

theorem defer_intro {P : IProp GF} : P ⊢ defer P :=
  later_intro.trans defer_intro_later

/-- `defer` is contractive: its argument sits under a `▷`. -/
instance defer_contractive : OFE.Contractive (defer (GF := GF)) where
  distLater_dist h := fupd_ne.ne <| OFE.Contractive.distLater_dist (f := BIBase.later) fun m hm =>
    fupd_ne.ne <| fupd_ne.ne <| ALC_ne.ne <| fupd_ne.ne (h m hm)

instance defer_ne : OFE.NonExpansive (defer (GF := GF)) := inferInstance

/-- The wand under the deferred shape is only needed one step later. -/
theorem defer_wand_later {P Q : IProp GF} : ▷ (P -∗ Q) ⊢ defer P -∗ defer Q := by
  iintro HW H
  unfold defer
  imod H
  imodintro
  inext
  imod H
  imodintro
  imod H
  imodintro
  imod H
  imod H
  imodintro
  iapply HW
  iexact H

/-- Satisfiability eliminates the deferred shape. -/
theorem sat_defer {F P : IProp GF} (h : (iPropSatLcAtFrame F ⊤).sat (defer P)) :
    (iPropSatLcAtFrame F ⊤).sat P :=
  SatFUpd.fupd (sat_ALC (SatFUpd.fupd (SatFUpd.fupd (SatPred.sat_later _ (SatFUpd.fupd h)))))

/-- One unfolding of `always`: `P` now, and `always P` at the next position, deferred. (Rocq's
`trI_always_pre` carries two formulas; the second is only used with `True`, so it is dropped.) -/
@[lantana_alias trI_always_pre]
def alwaysPre (P : TrIProp Expr State GF) (R : TrIProp Expr State GF) : TrIProp Expr State GF :=
  fun τ => defer iprop(P τ ∧ R τ.next)

@[lantana_alias trI_always_pre_contractive]
instance alwaysPre_contractive (P : TrIProp Expr State GF) : OFE.Contractive (alwaysPre P) where
  distLater_dist h τ :=
    OFE.Contractive.distLater_dist (f := defer) fun m hm => and_ne.ne .rfl (h m hm τ.next)

/-- `always P`: `P` holds at every position from the current one on (guarded fixpoint). -/
@[lantana_alias trI_always]
def always (P : TrIProp Expr State GF) : TrIProp Expr State GF := fixpoint (alwaysPre P)

@[lantana_alias trI_always_unfold]
theorem always_unfold (P : TrIProp Expr State GF) (τ : Trace Expr State) :
    always P τ ⊣⊢ alwaysPre P (always P) τ :=
  BiEntails.of_eq (congrFun (fixpoint_unfold (alwaysPre P).toContractiveHom) τ)

/-- One unfolding of `strongUntil`: `Q` now, or `P` now and `until` at a smaller rank at the next
position, deferred. -/
@[lantana_alias trI_until_pre]
def untilPre (P Q : TrIProp Expr State GF) (R : Fuel → TrIProp Expr State GF)
    (a : Fuel) : TrIProp Expr State GF :=
  fun τ => defer iprop(Q τ ∨ (P τ ∧ ∃ a' : Fuel, ⌜a' < a⌝ ∧ R a' τ.next))

@[lantana_alias trI_until_pre_contractive]
instance untilPre_contractive (P Q : TrIProp Expr State GF) : OFE.Contractive (untilPre P Q) where
  distLater_dist h _ τ :=
    OFE.Contractive.distLater_dist (f := defer) fun m hm => or_ne.ne .rfl <| and_ne.ne .rfl <|
      exists_ne fun a' => and_ne.ne .rfl (h m hm a' τ.next)

/-- `strongUntil P Q a`: `Q` eventually holds and `P` holds before, with a fuel rank `a` that
decreases at every step (guarded fixpoint). -/
@[lantana_alias trI_until]
def strongUntil (P Q : TrIProp Expr State GF) : Fuel → TrIProp Expr State GF :=
  fixpoint (untilPre P Q)

@[lantana_alias trI_until_unfold]
theorem until_unfold (P Q : TrIProp Expr State GF) (a : Fuel) (τ : Trace Expr State) :
    strongUntil P Q a τ ⊣⊢ untilPre P Q (strongUntil P Q) a τ :=
  BiEntails.of_eq (congrFun (congrFun (fixpoint_unfold (untilPre P Q).toContractiveHom) a) τ)

/-! ## Reading the fixpoints off a trace, by satisfiability -/

/-- Satisfiability of `always P` at `τ` gives `P` at `τ` and `always P` at the next position. -/
theorem always_sat_unfold {F : IProp GF} {P : TrIProp Expr State GF} {τ : Trace Expr State}
    (hs : (iPropSatLcAtFrame F ⊤).sat (always P τ)) :
    (iPropSatLcAtFrame F ⊤).sat (P τ) ∧ (iPropSatLcAtFrame F ⊤).sat (always P τ.next) :=
  SatPred.sat_and _ (sat_defer ((iPropSatLcAtFrame F ⊤).mono (always_unfold P τ).mp hs))

@[lantana_alias trI_always_trace_next]
theorem always_trace_next {F : IProp GF} {P : TrIProp Expr State GF} {τ : Trace Expr State}
    (hs : (iPropSatLcAtFrame F ⊤).sat (always P τ)) :
    (iPropSatLcAtFrame F ⊤).sat (always P τ.next) :=
  (always_sat_unfold hs).2

@[lantana_alias trI_always_tr_always]
theorem always_tr_always (F : IProp GF) (P : TrIProp Expr State GF) (R : TrProp Expr State)
    (h : ∀ τ, (iPropSatLcAtFrame F ⊤).sat (P τ) → R τ) (τ : Trace Expr State)
    (hs : (iPropSatLcAtFrame F ⊤).sat (always P τ)) : (□ₜ R) τ :=
  TrProp.always_coind (X := fun τ => (iPropSatLcAtFrame F ⊤).sat (always P τ))
    (fun τ hs => And.intro (h τ (always_sat_unfold hs).1) (always_sat_unfold hs).2) τ hs

/-- Satisfiability of `strongUntil P Q a` at `τ` gives `Q` at `τ`, or `P` at `τ` and
`strongUntil P Q a'` at the next position for a smaller rank `a'`. -/
theorem until_sat_unfold {F : IProp GF} {P Q : TrIProp Expr State GF} {a : Fuel}
    {τ : Trace Expr State} (hs : (iPropSatLcAtFrame F ⊤).sat (strongUntil P Q a τ)) :
    (iPropSatLcAtFrame F ⊤).sat (Q τ) ∨ ((iPropSatLcAtFrame F ⊤).sat (P τ) ∧
      ∃ a' < a, (iPropSatLcAtFrame F ⊤).sat (strongUntil P Q a' τ.next)) := by
  have h := sat_defer ((iPropSatLcAtFrame F ⊤).mono (until_unfold P Q a τ).mp hs)
  refine (SatPred.sat_or _ h).imp id fun h => ?_
  obtain ⟨h₁, h₂⟩ := SatPred.sat_and _ h
  obtain ⟨a', h₂⟩ := SatPred.sat_exists _ h₂
  obtain ⟨hlt, h₂⟩ := SatPred.sat_and _ h₂
  exact ⟨h₁, a', (iPropSatLcAtFrame F ⊤).elim hlt, h₂⟩

@[lantana_alias trI_until_tr_until_gen]
theorem until_tr_until (F : IProp GF) (P Q : TrIProp Expr State GF) (R S : TrProp Expr State)
    (hP : ∀ τ, (iPropSatLcAtFrame F ⊤).sat (P τ) → R τ)
    (hQ : ∀ τ, (iPropSatLcAtFrame F ⊤).sat (Q τ) → S τ)
    (τ : Trace Expr State)
    (hs : (iPropSatLcAtFrame F ⊤).sat (ex (fun a => strongUntil P Q a) τ)) :
    (R 𝒰ₜ S) τ := by
  obtain ⟨a, ha⟩ := SatPred.sat_exists _ hs
  clear hs
  induction a using Ordinals.Ordinal.lt_wf.induction generalizing τ with
  | _ a ih =>
  rcases until_sat_unfold ha with h | ⟨h₁, a', hlt, h₂⟩
  · exact TrProp.until_now τ (hQ τ h)
  · exact TrProp.until_step τ ⟨hP τ h₁, ih a' hlt τ.next h₂⟩

/-! ## In-logic monotonicity (one step later) -/

@[lantana_alias trI_always_mono_i]
theorem always_mono_i (P P' : TrIProp Expr State GF) :
    ▷ □ (∀ τ, P τ -∗ P' τ) ⊢ ∀ τ, always P τ -∗ always P' τ := by
  iintro #HW
  iloeb as IH
  iintro %τ H
  have h₁ : always P τ ⊢ defer iprop(P τ ∧ always P τ.next) := (always_unfold P τ).mp
  have h₂ : defer iprop(P' τ ∧ always P' τ.next) ⊢ always P' τ := (always_unfold P' τ).mpr
  iapply h₂
  ihave H := h₁ $$ H
  iapply defer_wand_later $$ [] H
  inext
  iintro H
  isplit
  · icases H with ⟨H, -⟩
    iapply HW
    iexact H
  · icases H with ⟨-, H⟩
    iapply IH
    iexact H

@[lantana_alias trI_until_mono_i]
theorem until_mono_i (P P' Q Q' : TrIProp Expr State GF) :
    ▷ □ (∀ τ, P τ -∗ P' τ) ⊢ ▷ □ (∀ τ, Q τ -∗ Q' τ) -∗
      ∀ a τ, strongUntil P Q a τ -∗ strongUntil P' Q' a τ := by
  iintro #HP #HQ
  iloeb as IH
  iintro %a %τ H
  have h₁ : strongUntil P Q a τ ⊢
      defer iprop(Q τ ∨ (P τ ∧ ∃ a' : Fuel, ⌜a' < a⌝ ∧ strongUntil P Q a' τ.next)) :=
    (until_unfold P Q a τ).mp
  have h₂ : defer iprop(Q' τ ∨ (P' τ ∧ ∃ a' : Fuel, ⌜a' < a⌝ ∧ strongUntil P' Q' a' τ.next)) ⊢
      strongUntil P' Q' a τ :=
    (until_unfold P' Q' a τ).mpr
  iapply h₂
  ihave H := h₁ $$ H
  iapply defer_wand_later $$ [] H
  inext
  iintro H
  icases H with (H | H)
  · ileft
    iapply HQ
    iexact H
  · iright
    isplit
    · icases H with ⟨H, -⟩
      iapply HP
      iexact H
    · icases H with ⟨-, %a', %hlt, H⟩
      iexists a'
      isplitr
      · ipureintro
        exact hlt
      iapply IH
      iexact H

end Fixpoints

end TrIProp
end Lantana
