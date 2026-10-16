/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra.StepIndexChoice
public import Lantana.Trace.TrIProp

/-! # Trace specifications

Rocq `lantana/trace/trspec.v` and `trspec_rules.v`: a trace specification `TrSpec` pairs a
step-indexed reading (`internal`, established by a run) with a trace reading (`external`,
concluded by adequacy) and a proof that the former is adequate for the latter. The connectives
carry a subscript `ₛ`. In-logic entailment `G ⊑ₛ H` compares internal readings; it transports
guarantees but is too weak for temporal reasoning, which happens on the external readings
(`TrProp`) and is imported with `TrSpec.cast`.

The adequacy obligations are the satisfiability laws (`Lantana.SatPred`) and, for `always` and
`strongUntil`, the reading lemmas of `Lantana.Trace.TrIProp`. `always` and `strongUntil` are
complete (by Löb induction and by induction on the trace-level until) but not instant.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open scoped Lantana.TrProp

/-- A trace specification: an internal (step-indexed) reading adequate for an external (trace)
reading. The internal reading is stated for every instance of the ghost state. -/
@[lantana_alias trSpec]
structure TrSpec (Expr State : Type) (GF : BundledGFunctors) where
  /-- The step-indexed reading, which a run establishes. -/
  internal : ∀ [ModelGS GF] [TemporalGS Expr State GF],
    TrIProp Expr State GF
  /-- The trace reading, which adequacy concludes. -/
  external : TrProp Expr State
  /-- Adequacy: satisfiability of the internal reading at `τ` (with any frame, under the
  credit supply and world satisfaction) gives the external reading at `τ`. -/
  adeq : ∀ [ModelGS GF] [TemporalGS Expr State GF]
    (F : IProp GF) (τ : Trace Expr State), (iPropSatLcAtFrame F ⊤).sat (internal τ) → external τ

namespace TrSpec

variable {Expr State : Type} {GF : BundledGFunctors}

/-- In-logic entailment of trace specifications. -/
@[lantana_alias trSpec_le]
def le (G H : TrSpec Expr State GF) : Prop :=
  ∀ [ModelGS GF] [TemporalGS Expr State GF]
    (τ : Trace Expr State), G.internal τ ⊢ H.internal τ

scoped infix:50 " ⊑ₛ " => TrSpec.le

#lantana_ignore trSpec_sqsubseteq "The notation `⊑ₛ`."
#lantana_ignore trSpec_le_preorder "`TrSpec.le_refl` and `TrSpec.le_trans`."

/-! ## Connectives -/

@[lantana_alias trSpec_pure]
def pure (p : Prop) : TrSpec Expr State GF where
  internal := TrIProp.pure p
  external := TrProp.pure p
  adeq _ _ h := (iPropSatLcAtFrame _ ⊤).elim h

@[lantana_alias trSpec_true]
def true : TrSpec Expr State GF := pure True

@[lantana_alias trSpec_and]
def and (G H : TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := TrIProp.and G.internal H.internal
  external := G.external ∧ₜ H.external
  adeq F τ h :=
    And.intro (G.adeq F τ (SatPred.sat_and _ h).1) (H.adeq F τ (SatPred.sat_and _ h).2)

@[lantana_alias trSpec_or]
def or (G H : TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := TrIProp.or G.internal H.internal
  external := G.external ∨ₜ H.external
  adeq F τ h := (SatPred.sat_or _ h).imp (G.adeq F τ) (H.adeq F τ)

/-- Implication: both readings assume the antecedent at the level of traces. -/
@[lantana_alias trSpec_impl]
def imp (A G : TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := TrIProp.imp A.external G.internal
  external := A.external →ₜ G.external
  adeq F τ h hA := G.adeq F τ (SatPred.sat_impl _ h (pure_intro hA))

@[lantana_alias trSpec_forall]
def all {X : Type _} (G : X → TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := TrIProp.all fun x => (G x).internal
  external := ∀ₜ x, (G x).external
  adeq F τ h x := (G x).adeq F τ (SatPred.sat_forall _ x h)

/-- Existential quantification needs the existential property of the step index, so only
small types qualify (`Nat`, `Fuel`, ghost names, …). -/
@[lantana_alias trSpec_exist]
def ex {X : Type _} [SIdxLarge SI X] (G : X → TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := TrIProp.ex fun x => (G x).internal
  external := ∃ₜ x, (G x).external
  adeq F τ h := (SatPred.sat_exists _ h).imp fun x => (G x).adeq F τ

@[lantana_alias trSpec_always]
def always (G : TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := TrIProp.always G.internal
  external := □ₜ G.external
  adeq F τ h := TrIProp.always_tr_always F G.internal G.external (G.adeq F) τ h

@[lantana_alias trSpec_until]
def strongUntil (G H : TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := TrIProp.ex fun a : Fuel => TrIProp.strongUntil G.internal H.internal a
  external := G.external 𝒰ₜ H.external
  adeq F τ h :=
    TrIProp.until_tr_until F G.internal H.internal G.external H.external (G.adeq F) (H.adeq F) τ h

@[lantana_alias trSpec_finally]
def eventually (G : TrSpec Expr State GF) : TrSpec Expr State GF := strongUntil true G

/-- A state atom: a predicate on the current state and thread pool. -/
@[lantana_alias trSpec_state]
def state (φ : State → ThreadPool Expr → Prop) : TrSpec Expr State GF where
  internal := fun τ => iprop(⌜φ τ.cfg.2 τ.cfg.1⌝)
  external := TrProp.state φ
  adeq _ _ h := (iPropSatLcAtFrame _ ⊤).elim h

/-- The same internal reading with a weaker external one: imports trace-level reasoning. -/
@[lantana_alias trSpec_cast]
def cast (G : TrSpec Expr State GF) (R : TrProp Expr State) (pf : G.external ⊆ R) :
    TrSpec Expr State GF where
  internal := G.internal
  external := R
  adeq _ τ h := pf τ (G.adeq _ τ h)

/-! ## In-logic monotonicity (one step later) -/

@[lantana_alias trSpec_always_mono_i]
theorem always_mono_i [ModelGS GF] [TemporalGS Expr State GF] (G G' : TrSpec Expr State GF) :
    ▷ □ (∀ τ, G.internal τ -∗ G'.internal τ) ⊢
      ∀ τ, (always G).internal τ -∗ (always G').internal τ :=
  TrIProp.always_mono_i _ _

@[lantana_alias trSpec_until_mono_i]
theorem strongUntil_mono_i [ModelGS GF] [TemporalGS Expr State GF]
    (G H G' H' : TrSpec Expr State GF) :
    ▷ □ (∀ τ, G.internal τ -∗ G'.internal τ) ⊢ ▷ □ (∀ τ, H.internal τ -∗ H'.internal τ) -∗
      ∀ τ, (strongUntil G H).internal τ -∗ (strongUntil G' H').internal τ := by
  iintro #HG #HH %τ HU
  have h₁ : (strongUntil G H).internal τ ⊢
      iprop(∃ a : Fuel, TrIProp.strongUntil G.internal H.internal a τ) := .rfl
  have h₂ : iprop(∃ a : Fuel, TrIProp.strongUntil G'.internal H'.internal a τ) ⊢
      (strongUntil G' H').internal τ := .rfl
  iapply h₂
  ihave ⟨%a, HU⟩ := h₁ $$ HU
  iexists a
  iapply TrIProp.until_mono_i G.internal G'.internal H.internal H'.internal $$ HG HH HU

/-! ## Notations -/

scoped notation:max "⌜" p "⌝ₛ" => TrSpec.pure p
scoped infixr:35 " ∧ₛ " => TrSpec.and
scoped infixr:30 " ∨ₛ " => TrSpec.or
scoped infixr:25 " →ₛ " => TrSpec.imp
scoped notation:max "□ₛ " G:40 => TrSpec.always G
scoped notation:max "◇ₛ " G:40 => TrSpec.eventually G
scoped infixr:40 " 𝒰ₛ " => TrSpec.strongUntil

open Lean in
/-- `∀ₛ x, G`. -/
scoped syntax "∀ₛ " explicitBinders ", " term : term
open Lean in
/-- `∃ₛ x, G`. -/
scoped syntax "∃ₛ " explicitBinders ", " term : term
open Lean in
scoped macro_rules
  | `(∀ₛ $xs, $b) => Lean.expandExplicitBinders ``TrSpec.all xs b
  | `(∃ₛ $xs, $b) => Lean.expandExplicitBinders ``TrSpec.ex xs b

/-! ## Complete and instant specifications -/

/-- The trace reading gives the in-logic reading. -/
@[lantana_alias TrSpecComplete]
class Complete (G : TrSpec Expr State GF) : Prop where
  complete : ∀ [ModelGS GF] [TemporalGS Expr State GF]
    (τ : Trace Expr State), G.external τ → ⊢ G.internal τ

/-- The in-logic reading gives the trace reading, internally. -/
@[lantana_alias TrSpecInstant]
class Instant (G : TrSpec Expr State GF) : Prop where
  instant : ∀ [ModelGS GF] [TemporalGS Expr State GF]
    (τ : Trace Expr State), G.internal τ ⊢ ⌜G.external τ⌝

@[lantana_alias trSpec_complete_pure]
instance pure_complete (p : Prop) : Complete (pure (Expr := Expr) (State := State) (GF := GF) p) :=
  ⟨fun _ h => pure_intro h⟩
@[lantana_alias trSpec_complete_and]
instance and_complete (G H : TrSpec Expr State GF) [Complete G] [Complete H] : Complete (G ∧ₛ H) :=
  ⟨fun τ h => and_intro (Complete.complete τ h.1) (Complete.complete τ h.2)⟩
@[lantana_alias trSpec_complete_or]
instance or_complete (G H : TrSpec Expr State GF) [Complete G] [Complete H] : Complete (G ∨ₛ H) :=
  ⟨fun τ h => h.elim (fun h => (Complete.complete τ h).trans or_intro_l)
    (fun h => (Complete.complete τ h).trans or_intro_r)⟩
@[lantana_alias trSpec_complete_impl]
instance imp_complete (A G : TrSpec Expr State GF) [Complete G] : Complete (A →ₛ G) :=
  ⟨fun τ h => imp_intro <| pure_elim _ and_elim_r fun hA =>
    and_elim_l.trans (Complete.complete τ (h hA))⟩
@[lantana_alias trSpec_complete_forall]
instance all_complete {X : Type _} (G : X → TrSpec Expr State GF) [∀ x, Complete (G x)] :
    Complete (all G) :=
  ⟨fun τ h => forall_intro fun x => Complete.complete τ (h x)⟩
@[lantana_alias trSpec_complete_exist]
instance ex_complete {X : Type _} [SIdxLarge SI X] (G : X → TrSpec Expr State GF)
    [∀ x, Complete (G x)] : Complete (ex G) :=
  ⟨fun τ ⟨x, h⟩ => (Complete.complete τ h).trans (exists_intro (Ψ := fun x => (G x).internal τ) x)⟩
/-- By Löb induction: `always` is a guarded fixpoint. -/
@[lantana_alias trSpec_complete_always]
instance always_complete (G : TrSpec Expr State GF) [Complete G] : Complete (□ₛ G) where
  complete τ h := by
    have hl : ⊢ ∀ τ, ⌜(□ₜ G.external) τ⌝ → TrIProp.always G.internal τ := by
      iloeb as IH
      iintro %τ %hτ
      have h₁ : TrIProp.defer iprop(G.internal τ ∧ TrIProp.always G.internal τ.next) ⊢
          TrIProp.always G.internal τ :=
        (TrIProp.always_unfold G.internal τ).mpr
      iapply h₁
      iapply TrIProp.defer_intro_later
      inext
      isplit
      · iapply Complete.complete τ (TrProp.always_elim τ hτ)
      · iapply IH
        ipureintro
        exact TrProp.always_next τ hτ
    exact hl.trans <| (forall_elim τ).trans <| (and_intro (pure_intro h) .rfl).trans imp_elim_right
/-- By induction on the trace-level until, with ranks `0` at the end and `succ` at each step. -/
@[lantana_alias trSpec_complete_until]
instance strongUntil_complete (G H : TrSpec Expr State GF) [Complete G] [Complete H] :
    Complete (G 𝒰ₛ H) where
  complete τ h := by
    obtain ⟨a, ha⟩ := TrProp.until_ind
      (X := fun τ => ∃ a : Fuel, ⊢ TrIProp.strongUntil G.internal H.internal a τ)
      (fun τ hH => ⟨0, (Complete.complete τ hH).trans <| or_intro_l.trans <|
        TrIProp.defer_intro.trans (TrIProp.until_unfold G.internal H.internal 0 τ).mpr⟩)
      (fun τ ⟨hG, a, ha⟩ => ⟨Ordinals.Ordinal.succ a, (and_intro (Complete.complete τ hG)
        ((and_intro (pure_intro (Ordinals.Ordinal.lt_succ a)) ha).trans
          (exists_intro (Ψ := fun a' => iprop(⌜a' < Ordinals.Ordinal.succ a⌝ ∧
            TrIProp.strongUntil G.internal H.internal a' τ.next)) a))).trans <|
        or_intro_r.trans <| TrIProp.defer_intro.trans
          (TrIProp.until_unfold G.internal H.internal _ τ).mpr⟩) τ h
    exact ha.trans (exists_intro (Ψ := fun a => TrIProp.strongUntil G.internal H.internal a τ) a)
@[lantana_alias trSpec_complete_finally]
instance eventually_complete (G : TrSpec Expr State GF) [Complete G] : Complete (◇ₛ G) :=
  @strongUntil_complete _ _ _ true G (pure_complete True) _
@[lantana_alias trSpec_complete_state]
instance state_complete (φ : State → ThreadPool Expr → Prop) :
    Complete (state (GF := GF) φ) :=
  ⟨fun _ h => pure_intro h⟩
@[lantana_alias trSpec_instant_pure]
instance pure_instant (p : Prop) : Instant (pure (Expr := Expr) (State := State) (GF := GF) p) :=
  ⟨fun _ => .rfl⟩
@[lantana_alias trSpec_instant_and]
instance and_instant (G H : TrSpec Expr State GF) [Instant G] [Instant H] : Instant (G ∧ₛ H) :=
  ⟨fun τ => (and_mono (Instant.instant τ) (Instant.instant τ)).trans pure_and.mp⟩
@[lantana_alias trSpec_instant_or]
instance or_instant (G H : TrSpec Expr State GF) [Instant G] [Instant H] : Instant (G ∨ₛ H) :=
  ⟨fun τ => or_elim ((Instant.instant τ).trans (pure_mono Or.inl))
    ((Instant.instant τ).trans (pure_mono Or.inr))⟩
/-- Classical: by cases on the antecedent. -/
@[lantana_alias trSpec_instant_impl]
instance imp_instant (A G : TrSpec Expr State GF) [Instant G] : Instant (A →ₛ G) where
  instant τ := by
    by_cases hA : A.external τ
    · exact ((and_intro (pure_intro hA) .rfl).trans imp_elim_right).trans <|
        (Instant.instant τ).trans (pure_mono fun h _ => h)
    · exact pure_intro fun h => absurd h hA
/-- Classical: some instance fails, or all hold. -/
@[lantana_alias trSpec_instant_forall]
instance all_instant {X : Type _} (G : X → TrSpec Expr State GF) [∀ x, Instant (G x)] :
    Instant (all G) where
  instant τ := by
    by_cases hall : ∀ x, (G x).external τ
    · exact pure_intro hall
    · obtain ⟨x, hx⟩ := Classical.not_forall.mp hall
      exact (forall_elim x).trans <| (Instant.instant τ).trans (pure_mono fun h => absurd h hx)
@[lantana_alias trSpec_instant_exist]
instance ex_instant {X : Type _} [SIdxLarge SI X] (G : X → TrSpec Expr State GF)
    [∀ x, Instant (G x)] : Instant (ex G) :=
  ⟨fun τ => exists_elim fun x => (Instant.instant τ).trans (pure_mono fun h => ⟨x, h⟩)⟩
@[lantana_alias trSpec_instant_state]
instance state_instant (φ : State → ThreadPool Expr → Prop) : Instant (state (GF := GF) φ) :=
  ⟨fun _ => .rfl⟩

/-! ## Rules of `⊑ₛ` -/

section Rules
variable {G G' H H' A A' X : TrSpec Expr State GF}

@[lantana_alias trSpec_le_refl]
theorem le_refl (G : TrSpec Expr State GF) : G ⊑ₛ G := fun _ => .rfl

@[lantana_alias trSpec_le_trans]
theorem le_trans (h₁ : G ⊑ₛ H) (h₂ : H ⊑ₛ X) : G ⊑ₛ X := fun τ => (h₁ τ).trans (h₂ τ)

@[lantana_alias trSpec_le_true]
theorem le_true : G ⊑ₛ true := fun _ => pure_intro trivial

@[lantana_alias trSpec_and_elim_l]
theorem and_elim_l : (G ∧ₛ H) ⊑ₛ G := fun _ => BI.and_elim_l

@[lantana_alias trSpec_and_elim_r]
theorem and_elim_r : (G ∧ₛ H) ⊑ₛ H := fun _ => BI.and_elim_r

@[lantana_alias trSpec_and_mono]
theorem and_mono (h₁ : G ⊑ₛ G') (h₂ : H ⊑ₛ H') : (G ∧ₛ H) ⊑ₛ (G' ∧ₛ H') :=
  fun τ => BI.and_mono (h₁ τ) (h₂ τ)

@[lantana_alias trSpec_or_mono]
theorem or_mono (h₁ : G ⊑ₛ G') (h₂ : H ⊑ₛ H') : (G ∨ₛ H) ⊑ₛ (G' ∨ₛ H') :=
  fun τ => BI.or_mono (h₁ τ) (h₂ τ)

@[lantana_alias trSpec_impl_mono]
theorem imp_mono (hA : A'.external ⊆ A.external) (h : G ⊑ₛ G') : (A →ₛ G) ⊑ₛ (A' →ₛ G') :=
  fun τ => BI.imp_mono (pure_mono (hA τ)) (h τ)

@[lantana_alias trSpec_impl_intro_le]
theorem imp_intro_le : G ⊑ₛ (A →ₛ G) := fun _ => BI.imp_intro BI.and_elim_l

@[lantana_alias trSpec_forall_mono]
theorem all_mono {Y : Type _} {G G' : Y → TrSpec Expr State GF} (h : ∀ y, G y ⊑ₛ G' y) :
    all G ⊑ₛ all G' :=
  fun τ => forall_mono fun y => h y τ

@[lantana_alias trSpec_exist_mono]
theorem ex_mono {Y : Type _} [SIdxLarge SI Y] {G G' : Y → TrSpec Expr State GF}
    (h : ∀ y, G y ⊑ₛ G' y) : ex G ⊑ₛ ex G' :=
  fun τ => exists_mono fun y => h y τ

@[lantana_alias trSpec_always_mono]
theorem always_mono (h : G ⊑ₛ G') : (□ₛ G) ⊑ₛ (□ₛ G') := fun τ => by
  change TrIProp.always G.internal τ ⊢ TrIProp.always G'.internal τ
  iintro HG
  iapply TrIProp.always_mono_i G.internal G'.internal $$ [] HG
  inext
  imodintro
  iintro %τ' H
  iapply h τ'
  iexact H

@[lantana_alias trSpec_until_mono]
theorem strongUntil_mono (h₁ : G ⊑ₛ G') (h₂ : H ⊑ₛ H') : (G 𝒰ₛ H) ⊑ₛ (G' 𝒰ₛ H') := fun τ => by
  change iprop(∃ a : Fuel, TrIProp.strongUntil G.internal H.internal a τ) ⊢
    iprop(∃ a : Fuel, TrIProp.strongUntil G'.internal H'.internal a τ)
  iintro ⟨%a, HU⟩
  iexists a
  iapply TrIProp.until_mono_i G.internal G'.internal H.internal H'.internal $$ [] [] HU
  · inext
    imodintro
    iintro %τ' H
    iapply h₁ τ'
    iexact H
  · inext
    imodintro
    iintro %τ' H
    iapply h₂ τ'
    iexact H

@[lantana_alias trSpec_impl_intro]
theorem imp_intro [Complete A] (h : (A ∧ₛ H) ⊑ₛ G) : H ⊑ₛ (A →ₛ G) := fun τ =>
  BI.imp_intro <| pure_elim _ BI.and_elim_r fun hA =>
    BI.and_elim_l.trans <| (BI.and_intro (true_intro.trans (Complete.complete τ hA)) .rfl).trans
      (h τ)

@[lantana_alias trSpec_impl_elim]
theorem imp_elim [Instant A] : (A ∧ₛ (A →ₛ G)) ⊑ₛ G := fun τ =>
  pure_elim _ (BI.and_elim_l.trans (Instant.instant τ)) fun hA =>
    BI.and_elim_r.trans <| (BI.and_intro (pure_intro hA) .rfl).trans imp_elim_right

@[lantana_alias trSpec_cast_le]
theorem cast_le (R : TrProp Expr State) (pf : G.external ⊆ R) : G ⊑ₛ G.cast R pf :=
  fun _ => .rfl

@[lantana_alias trSpec_le_cast]
theorem le_cast (R : TrProp Expr State) (pf : G.external ⊆ R) : G.cast R pf ⊑ₛ G :=
  fun _ => .rfl

@[lantana_alias trSpec_cast_ext]
theorem cast_external (R : TrProp Expr State) (pf : G.external ⊆ R) : (G.cast R pf).external = R :=
  rfl

@[lantana_alias trSpec_cast_complete]
theorem cast_complete [Complete G] (R : TrProp Expr State) (pf : G.external ⊆ R)
    (hR : R ⊆ G.external) : Complete (G.cast R pf) :=
  ⟨fun τ h => Complete.complete (G := G) τ (hR τ h)⟩

/-! ### Antecedents, read on the trace -/

/-- An implication is the disjunction of its consequent with the negated antecedent
(classical). -/
@[lantana_alias trSpec_impl_or_not]
theorem imp_or_not : (A →ₛ G) ⊑ₛ ((A →ₛ ⌜False⌝ₛ) ∨ₛ G) := fun τ => by
  by_cases hA : A.external τ
  · exact ((BI.and_intro (pure_intro hA) .rfl).trans imp_elim_right).trans or_intro_r
  · exact (pure_intro (P := iprop(⌜A.external τ⌝ → G.internal τ)) hA).trans <|
      (BI.imp_intro <| pure_elim _ BI.and_elim_r fun h => absurd h hA).trans or_intro_l

@[lantana_alias trSpec_or_not_impl]
theorem or_not_imp : ((A →ₛ ⌜False⌝ₛ) ∨ₛ G) ⊑ₛ (A →ₛ G) := fun _ =>
  or_elim (BI.imp_mono .rfl (pure_elim' False.elim)) (BI.imp_intro BI.and_elim_l)

@[lantana_alias trSpec_impl_curry]
theorem imp_curry : (A →ₛ (A' →ₛ G)) ⊑ₛ ((A ∧ₛ A') →ₛ G) := fun _ =>
  BI.imp_intro <| pure_elim _ BI.and_elim_r fun h =>
    BI.and_elim_l.trans <| ((BI.and_intro (pure_intro h.1) .rfl).trans imp_elim_right).trans <|
      (BI.and_intro (pure_intro h.2) .rfl).trans imp_elim_right

@[lantana_alias trSpec_impl_uncurry]
theorem imp_uncurry : ((A ∧ₛ A') →ₛ G) ⊑ₛ (A →ₛ (A' →ₛ G)) := fun _ =>
  BI.imp_intro <| pure_elim _ BI.and_elim_r fun h₁ => BI.imp_intro <|
    pure_elim _ BI.and_elim_r fun h₂ => BI.and_elim_l.trans <| BI.and_elim_l.trans <|
      (BI.and_intro (pure_intro (And.intro h₁ h₂)) .rfl).trans imp_elim_right

@[lantana_alias trSpec_impl_or_split]
theorem imp_or_split : ((A →ₛ G) ∧ₛ (A' →ₛ G)) ⊑ₛ ((A ∨ₛ A') →ₛ G) := fun _ =>
  BI.imp_intro <| pure_elim _ BI.and_elim_r fun h => BI.and_elim_l.trans <| h.elim
    (fun h => BI.and_elim_l.trans <| (BI.and_intro (pure_intro h) .rfl).trans imp_elim_right)
    (fun h => BI.and_elim_r.trans <| (BI.and_intro (pure_intro h) .rfl).trans imp_elim_right)

@[lantana_alias trSpec_impl_or_join]
theorem imp_or_join : ((A ∨ₛ A') →ₛ G) ⊑ₛ ((A →ₛ G) ∧ₛ (A' →ₛ G)) := fun _ =>
  BI.and_intro (BI.imp_mono (pure_mono Or.inl) .rfl) (BI.imp_mono (pure_mono Or.inr) .rfl)

@[lantana_alias trSpec_impl_exist]
theorem imp_ex {Y : Type _} [SIdxLarge SI Y] {A : Y → TrSpec Expr State GF} :
    (∀ₛ y, A y →ₛ G) ⊑ₛ (ex A →ₛ G) := fun _ =>
  BI.imp_intro <| pure_elim _ BI.and_elim_r fun ⟨y, h⟩ => BI.and_elim_l.trans <|
    (forall_elim y).trans <| (BI.and_intro (pure_intro h) .rfl).trans imp_elim_right

end Rules

/-! ## Reading off the external property from the shape -/

/-- `Ext G R`: the external reading of `G` entails `R` (computed from the shape of `G`; the
fallback is `G.external` itself). -/
@[lantana_alias TrSpecExt]
class Ext (G : TrSpec Expr State GF) (R : outParam (TrProp Expr State)) : Prop where
  ext_of : G.external ⊆ R

@[lantana_alias trSpec_ext_default]
instance (priority := low) ext_default (G : TrSpec Expr State GF) : Ext G G.external :=
  ⟨TrProp.le_refl _⟩
@[lantana_alias trSpec_ext_pure]
instance ext_pure (p : Prop) : Ext (pure (Expr := Expr) (State := State) (GF := GF) p) ⌜p⌝ₜ :=
  ⟨TrProp.le_refl _⟩
@[lantana_alias trSpec_ext_state]
instance ext_state (φ : State → ThreadPool Expr → Prop) :
    Ext (state (GF := GF) φ) (TrProp.state φ) := ⟨TrProp.le_refl _⟩
@[lantana_alias trSpec_ext_and]
instance ext_and (G H : TrSpec Expr State GF) (R S : TrProp Expr State) [Ext G R] [Ext H S] :
    Ext (G ∧ₛ H) (R ∧ₜ S) := ⟨TrProp.and_mono Ext.ext_of Ext.ext_of⟩
@[lantana_alias trSpec_ext_or]
instance ext_or (G H : TrSpec Expr State GF) (R S : TrProp Expr State) [Ext G R] [Ext H S] :
    Ext (G ∨ₛ H) (R ∨ₜ S) := ⟨TrProp.or_mono Ext.ext_of Ext.ext_of⟩
@[lantana_alias trSpec_ext_impl]
instance ext_imp (A G : TrSpec Expr State GF) (R : TrProp Expr State) [Ext G R] :
    Ext (A →ₛ G) (A.external →ₜ R) := ⟨TrProp.imp_mono (TrProp.le_refl _) Ext.ext_of⟩
@[lantana_alias trSpec_ext_forall]
instance ext_all {Y : Type _} (G : Y → TrSpec Expr State GF) (R : Y → TrProp Expr State)
    [∀ y, Ext (G y) (R y)] : Ext (all G) (∀ₜ y, R y) := ⟨TrProp.all_mono fun _ => Ext.ext_of⟩
@[lantana_alias trSpec_ext_exist]
instance ext_ex {Y : Type _} [SIdxLarge SI Y] (G : Y → TrSpec Expr State GF)
    (R : Y → TrProp Expr State) [∀ y, Ext (G y) (R y)] : Ext (ex G) (∃ₜ y, R y) :=
  ⟨TrProp.ex_mono fun _ => Ext.ext_of⟩
@[lantana_alias trSpec_ext_always]
instance ext_always (G : TrSpec Expr State GF) (R : TrProp Expr State) [Ext G R] :
    Ext (□ₛ G) (□ₜ R) := ⟨TrProp.always_mono Ext.ext_of⟩
@[lantana_alias trSpec_ext_finally]
instance (priority := high) ext_eventually (G : TrSpec Expr State GF) (R : TrProp Expr State)
    [Ext G R] : Ext (◇ₛ G) (◇ₜ R) := ⟨TrProp.until_mono (TrProp.le_refl _) Ext.ext_of⟩
@[lantana_alias trSpec_ext_until]
instance ext_strongUntil (G H : TrSpec Expr State GF) (R S : TrProp Expr State) [Ext G R]
    [Ext H S] : Ext (G 𝒰ₛ H) (R 𝒰ₜ S) := ⟨TrProp.until_mono Ext.ext_of Ext.ext_of⟩
@[lantana_alias trSpec_ext_cast]
instance ext_cast (G : TrSpec Expr State GF) (R : TrProp Expr State) (pf : G.external ⊆ R) :
    Ext (G.cast R pf) R := ⟨TrProp.le_refl _⟩

end TrSpec
end Lantana
