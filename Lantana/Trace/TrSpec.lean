/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
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

**Skeleton (M1):** the adequacy obligations and the rules are `sorry`.
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

/-! ## Connectives -/

@[lantana_alias trSpec_pure]
def pure (p : Prop) : TrSpec Expr State GF where
  internal := TrIProp.pure p
  external := TrProp.pure p
  adeq := sorry

@[lantana_alias trSpec_true]
def true : TrSpec Expr State GF := pure True

@[lantana_alias trSpec_and]
def and (G H : TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := TrIProp.and G.internal H.internal
  external := G.external ∧ₜ H.external
  adeq := sorry

@[lantana_alias trSpec_or]
def or (G H : TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := TrIProp.or G.internal H.internal
  external := G.external ∨ₜ H.external
  adeq := sorry

/-- Implication: both readings assume the antecedent at the level of traces. -/
@[lantana_alias trSpec_impl]
def imp (A G : TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := TrIProp.imp A.external G.internal
  external := A.external →ₜ G.external
  adeq := sorry

@[lantana_alias trSpec_forall]
def all {X : Type _} (G : X → TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := TrIProp.all fun x => (G x).internal
  external := ∀ₜ x, (G x).external
  adeq := sorry

/-- Existential quantification needs the existential property of the step index, so only
small types qualify (`Nat`, `Fuel`, ghost names, …). -/
@[lantana_alias trSpec_exist]
def ex {X : Type _} [SIdxLarge SI X] (G : X → TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := TrIProp.ex fun x => (G x).internal
  external := ∃ₜ x, (G x).external
  adeq := sorry

@[lantana_alias trSpec_always]
def always (G : TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := TrIProp.always G.internal
  external := □ₜ G.external
  adeq := sorry

@[lantana_alias trSpec_until]
def strongUntil (G H : TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := TrIProp.ex fun a : Fuel => TrIProp.strongUntil G.internal H.internal a
  external := G.external 𝒰ₜ H.external
  adeq := sorry

@[lantana_alias trSpec_finally]
def eventually (G : TrSpec Expr State GF) : TrSpec Expr State GF := strongUntil true G

/-- A state atom: a predicate on the current state and thread pool. -/
@[lantana_alias trSpec_state]
def state (φ : State → ThreadPool Expr → Prop) : TrSpec Expr State GF where
  internal := fun τ => iprop(⌜φ τ.cfg.2 τ.cfg.1⌝)
  external := TrProp.state φ
  adeq := sorry

/-- The same internal reading with a weaker external one: imports trace-level reasoning. -/
@[lantana_alias trSpec_cast]
def cast (G : TrSpec Expr State GF) (R : TrProp Expr State) (pf : G.external ⊆ R) :
    TrSpec Expr State GF where
  internal := G.internal
  external := R
  adeq _ τ h := pf τ (G.adeq _ τ h)

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

instance pure_complete (p : Prop) : Complete (pure (Expr := Expr) (State := State) (GF := GF) p) :=
  sorry
instance and_complete (G H : TrSpec Expr State GF) [Complete G] [Complete H] : Complete (G ∧ₛ H) :=
  sorry
instance or_complete (G H : TrSpec Expr State GF) [Complete G] [Complete H] : Complete (G ∨ₛ H) :=
  sorry
instance imp_complete (A G : TrSpec Expr State GF) [Complete G] : Complete (A →ₛ G) := sorry
instance all_complete {X : Type _} (G : X → TrSpec Expr State GF) [∀ x, Complete (G x)] :
    Complete (all G) := sorry
instance ex_complete {X : Type _} [SIdxLarge SI X] (G : X → TrSpec Expr State GF)
    [∀ x, Complete (G x)] : Complete (ex G) := sorry
instance always_complete (G : TrSpec Expr State GF) [Complete G] : Complete (□ₛ G) := sorry
instance strongUntil_complete (G H : TrSpec Expr State GF) [Complete G] [Complete H] :
    Complete (G 𝒰ₛ H) := sorry
instance state_complete (φ : State → ThreadPool Expr → Prop) :
    Complete (state (GF := GF) φ) := sorry
instance pure_instant (p : Prop) : Instant (pure (Expr := Expr) (State := State) (GF := GF) p) :=
  sorry
instance and_instant (G H : TrSpec Expr State GF) [Instant G] [Instant H] : Instant (G ∧ₛ H) :=
  sorry
instance or_instant (G H : TrSpec Expr State GF) [Instant G] [Instant H] : Instant (G ∨ₛ H) :=
  sorry
instance imp_instant (A G : TrSpec Expr State GF) [Instant G] : Instant (A →ₛ G) := sorry
instance all_instant {X : Type _} (G : X → TrSpec Expr State GF) [∀ x, Instant (G x)] :
    Instant (all G) := sorry
instance ex_instant {X : Type _} [SIdxLarge SI X] (G : X → TrSpec Expr State GF)
    [∀ x, Instant (G x)] : Instant (ex G) := sorry
instance state_instant (φ : State → ThreadPool Expr → Prop) : Instant (state (GF := GF) φ) :=
  sorry

/-! ## Rules of `⊑ₛ` -/

section Rules
variable {G G' H H' A A' X : TrSpec Expr State GF}

@[lantana_alias trSpec_le_refl]
theorem le_refl (G : TrSpec Expr State GF) : G ⊑ₛ G := fun _ => .rfl

@[lantana_alias trSpec_le_trans]
theorem le_trans (h₁ : G ⊑ₛ H) (h₂ : H ⊑ₛ X) : G ⊑ₛ X := fun τ => (h₁ τ).trans (h₂ τ)

@[lantana_alias trSpec_le_true]
theorem le_true : G ⊑ₛ true := sorry

@[lantana_alias trSpec_and_elim_l]
theorem and_elim_l : (G ∧ₛ H) ⊑ₛ G := sorry

@[lantana_alias trSpec_and_elim_r]
theorem and_elim_r : (G ∧ₛ H) ⊑ₛ H := sorry

@[lantana_alias trSpec_and_mono]
theorem and_mono (h₁ : G ⊑ₛ G') (h₂ : H ⊑ₛ H') : (G ∧ₛ H) ⊑ₛ (G' ∧ₛ H') := sorry

@[lantana_alias trSpec_or_mono]
theorem or_mono (h₁ : G ⊑ₛ G') (h₂ : H ⊑ₛ H') : (G ∨ₛ H) ⊑ₛ (G' ∨ₛ H') := sorry

@[lantana_alias trSpec_impl_mono]
theorem imp_mono (hA : A'.external ⊆ A.external) (h : G ⊑ₛ G') : (A →ₛ G) ⊑ₛ (A' →ₛ G') := sorry

@[lantana_alias trSpec_impl_intro_le]
theorem imp_intro_le : G ⊑ₛ (A →ₛ G) := sorry

@[lantana_alias trSpec_forall_mono]
theorem all_mono {Y : Type _} {G G' : Y → TrSpec Expr State GF} (h : ∀ y, G y ⊑ₛ G' y) :
    all G ⊑ₛ all G' := sorry

@[lantana_alias trSpec_exist_mono]
theorem ex_mono {Y : Type _} [SIdxLarge SI Y] {G G' : Y → TrSpec Expr State GF}
    (h : ∀ y, G y ⊑ₛ G' y) : ex G ⊑ₛ ex G' := sorry

@[lantana_alias trSpec_always_mono]
theorem always_mono (h : G ⊑ₛ G') : (□ₛ G) ⊑ₛ (□ₛ G') := sorry

@[lantana_alias trSpec_until_mono]
theorem strongUntil_mono (h₁ : G ⊑ₛ G') (h₂ : H ⊑ₛ H') : (G 𝒰ₛ H) ⊑ₛ (G' 𝒰ₛ H') := sorry

@[lantana_alias trSpec_impl_intro]
theorem imp_intro [Complete A] (h : (A ∧ₛ H) ⊑ₛ G) : H ⊑ₛ (A →ₛ G) := sorry

@[lantana_alias trSpec_impl_elim]
theorem imp_elim [Instant A] : (A ∧ₛ (A →ₛ G)) ⊑ₛ G := sorry

@[lantana_alias trSpec_cast_le]
theorem cast_le (R : TrProp Expr State) (pf : G.external ⊆ R) : G ⊑ₛ G.cast R pf :=
  fun _ => .rfl

@[lantana_alias trSpec_le_cast]
theorem le_cast (R : TrProp Expr State) (pf : G.external ⊆ R) : G.cast R pf ⊑ₛ G :=
  fun _ => .rfl

end Rules

/-! ## Reading off the external property from the shape -/

/-- `Ext G R`: the external reading of `G` entails `R` (computed from the shape of `G`; the
fallback is `G.external` itself). -/
@[lantana_alias TrSpecExt]
class Ext (G : TrSpec Expr State GF) (R : outParam (TrProp Expr State)) : Prop where
  ext_of : G.external ⊆ R

instance (priority := low) ext_default (G : TrSpec Expr State GF) : Ext G G.external :=
  ⟨TrProp.le_refl _⟩
instance ext_pure (p : Prop) : Ext (pure (Expr := Expr) (State := State) (GF := GF) p) ⌜p⌝ₜ :=
  ⟨TrProp.le_refl _⟩
instance ext_state (φ : State → ThreadPool Expr → Prop) :
    Ext (state (GF := GF) φ) (TrProp.state φ) := ⟨TrProp.le_refl _⟩
instance ext_and (G H : TrSpec Expr State GF) (R S : TrProp Expr State) [Ext G R] [Ext H S] :
    Ext (G ∧ₛ H) (R ∧ₜ S) := ⟨TrProp.and_mono Ext.ext_of Ext.ext_of⟩
instance ext_or (G H : TrSpec Expr State GF) (R S : TrProp Expr State) [Ext G R] [Ext H S] :
    Ext (G ∨ₛ H) (R ∨ₜ S) := ⟨TrProp.or_mono Ext.ext_of Ext.ext_of⟩
instance ext_imp (A G : TrSpec Expr State GF) (R : TrProp Expr State) [Ext G R] :
    Ext (A →ₛ G) (A.external →ₜ R) := ⟨TrProp.imp_mono (TrProp.le_refl _) Ext.ext_of⟩
instance ext_all {Y : Type _} (G : Y → TrSpec Expr State GF) (R : Y → TrProp Expr State)
    [∀ y, Ext (G y) (R y)] : Ext (all G) (∀ₜ y, R y) := ⟨TrProp.all_mono fun y => Ext.ext_of⟩
instance ext_ex {Y : Type _} [SIdxLarge SI Y] (G : Y → TrSpec Expr State GF)
    (R : Y → TrProp Expr State) [∀ y, Ext (G y) (R y)] : Ext (ex G) (∃ₜ y, R y) :=
  ⟨TrProp.ex_mono fun y => Ext.ext_of⟩
instance ext_always (G : TrSpec Expr State GF) (R : TrProp Expr State) [Ext G R] :
    Ext (□ₛ G) (□ₜ R) := ⟨TrProp.always_mono Ext.ext_of⟩
instance (priority := high) ext_eventually (G : TrSpec Expr State GF) (R : TrProp Expr State)
    [Ext G R] : Ext (◇ₛ G) (◇ₜ R) := ⟨TrProp.until_mono (TrProp.le_refl _) Ext.ext_of⟩
instance ext_strongUntil (G H : TrSpec Expr State GF) (R S : TrProp Expr State) [Ext G R]
    [Ext H S] : Ext (G 𝒰ₛ H) (R 𝒰ₜ S) := ⟨TrProp.until_mono Ext.ext_of Ext.ext_of⟩
instance ext_cast (G : TrSpec Expr State GF) (R : TrProp Expr State) (pf : G.external ⊆ R) :
    Ext (G.cast R pf) R := ⟨TrProp.le_refl _⟩

end TrSpec
end Lantana
