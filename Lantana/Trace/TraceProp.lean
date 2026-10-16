/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.ProgramLogic.Trace

/-! # Trace properties

Predicates on traces (`TrProp`, Rocq `trProp`): the external reading of temporal properties,
where LTL is reasoned about classically. The connectives carry a subscript `ₜ` (`∧ₜ`, `□ₜ`,
`◇ₜ`, `○ₜ`, `𝒰ₜ`, …) so that they never clash with the `iProp` connectives (D28).
Entailment `R ⊆ S` is validity of `R →ₜ S`. Rules are in `Lantana.Trace.TracePropRules`,
fair scheduling in `Lantana.Trace.FairScheduling`.
-/

@[expose] public section

namespace Lantana


/-- A predicate on trace states. -/
@[lantana_alias tsProp]
abbrev TsProp (Expr : Type) (State : Type) := TraceState Expr State → Prop

/-- A predicate on traces: the external reading of a temporal property. -/
@[lantana_alias trProp]
abbrev TrProp (Expr : Type) (State : Type) := Trace Expr State → Prop

namespace TrProp

variable {Expr : Type} {State : Type}

/-- A predicate on the current trace state. -/
@[lantana_alias ts_emb]
def now (P : TsProp Expr State) : TrProp Expr State := fun τ => P τ.now

/-- A predicate on the current state and thread pool: the state atoms. -/
@[lantana_alias tr_state]
def state (φ : State → ThreadPool Expr → Prop) : TrProp Expr State :=
  fun τ => φ τ.cfg.2 τ.cfg.1

@[lantana_alias tr_pure]
def pure (p : Prop) : TrProp Expr State := fun _ => p

@[lantana_alias tr_and]
def and (P Q : TrProp Expr State) : TrProp Expr State := fun τ => P τ ∧ Q τ

@[lantana_alias tr_or]
def or (P Q : TrProp Expr State) : TrProp Expr State := fun τ => P τ ∨ Q τ

@[lantana_alias tr_impl]
def imp (P Q : TrProp Expr State) : TrProp Expr State := fun τ => P τ → Q τ

@[lantana_alias tr_forall]
def all {A : Sort _} (P : A → TrProp Expr State) : TrProp Expr State := fun τ => ∀ a, P a τ

@[lantana_alias tr_exist]
def ex {A : Sort _} (P : A → TrProp Expr State) : TrProp Expr State := fun τ => ∃ a, P a τ

/-- `□ₜ P`: `P` holds at every position from the current one on. -/
@[lantana_alias tr_always]
def always (P : TrProp Expr State) : TrProp Expr State :=
  fun τ => ∀ m, τ.pos ≤ m → P { τ with pos := m }

/-- `P 𝒰ₜ Q` (strong until): `Q` holds at some later position, and `P` at every position
before it. -/
@[lantana_alias tr_until]
def strongUntil (P Q : TrProp Expr State) : TrProp Expr State :=
  fun τ => ∃ m, τ.pos ≤ m ∧ Q { τ with pos := m } ∧ ∀ l, τ.pos ≤ l → l < m → P { τ with pos := l }

/-- `◇ₜ Q`: `Q` holds at some position from the current one on. -/
@[lantana_alias tr_eventually]
def eventually (Q : TrProp Expr State) : TrProp Expr State := strongUntil (pure True) Q

/-- `○ₜ P`: `P` holds at the next position. -/
@[lantana_alias tr_next]
def next (P : TrProp Expr State) : TrProp Expr State := fun τ => P τ.next

/-! ## Notations -/

scoped notation:max "⌜" p "⌝ₜ" => TrProp.pure p
scoped infixr:35 " ∧ₜ " => TrProp.and
scoped infixr:30 " ∨ₜ " => TrProp.or
scoped infixr:25 " →ₜ " => TrProp.imp
scoped notation:max "□ₜ " P:40 => TrProp.always P
scoped notation:max "◇ₜ " P:40 => TrProp.eventually P
scoped notation:max "○ₜ " P:40 => TrProp.next P
scoped infixr:40 " 𝒰ₜ " => TrProp.strongUntil

open Lean in
/-- `∀ₜ x y, P`: the trace-level universal quantifier. -/
scoped syntax "∀ₜ " explicitBinders ", " term : term
open Lean in
/-- `∃ₜ x y, P`: the trace-level existential quantifier. -/
scoped syntax "∃ₜ " explicitBinders ", " term : term

open Lean in
scoped macro_rules
  | `(∀ₜ $xs, $b) => Lean.expandExplicitBinders ``TrProp.all xs b
  | `(∃ₜ $xs, $b) => Lean.expandExplicitBinders ``TrProp.ex xs b

/-- Trace entailment `R ⊆ S`: the validity of `R →ₜ S`. -/
@[lantana_alias tr_le]
def le (R S : TrProp Expr State) : Prop := ∀ τ, R τ → S τ

instance : HasSubset (TrProp Expr State) := ⟨le⟩

@[lantana_alias tr_le_impl]
theorem le_iff_imp (R S : TrProp Expr State) : R ⊆ S ↔ ∀ τ, (R →ₜ S) τ := Iff.rfl

/-! ## Fixpoints (Knaster–Tarski at `Prop`) -/

/-- A monotone trace functor. -/
@[lantana_alias tr_mono]
def Mono (Φ : TrProp Expr State → TrProp Expr State) : Prop :=
  ∀ R R', (∀ τ, R τ → R' τ) → ∀ τ, Φ R τ → Φ R' τ

/-- The greatest fixpoint: the union of the post-fixpoints. -/
@[lantana_alias tr_gfp]
def gfp (Φ : TrProp Expr State → TrProp Expr State) : TrProp Expr State :=
  fun τ => ∃ R, (∀ τ', R τ' → Φ R τ') ∧ R τ

/-- The least fixpoint: the intersection of the pre-fixpoints. -/
@[lantana_alias tr_lfp]
def lfp (Φ : TrProp Expr State → TrProp Expr State) : TrProp Expr State :=
  fun τ => ∀ R, (∀ τ', Φ R τ' → R τ') → R τ

end TrProp
end Lantana
