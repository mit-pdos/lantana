/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.ProgramLogic.Configuration

/-! # The state atom

The state atom of Lantana's trace properties: a predicate on the current state and thread pool,
and its rules; the connectives and the LTL rules are generic (`Lantana.Temporal`).

Trace properties (`TrProp`, Rocq `trProp`), their connectives and notations are generic, over
any configuration type (`Lantana.Temporal.Trace`), and so are the rules of `R ⊆ S` (Rocq
`trace_prop_rules.v`) for the connectives, LTL and the fixpoints
(`Lantana.Temporal.TracePropRules`). Lantana's traces are `Trace (Cfg Expr State)`, and this
module adds the language's atom (`TrProp.state`) and its rules.
-/

@[expose] public section

namespace Lantana.TrProp

variable {Expr : Type} {State : Type}

open scoped Lantana.TrProp

/-- A predicate on the current state and thread pool: the state atoms. -/
@[lantana_alias tr_state]
def state (φ : State → ThreadPool Expr → Prop) : TrProp (Cfg Expr State) :=
  fun τ => φ τ.now.2 τ.now.1

/-! ## Rules -/

@[lantana_alias tr_state_mono]
theorem state_mono {φ ψ : State → ThreadPool Expr → Prop} (h : ∀ σ tp, φ σ tp → ψ σ tp) :
    state φ ⊆ state ψ := fun _ hφ => h _ _ hφ

@[lantana_alias tr_state_and]
theorem state_and {φ ψ : State → ThreadPool Expr → Prop} :
    (state φ ∧ₜ state ψ) ⊆ state fun σ tp => φ σ tp ∧ ψ σ tp := fun _ h => h

@[lantana_alias tr_and_state]
theorem and_state {φ ψ : State → ThreadPool Expr → Prop} :
    state (fun σ tp => φ σ tp ∧ ψ σ tp) ⊆ (state φ ∧ₜ state ψ) := fun _ h => h

@[lantana_alias tr_state_pure]
theorem state_pure {φ : State → ThreadPool Expr → Prop} {ψ : Prop} (h : ∀ σ tp, φ σ tp → ψ) :
    state φ ⊆ ⌜ψ⌝ₜ := fun _ hφ => h _ _ hφ

@[lantana_alias tr_pure_state]
theorem pure_state {φ : Prop} {ψ : State → ThreadPool Expr → Prop} (h : φ → ∀ σ tp, ψ σ tp) :
    (⌜φ⌝ₜ : TrProp (Cfg Expr State)) ⊆ state ψ := fun _ hφ => h hφ _ _

end Lantana.TrProp
