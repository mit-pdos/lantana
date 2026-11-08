/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TraceProp

/-! # Rules of the state atoms

The rules of `R ⊆ S` (Rocq `trace_prop_rules.v`) for Lantana's state atoms (`TrProp.state`). The
rules of the connectives, of LTL and of the fixpoints are generic, in
`Lantana.Temporal.TracePropRules`.
-/

@[expose] public section

namespace Lantana.TrProp


variable {Expr : Type} {State : Type}

open scoped Lantana.TrProp

/-! ## State atoms -/

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
