/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.HeapLang.PrimitiveLaws
public import Lantana.Trace.Guarantee

/-! # The temporal laws of HeapLang

Rocq `lantana_heap_lang/temporal_laws.v`: the heap assertions are state facts (`StateFact`),
so that they are the atoms of trace specifications: `l ↦{dq} v` says `pointstoSat l dq v`,
`threadExpr i C e` says `threadExprSat i C e`, and a freed location `l ↦{dq} none` says
`freedSat l`.
-/

@[expose] public noncomputable section

namespace Lantana.HeapLang

open Iris Iris.BI Iris.ProofMode Lantana

variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]

omit [ModelGS GF] in
theorem freed_stateInterp (σ : State) (tp : ThreadPool Exp) (l : Loc) (dq : DFrac) :
    stateInterp (GF := GF) σ tp ∗ l ↦{dq} (none : Option Val) ⊢ ⌜freedSat l σ tp⌝ := by
  unfold stateInterp
  iintro ⟨⟨Hh, -⟩, Hl⟩
  ihave %h : ⌜σ.get? l = some none⌝ $$ [Hh Hl]
  · iapply genHeapInterp_lookup
    iframe
  ipureintro
  exact h

@[lantana_alias pointsto_state_fact]
instance pointsTo_stateFact (l : Loc) (dq : DFrac) (v : Val) :
    StateFact (l ↦{dq} some v : IProp GF) (pointstoSat l dq v) where
  state_fact σ tp := pointsTo_stateInterp σ tp l dq v

@[lantana_alias thread_expr_state_fact]
instance threadExpr_stateFact (i : ThreadId) (C : List ECtxItem) (e : Exp) :
    StateFact (threadExpr (GF := GF) i C e) (threadExprSat i C e) where
  state_fact σ tp := threadExpr_stateInterp σ tp i C e

@[lantana_alias freed_state_fact]
instance freed_stateFact (l : Loc) (dq : DFrac) :
    StateFact (l ↦{dq} (none : Option Val) : IProp GF) (freedSat l) where
  state_fact σ tp := freed_stateInterp σ tp l dq

/-! ## Trace-level facts about the heap atoms -/

open scoped Lantana.TrProp

/-- A freed location as a trace specification (Rocq `freed_trSpec`). -/
@[lantana_alias freed_trSpec]
abbrev freedTrSpec {GF : BundledGFunctors} (l : Loc) : TrSpec Exp State GF :=
  TrSpec.state (freedSat l)

/-- A location holds one value at a time (Rocq `tr_pointsto_agree`). -/
@[lantana_alias tr_pointsto_agree]
theorem pointsToTr_agree (l : Loc) (dq₁ dq₂ : DFrac) (v₁ v₂ : Val) :
    (TrProp.state (pointstoSat l dq₁ v₁) ∧ₜ TrProp.state (pointstoSat l dq₂ v₂) :
      TrProp Exp State) ⊆ ⌜v₁ = v₂⌝ₜ := by
  intro τ ⟨h₁, h₂⟩
  simp only [TrProp.state, pointstoSat] at h₁ h₂
  exact (by simpa using h₁.symm.trans h₂ : v₁ = v₂)

/-- A location is not both allocated and freed (Rocq `tr_pointsto_freed`). -/
@[lantana_alias tr_pointsto_freed]
theorem state_pointsto_freed {l : Loc} {dq : DFrac} {v : Val} {τ : Trace Exp State}
    (h₁ : TrProp.state (pointstoSat l dq v) τ) (h₂ : TrProp.state (freedSat l) τ) : False := by
  simp only [TrProp.state, pointstoSat, freedSat] at h₁ h₂
  exact absurd (h₁.symm.trans h₂) (by simp)

end Lantana.HeapLang
