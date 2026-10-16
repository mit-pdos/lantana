/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
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
@[lantana_alias freed_state_interp]
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

end Lantana.HeapLang
