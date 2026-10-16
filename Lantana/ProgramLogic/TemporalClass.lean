/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.ProgramLogic.HistoryInterp

/-! # The ghost state of the temporal layer

Rocq `lantana/program_logic/temporal_class.v`: `TemporalGS` bundles the ghost state of the
obligation model, of the history and of the temporal registry; `TemporalInterp` is the
interpretation of the temporal layer, a parameter the program logic threads without knowing
its content (the trace layer fixes it to the registry state).

**Skeleton (M1):** `ModelGS` and `RegGS` are placeholders; their fields (ghost names) come
with the model (M4) and the registry (M5).
-/

@[expose] public noncomputable section

namespace Lantana

open Iris


/-- The ghost state of the obligation model. (Placeholder.) -/
@[lantana_alias mupdGS]
class ModelGS (GF : BundledGFunctors) : Type where

/-- The ghost state of the temporal registry (it saves trace predicates, hence the
language). (Placeholder.) -/
@[lantana_alias tregGS]  -- Rocq `tregGS.tregGS`
class RegGS (Expr : Type) (State : Type) (GF : BundledGFunctors) : Type where

/-- The language-dependent ghost state of the temporal layer: the history and the registry.
The ghost state of the obligation model (`ModelGS GF`) is independent of the language and
stays a separate instance argument (Lean cannot project it from a bundle whose other
parameters it does not mention). -/
@[lantana_alias temporalGS]
class TemporalGS (Expr : Type) (State : Type) (GF : BundledGFunctors)
    extends HistGS Expr State GF, RegGS Expr State GF

/-- The interpretation of the temporal layer; one interpretation per instance of the ghost
state. The language is an output parameter: a world `GF` carries one language (so that the
model update `|={E}=>m P`, whose `P` does not mention the language, elaborates). -/
@[lantana_alias TemporalInterp]
class TemporalInterp (Expr : outParam Type) (State : outParam Type) (GF : BundledGFunctors)
    [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF] where
  /-- The interpretation. -/
  interp : IProp GF

/-- The interpretation of the temporal layer, with the language explicit. -/
abbrev temporalInterp (Expr : Type) (State : Type) {GF : BundledGFunctors} [ModelGS GF]
    [TemporalGS Expr State GF] [StateInterp Expr State GF] [TemporalInterp Expr State GF] :
    IProp GF :=
  TemporalInterp.interp (Expr := Expr) (State := State)

/-- What the program logic threads between steps and through model updates: the history
interpretation and the interpretation of the temporal layer (Rocq `history_tinterp`). -/
@[lantana_alias history_tinterp]
def historyTInterp {Expr : Type} {State : Type} {GF : BundledGFunctors} [ModelGS GF]
    [TemporalGS Expr State GF] [StateInterp Expr State GF] [TemporalInterp Expr State GF]
    (h : List (HistEntry Expr State)) (n : Nat) (σ : State) (tp : ThreadPool Expr) : IProp GF :=
  iprop(historyInterp h n σ tp ∗ temporalInterp Expr State)

end Lantana
