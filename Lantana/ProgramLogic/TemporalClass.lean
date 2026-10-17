/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.ProgramLogic.TemporalRegistry
public import Lantana.BaseLogic.Model.MUpd

/-! # The ghost state of the temporal layer

Rocq `lantana/program_logic/temporal_class.v`: `TemporalGS` bundles the ghost state of the
obligation model, of the history and of the temporal registry; `TemporalInterp` is the
interpretation of the temporal layer, a parameter the program logic threads without knowing
its content (the trace layer fixes it to the registry state).

The ghost state of the model, `ModelGS`, is in `Lantana.BaseLogic.Model.MUpd`; the ghost state
of the registry, `RegGS`, is in `Lantana.ProgramLogic.TemporalRegistry`.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris



/-- The language-dependent ghost state of the temporal layer: the history and the registry.
The language is an output parameter: a world `GF` carries one language (D30), so that
formulas such as `alwaysI N P : IProp GF` need no language annotations. The ghost state of the
obligation model (`ModelGS GF`) is independent of the language and stays a separate instance
argument. -/
@[lantana_alias temporalGS]
class TemporalGS (Expr : outParam Type) (State : outParam Type) (GF : BundledGFunctors)
    extends HistGS Expr State GF, RegGS Expr State GF

/-- The ghost names of the temporal layer: of the history and of the registry list (D32: small
enough for the existential property of satisfiability, unlike `TemporalGS Expr State GF`). -/
structure TemporalNames where
  /-- The ghost name of the history. -/
  hist : GName
  /-- The ghost name of the registry list. -/
  reg : GName

/-- The ghost state of the temporal layer at the names `γ`, over the world's cameras. -/
@[reducible] def TemporalGS.ofNames {Expr State : Type} {GF : BundledGFunctors}
    [RegGpreS Expr State GF] [MonoListG GF (HistEntry Expr State)] (γ : TemporalNames) :
    TemporalGS Expr State GF where
  toHistGS := HistGS.ofName γ.hist
  toRegGS := RegGS.ofName γ.reg

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
