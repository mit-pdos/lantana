/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.Adequacy.Temporal

/-! # Adequacy: safety

Rocq `lantana/trace/adequacy_safety.v`: Iris-style safety on fair behaviors, read off the run
directly (no guarantees, no registry): the scheduled thread is never stuck, and a terminated
thread `j` satisfies its postcondition. Lantana-Lean derives it from the generalized single-step
simulation of the temporal adequacy proof (D20) instead of duplicating that proof.

**Skeleton (M1):** the statement; the proof is M6.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open Iris.ProgramLogic (toVal)
open scoped Lantana.TrProp

variable {Expr State Val : Type} [Language Expr State Val]

/-- The scheduled thread of a trace state is a value or can step (Rocq `not_stuck`). -/
@[lantana_alias adequacy_safety.not_stuck] -- shadows `language.not_stuck` in Rocq too
def TraceState.notStuck (ts : TraceState Expr State) : Prop :=
  ∃ e, ts.cfg.1[ts.thread]? = some e ∧ Language.NotStuck e ts.cfg.2

/-- If thread `j` has terminated with the value `v`, then `Φ j v` (Rocq `if_term_val`). -/
@[lantana_alias if_term_val]
def TraceState.ifTermVal (j : ThreadId) (Φ : ThreadId → Val → Prop)
    (ts : TraceState Expr State) : Prop :=
  ∀ e v, ts.cfg.1[j]? = some e → toVal e = some v → Φ j v

/-- Safety in the sense of Iris: always, the scheduled thread is not stuck and a terminated
thread `j` satisfies `Φ j` (Rocq `safety_iris`). -/
@[lantana_alias safety_iris]
def safetyIris (j : ThreadId) (Φ : ThreadId → Val → Prop) : TrProp Expr State :=
  □ₜ (TrProp.now TraceState.notStuck ∧ₜ TrProp.now (TraceState.ifTermVal (Val := Val) j Φ))

/-- Safety adequacy (Rocq `lwp_adequacy_safety_iris`): if, in every world, the initial threads
can be given `lWP`s whose postcondition for thread `j` implies `Φ j`, then every fair behavior
from the initial configuration is safe for `j`. -/
@[lantana_alias lwp_adequacy_safety_iris]
theorem lwp_adequacy_safety {GF : BundledGFunctors} [TemporalGpreS Expr State GF]
    (σ : State) (tp : ThreadPool Expr) (i j : ThreadId) (Φ : ThreadId → Val → Prop)
    (τ : Trace Expr State) (hbeh : IsBehavior τ) (hfair : fairScheduling τ) (hpos : τ.pos = 0)
    (hinit : τ.seq 0 = ⟨(tp, σ), i⟩)
    (hwp : ∀ [ModelGS GF] [TemporalGS Expr State GF],
      ∃ c : Fuel, ⊢@{IProp GF} |={⊤}=>
        ∃ (SI : StateInterp Expr State GF) (forkPost : ThreadId → Val → IProp GF)
          (Ψ : ThreadId → Val → IProp GF),
          let _ : LantanaGS Expr State Val GF :=
            { toTemporalGS := inferInstance, toStateInterp := SI, forkPost := forkPost }
          iprop(⌜∀ v, Ψ j v ⊢ ⌜Φ j v⌝⌝ ∧ stateInterp σ tp ∗
            (£ₒ c -∗ ([∗list] j ∈ List.range tp.length, thKids j ∅) -∗
              |={⊤}=>m [∗list] j ↦ e ∈ tp, lWP e @ j; ⊤ {{ liftTerm j Ψ }}))) :
    safetyIris j Φ τ := sorry

end Lantana
