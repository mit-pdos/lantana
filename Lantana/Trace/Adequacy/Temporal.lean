/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TemporalFormula
public import Lantana.Trace.FairScheduling
public import Lantana.Trace.Adequacy.Alloc

/-! # Adequacy (Theorem 1)

Rocq `lantana/trace/adequacy_temporal.v`: `lWP` is a running system with the one-step
property, so if the initial resources guarantee `G`, every fair behavior from the initial
configuration satisfies the trace reading of `G`.

**Skeleton (M1):** the statement; the proof (the run `run_step`, the certification of the
registry, the one-step property `sys_step_lwp`) is M6. The ghost state is allocated inside
the proof, so the premise quantifies over its instances; the user then chooses the state
interpretation (after allocating the language's ghost state), the fork postcondition and
the per-thread postconditions.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open scoped Lantana.TrSpec Lantana.TrProp

/-- The ghost state a world must provide before the temporal layer is allocated: the model's
(Rocq `mupdGpreS`), the history's (`histGpreS`) and the registry's (`tregGpreS`). -/
class TemporalGpreS (Expr State : Type) (GF : BundledGFunctors) where
  [modelG : ModelGpreS GF]
  [histG : MonoListG GF (HistEntry Expr State)]
  [regG : RegGpreS Expr State GF]

attribute [reducible, instance] TemporalGpreS.modelG TemporalGpreS.histG TemporalGpreS.regG

/-- **Theorem 1 (adequacy).** Let `G` be a trace specification and `R` a trace property implied
by its trace reading. If, for every allocation of the temporal ghost state, the user can
produce (under a fancy update, from some amount `c` of later credits and the initial threads'
empty sets of children) a resource `P` that guarantees `G` together with `lWP`s for the
initial threads, then every fair behavior from the initial configuration satisfies `R`. -/
@[lantana_alias lwp_adequacy_temporal]
theorem lwp_adequacy_temporal {Expr State Val : Type} [Language Expr State Val]
    {GF : BundledGFunctors} [TemporalGpreS Expr State GF]
    (σ : State) (tp : ThreadPool Expr) (i : ThreadId) (G : TrSpec Expr State GF)
    (R : TrProp Expr State) (hGR : G.external ⊆ R) (τ : Trace Expr State)
    (hbeh : IsBehavior τ) (hfair : fairScheduling τ) (hpos : τ.pos = 0)
    (hinit : τ.seq 0 = ⟨(tp, σ), i⟩)
    (hwp : ∀ [ModelGS GF] [TemporalGS Expr State GF],
      ∃ c : Fuel, ⊢@{IProp GF} |={⊤}=>
        ∃ (SI : StateInterp Expr State GF) (forkPost : ThreadId → Val → IProp GF)
          (Ψ : ThreadId → Val → IProp GF),
          let _ : LantanaGS Expr State Val GF :=
            { toTemporalGS := inferInstance, toStateInterp := SI, forkPost := forkPost }
          iprop(stateInterp σ tp ∗
            (£ₒ c -∗ ([∗list] j ∈ List.range tp.length, thKids j ∅) -∗
              |={⊤}=>m ∃ P : IProp GF, (P ⊨ₜ G) ∗ P ∗
                (P -∗ |={⊤}=>m [∗list] j ↦ e ∈ tp, lWP e @ j; ⊤ {{ liftTerm j Ψ }})))) :
    R τ := sorry

end Lantana
