/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.BaseLogic.Satisfiable
public import Lantana.ProgramLogic.OblForest

/-! # Adequacy: allocating the ghost state

What the adequacy theorems allocate before the user's resources (Rocq
`lantana/trace/adequacy_temporal.v`, the proof of `lwp_adequacy_temporal`: `model_interp_alloc 0`,
`history_interp_init`, `reg_alloc`, `thP_kids_alloc_threads`), in the form of decision D32: the
existential is over the ghost *names* (`ModelNames × TemporalNames`, small enough for the
existential property of satisfiability), and the instances are rebuilt from the world's
cameras and the names (`ModelGS.ofNames`, `TemporalGS.ofNames`). The instance records themselves
(`ModelGS GF`, `TemporalGS Expr State GF`) are in `Type 4`, too large for `sat_exists`.

`iPropSat.sat_bupd_exists` extracts the names from the satisfiability of an allocation;
`iPropSat.sat_alloc` from an allocation lemma directly.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode Ordinals

universe u v

/-! ## Extracting the ghost names -/

section Sat

variable {GF : BundledGFunctors.{u}} {X : Type v} [SIdxLarge SI X] {Φ : X → IProp GF}

/-- The ghost names of a satisfiable allocation: `sat_bupd`, then `sat_exists`. -/
theorem iPropSat.sat_bupd_exists (h : iPropSat.sat iprop(|==> ∃ x, Φ x)) :
    ∃ x, iPropSat.sat (Φ x) :=
  iPropSat.sat_exists (iPropSat.sat_bupd h)

/-- An allocation lemma gives satisfiable resources at some ghost names. -/
theorem iPropSat.sat_alloc (h : ⊢ |==> ∃ x, Φ x) : ∃ x, iPropSat.sat (Φ x) :=
  iPropSat.sat_bupd_exists (iPropSat.mono (true_emp.mp.trans h) iPropSat_intro)

end Sat

/-! ## The initial ghost state of adequacy -/

section Alloc

variable {Expr State : Type} {GF : BundledGFunctors} [ModelGpreS GF] [RegGpreS Expr State GF]
  [MonoListG GF (HistEntry Expr State)]

/-- Allocation of the ghost state of adequacy for the initial configuration `(tp, σ)`, at
names `γ` (D32; the world's cameras are those of `TemporalGpreS`): the credit supply, world
satisfaction and the full mask; the model at step `0` with no obligation and no witness,
over the threads of `tp`; the empty children of the initial threads; the history with its first
entry, for every state interpretation (chosen after the allocation); the empty registry. -/
theorem adequacy_alloc_names (σ : State) (tp : ThreadPool Expr) :
    ⊢@{IProp GF} |==> ∃ γ : ModelNames × TemporalNames,
      letI := ModelGS.ofNames (GF := GF) γ.1
      letI := TemporalGS.ofNames (Expr := Expr) (State := State) (GF := GF) γ.2
      iprop((∃ x : Ordinal.{1}, ●£ₒ x) ∗ wsat ∗ ownE ⊤ ∗
        Model.modelInterp [(0, ∅)] 0 ∅ ∅ 0 tp.length ∗
        ([∗list] j ∈ List.range tp.length, thKids j ∅) ∗
        (∀ _ : StateInterp Expr State GF,
          stateInterp σ tp ==∗ historyInterp [(σ, tp)] 0 σ tp) ∗
        regAuth []) := by
  imod Model.modelInterp_alloc_names (GF := GF) 0 with ⟨%γm, Hc, Hw, HE, HM⟩
  imod historyInterp_init_names (GF := GF) σ tp with ⟨%γh, HH⟩
  imod regGS_alloc_names (Expr := Expr) (State := State) (GF := GF) with ⟨%γr, HR⟩
  letI := ModelGS.ofNames (GF := GF) γm
  have hk := thKids_alloc_threads (GF := GF) ∅ 0 tp.length
  rw [Nat.zero_add, ← List.range_eq_range'] at hk
  unfold Model.modelInterp
  icases HM with ⟨HMH, Hs, Hf, Hwit, %hI⟩
  imod hk $$ Hf with ⟨Hf, Hk⟩
  imodintro
  iexists (γm, ⟨γh, γr⟩)
  iframe Hc Hw HE HMH Hs Hf Hwit Hk HH HR
  ipureintro
  exact hI

end Alloc

end Lantana
