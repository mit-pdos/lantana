module

public import Lantana

/-! Tests for the model of trace specifications: a closed world `TestGF : BundledGFunctors.{0}`
with all the ghost state the temporal layer of HeapLang needs before allocation, that is,
world satisfaction and credits (slots 0–3, as in `LantanaTest.FUpd`), obligations (4–7, as in
`LantanaTest.OSat`), witnesses (8–9, as in `LantanaTest.OWit`), the forest (10–11, as in
`LantanaTest.OForest`), the model history (12), the registry (13–14, as in
`LantanaTest.Registry`) and the history (15); its `TemporalGpreS` instance (the universe check
of the adequacy theorem's assumptions), and the lemmas of `Lantana.Trace.TrSpecModel` in it.

Universes: the model history holds obligation maps (ordinals, `Type 2`), so its slot is
`ULiftOF.{4}` of `constOFP` of the camera, read back with `ElemG.ofLift`, as for the bound and
the bank of obligations. The instance records are in `Type 4`, too large for the existential
property of satisfiability (the last example); the ghost names are small. -/

namespace LantanaTest.TrSpecModel

open Iris Iris.BI Iris.ProofMode Iris.Std LawfulPartialMap
open Ordinals Ordinal Lantana Lantana.Model Lantana.HeapLang
open scoped Lantana.TrProp Lantana.TrSpec

/-- The functor of saved trace predicates of HeapLang. -/
abbrev TrPredF : COFE.OFunctorPre := DiscreteFunOF fun _ : Trace Exp State => LaterOF IdOF

noncomputable def TestGF : BundledGFunctors.{0} := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨ULiftOF (constOF CoPsetDisjL), by infer_instance⟩
  | 2 => ⟨ULiftOF (constOF (DisjointLeibnizSet PosSet)), by infer_instance⟩
  | 3 => ⟨ULiftOF.{4} (CreditF Ordinal.{1}), by infer_instance⟩
  | 4 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO Bool)) OidMap)), by infer_instance⟩
  | 5 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO OblNames)) OidMap)), by infer_instance⟩
  | 6 => ⟨ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel))), by infer_instance⟩
  | 7 => ⟨ULiftOF.{4} (constOFP (Bank Fuel)), by infer_instance⟩
  | 8 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO GName)) OidMap)), by infer_instance⟩
  | 9 => ⟨ULiftOF.{4} (constOFP (BCred Fuel)), by infer_instance⟩
  | 10 => ⟨ULiftOF (constOF (HeapView Parent (Agree (DiscreteO Oids)) ParentMap)),
      by infer_instance⟩
  | 11 => ⟨ULiftOF (constOF (HeapView ThreadId (Agree (DiscreteO ThreadStatus)) ThreadMap)),
      by infer_instance⟩
  | 12 => ⟨ULiftOF.{4} (constOFP (MonoList (DiscreteO MEvent))), by infer_instance⟩
  | 13 => ⟨ULiftOF (constOF (MonoList (DiscreteO (Nat × RegEntry)))), by infer_instance⟩
  | 14 => ⟨DFracAgree.DFracAgreeRF TrPredF, by infer_instance⟩
  | 15 => ⟨ULiftOF (constOF (MonoList (DiscreteO (HistEntry Exp State)))), by infer_instance⟩
  | _ => ⟨constOFU Unit, by infer_instance⟩

noncomputable instance : WsatGpreS TestGF where
  inv := ElemG.ofEq 0 (by unfold TestGF; rfl)
  enabled := ElemG.ofEqLift 1 (by unfold TestGF; rfl)
  disabled := ElemG.ofEqLift 2 (by unfold TestGF; rfl)

noncomputable instance : TlcGpreS TestGF where
  elem := (ElemG.ofEq 3 (by unfold TestGF; rfl)).ofLift

noncomputable instance : InvGpreS TestGF where
  toWsatGpreS := inferInstance
  toTlcGpreS := inferInstance

noncomputable instance : OSatGpreS TestGF where
  stateG := ⟨ElemG.ofEqLift 4 (by unfold TestGF; rfl)⟩
  namesG := ⟨ElemG.ofEqLift 5 (by unfold TestGF; rfl)⟩
  boundG := (ElemG.ofEq 6 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel))))).ofLift
  bankG := (ElemG.ofEq 7 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (Bank Fuel)))).ofLift

noncomputable instance : OWitGpreS TestGF where
  namesG := ⟨ElemG.ofEqLift 8 (by unfold TestGF; rfl)⟩
  credG := (ElemG.ofEq 9 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (BCred Fuel)))).ofLift

noncomputable instance : OForestGpreS TestGF where
  kidsG := ⟨ElemG.ofEqLift 10 (by unfold TestGF; rfl)⟩
  statusG := ⟨ElemG.ofEqLift 11 (by unfold TestGF; rfl)⟩

noncomputable instance : MHistGpreS TestGF where
  elem := (ElemG.ofEq 12 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (MonoList (DiscreteO MEvent))))).ofLift

noncomputable instance : ModelGpreS TestGF where

noncomputable instance : RegGpreS Exp State TestGF where
  listG := ⟨ElemG.ofEqLift 13 (by unfold TestGF; rfl)⟩
  predG := { elemG := ElemG.ofEq 14 (by unfold TestGF; rfl) }

noncomputable instance : MonoListG TestGF (HistEntry Exp State) :=
  ⟨ElemG.ofEqLift 15 (by unfold TestGF; rfl)⟩

noncomputable instance : TemporalGpreS Exp State TestGF where

/-! Allocation: the model (with its `ModelGS`), and world satisfaction with its names. -/

example : ⊢@{IProp TestGF} |==> ∃ _ : ModelGS TestGF,
    (∃ x : Ordinal.{1}, ●£ₒ x) ∗ wsat ∗ ownE ⊤ ∗ modelInterp [(0, ∅)] 0 ∅ ∅ 0 0 :=
  modelInterp_alloc 0

example : ⊢@{IProp TestGF} |==> ∃ γ : GName × GName × GName × GName,
    @invInitRes TestGF (InvGS.ofNames γ) :=
  invGS_alloc_names

/-! The lemmas in the closed world. -/

section
variable (τ : Trace Exp State)

example (G : TrSpec Exp State TestGF)
    (h : ∀ [ModelGS TestGF] [TemporalGS Exp State TestGF], ⊢ G.internal τ) : G.external τ :=
  TrSpec.valid_ext G τ h

/-- A complete specification true on the trace is valid, so it holds there: `□ ⊤`. -/
example : (□ₛ (⌜True⌝ₛ : TrSpec Exp State TestGF)).external τ :=
  TrSpec.valid_ext _ τ (TrSpec.Complete.complete τ fun _ _ => trivial)

example (G G' : TrSpec Exp State TestGF) [TrSpec.Complete G] (h : G ⊑ₛ G') :
    G.external ⊆ G'.external :=
  TrSpec.le_sound G G' h

/-- Soundness with an `always`: `□ (φ ∧ ψ) ⊑ₛ □ φ`, read on traces. -/
example (φ ψ : State → ThreadPool Exp → Prop) :
    (□ₛ (TrSpec.state φ ∧ₛ TrSpec.state ψ : TrSpec Exp State TestGF)).external ⊆
      (□ₛ (TrSpec.state φ : TrSpec Exp State TestGF)).external :=
  TrSpec.le_sound _ _ (TrSpec.always_mono TrSpec.and_elim_l)

example : ¬ ((□ₛ ⌜False⌝ₛ) ⊑ₛ (⌜False⌝ₛ : TrSpec Exp State TestGF)) :=
  TrSpec.always_elim_not_le τ

example : ¬ (TrSpec.untilBody TrSpec.true ⌜False⌝ₛ
      (TrSpec.mu (TrSpec.untilBody TrSpec.true ⌜False⌝ₛ)) ⊑ₛ
    TrSpec.mu (TrSpec.untilBody (TrSpec.true : TrSpec Exp State TestGF) ⌜False⌝ₛ)) :=
  TrSpec.mu_unfold_r_guarded τ

end

/-! The universe finding: the instance records are too large for the existential property. -/

example : True := by
  fail_if_success have : SIdxLarge SI (ModelGS TestGF) := inferInstance
  fail_if_success have : SIdxLarge SI (TemporalGS Exp State TestGF) := inferInstance
  trivial

example : SIdxLarge SI (GName × GName × GName × GName) := inferInstance

end LantanaTest.TrSpecModel
