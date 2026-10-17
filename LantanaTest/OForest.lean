/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for the obligation forest: a closed world `TestGF : BundledGFunctors.{0}` with the ghost
state of obligations (slots 0 to 3, as in `LantanaTest.OSat`) and of the forest: the children map
(slot 4) and the status map (slot 5), its `OSatGpreS` and `OForestGpreS` instances (the universe
check), the allocation of `osat` and `oforest`, and the life of a thread with one obligation below
it: allocation, a step of the thread, discharge, termination.

Universes: the children and status maps hold `Type` values (`Oids`, `ThreadStatus`), so their
slots are `ULiftOF` of `constOF` of the camera (`ElemG.ofEqLift`), as for the state map. -/

namespace LantanaTest.OForest

open Iris Iris.BI Iris.ProofMode Iris.Std LawfulPartialMap
open Ordinals Ordinal Lantana Lantana.Model

noncomputable def TestGF : BundledGFunctors.{0} := fun n =>
  match n with
  | 0 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO Bool)) OidMap)), by infer_instance⟩
  | 1 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO OblNames)) OidMap)), by infer_instance⟩
  | 2 => ⟨ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel))), by infer_instance⟩
  | 3 => ⟨ULiftOF.{4} (constOFP (Bank Fuel)), by infer_instance⟩
  | 4 => ⟨ULiftOF (constOF (HeapView Parent (Agree (DiscreteO Oids)) ParentMap)),
      by infer_instance⟩
  | 5 => ⟨ULiftOF (constOF (HeapView ThreadId (Agree (DiscreteO ThreadStatus)) ThreadMap)),
      by infer_instance⟩
  | _ => ⟨constOFU Unit, by infer_instance⟩

noncomputable instance : OSatGpreS TestGF where
  stateG := ⟨ElemG.ofEqLift 0 (by unfold TestGF; rfl)⟩
  namesG := ⟨ElemG.ofEqLift 1 (by unfold TestGF; rfl)⟩
  boundG := (ElemG.ofEq 2 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel))))).ofLift
  bankG := (ElemG.ofEq 3 (by unfold TestGF; rfl) :
    ElemG TestGF (ULiftOF.{4} (constOFP (Bank Fuel)))).ofLift

noncomputable instance : OForestGpreS TestGF where
  kidsG := ⟨ElemG.ofEqLift 4 (by unfold TestGF; rfl)⟩
  statusG := ⟨ElemG.ofEqLift 5 (by unfold TestGF; rfl)⟩

/-! Allocation. -/

example : ⊢@{IProp TestGF} |==> ∃ _ : OSatGS TestGF, ∃ _ : OForestGS TestGF,
    osat ∅ ∗ oforest ∅ 0 := by
  imod osat_alloc with ⟨%GS, Hs⟩
  imod @oforest_alloc _ GS _ with ⟨%GF, Hf⟩
  imodintro
  iexists GS, GF
  iframe

section
variable [OSatGS TestGF] [OForestGS TestGF]

/-- Two new threads. -/
example (Ω : Obls) : oforest Ω 0 ⊢@{IProp TestGF} |==> (oforest Ω 2 ∗
    OForest.kids (.thread 0) ∅ ∗ OForest.kids (.thread 1) ∅) := by
  iintro Hf
  imod oforest_alloc_threads Ω 0 2 $$ Hf with ⟨Hf, Hl⟩
  rw [show List.range' 0 2 = [0, 1] from rfl]
  icases BigSepL.bigSepL_cons.mp $$ Hl with ⟨⟨Hk₀, -⟩, Hl⟩
  icases BigSepL.bigSepL_cons.mp $$ Hl with ⟨⟨Hk₁, -⟩, -⟩
  imodintro
  iframe

/-- A new thread with a new obligation below it. -/
example (Ω : Obls) (tc : Nat) :
    osat Ω ∗ oforest Ω tc ⊢@{IProp TestGF} |==>
      (osat (insert Ω Ω.fresh (.assigned 1 tc)) ∗ oforest (insert Ω Ω.fresh (.assigned 1 tc))
        (tc + 1) ∗ OForest.kids (.thread tc) ({Ω.fresh} ∪ ∅) ∗
        OForest.kids (.obl Ω.fresh) ∅) := by
  iintro ⟨Hs, Hf⟩
  imod oforest_alloc_thread Ω tc $$ Hf with ⟨Hf, Hk, -⟩
  imod osat_alloc_obl_assigned (Obls.get?_fresh Ω) (1 : Ordinal.{1}) tc $$ Hs
    with ⟨Hs, #Hb, -, -, -, -⟩
  imod oforest_alloc_obl (p := .thread tc) (Obls.get?_fresh Ω) rfl Ordinal.le_rfl
    $$ [$Hf $Hk $Hb //] with ⟨Hf, -, Hk, Hkk⟩
  imodintro
  iframe

/-- The life of a thread with one obligation: allocation of the thread and of the obligation
(fuel `1`), a step of the thread (the obligation burns its unit), discharge, termination. -/
example (Ω : Obls) (tc : Nat) :
    osat Ω ∗ oforest Ω tc ⊢@{IProp TestGF} |==> ∃ Ω', osat Ω' ∗ oforest Ω' (tc + 1) ∗
      OForest.done tc := by
  have hsing : ({Ω.fresh} ∪ ∅ : Oids) = {Ω.fresh} :=
    LawfulSet.ext fun x => by
      rw [LawfulSet.mem_union]
      exact ⟨fun h => h.resolve_right LawfulSet.mem_empty, .inl⟩
  have hset : (({Ω.fresh} : Oids) \ {Ω.fresh}) = ∅ :=
    LawfulSet.ext fun x => by
      rw [LawfulSet.mem_diff]
      exact ⟨fun h => (h.2 h.1).elim, fun h => (LawfulSet.mem_empty h).elim⟩
  have hk : Ω.fresh ∈ ({Ω.fresh} : Oids) := LawfulSet.mem_singleton.2 rfl
  iintro ⟨Hs, Hf⟩
  imod oforest_alloc_thread Ω tc $$ Hf with ⟨Hf, Hk, He⟩
  imod osat_alloc_obl_assigned (Obls.get?_fresh Ω) (1 : Ordinal.{1}) tc $$ Hs
    with ⟨Hs, #Hb, -, Ha, Hu, -⟩
  imod oforest_alloc_obl (p := .thread tc) (Obls.get?_fresh Ω) rfl Ordinal.le_rfl
    $$ [$Hf $Hk $Hb //] with ⟨Hf, -, Hk, Hkk⟩
  rw [hsing]
  ihave Hus : [∗set] x ∈ ({Ω.fresh} : Oids), ∃ c, ⌜0 < c⌝ ∗ OSat.fuel x c $$ [Hu]
  · iapply BigSepS.bigSepS_singleton.mpr
    iexists 1
    iframe Hu
    ipureintro
    exact Ordinal.zero_lt_one
  imod oforest_osat_step _ _ tc _ $$ [$Hs $Hf $Hk $Hus] with ⟨%Ω₂, -, Hs, Hf, Hk⟩
  imod osat_discharge _ _ $$ [$Hs $Ha] with ⟨Hs, -, -⟩
  imod oforest_discharge_obl hk $$ [$Hf $Hk $Hkk] with ⟨Hf, Hk⟩
  rw [hset]
  imod oforest_exec_to_done _ _ tc $$ [$Hf $He $Hk] with ⟨Hf, Hd⟩
  imodintro
  iexists _
  iframe

/-- A terminated thread owns no obligation. -/
example (Ω : Obls) (tc : Nat) (k : Oid) (a : Fuel) (hk : get? Ω k = some (.assigned a 0)) :
    oforest Ω tc ∗ OForest.done 0 ⊢@{IProp TestGF} False :=
  oforest_assigned_done_false hk

end

end LantanaTest.OForest
