/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.HeapLang.ProofMode
public import Lantana.HeapLang.TemporalLaws
public import Lantana.Trace

/-! # Lemmas shared by the examples

* `oblFuels_subset`: the fuel of a set of obligations gives that of a subset.
* `threadExpr_terminate_finally` (Rocq `thread_expr_terminate_finally`, `temporal_laws.v`):
  a thread that has returned the value `v` discharges a `finallyI` on its own obligation with its
  final expression `exits v @ i`, and terminates.
* `HeapStateGpreS` and `heapState_init`: the cameras of HeapLang's ghost state before
  allocation (the heap and the thread-expression map), and the allocation of the ghost state
  for an initial state and thread pool (Rocq `gen_heap_init` and `thread_map_init` in the
  adequacy proofs of the examples). The instance `HeapStateGS` is then built from the names.
-/

@[expose] public noncomputable section

namespace Lantana.Examples

open Iris Iris.BI Iris.ProofMode Lantana Lantana.HeapLang Lantana.Language

/-! ## Fuel of a subset -/

section Fuel
variable {GF : BundledGFunctors} [ModelGS GF]

/-- The fuel of a set of obligations gives that of a subset. -/
theorem oblFuels_subset {A B : Oids} (n : Measure) (h : B ⊆ A) :
    oblFuels (GF := GF) A n ⊢ oblFuels B n := by
  unfold oblFuels
  exact BigSepS.bigSepS_subseteq h

end Fuel

/-! ## Terminating on a `finallyI` -/

section Terminate
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]

/-- Discharging a `finallyI` on the thread's final value, with a later credit from an earlier
step: the thread then has no children and terminates. -/
@[lantana_alias thread_expr_terminate_finally]
theorem threadExpr_terminate_finally (i : ThreadId) (E : CoPset) (v : Val) (k : Oid)
    (N : Namespace) (hN : ↑N ⊆ E) :
    threadExpr (GF := GF) i [] (.val v) ⊢ £ₙ 1 -∗ thKids i {k} -∗ oblKids k ∅ -∗
      finallyI N k 1 (threadExpr i [] (.val v)) -∗
      |={E}=>m threadExpr i [] (.val v) ∗ Th.done i := by
  iintro HT Hc HG Hk HF
  imod finallyI_discharge (.thread i) {k} hN (Iris.Std.LawfulSet.mem_singleton.mpr rfl)
    $$ Hc HG Hk HF HT with ⟨HT, HG, -⟩
  imod Th.terminate E i $$ [HG] with #Hd
  · iapply Par.kids_congr _ $$ HG
    intro z
    simp only [Std.ExtTreeSet.mem_erase, Iris.Std.LawfulSet.mem_singleton,
      Std.ExtTreeSet.not_mem_empty]
    grind
  imodintro
  iframe HT
  iexact Hd

end Terminate

/-! ## Allocating HeapLang's ghost state -/

/-- The cameras of HeapLang's ghost state, before allocation: the heap (with its meta data)
and the thread-expression map. -/
@[lantana_alias heap_stateGpreS]
class HeapStateGpreS (GF : BundledGFunctors) where
  [genHeapPre : genHeapPreS Loc (Option Val) GF HeapF]
  [threadMapPre : GhostMapG GF ThreadId Exp ThreadMapF]

attribute [reducible, instance] HeapStateGpreS.genHeapPre HeapStateGpreS.threadMapPre

section Alloc
variable {GF : BundledGFunctors} [HeapStateGpreS GF]

/-- The ghost state of HeapLang from its names. -/
abbrev HeapStateGS.ofNames (γh γm γt : GName) : HeapStateGS GF where
  genHeap := ⟨γh, γm⟩
  threadMap := inferInstance
  threadMapName := γt

/-- Allocation of HeapLang's ghost state for the state `σ` and the pool `tp`: the state
interpretation, a points-to for each location of `σ` and a token for each thread of `tp`. -/
theorem heapState_init (σ : State) (tp : ThreadPool Exp) :
    ⊢@{IProp GF} |==> ∃ _ : HeapStateGS GF, HeapLang.stateInterp σ tp ∗
      bigSepM (M := HeapF) (fun l v => l ↦ v) σ.heap ∗
      ([∗list] j ↦ e ∈ tp, threadExpr j [] e) := by
  imod genHeap_init_names (L := Loc) (V := Option Val) (GF := GF) (H := HeapF) σ.heap with
    ⟨%γh, %γm, Hh, Hpts, -⟩
  imod ghost_map_alloc (GF := GF) (K := ThreadId) (V := Exp) (H := ThreadMapF)
    (ThreadPool.toMap tp) with ⟨%γt, Ha, Hfr⟩
  imodintro
  iexists HeapStateGS.ofNames γh γm γt
  isplitl [Hh Ha]
  · unfold HeapLang.stateInterp
    iframe
  iframe Hpts
  unfold ThreadPool.toMap
  ihave Hfr := (BigSepM.bigSepM_map_seq (PROP := IProp GF) (M' := ThreadMapF) (start := 0)
    (l := tp)).mp $$ Hfr
  unfold threadExpr
  simp only [Nat.zero_add, EctxItemLanguage.fill_nil]
  iexact Hfr

end Alloc

end Lantana.Examples
