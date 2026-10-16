/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TracePropRules

/-! # Fair scheduling

Every active thread is eventually scheduled (Rocq `fair_scheduling.v`). The fairness counter
that the adequacy proof threads (Rocq `beh_fscnt`, a coinductive predicate obtained by choice)
is replaced by an explicit sequence chosen once from `fairScheduling` (D18); it lives with the
adequacy proof.
-/

@[expose] public section

namespace Lantana

universe u v w

variable {Expr : Type u} {State : Type v} {Val : Type w} [Λ : Language Expr State Val]

open scoped TrProp

/-- Fair scheduling: at every position, every thread is inactive or active and eventually
scheduled. -/
@[lantana_alias fair_scheduling]
def fairScheduling : TrProp Expr State :=
  □ₜ (∀ₜ i : ThreadId, TrProp.now (TraceState.inactive i) ∨ₜ
    (TrProp.now (TraceState.active i) ∧ₜ ◇ₜ TrProp.now (TraceState.turn i)))

@[lantana_alias fair_scheduling_next]
theorem fairScheduling_next {τ : Trace Expr State} (h : fairScheduling τ) :
    fairScheduling τ.next :=
  fun m hm => h m (Nat.le_of_succ_le hm)

end Lantana
