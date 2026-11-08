/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TracePropRules

/-! # Fair scheduling of Lantana's threads

Fair scheduling (`fairScheduling`, Rocq `fair_scheduling.v`) is the generic trace property of
`Lantana.Temporal.FairScheduling` at Lantana's thread system (`Pool (Cfg Expr State)`): the strong
fairness of every thread's scheduling action, enabled where the thread is active (`Cfg.active`)
and granted at its trace step (`TraceStep`).  The schedule and the fairness counters under it,
which the adequacy proof threads along the run (`Schedule`, `BehFscnt`,
`exists_fair_schedule_behFscnt`), are generic too.

This module holds the facts of Lantana's instance.  Activity is convex along a behavior: a thread
is active from its fork until it becomes a value, and never again (`Cfg.active_convex'`).  So fair
scheduling of Lantana's threads is the usual justice requirement, weak fairness
(`fairScheduling_sf_iff_wf'`).
-/

@[expose] public section

namespace Lantana

variable {Expr : Type} {State : Type} {Val : Type} [Λ : Language Expr State Val]

open scoped TrProp

#lantana_ignore fscnt_next_rel_th
  "the counters are global along the run under the schedule; the next-position relation is `BehFscnt` at one position"
#lantana_ignore fscnt_next_rel
  "the counters are global along the run under the schedule; the next-position relation is `BehFscnt` at one position"
#lantana_ignore exists_fscnt_next
  "the counters are global along the run under the schedule; the next-position relation is `BehFscnt` at one position"

/-- Activity is convex along a behavior: a thread is active from its fork until it becomes a
value, and never again. -/
theorem Cfg.active_convex' {i : ThreadId} :
    (IsBehavior : TrProp (Cfg Expr State)) ⊆ Fairness.Action.Convex (Cfg.active i) := by
  intro τ hbeh m hm hA k hmk hev
  obtain ⟨k', hkk', hA'⟩ := TrProp.eventually_iff.mp hev
  have hrun : ∀ n, ∃ j, TraceStep j (τ.seq (m + n)) (τ.seq (m + n + 1)) :=
    fun n => isBehavior_iff.mp hbeh (m + n) (Nat.le_trans hm (Nat.le_add_right m n))
  have h := Cfg.active_convex (σ := fun n => τ.seq (m + n)) (i := i) hrun 0 (k - m) (k' - m)
    (Nat.zero_le _) (Nat.sub_le_sub_right hkk' m) (by simp only [Nat.add_zero]; exact hA)
    (by simp only [Nat.add_sub_cancel' (Nat.le_trans hmk hkk')]; exact hA')
  simp only [Nat.add_sub_cancel' hmk] at h
  exact h

/-- Fair scheduling of Lantana's threads is the usual justice requirement, weak fairness, since
activity is convex (a thread is active from its fork until it becomes a value). -/
theorem fairScheduling_sf_iff_wf' {τ : Trace (Cfg Expr State)} (hrun : IsBehavior τ)
    (i : ThreadId) :
    Fairness.Sched.SF i τ ↔ Fairness.Action.WF (Cfg.active i) (TraceStep i) τ :=
  fairScheduling_sf_iff_wf (Cfg.active_convex' τ hrun)

end Lantana
