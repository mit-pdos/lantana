/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.ThreadSystem
public import Lantana.Temporal.Fairness.Action

/-! # The recipe `own`: a thread's view of an action

`a.own i` is the fairness assumption whose attempts are the steps of the thread at `i` from a
configuration where the action `a` is enabled.  Its counter moves only at the thread's own steps
(`own_counterMove_stay_of_other`).  The view is sound when every grant is one of the thread's
transitions (`OwnGrant`, `own_holds_of_sf`), and it loses nothing when the thread steps infinitely
often and the enabling condition persists (`Persists`, from `Stable`; `sf_of_own_holds`,
`sf_iff_own_holds`).
See `docs/temporal.md`.
-/

@[expose] public section

namespace Lantana.Fairness

open scoped Lantana.TrProp

namespace Action

variable {C : Type} [ThreadSystem C]

/-! ### Definitions -/

/-- The thread's own view of the action: the attempts are the steps of the thread at `i` from a
configuration where the action is enabled. -/
def own (i : ThreadId) (a : Action C) : FairnessAssumption C :=
  ⟨fun c c' => ThreadSystem.step i c c' ∧ a.enabled c, a.grant⟩

/-- Own grant: every grant of the action is a step of the thread at `i`. -/
def OwnGrant (a : Action C) (i : ThreadId) : Prop :=
  ∀ {c c' : C}, a.grant c c' → ThreadSystem.step i c c'

/-- The enabling condition is stable under every other thread's step. -/
def Stable (a : Action C) (i : ThreadId) : Prop :=
  ∀ {j : ThreadId} {c c' : C}, j ≠ i → ThreadSystem.step j c c' → a.enabled c → a.enabled c'

/-- The enabling condition persists along the run: where it holds, the thread at `i` steps now,
or it still holds at the next position, or it never holds again. -/
def Persists (a : Action C) (i : ThreadId) : TrProp C :=
  □ₜ (a.enabledNow →ₜ stepOf i ∨ₜ ○ₜ a.enabledNow ∨ₜ ○ₜ □ₜ ¬ₜ a.enabledNow)

variable {i : ThreadId} {a : Action C} {c c' : C} {τ : Trace C}

/-! ### The view -/

/-- The meaning: a thread that attempts infinitely often is granted infinitely often. -/
theorem own_holds_iff : (a.own i).holds τ ↔
    ((□ₜ ◇ₜ (stepOf i ∧ₜ a.enabledNow)) τ →
      (□ₜ ◇ₜ ((stepOf i ∧ₜ a.enabledNow) ∧ₜ a.granted)) τ) :=
  FairnessAssumption.holds_iff_attempted

/-- The counter of the view stays at every transition that is not a step of the thread. -/
theorem own_counterMove_stay_of_other (hs : ¬ ThreadSystem.step i c c') :
    (a.own i).counterMove c c' = .stay :=
  FairnessAssumption.counterMove_eq_stay_iff.2 fun h => hs h.1

/-! ### Soundness: under own grant, `SF` gives the view -/

/-- Under own grant, `SF` gives the thread's view, by restriction of the strong recipe. -/
theorem own_holds_of_sf (hown : a.OwnGrant i) : a.SF ⊆ (a.own i).holds :=
  fun τ hsf => AttemptGrant.fair_mono_of_le (fun _ ha => ha.2)
    (fun _ ⟨hA, hg⟩ => ⟨hown hg, hA⟩) τ (holds_strong.2 hsf)

/-! ### Completeness: with persistence and a thread that steps infinitely often, the view gives
`SF` back -/

/-- Stability gives persistence on any behavior. -/
theorem persists_of_stable (hstab : a.Stable i) : IsBehavior ⊆ a.Persists i := by
  intro τ hrun m hm hA
  obtain ⟨j, hs⟩ := hrun m hm
  by_cases hji : j = i
  · subst hji
    exact Or.inl hs
  · exact Or.inr (Or.inl (hstab hji hs hA))

/-- Where the thread steps infinitely often and the enabling condition persists, the view gives
`SF`. -/
theorem sf_of_own_holds :
    (StepOfInfOften i ∧ₜ a.Persists i ∧ₜ (a.own i).holds) ⊆ a.SF := by
  rintro τ ⟨hsched, hper, hag⟩ hA
  refine Classical.byContradiction fun hno => hno ?_
  obtain ⟨N, -, hN⟩ := TrProp.eventually_always_iff.mp (TrProp.not_always_eventually_le τ hno)
  refine TrProp.always_eventually_mono (fun _ hh => ⟨hh.1.2, hh.2⟩) τ (hag ?_)
  refine TrProp.always_eventually_iff.mpr fun n₀ hn₀ => ?_
  obtain ⟨n, hn, hAn⟩ :=
    TrProp.always_eventually_iff.mp hA (max n₀ N) (Nat.le_trans hn₀ (Nat.le_max_left _ _))
  have hτn : τ.pos ≤ n := Nat.le_trans hn₀ (Nat.le_trans (Nat.le_max_left _ _) hn)
  obtain ⟨m, hm, hsm⟩ := TrProp.always_eventually_iff.mp hsched n hτn
  obtain ⟨m', ⟨hnm', hsm'⟩, hmin⟩ :=
    Nat.exists_min (p := fun m => n ≤ m ∧ stepOf i { τ with pos := m }) m ⟨hm, hsm⟩
  have hAk : ∀ k, n ≤ k → k ≤ m' → a.enabled (τ.seq k) := by
    intro k hnk hkm
    induction k with
    | zero =>
      rw [← Nat.le_zero.1 hnk]
      exact hAn
    | succ k ih =>
      rcases Nat.lt_or_eq_of_le hnk with hlt | heq
      · have hk := ih (Nat.le_of_lt_succ hlt) (Nat.le_of_succ_le hkm)
        rcases hper k (Nat.le_trans hτn (Nat.le_of_lt_succ hlt)) hk with hs | hA' | hgone
        · exact absurd ⟨Nat.le_of_lt_succ hlt, hs⟩
            (hmin k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hkm))
        · exact hA'
        · obtain ⟨m'', hm'', hA''⟩ := TrProp.always_eventually_iff.mp hA (k + 1)
            (Nat.le_trans hτn (Nat.le_of_lt hlt))
          exact absurd hA'' (hgone m'' hm'')
      · rw [← heq]
        exact hAn
  have hAm := hAk m' hnm' (Nat.le_refl _)
  exact ⟨m', Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans hn hnm'), ⟨hsm', hAm⟩,
    fun hg => hN m' (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans hn hnm')) ⟨hAm, hg⟩⟩

/-- Under own grant, where the thread steps infinitely often and the enabling condition persists,
`SF` and the view coincide. -/
theorem sf_iff_own_holds (hown : a.OwnGrant i) (hsched : StepOfInfOften i τ)
    (hper : a.Persists i τ) : a.SF τ ↔ (a.own i).holds τ :=
  ⟨own_holds_of_sf hown τ, fun hag => sf_of_own_holds τ ⟨hsched, hper, hag⟩⟩

end Action

end Lantana.Fairness
