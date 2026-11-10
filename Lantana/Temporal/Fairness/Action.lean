/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Fairness.FairnessAssumption

/-! # Actions: strong and weak fairness, the recipes `strong` and `weak`

An `Action` is an enabling condition on configurations and a grant relation on steps, the usual
state form of a fairness assumption.  Its strong fairness `SF` is the textbook one and its weak
fairness `WF` has `◇ₜ □ₜ a.enabledNow` as premise.  Both are assumptions by a recipe:
`a.strong.holds ↔ a.SF` (`holds_strong`) and `a.weak.holds ↔ a.WF` (`holds_weak`).  For a convex
enabling condition (`Convex`) the two coincide (`sf_iff_wf_of_convex`).
See `docs/temporal.md`.
-/

@[expose] public section

namespace Lantana.Fairness

open scoped Lantana.TrProp

/-- An action: an enabling condition on the configuration and a grant relation on the step. -/
structure Action (C : Type) where
  /-- The enabling condition: the configurations where the action is enabled. -/
  enabled : C → Prop
  /-- The grant relation: the steps that grant the action. -/
  grant : C → C → Prop

namespace Action

variable {C : Type}

/-! ### Definitions -/

/-- The action is enabled at the current configuration. -/
abbrev enabledNow (a : Action C) : TrProp C := TrProp.atomic a.enabled

/-- The step at the current position is a grant of the action, whoever takes it. -/
abbrev granted (a : Action C) : TrProp C := TrProp.step a.grant

/-- Strong fairness of the action: enabled infinitely often, it is granted infinitely often while
enabled.  A statement about the run that names no thread. -/
def SF (a : Action C) : TrProp C := □ₜ ◇ₜ a.enabledNow →ₜ □ₜ ◇ₜ (a.enabledNow ∧ₜ a.granted)

/-- Weak fairness of the action: enabled from some position on, it is granted infinitely often
while enabled. -/
def WF (a : Action C) : TrProp C := ◇ₜ □ₜ a.enabledNow →ₜ □ₜ ◇ₜ (a.enabledNow ∧ₜ a.granted)

/-- The enabling condition is convex along the run: true now and at some later position makes it
true at every position in between. -/
def Convex (a : Action C) : TrProp C :=
  □ₜ (a.enabledNow →ₜ □ₜ (◇ₜ a.enabledNow →ₜ a.enabledNow))

/-- The strong recipe: the attempts are the positions where the action is enabled, whoever
steps. -/
def strong (a : Action C) : FairnessAssumption C := ⟨fun c _ => a.enabled c, a.grant⟩

/-- The weak recipe: every position is an attempt, granted when the action is disabled or the
step is a grant. -/
def weak (a : Action C) : FairnessAssumption C :=
  ⟨fun _ _ => True, fun c c' => ¬ a.enabled c ∨ a.grant c c'⟩

variable {a : Action C} {τ : Trace C}

/-! ### Strong fairness -/

/-- `SF` is the same at every position of the run. -/
theorem sf_absolute : TrProp.Absolute a.SF :=
  TrProp.absolute_imp TrProp.absolute_always_eventually TrProp.absolute_always_eventually

/-- The strong recipe holds exactly when the action is strongly fair. -/
theorem holds_strong : a.strong.holds τ ↔ a.SF τ := AttemptGrant.fair_iff_attempt

/-- `SF` is the existence of a counter of the strong recipe. -/
theorem sf_iff_counter : a.SF τ ↔ ∃ δ, a.strong.IsCounter δ τ :=
  holds_strong.symm.trans FairnessAssumption.holds_iff_counter

/-! ### Weak fairness -/

/-- The weak recipe holds exactly when the action is weakly fair. -/
theorem holds_weak : a.weak.holds τ ↔ a.WF τ := by
  constructor
  · intro hag hev
    refine Classical.byContradiction fun hno => ?_
    obtain ⟨N, hN, hen⟩ := TrProp.eventually_always_iff.mp hev
    obtain ⟨N', -, hnh⟩ :=
      TrProp.eventually_always_iff.mp (TrProp.not_always_eventually_le τ hno)
    have hle : ∀ m, max N N' ≤ m → N ≤ m ∧ N' ≤ m := fun m hm =>
      ⟨Nat.le_trans (Nat.le_max_left _ _) hm, Nat.le_trans (Nat.le_max_right _ _) hm⟩
    have hmiss : (□ₜ ◇ₜ a.weak.miss) τ := TrProp.always_eventually_iff.mpr fun n _ =>
      ⟨max n (max N N'), Nat.le_max_left _ _, trivial, fun hg =>
        have h := hle _ (Nat.le_max_right _ _)
        hg.elim (fun hA => hA (hen _ h.1)) fun hg => hnh _ h.2 ⟨hen _ h.1, hg⟩⟩
    obtain ⟨m, hm, -, hg⟩ := TrProp.always_eventually_iff.mp (hag hmiss) (max N N')
      (Nat.le_trans hN (Nat.le_max_left _ _))
    have hAm := hen m (hle m hm).1
    exact hnh m (hle m hm).2 ⟨hAm, hg.resolve_left (absurd hAm)⟩
  · intro hwf _
    refine TrProp.always_eventually_iff.mpr fun n hn => Classical.byContradiction fun hno => ?_
    have hen : ∀ m, n ≤ m → a.enabledNow { τ with pos := m } := fun m hm =>
      Classical.byContradiction fun hA => hno ⟨m, hm, trivial, Or.inl hA⟩
    obtain ⟨m, hm, -, hg⟩ :=
      TrProp.always_eventually_iff.mp (hwf (TrProp.eventually_always_iff.mpr ⟨n, hn, hen⟩)) n hn
    exact hno ⟨m, hm, trivial, Or.inr hg⟩

/-- `SF` gives weak fairness. -/
theorem wf_of_sf : a.SF ⊆ a.WF :=
  fun τ hsf hev => hsf (TrProp.eventually_always_le τ hev)

/-! ### A convex enabling condition -/

/-- A convex condition that holds infinitely often holds from some position on. -/
theorem eventually_always_of_infOften_of_convex :
    (a.Convex ∧ₜ □ₜ ◇ₜ a.enabledNow) ⊆ ◇ₜ □ₜ a.enabledNow := by
  rintro τ ⟨hconv, hinf⟩
  obtain ⟨m, hm, hA⟩ := TrProp.always_eventually_iff.mp hinf τ.pos (Nat.le_refl _)
  exact TrProp.eventually_always_iff.mpr
    ⟨m, hm, fun l hl => hconv m hm hA l hl (hinf l (Nat.le_trans hm hl))⟩

/-- For a convex enabling condition, strong and weak fairness coincide. -/
theorem sf_iff_wf_of_convex (hconv : a.Convex τ) : a.SF τ ↔ a.WF τ :=
  ⟨wf_of_sf τ, fun hwf hinf => hwf (eventually_always_of_infOften_of_convex τ ⟨hconv, hinf⟩)⟩

end Action

end Lantana.Fairness
