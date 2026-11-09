/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Fairness.AttemptGrant

/-! # The state form of an action (layer 1)

An action `a : Action C` is an enabling condition `a.enabled` on configurations and a grant
relation `a.grant` on steps.  Its strong fairness `a.SF := □ₜ ◇ₜ a.enabledNow →ₜ □ₜ ◇ₜ a.hit` is
the trusted form of every fairness assumption; it names no thread.  The action is layer 0 with the
positions where it is enabled as the attempts (`enabledNow`, the atom `atomic a.enabled`) and the
steps in its grant as the grants (`granted`, the two-position atom `step a.grant`), so layer 0's
theorems apply to it as they stand and the layer copies none of them.  Weak fairness `WF` has
`◇ₜ □ₜ a.enabledNow` as its premise; for a convex condition (`Convex`, true in between two
positions where it is true) the two coincide (`sf_iff_wf_of_convex`).
-/

@[expose] public section

namespace Lantana.Fairness

open scoped Lantana.TrProp

/-! ## 2. Layer 1: the state form of an action (`Action`) -/

/-- An action: an enabling condition on the configuration and a grant relation on the step. -/
structure Action (C : Type) where
  /-- The enabling condition: the configurations where the action is enabled. -/
  enabled : C → Prop
  /-- The grant relation: the steps that grant the action. -/
  grant : C → C → Prop

namespace Action

variable {C : Type}

/-! ### Definitions -/

/-- The positions where the action is enabled: its attempts. -/
abbrev enabledNow (a : Action C) : TrProp C := TrProp.atomic a.enabled

/-- The step at the current position is a grant: the action's grant relates the configuration to
the next one, whoever takes the step. -/
abbrev granted (a : Action C) : TrProp C := TrProp.step a.grant

/-- The position is granted: the action is enabled and the step taken is a grant, whoever takes
it. -/
abbrev hit (a : Action C) : TrProp C := AttemptGrant.hit a.enabledNow a.granted

/-- The position is refused: the action is enabled and the step taken is not a grant, whoever
takes it. -/
abbrev miss (a : Action C) : TrProp C := AttemptGrant.miss a.enabledNow a.granted

/-- The counter of the action: zero at a granted position, one more at a refused position than at
the next, unchanged where the action is not enabled. -/
abbrev IsCounter (a : Action C) (δ : Nat → Nat) : TrProp C :=
  AttemptGrant.IsCounter a.enabledNow a.granted δ

/-- The grant is certain: every position where the action is enabled is granted. -/
abbrev Certain (a : Action C) : TrProp C := AttemptGrant.Certain a.enabledNow a.granted

/-- Strong fairness of the action, the textbook statement: the action enabled infinitely often
forces infinitely many grants.  The trusted form of every fairness assumption; a statement about
the run, naming no thread. -/
def SF (a : Action C) : TrProp C := □ₜ ◇ₜ a.enabledNow →ₜ □ₜ ◇ₜ a.hit

/-- The response form: every position where the action is enabled is followed by a granted
position, at it or later. -/
def Response (a : Action C) : TrProp C := □ₜ (a.enabledNow →ₜ ◇ₜ a.hit)

/-- Weak fairness of the action: the action enabled from some position on forces infinitely many
grants. -/
def WF (a : Action C) : TrProp C := ◇ₜ □ₜ a.enabledNow →ₜ □ₜ ◇ₜ a.hit

/-- The enabling condition is convex along the run: true now and at some later position makes it
true at every position in between.  A thread's activity is convex: a Lantana thread is active
from its fork until it becomes a value. -/
def Convex (a : Action C) : TrProp C :=
  □ₜ (a.enabledNow →ₜ □ₜ (◇ₜ a.enabledNow →ₜ a.enabledNow))

variable {a : Action C} {δ : Nat → Nat} {τ : Trace C}

/-! ### `SF` is layer 0's fairness, and the existence of a counter -/

/-- `SF` is layer 0's fairness at the action's attempts: this is layer 0's meaning
(`AttemptGrant.fair_iff_attempt`). -/
theorem sf_iff_fair : a.SF τ ↔ AttemptGrant.Fair a.enabledNow a.granted τ :=
  AttemptGrant.fair_iff_attempt.symm

/-- `SF` is the same at every position of the run. -/
theorem sf_absolute : TrProp.Absolute a.SF :=
  TrProp.absolute_imp TrProp.absolute_always_eventually TrProp.absolute_always_eventually

/-- `SF` is the existence of a counter. -/
theorem sf_iff_counter : a.SF τ ↔ ∃ δ, a.IsCounter δ τ :=
  sf_iff_fair.trans AttemptGrant.fair_iff_counter

/-- `SF` gives a counter. -/
theorem counter_of_sf (hsf : a.SF τ) : ∃ δ, a.IsCounter δ τ := sf_iff_counter.1 hsf

/-- A counter gives `SF`. -/
theorem sf_of_counter (hδ : a.IsCounter δ τ) : a.SF τ := sf_iff_counter.2 ⟨δ, hδ⟩

/-! ### The variants: response, weak fairness, a certain grant -/

/-- The response form gives `SF`. -/
theorem sf_of_response : a.Response ⊆ a.SF :=
  fun τ h => sf_iff_fair.2 (AttemptGrant.fair_of_response τ h)

/-- `SF` gives weak fairness. -/
theorem wf_of_sf : a.SF ⊆ a.WF :=
  fun τ hsf hev => hsf (TrProp.eventually_always_le τ hev)

/-- A certain grant gives the response form: every position where the action is enabled is
granted at once. -/
theorem response_of_certain : a.Certain ⊆ a.Response :=
  fun _ hc m hm hA => TrProp.eventually_intro _ ⟨hA, hc m hm hA⟩

/-- A certain grant gives `SF` outright. -/
theorem sf_of_certain : a.Certain ⊆ a.SF := TrProp.le_trans response_of_certain sf_of_response

/-! ### Weak and strong fairness coincide for a convex condition -/

/-- A convex condition that holds infinitely often holds from some position on. -/
theorem eventually_always_of_infOften_of_convex :
    (a.Convex ∧ₜ □ₜ ◇ₜ a.enabledNow) ⊆ ◇ₜ □ₜ a.enabledNow := by
  rintro τ ⟨hconv, hinf⟩
  obtain ⟨m, hm, hA⟩ := TrProp.always_eventually_iff.mp hinf τ.pos (Nat.le_refl _)
  exact TrProp.eventually_always_iff.mpr
    ⟨m, hm, fun l hl => hconv m hm hA l hl (hinf l (Nat.le_trans hm hl))⟩

/-- For a convex condition, strong and weak fairness of the action coincide. -/
theorem sf_iff_wf_of_convex (hconv : a.Convex τ) : a.SF τ ↔ a.WF τ :=
  ⟨wf_of_sf τ, fun hwf hinf => hwf (eventually_always_of_infOften_of_convex τ ⟨hconv, hinf⟩)⟩

end Action

end Lantana.Fairness
