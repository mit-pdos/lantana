/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Fairness.AttemptGrant

/-! # The state form of an action (layer 1)

An action is an enabling condition `A` on configurations and a grant relation `G` on steps.  Its
strong fairness `SF A G := □ₜ ◇ₜ A →ₜ □ₜ ◇ₜ (A ∧ₜ G)` is the trusted form of every fairness
assumption; it names no thread.  The action is layer 0 with the positions where `A` holds as the
attempts (`enabled`, the atom `now A`) and the steps in `G` as the grants (`grant`, the
two-position atom `step G`), so layer 0's theorems apply to it as they stand and the layer copies
none of them.  Weak fairness `WF` has `◇ₜ □ₜ A` as its premise; for a convex condition (`Convex`,
true in between two positions where it is true) the two coincide (`sf_iff_wf_of_convex`).
-/

@[expose] public section

namespace Lantana.Fairness

open scoped Lantana.TrProp

/-! ## 2. Layer 1: the state form of an action (`Action`) -/

namespace Action

variable {C : Type}

/-! ### Definitions -/

/-- The positions where `A` holds: the action's attempts. -/
abbrev enabled (A : C → Prop) : TrProp C := TrProp.now A

/-- The step at the current position is a grant: `G` relates the configuration to the next one,
whoever takes the step. -/
abbrev grant (G : C → C → Prop) : TrProp C := TrProp.step G

/-- The position is granted: `A` holds and the step taken is a grant, whoever takes it. -/
abbrev hit (A : C → Prop) (G : C → C → Prop) : TrProp C :=
  AttemptGrant.hit (enabled A) (grant G)

/-- The position is refused: `A` holds and the step taken is not a grant, whoever takes it. -/
abbrev miss (A : C → Prop) (G : C → C → Prop) : TrProp C :=
  AttemptGrant.miss (enabled A) (grant G)

/-- The counter of the action: zero at a granted position, one more at a refused position than at
the next, unchanged where `A` fails. -/
abbrev IsCounter (A : C → Prop) (G : C → C → Prop) (δ : Nat → Nat) : TrProp C :=
  AttemptGrant.IsCounter (enabled A) (grant G) δ

/-- The grant is certain: every position where `A` holds is granted. -/
abbrev Certain (A : C → Prop) (G : C → C → Prop) : TrProp C :=
  AttemptGrant.Certain (enabled A) (grant G)

/-- Strong fairness of the action, the textbook statement: `A` holding infinitely often forces
infinitely many grants.  The trusted form of every fairness assumption; a statement about the
run, naming no thread. -/
def SF (A : C → Prop) (G : C → C → Prop) : TrProp C := □ₜ ◇ₜ enabled A →ₜ □ₜ ◇ₜ hit A G

/-- The response form: every position where `A` holds is followed by a granted position, at it
or later. -/
def Response (A : C → Prop) (G : C → C → Prop) : TrProp C := □ₜ (enabled A →ₜ ◇ₜ hit A G)

/-- Weak fairness of the action: `A` holding from some position on forces infinitely many
grants. -/
def WF (A : C → Prop) (G : C → C → Prop) : TrProp C := ◇ₜ □ₜ enabled A →ₜ □ₜ ◇ₜ hit A G

/-- `A` is convex along the run: true now and at some later position makes it true at every
position in between.  A thread's activity is convex: a Lantana thread is active from its fork
until it becomes a value. -/
def Convex (A : C → Prop) : TrProp C := □ₜ (enabled A →ₜ □ₜ (◇ₜ enabled A →ₜ enabled A))

variable {A : C → Prop} {G : C → C → Prop} {δ : Nat → Nat} {τ : Trace C}

/-! ### `SF` is layer 0's fairness, and the existence of a counter -/

/-- `SF` is layer 0's fairness at the action's attempts: this is layer 0's meaning
(`AttemptGrant.fair_iff_attempt`). -/
theorem sf_iff_fair : SF A G τ ↔ AttemptGrant.Fair (enabled A) (grant G) τ :=
  AttemptGrant.fair_iff_attempt.symm

/-- `SF` is the same at every position of the run. -/
theorem sf_absolute : TrProp.Absolute (SF A G) :=
  TrProp.absolute_imp TrProp.absolute_always_eventually TrProp.absolute_always_eventually

/-- `SF` is the existence of a counter. -/
theorem sf_iff_counter : SF A G τ ↔ ∃ δ, IsCounter A G δ τ :=
  sf_iff_fair.trans AttemptGrant.fair_iff_counter

/-- `SF` gives a counter. -/
theorem counter_of_sf (hsf : SF A G τ) : ∃ δ, IsCounter A G δ τ := sf_iff_counter.1 hsf

/-- A counter gives `SF`. -/
theorem sf_of_counter (hδ : IsCounter A G δ τ) : SF A G τ := sf_iff_counter.2 ⟨δ, hδ⟩

/-! ### The variants: response, weak fairness, a certain grant -/

/-- The response form gives `SF`. -/
theorem sf_of_response : Response A G ⊆ SF A G :=
  fun τ h => sf_iff_fair.2 (AttemptGrant.fair_of_response τ h)

/-- `SF` gives weak fairness. -/
theorem wf_of_sf : SF A G ⊆ WF A G :=
  fun τ hsf hev => hsf (TrProp.eventually_always_le τ hev)

/-- A certain grant gives the response form: every position where `A` holds is granted at
once. -/
theorem response_of_certain : Certain A G ⊆ Response A G :=
  fun _ hc m hm hA => TrProp.eventually_intro _ ⟨hA, hc m hm hA⟩

/-- A certain grant gives `SF` outright. -/
theorem sf_of_certain : Certain A G ⊆ SF A G := TrProp.le_trans response_of_certain sf_of_response

/-! ### Weak and strong fairness coincide for a convex condition -/

/-- A convex condition that holds infinitely often holds from some position on. -/
theorem eventually_always_of_infOften_of_convex :
    (Convex A ∧ₜ □ₜ ◇ₜ enabled A) ⊆ ◇ₜ □ₜ enabled A := by
  rintro τ ⟨hconv, hinf⟩
  obtain ⟨m, hm, hA⟩ := TrProp.always_eventually_iff.mp hinf τ.pos (Nat.le_refl _)
  exact TrProp.eventually_always_iff.mpr
    ⟨m, hm, fun l hl => hconv m hm hA l hl (hinf l (Nat.le_trans hm hl))⟩

/-- For a convex condition, strong and weak fairness of the action coincide. -/
theorem sf_iff_wf_of_convex (hconv : Convex A τ) : SF A G τ ↔ WF A G τ :=
  ⟨wf_of_sf τ, fun hwf hinf => hwf (eventually_always_of_infOften_of_convex τ ⟨hconv, hinf⟩)⟩

end Action

end Lantana.Fairness
