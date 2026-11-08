/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Trace.Fairness.AttemptGrant

/-! # The state form of an action (layer 1)

Layer 1 of the attempt–grant model of fairness (`Lantana.Trace.Fairness`): an action's enabling
condition and grant, its strong fairness `SF` and the existence of its counter. -/

@[expose] public section

namespace Lantana.Fairness

/-! ## 2. Layer 1: the state form of an action (`Action`)

An action is an enabling condition `A` on configurations and a grant relation `G` on pairs of
configurations.  Its strong fairness `SF` says that where `A` holds infinitely often, a grant
happens infinitely often.  `SF` is the trusted form of every fairness assumption, and it names no
thread.  The layer uses configurations only, and no pool.

The action is layer 0 with the positions where `A` holds as the attempts (`enabled`) and the
steps in `G` as the grants (`grant`).  A hit is a position where `A` holds and the step taken is a
grant; a miss is a position where `A` holds and the step taken is not a grant, whoever takes it.
`SF` is layer 0's fairness of that pair (`sf_iff_fair`), so it is the existence of a counter
(`sf_iff_counter`).  The counter moves at any step, whoever takes it: it resets at a grant, drops
at a refused position and stays where `A` fails.

The layer's `hit`, `miss`, `IsCounter` and `Certain` are abbreviations of layer 0's, so layer 0's
theorems apply to them as they stand, and the layer copies none of them.  For example, from
`hδ : Action.IsCounter A G σ δ`, `hA : A (σ n)` and `hG : G (σ n) (σ (n + 1))`, the reset rule
`AttemptGrant.counter_reset hδ hA hG` gives `δ n = 0`.

Lantana's trace side implements exactly this layer: one counter per declared action, updated at
every step (the owner's decision of 2026-11-06).  How a thread learns of an update of the counter
at another thread's step is the program logic's business.  Layer 2 (section 5) avoids the question
for the actions whose grant is one of the thread's own transitions. -/

namespace Action

variable {Cfg : Type}

/-! ### Definitions -/

/-- The step at `n` is a grant: `G` relates the configuration at `n` to the next one, whoever takes
the step. -/
def grant (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop := G (σ n) (σ (n + 1))

/-- The positions where `A` holds: the action's attempts. -/
abbrev enabled (A : Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop := A (σ n)

/-- Position `n` is granted: `A` holds there and the step taken is a grant, whoever takes it. -/
abbrev hit (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop :=
  AttemptGrant.hit (enabled A σ) (grant G σ) n

/-- Position `n` is refused: `A` holds there and the step taken is not a grant, whoever takes
it. -/
abbrev miss (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop :=
  AttemptGrant.miss (enabled A σ) (grant G σ) n

/-- The counter of the action: zero at a granted position, one more at a refused position than at
the next, unchanged where `A` fails. -/
abbrev IsCounter (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (δ : Nat → Nat) :
    Prop :=
  AttemptGrant.IsCounter (enabled A σ) (grant G σ) δ

/-- The grant is certain: every position where `A` holds is granted. -/
abbrev Certain (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  AttemptGrant.Certain (enabled A σ) (grant G σ)

/-- Strong fairness of the action, the textbook statement: `A` holding infinitely often forces
infinitely many grants.  The trusted form of every fairness assumption; a statement about the
run, naming no thread. -/
def SF (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  MissHit.InfOften (enabled A σ) → MissHit.InfOften (hit A G σ)

/-- The response form: every position where `A` holds is followed by a granted position, at it
or later. -/
def Response (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  ∀ n, A (σ n) → ∃ m ≥ n, hit A G σ m

/-- Weak fairness of the action: `A` holding from some position on forces infinitely many
grants. -/
def WF (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  (∃ N, ∀ n, N ≤ n → A (σ n)) → MissHit.InfOften (hit A G σ)

variable {A : Cfg → Prop} {G : Cfg → Cfg → Prop} {σ : Nat → Cfg} {δ : Nat → Nat}

/-! ### `SF` is layer 0's fairness, and the existence of a counter -/

/-- `SF` is layer 0's fairness at the action's attempts: this is layer 0's meaning
(`AttemptGrant.fair_iff_attempt`). -/
theorem sf_iff_fair : SF A G σ ↔ AttemptGrant.Fair (enabled A σ) (grant G σ) :=
  AttemptGrant.fair_iff_attempt.symm

/-- `SF` is the existence of a counter. -/
theorem sf_iff_counter : SF A G σ ↔ ∃ δ, IsCounter A G σ δ :=
  sf_iff_fair.trans AttemptGrant.fair_iff_counter

/-- `SF` gives a counter. -/
theorem counter_of_sf (hsf : SF A G σ) : ∃ δ, IsCounter A G σ δ := sf_iff_counter.1 hsf

/-- A counter gives `SF`. -/
theorem sf_of_counter (hδ : IsCounter A G σ δ) : SF A G σ := sf_iff_counter.2 ⟨δ, hδ⟩

/-! ### The variants: response, weak fairness, a certain grant

The response form gives `SF`, and `SF` gives weak fairness `WF`.  A certain grant has no refused
position, so it gives the response form and `SF` outright, and its counter is zero
(`AttemptGrant.counter_zero_of_certain`). -/

/-- The response form gives `SF`. -/
theorem sf_of_response (h : Response A G σ) : SF A G σ :=
  fun hinf n =>
    let ⟨m, hm, hAm⟩ := hinf n
    let ⟨k, hk, hhit⟩ := h m hAm
    ⟨k, Nat.le_trans hm hk, hhit⟩

/-- `SF` gives weak fairness. -/
theorem wf_of_sf (hsf : SF A G σ) : WF A G σ :=
  fun ⟨N, hN⟩ => hsf fun n => ⟨n + N, Nat.le_add_right n N, hN _ (Nat.le_add_left N n)⟩

/-- A certain grant gives the response form: every position where `A` holds is granted at
once. -/
theorem response_of_certain (hc : Certain A G σ) : Response A G σ :=
  fun n hA => ⟨n, Nat.le_refl n, hA, hc n hA⟩

/-- A certain grant gives `SF` outright. -/
theorem sf_of_certain (hc : Certain A G σ) : SF A G σ := sf_of_response (response_of_certain hc)

end Action

end Lantana.Fairness
