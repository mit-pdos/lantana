/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Fairness.Sched

/-! # The thread's view of an action (layer 2)

The thread's view is layer 0 with the thread's own attempts: a step of the thread at `i` from a
configuration where `A` holds.  Its attempts are the thread's steps (`ownStep`), so its counter
moves only at the thread's own steps (`counter_stay_of_other`): the cheap path.  The view is
sound under own grant (`OwnGrant`: every grant is a step of the thread; `attemptGrant_of_sf`),
and it loses nothing under persistence of `A` (`Persists`, from stability `Stable` on a
behavior) and fair scheduling of the thread (`sf_of_attemptGrant`), so with own grant the two
forms coincide (`sf_iff_attemptGrant`).  A grant certain at the thread's attempts (`Certain`)
gives the view outright and `WF` from fair scheduling alone.
-/

@[expose] public section

namespace Lantana.Fairness

open scoped Lantana.TrProp

/-! ## 5. Layer 2: the thread's view of an action (`Thread`) -/

namespace Thread

variable {C : Type} [Pool C]

/-! ### Definitions -/

/-- The thread at `i` attempts: it steps from a configuration where `A` holds. -/
abbrev attempt (i : ThreadId) (A : C → Prop) : TrProp C := Steps i ∧ₜ Action.enabled A

/-- The thread's attempt is granted: it steps from a configuration where `A` holds, and its step
is a grant. -/
abbrev hit (i : ThreadId) (A : C → Prop) (G : C → C → Prop) : TrProp C :=
  AttemptGrant.hit (attempt i A) (Action.grant G)

/-- The thread's attempt is refused. -/
abbrev miss (i : ThreadId) (A : C → Prop) (G : C → C → Prop) : TrProp C :=
  AttemptGrant.miss (attempt i A) (Action.grant G)

/-- The attempt–grant form of the thread's view: infinitely many refused attempts force infinitely
many granted ones.  The form the logic consumes on the cheap path. -/
abbrev AttemptGrant (i : ThreadId) (A : C → Prop) (G : C → C → Prop) : TrProp C :=
  AttemptGrant.Fair (attempt i A) (Action.grant G)

/-- The counter of the thread's view: zero at a granted attempt, one more at a refused attempt
than at the next position, unchanged where the thread does not attempt. -/
abbrev IsCounter (i : ThreadId) (A : C → Prop) (G : C → C → Prop) (δ : Nat → Nat) : TrProp C :=
  AttemptGrant.IsCounter (attempt i A) (Action.grant G) δ

/-- The grant is certain at the thread's attempts: every attempt of the thread at `i` is
granted. -/
abbrev Certain (i : ThreadId) (A : C → Prop) (G : C → C → Prop) : TrProp C :=
  AttemptGrant.Certain (attempt i A) (Action.grant G)

/-- Own grant: the grant is one of the thread's transitions.  The property that makes the thread's
view sound. -/
def OwnGrant (i : ThreadId) (G : C → C → Prop) : Prop :=
  ∀ {c c' : C}, G c c' → Pool.Step i c c'

/-- `A` is stable under every other thread's step. -/
def Stable (i : ThreadId) (A : C → Prop) : Prop :=
  ∀ {j : ThreadId} {c c' : C}, j ≠ i → Pool.Step j c c' → A c → A c'

/-- `A` persists along the run: where it holds, the thread steps now, or `A` still holds at the
next position, or `A` never holds again.  The general interface: it says nothing about how `A`
can be lost. -/
def Persists (i : ThreadId) (A : C → Prop) : TrProp C :=
  □ₜ (Action.enabled A →ₜ Steps i ∨ₜ ○ₜ Action.enabled A ∨ₜ ○ₜ □ₜ ¬ₜ Action.enabled A)

variable {i : ThreadId} {A : C → Prop} {G : C → C → Prop} {δ : Nat → Nat} {τ : Trace C}

/-! ### The pair is the thread's, and the action's at the thread's steps -/

/-- The attempts are steps of the thread, for every action. -/
theorem ownStep : AttemptGrant.OwnStep i (attempt i A) := by
  sorry

/-- A miss is a step of the thread from a configuration where `A` holds that is not a grant. -/
theorem miss_iff : miss i A G τ ↔ Steps i τ ∧ A τ.now ∧ ¬ G τ.now τ.next.now := by
  sorry

/-- A hit of the thread is a step of the thread at a granted position of the action. -/
theorem hit_iff_steps_action_hit : hit i A G τ ↔ Steps i τ ∧ Action.hit A G τ := by
  sorry

/-- A miss of the thread is a step of the thread at a refused position of the action. -/
theorem miss_iff_steps_action_miss : miss i A G τ ↔ Steps i τ ∧ Action.miss A G τ := by
  sorry

/-- The meaning of the attempt–grant form: a thread that attempts infinitely often is granted
infinitely often. -/
theorem attemptGrant_iff_attempt :
    AttemptGrant i A G τ ↔ ((□ₜ ◇ₜ attempt i A) τ → (□ₜ ◇ₜ hit i A G) τ) := by
  sorry

/-! ### Soundness: under own grant, `SF` gives the thread's counter -/

/-- **Soundness.**  Under own grant, `SF` gives the attempt–grant form: layer 0's restriction
`AttemptGrant.fair_mono` applied to `Action.sf_iff_fair`. -/
theorem attemptGrant_of_sf (hown : OwnGrant i G) : Action.SF A G ⊆ AttemptGrant i A G := by
  sorry

/-- Under own grant, the response form gives the attempt–grant form. -/
theorem attemptGrant_of_response (hown : OwnGrant i G) :
    Action.Response A G ⊆ AttemptGrant i A G := by
  sorry

/-- Under own grant, the trusted form gives the thread's counter. -/
theorem counter_of_sf (hown : OwnGrant i G) (hsf : Action.SF A G τ) :
    ∃ δ, IsCounter i A G δ τ := by
  sorry

/-- Stay: at every step that is not the thread's the counter is unchanged. -/
theorem counter_stay_of_other (hδ : IsCounter i A G δ τ) (hs : ¬ Steps i τ) :
    δ τ.pos = δ (τ.pos + 1) := by
  sorry

/-! ### Completeness: under persistence and fair scheduling, the view gives `SF` back -/

/-- Stability gives persistence on any behavior. -/
theorem persists_of_stable (hstab : Stable i A) : IsBehavior ⊆ Persists i A := by
  sorry

/-- A pending attempt survives the other threads' steps: if `A` is stable and holds now, it holds
at every later position reached by other threads' steps only, in particular at the thread's next
step. -/
theorem attempt_pending (hstab : Stable i A) (hA : A τ.now) {k : Nat} (hk : τ.pos ≤ k)
    (hothers : ∀ k', τ.pos ≤ k' → k' < k → ∃ j, j ≠ i ∧ Pool.Step j (τ.seq k') (τ.seq (k' + 1))) :
    A (τ.seq k) := by
  sorry

/-- **Completeness.**  Under fair scheduling of the thread and persistence of `A`, the
attempt–grant form gives `SF`. -/
theorem sf_of_attemptGrant :
    (StepsInfOften i ∧ₜ Persists i A ∧ₜ AttemptGrant i A G) ⊆ Action.SF A G := by
  sorry

/-- Under own grant, persistence and fair scheduling, the trusted form and the attempt–grant form
coincide. -/
theorem sf_iff_attemptGrant (hown : OwnGrant i G) (hsched : StepsInfOften i τ)
    (hper : Persists i A τ) : Action.SF A G τ ↔ AttemptGrant i A G τ := by
  sorry

/-! ### A grant certain at the thread's own attempts -/

/-- With a grant certain at the thread's attempts there are no misses, so the attempt–grant form
holds outright. -/
theorem attemptGrant_of_certain : Certain i A G ⊆ AttemptGrant i A G := by
  sorry

/-- With a grant certain at the thread's attempts the zero function is a counter. -/
theorem counter_zero_of_certain (hc : Certain i A G τ) : IsCounter i A G (fun _ => 0) τ := by
  sorry

/-- With a grant certain at the thread's attempts, weak fairness follows from fair scheduling
alone. -/
theorem wf_of_certain : (StepsInfOften i ∧ₜ Certain i A G) ⊆ Action.WF A G := by
  sorry

/-- With a grant certain at the thread's attempts, `SF` follows from fair scheduling and
persistence. -/
theorem sf_of_certain : (StepsInfOften i ∧ₜ Persists i A ∧ₜ Certain i A G) ⊆ Action.SF A G := by
  sorry

end Thread

end Lantana.Fairness
