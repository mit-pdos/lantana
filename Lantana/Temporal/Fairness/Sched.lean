/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Pool
public import Lantana.Temporal.Fairness.Action

/-! # A pair that is one thread's; the scheduling action and the schedule

Over a thread system (`Pool`, `Lantana.Temporal.Pool`).  A pair of layer 0 is the thread's at `i`
when its attempts are steps of that thread (`AttemptGrant.OwnStep`); its counter then stays at
every other thread's step (`AttemptGrant.counter_stay_of_other`), the one rule that names a
thread.

Fair scheduling is an action of the attempt–grant model: enabled where the thread is active, the
predicate the thread system supplies, and granted at the thread's trace step (`Sched.SF`).  It
gives a thread active infinitely often infinitely many steps (`Sched.stepsInfOften_of_sf`).  The
thread's own view of its scheduling has no misses (`Sched.certain`), so scheduling has no cheap
path.  A schedule names the stepping thread at each position, a proof instrument of adequacy
(`Schedule`, in `Lantana.Temporal.Pool`); under any schedule, an action whose hit only its thread
can take (`SoleOwner`) gives that thread its labelled view (`labelledView_of_sf`).
-/

@[expose] public section

namespace Lantana.Fairness

open scoped Lantana.TrProp

variable {C : Type} [Pool C]

/-! ## 3. A pair that is one thread's -/

namespace AttemptGrant

variable {i : ThreadId} {attempt grant : TrProp C} {δ : Nat → Nat} {τ : Trace C}

/-- The attempts are steps of the thread at `i`: the pair is the thread's. -/
def OwnStep (i : ThreadId) (attempt : TrProp C) : Prop := attempt ⊆ Steps i

/-- A thread's pair has a counter that never moves at another thread's step.  The one rule that
names a thread. -/
theorem counter_stay_of_other (hos : OwnStep i attempt) (hδ : IsCounter attempt grant δ τ)
    (hs : ¬ Steps i τ) : δ τ.pos = δ (τ.pos + 1) := by
  sorry

end AttemptGrant

/-! ## 4. The scheduling action, and the schedule as a proof instrument (`Sched`, `SoleOwner`) -/

namespace Sched

/-- The grant of the scheduling action of the thread at `i`: its trace step. -/
abbrev grant (i : ThreadId) : C → C → Prop := Pool.Step i

/-- Fair scheduling of the thread at `i`: the strong fairness of its scheduling action, enabled
where the thread is active and granted at its trace step. -/
abbrev SF (i : ThreadId) : TrProp C := Action.SF (Pool.active i) (grant i)

/-- The thread at `i` attempts, in its view of its scheduling: it steps while active.
`Thread.attempt i (Pool.active i)`, restated because layer 2 comes later. -/
abbrev attempt (i : ThreadId) : TrProp C := Steps i ∧ₜ active i

/-- The thread's own view of its scheduling: `Thread.AttemptGrant i (Pool.active i) (grant i)`. -/
abbrev AG (i : ThreadId) : TrProp C := AttemptGrant.Fair (attempt i) (Action.grant (grant i))

variable {i : ThreadId} {τ : Trace C}

/-- Own grant: the grant is the thread's step.  `Thread.OwnGrant i (grant i)`. -/
theorem ownGrant : ∀ {c c' : C}, grant i c c' → Pool.Step i c c' := by
  sorry

/-- What every completeness theorem needs: a thread active infinitely often and fairly scheduled
steps infinitely often. -/
theorem stepsInfOften_of_sf : (SF i ∧ₜ □ₜ ◇ₜ active i : TrProp C) ⊆ StepsInfOften i := by
  sorry

/-- The thread's view of its own scheduling has no misses: every attempt is a step, so every
attempt is granted.  Scheduling has no cheap path. -/
theorem certain : AttemptGrant.Certain (attempt i) (Action.grant (grant i)) τ := by
  sorry

/-- The thread's view of its scheduling holds outright. -/
theorem ag : AG i τ := by
  sorry

/-- The counter of the thread's view of its scheduling is zero. -/
theorem counter_zero :
    AttemptGrant.IsCounter (attempt i) (Action.grant (grant i)) (fun _ => 0) τ := by
  sorry

end Sched

/-! ### The schedule, a proof instrument -/

/-- A relation that only its thread can take: whenever `G c c'` holds, the only thread whose
trace step accepts the transition is `i`.  Stated for the hit `A c ∧ G c c'` of an action, since a
stuttering thread's step may satisfy a grant vacuously. -/
def SoleOwner (i : ThreadId) (G : C → C → Prop) : Prop :=
  ∀ c c', G c c' → ∀ j, Pool.Step j c c' → j = i

/-- The thread's view under a schedule: attempts are the positions where the schedule names the
thread and `A` holds. -/
abbrev labelledView (sched : Nat → ThreadId) (i : ThreadId) (A : C → Prop) (G : C → C → Prop) :
    TrProp C :=
  AttemptGrant.Fair (TrProp.atPos (fun n => sched n = i) ∧ₜ Action.enabled A) (Action.grant G)

variable {τ : Trace C} {sched : Nat → ThreadId} {i : ThreadId} {A : C → Prop} {G : C → C → Prop}

/-- Under a schedule, the relational `SF` of an action whose hits have a sole owner gives the
thread's labelled view: a relational hit is a labelled hit, because the schedule must name the
owner, and a labelled miss is a relational miss.  Layer 0's restriction
(`AttemptGrant.fair_mono`). -/
theorem labelledView_of_sf (hsch : Schedule sched τ)
    (hso : SoleOwner i (fun c c' => A c ∧ G c c')) (hsf : Action.SF A G τ) :
    labelledView sched i A G τ := by
  sorry

end Lantana.Fairness
