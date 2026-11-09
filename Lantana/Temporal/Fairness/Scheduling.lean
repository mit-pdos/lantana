/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.ThreadSystem
public import Lantana.Temporal.Fairness.Action

/-! # A pair that is one thread's; the scheduling action and the schedule

Over a thread system (`ThreadSystem`, `Lantana.Temporal.ThreadSystem`).  A pair of layer 0 is
the thread's at `i` when its attempts are steps of that thread (`AttemptGrant.OwnStep`); its
counter then stays at every other thread's step (`AttemptGrant.counter_stay_of_other`), the one
rule that names a thread.

Fair scheduling is an action of the attempt–grant model (`Sched.action`): enabled where the thread
is active, the predicate the thread system supplies, and granted at the thread's trace step
(`Sched.SF`).  It gives a thread active infinitely often infinitely many steps
(`Sched.threadStepInfOften_of_sf`).  The thread's own view of its scheduling has no misses
(`Sched.certain`), so scheduling has no cheap path.  A schedule names the stepping thread at each
position, a proof instrument of adequacy (`Schedule`, in `Lantana.Temporal.ThreadSystem`); under
any schedule, an action whose hit only its thread can take (`SoleOwner`) gives that thread its
labelled view (`labelledView_of_sf`).
-/

@[expose] public section

namespace Lantana.Fairness

open scoped Lantana.TrProp

variable {C : Type} [ThreadSystem C]

/-! ## 3. A pair that is one thread's -/

namespace AttemptGrant

variable {i : ThreadId} {attempt grant : TrProp C} {δ : Nat → Nat} {τ : Trace C}

/-- The attempts are steps of the thread at `i`: the pair is the thread's. -/
def OwnStep (i : ThreadId) (attempt : TrProp C) : Prop := attempt ⊆ threadStep i

/-- A thread's pair has a counter that never moves at another thread's step.  The one rule that
names a thread. -/
theorem counter_stay_of_other (hos : OwnStep i attempt) (hδ : IsCounter attempt grant δ τ)
    (hs : ¬ threadStep i τ) : δ τ.pos = δ (τ.pos + 1) :=
  counter_stay hδ fun ha => hs (hos τ ha)

end AttemptGrant

/-! ## 4. The scheduling action, and the schedule as a proof instrument (`Sched`, `SoleOwner`) -/

namespace Sched

/-- The grant of the scheduling action of the thread at `i`: its trace step. -/
abbrev grant (i : ThreadId) : C → C → Prop := ThreadSystem.step i

/-- The scheduling action of the thread at `i`: enabled where the thread is active, the predicate
the thread system supplies, and granted at its trace step. -/
def action (i : ThreadId) : Action C := ⟨ThreadSystem.active i, grant i⟩

/-- Fair scheduling of the thread at `i`: the strong fairness of its scheduling action, enabled
where the thread is active and granted at its trace step. -/
abbrev SF (i : ThreadId) : TrProp C := Action.SF (action i)

/-- The thread at `i` attempts, in its view of its scheduling: it steps while active.
`Thread.attempt i (action i)`, restated because layer 2 comes later. -/
abbrev attempt (i : ThreadId) : TrProp C := threadStep i ∧ₜ (action i).enabledNow

/-- The thread's own view of its scheduling: `Thread.AttemptGrant i (action i)`. -/
abbrev AG (i : ThreadId) : TrProp C := AttemptGrant.Fair (attempt i) (action i).granted

variable {i : ThreadId} {τ : Trace C}

/-- Own grant: the grant is the thread's step.  `Thread.OwnGrant i (action i)`. -/
theorem ownGrant : ∀ {c c' : C}, (action i).grant c c' → ThreadSystem.step i c c' := fun hg => hg

/-- What every completeness theorem needs: a thread active infinitely often and fairly scheduled
steps infinitely often. -/
theorem threadStepInfOften_of_sf : (SF i ∧ₜ □ₜ ◇ₜ active i : TrProp C) ⊆ ThreadStepInfOften i :=
  fun τ ⟨hsf, hinf⟩ => TrProp.always_eventually_mono (fun _ h => h.2) τ (hsf hinf)

/-- The thread's view of its own scheduling has no misses: every attempt is a step, so every
attempt is granted.  Scheduling has no cheap path. -/
theorem certain : AttemptGrant.Certain (attempt i) (action i).granted τ :=
  fun _ _ ha => ha.1

/-- The thread's view of its scheduling holds outright. -/
theorem ag : AG i τ := AttemptGrant.fair_of_certain τ certain

/-- The counter of the thread's view of its scheduling is zero. -/
theorem counter_zero : AttemptGrant.IsCounter (attempt i) (action i).granted (fun _ => 0) τ :=
  AttemptGrant.counter_zero_of_certain certain

end Sched

/-! ### The schedule, a proof instrument -/

/-- A relation that only its thread can take: whenever `G c c'` holds, the only thread whose
trace step accepts the transition is `i`.  Stated for the hit `a.enabled c ∧ a.grant c c'` of an
action, since a stuttering thread's step may satisfy a grant vacuously. -/
def SoleOwner (i : ThreadId) (G : C → C → Prop) : Prop :=
  ∀ c c', G c c' → ∀ j, ThreadSystem.step j c c' → j = i

/-- The thread's view under a schedule: attempts are the positions where the schedule names the
thread and the action is enabled. -/
abbrev labelledView (sched : Nat → ThreadId) (i : ThreadId) (a : Action C) : TrProp C :=
  AttemptGrant.Fair (TrProp.atPos (fun n => sched n = i) ∧ₜ a.enabledNow) a.granted

variable {τ : Trace C} {sched : Nat → ThreadId} {i : ThreadId} {a : Action C}

/-- Under a schedule, the relational `SF` of an action whose hits have a sole owner gives the
thread's labelled view: a relational hit is a labelled hit, because the schedule must name the
owner, and a labelled miss is a relational miss.  Layer 0's restriction
(`AttemptGrant.fair_mono`). -/
theorem labelledView_of_sf (hsch : Schedule sched τ)
    (hso : SoleOwner i (fun c c' => a.enabled c ∧ a.grant c c')) (hsf : a.SF τ) :
    labelledView sched i a τ :=
  AttemptGrant.fair_mono τ ⟨fun _ _ ha => ha.2,
    fun m hm ⟨hA, hg⟩ => ⟨hso _ _ ⟨hA, hg⟩ (sched m) (schedule_iff.mp hsch m hm), hA⟩,
    fun hmiss => hsf (TrProp.always_eventually_mono (fun _ h => h.1) τ hmiss)⟩

end Lantana.Fairness
