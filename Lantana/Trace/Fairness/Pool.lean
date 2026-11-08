/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Trace.Fairness.Action

/-! # The pool, the scheduling action and the schedule

Sections 3 and 4 of the attempt–grant model of fairness (`Lantana.Trace.Fairness`): the thread
pool (`Pool`), a pair that is one thread's, the scheduling action (`Sched`), weak and strong
fairness of a convex condition, and the schedule as a proof instrument. -/

@[expose] public section

namespace Lantana.Fairness

/-! ## 3. The pool, and a pair that is one thread's

A pool is a type of configurations with a step relation for the thread at each position, and a
run is a sequence of configurations.  The class `Pool` is all that the general theory takes from
a language.  Sections 1 and 2 use no pool; this section and the later ones use a thread's step. -/

/-- A thread pool: configurations, and the step of the thread at a position.  All the general
theory takes from a language.  MachCSL's instance is in `Fairness.lean`; Lantana's will be its
traces. -/
class Pool (Cfg : Type) where
  /-- The thread at position `i` steps from `c` to `c'`. -/
  Step : Nat → Cfg → Cfg → Prop

section Run

variable {Cfg : Type} [Pool Cfg]

/-- The thread at position `i` steps at position `n` of the run `σ`. -/
def Steps (i : Nat) (σ : Nat → Cfg) (n : Nat) : Prop := Pool.Step i (σ n) (σ (n + 1))

/-- Every position of the run is a step of some thread. -/
def PoolRun (σ : Nat → Cfg) : Prop := ∀ n, ∃ j, Pool.Step j (σ n) (σ (n + 1))

/-- The thread at `i` steps infinitely often: what fair scheduling gives a live thread (and
what a corpse's self-loops give a dead one). -/
def StepsInfOften (i : Nat) (σ : Nat → Cfg) : Prop := ∀ n, ∃ m ≥ n, Steps i σ m

end Run

/-! ### A pair that is one thread's

A pair of layer 0 is the thread's at `i` when its attempts are steps of that thread
(`AttemptGrant.OwnStep`).  Then its counter never moves at another thread's step
(`AttemptGrant.counter_stay_of_other`), and the thread can consume it at its own steps alone.  The
thread's view of section 5 is such a pair for every action (`Thread.ownStep`).  The action's pair
of layer 1 need not be one, because the step at a position where `A` holds may be any thread's. -/

namespace AttemptGrant

variable {Cfg : Type} [Pool Cfg] {i : Nat} {σ : Nat → Cfg} {attempt grant : Nat → Prop}
  {δ : Nat → Nat} {n : Nat}

/-- The attempts are steps of the thread at `i`: the pair is the thread's. -/
def OwnStep (i : Nat) (σ : Nat → Cfg) (attempt : Nat → Prop) : Prop :=
  ∀ n, attempt n → Steps i σ n

/-- A thread's pair has a counter that never moves at another thread's step.  The one rule that
names a thread. -/
theorem counter_stay_of_other (hos : OwnStep i σ attempt) (hδ : IsCounter attempt grant δ)
    (hs : ¬ Steps i σ n) : δ n = δ (n + 1) :=
  counter_stay hδ fun ha => hs (hos n ha)

end AttemptGrant

/-! ## 4. The scheduling action, and the schedule as a proof instrument (`Sched`, `Schedule`)

Fair scheduling is an action of the attempt–grant model, stated like every other fairness
assumption.  The language supplies an activity predicate `active`: the thread at `i` exists and
can step.  The enabling condition is that the thread is active, and the grant is the thread's step
(`Sched.grant`).  Strong fairness of this action is fair scheduling (`Sched.SF`).  It gives a
thread active infinitely often infinitely many steps (`Sched.stepsInfOften_of_sf`), which is the
hypothesis of every completeness theorem of section 5.  The thread's view of its scheduling has no
misses, because each attempt of the thread is one of its steps and so a grant (`Sched.certain`).
The view holds outright and its counter is zero (`Sched.ag`, `Sched.counter_zero`), so it tells
the thread nothing.  Scheduling has no cheap path; the logic consumes it on the general path only.

Fair scheduling is strong fairness, yet where activity is convex it is no stronger than weak
fairness, the usual justice requirement.  A condition is convex along a run when it holds at every
position between two where it holds (`Action.Convex`).  A convex condition that holds infinitely
often holds from some position on, so for it `SF` and `WF` coincide (`Action.sf_iff_wf_of_convex`).
A thread's activity is convex in both worlds: a MachCSL thread is live from its birth to its cut,
and a Lantana thread is active from its fork until it becomes a value.

A run carries no thread.  It is a sequence of configurations whose every transition is a step of
some thread (`PoolRun`), and no assumption names the thread that steps.  At a transition that
changes the configuration the stepping thread is determined.  At a no-op transition several
threads' step relations may hold: a corpse's self-loop, a blocked retry with nothing to drop, a
task at a closed gate.  Nothing observable depends on who took a no-op step.  The adequacy proof
still needs one owner per step: the owner's fuel pays for the step, and the scheduling counters of
the other active threads drop.  So the adequacy proof chooses a schedule, the stepping thread at
each position (`Schedule`), as a proof instrument.  Two facts carry the relational assumptions
over to the schedule's bookkeeping, and they are the bridge.  Under any schedule, an action whose
grant only its thread can take (`SoleOwner`) gives that thread its labelled view
(`labelledView_of_sf`).  Section 6 chooses a schedule under which a thread active infinitely
often is named infinitely often while active (`exists_fair_schedule`).

Section 5 comes after this one, so the thread's view of scheduling is stated here over layer 0.
`Sched.AG`, `Sched.certain` and `Sched.counter_zero` are section 5's `Thread.AttemptGrant`,
`Thread.Certain` and `Thread.IsCounter` at the scheduling action, by abbreviation, and section 5's
theorems apply to them as they stand. -/

/-! ### The scheduling action (`Sched`) -/

namespace Sched

variable {Cfg : Type} [Pool Cfg]

/-- Fair scheduling as an action of the attempt–grant model.  The language supplies `active`:
the thread at `i` exists and can step (MachCSL: a live hart or task; Lantana: not a value).  The
grant is the thread's step.  Its strong fairness is fair scheduling: a thread active infinitely
often steps infinitely often. -/
abbrev grant (i : Nat) (c c' : Cfg) : Prop := Pool.Step i c c'

/-- Fair scheduling of the thread at `i`, for the activity predicate `active`. -/
abbrev SF (active : Nat → Cfg → Prop) (i : Nat) (σ : Nat → Cfg) : Prop :=
  Action.SF (active i) (grant i) σ

/-- The thread at `i` attempts at `n`, in its view of its scheduling: it steps there while active.
Section 5's `Thread.attempt i (active i) σ`, restated because section 5 comes later. -/
abbrev attempt (active : Nat → Cfg → Prop) (i : Nat) (σ : Nat → Cfg) (n : Nat) : Prop :=
  Steps i σ n ∧ active i (σ n)

/-- The thread's own view of its scheduling: section 5's
`Thread.AttemptGrant i (active i) (grant i) σ`. -/
abbrev AG (active : Nat → Cfg → Prop) (i : Nat) (σ : Nat → Cfg) : Prop :=
  AttemptGrant.Fair (attempt active i σ) (Action.grant (grant i) σ)

variable {active : Nat → Cfg → Prop} {i : Nat} {σ : Nat → Cfg}

/-- Own grant: the grant is the thread's step.  Section 5's `Thread.OwnGrant i (grant i)`. -/
theorem ownGrant : ∀ {c c' : Cfg}, grant i c c' → Pool.Step i c c' := fun hg => hg

/-- What every completeness theorem needs: a thread active infinitely often and fairly scheduled
steps infinitely often. -/
theorem stepsInfOften_of_sf (hsf : SF active i σ)
    (hinf : MissHit.InfOften (fun n => active i (σ n))) : StepsInfOften i σ :=
  fun n => let ⟨m, hm, _, hs⟩ := hsf hinf n; ⟨m, hm, hs⟩

/-- The thread's view of its own scheduling has no misses: every attempt is a step, so every
attempt is granted.  Scheduling has no cheap path; it is consumed on the general path only.
Section 5's `Thread.Certain i (active i) (grant i) σ`. -/
theorem certain : AttemptGrant.Certain (attempt active i σ) (Action.grant (grant i) σ) :=
  fun _ ha => ha.1

/-- The thread's view of its scheduling holds outright. -/
theorem ag : AG active i σ := AttemptGrant.fair_of_certain certain

/-- The counter of the thread's view of its scheduling is zero.  Section 5's
`Thread.IsCounter i (active i) (grant i) σ (fun _ => 0)`. -/
theorem counter_zero :
    AttemptGrant.IsCounter (attempt active i σ) (Action.grant (grant i) σ) (fun _ => 0) :=
  AttemptGrant.counter_zero_of_certain certain

end Sched

/-! ### Weak and strong fairness coincide for a convex condition -/

namespace Action

variable {Cfg : Type}

/-- `A` is convex along the run: true at `n` and at `k ≥ n` makes it true in between.  A thread's
activity is convex in both worlds: a MachCSL thread is live from its birth to its cut, a Lantana
thread from its fork until it becomes a value. -/
def Convex (A : Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  ∀ n m k, n ≤ m → m ≤ k → A (σ n) → A (σ k) → A (σ m)

variable {A : Cfg → Prop} {G : Cfg → Cfg → Prop} {σ : Nat → Cfg}

/-- A convex condition that holds infinitely often holds from some position on. -/
theorem eventually_always_of_infOften_of_convex (hconv : Convex A σ)
    (hinf : MissHit.InfOften (fun n => A (σ n))) : ∃ N, ∀ n, N ≤ n → A (σ n) :=
  let ⟨N, _, hAN⟩ := hinf 0
  ⟨N, fun n hn => let ⟨k, hk, hAk⟩ := hinf n; hconv N n k hn hk hAN hAk⟩

/-- For a convex condition, strong and weak fairness of the action coincide. -/
theorem sf_iff_wf_of_convex (hconv : Convex A σ) : SF A G σ ↔ WF A G σ :=
  ⟨wf_of_sf, fun hwf hinf => hwf (eventually_always_of_infOften_of_convex hconv hinf)⟩

end Action

/-! ### The schedule, a proof instrument -/

section Schedule

variable {Cfg : Type} [Pool Cfg]

/-- A schedule of a run: the thread stepping at each position.  Not part of any assumption; the
adequacy proof picks one (`exists_fair_schedule`, section 6) to do its per-thread bookkeeping. -/
def Schedule (σ : Nat → Cfg) (sched : Nat → Nat) : Prop :=
  ∀ n, Pool.Step (sched n) (σ n) (σ (n + 1))

/-- A relation that only its thread can take: whenever `G c c'` holds, the only thread whose step
relation accepts the transition is `i`.  The six actions of MachCSL have it for `A c ∧ G c c'`, the
hit: a served transition changes the thread's entry, which another thread's step leaves in place.
Not for `G` alone, since a dead thread's self-loop satisfies a grant vacuously
(`Cycle.lean`, the `soleOwner` lemmas). -/
def SoleOwner (i : Nat) (G : Cfg → Cfg → Prop) : Prop :=
  ∀ c c', G c c' → ∀ j, Pool.Step j c c' → j = i

/-- The thread's view under a schedule: attempts are the positions where the schedule names the
thread and `A` holds. -/
abbrev labelledView (sched : Nat → Nat) (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop)
    (σ : Nat → Cfg) : Prop :=
  AttemptGrant.Fair (fun n => sched n = i ∧ A (σ n)) (Action.grant G σ)

variable {σ : Nat → Cfg} {sched : Nat → Nat} {i : Nat} {A : Cfg → Prop} {G : Cfg → Cfg → Prop}

/-- Under a schedule, the relational `SF` of an action whose hits have a sole owner gives the
thread's labelled view.  A relational hit is a labelled hit, because the schedule must name the
owner, and a labelled miss is a relational miss.  It is layer 0's restriction
(`AttemptGrant.fair_mono`). -/
theorem labelledView_of_sf (hsch : Schedule σ sched)
    (hso : SoleOwner i (fun c c' => A c ∧ G c c')) (hsf : Action.SF A G σ) :
    labelledView sched i A G σ :=
  AttemptGrant.fair_mono (fun _ ha => ha.2)
    (fun n hA hg => ⟨hso _ _ ⟨hA, hg⟩ (sched n) (hsch n), hA⟩) (Action.sf_iff_fair.1 hsf)

end Schedule

end Lantana.Fairness
