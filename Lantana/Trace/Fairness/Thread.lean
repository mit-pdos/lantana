/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Trace.Fairness.Pool

/-! # The thread's view of an action (layer 2)

Layer 2 of the attempt–grant model of fairness (`Lantana.Trace.Fairness`): the thread's view of an
action, its soundness under own grant and its completeness under persistence and fair
scheduling. -/

@[expose] public section

namespace Lantana.Fairness

/-! ## 5. Layer 2: the thread's view of an action (`Thread`)

The thread's view is layer 0 with the thread's own attempts.  An attempt is a step of the thread at
`i` from a configuration where `A` holds, and a grant is a step in `G`, as at layer 1.  A hit is
a granted attempt and a miss a refused one.  The view's attempts are the thread's steps for every
action (`ownStep`), so its counter moves only at the thread's own steps (`counter_stay_of_other`),
and the thread can consume it there with no help from the logic.  This is the cheap path, which
Lantana takes for a declared action with own grant.  Like layer 1, the layer states its pair as
abbreviations of layer 0's and copies none of its rules; it restates by the thread's name the three
facts the documents cite (`attemptGrant_iff_attempt`, `attemptGrant_of_certain`,
`counter_zero_of_certain`).

The view is sound under own grant (`OwnGrant`), which says that every grant is a step of the
thread.  Then the thread's attempts are the positions where `A` holds, cut down to the thread's
steps, and they keep every granted position.  That is layer 0's restriction (`fair_mono`), and
`SF` gives the attempt–grant form (`attemptGrant_of_sf`).  The view loses nothing under
persistence of `A` and fair scheduling of the thread (`sf_of_attemptGrant`), so the two forms
coincide (`sf_iff_attemptGrant`).  Without own grant a grant may happen at another thread's step.
The thread must then use the counter of layer 1, and the logic must tell it of the updates at the
other threads' steps.

The two layers' certain grants differ.  At layer 1 a certain grant covers every position where `A`
holds, whoever steps, and gives `SF` outright (`Action.sf_of_certain`).  At layer 2 it covers the
thread's own attempts only (`Certain`); it gives the attempt–grant form outright, and `SF` only
with persistence and fair scheduling (`sf_of_certain`).  A device task at a gate
(`Fairness.lean` 5.5) is the layer-2 case. -/

namespace Thread

variable {Cfg : Type} [Pool Cfg]

/-! ### Definitions -/

/-- The thread at `i` attempts at `n`: it steps there from a configuration where `A` holds. -/
abbrev attempt (i : Nat) (A : Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop :=
  Steps i σ n ∧ A (σ n)

/-- The thread's attempt at `n` is granted: the thread steps from a configuration where `A` holds,
and its step is a grant. -/
abbrev hit (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop :=
  AttemptGrant.hit (attempt i A σ) (Action.grant G σ) n

/-- The thread's attempt at `n` is refused. -/
abbrev miss (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop :=
  AttemptGrant.miss (attempt i A σ) (Action.grant G σ) n

/-- The attempt–grant form of the thread's view: infinitely many refused attempts force infinitely
many granted ones.  The form the logic consumes on the cheap path. -/
abbrev AttemptGrant (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  AttemptGrant.Fair (attempt i A σ) (Action.grant G σ)

/-- The counter of the thread's view: zero at a granted attempt, one more at a refused attempt
than at the next position, unchanged where the thread does not attempt. -/
abbrev IsCounter (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg)
    (δ : Nat → Nat) : Prop :=
  AttemptGrant.IsCounter (attempt i A σ) (Action.grant G σ) δ

/-- The grant is certain at the thread's attempts: every attempt of the thread at `i` is
granted. -/
abbrev Certain (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  AttemptGrant.Certain (attempt i A σ) (Action.grant G σ)

/-- Own grant: the grant is one of the thread's transitions.  The property that makes the thread's
view sound. -/
def OwnGrant (i : Nat) (G : Cfg → Cfg → Prop) : Prop :=
  ∀ {c c' : Cfg}, G c c' → Pool.Step i c c'

/-- `A` is stable under every other thread's step. -/
def Stable (i : Nat) (A : Cfg → Prop) : Prop :=
  ∀ {j : Nat} {c c' : Cfg}, j ≠ i → Pool.Step j c c' → A c → A c'

/-- `A` persists along the run: where it holds, the thread steps now, or `A` still holds at the
next position, or `A` never holds again.  The general interface: it says nothing about how `A`
can be lost. -/
def Persists (i : Nat) (A : Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  ∀ n, A (σ n) → Steps i σ n ∨ A (σ (n + 1)) ∨ ∀ m, n < m → ¬ A (σ m)

variable {i : Nat} {A : Cfg → Prop} {G : Cfg → Cfg → Prop} {σ : Nat → Cfg} {δ : Nat → Nat}
  {n : Nat}

/-! ### The pair is the thread's, and the action's at the thread's steps -/

/-- The attempts are steps of the thread, for every action. -/
theorem ownStep : AttemptGrant.OwnStep i σ (attempt i A σ) := fun _ h => h.1

/-- A miss is a step of the thread from a configuration where `A` holds that is not a grant. -/
theorem miss_iff : miss i A G σ n ↔ Steps i σ n ∧ A (σ n) ∧ ¬ G (σ n) (σ (n + 1)) :=
  ⟨fun ⟨⟨hs, hA⟩, hg⟩ => ⟨hs, hA, hg⟩, fun ⟨hs, hA, hg⟩ => ⟨⟨hs, hA⟩, hg⟩⟩

/-- A hit of the thread is a step of the thread at a granted position of the action. -/
theorem hit_iff_steps_action_hit : hit i A G σ n ↔ Steps i σ n ∧ Action.hit A G σ n :=
  ⟨fun ⟨⟨hs, hA⟩, hg⟩ => ⟨hs, hA, hg⟩, fun ⟨hs, hA, hg⟩ => ⟨⟨hs, hA⟩, hg⟩⟩

/-- A miss of the thread is a step of the thread at a refused position of the action. -/
theorem miss_iff_steps_action_miss : miss i A G σ n ↔ Steps i σ n ∧ Action.miss A G σ n :=
  miss_iff

/-- The meaning of the attempt–grant form: a thread that attempts infinitely often is granted
infinitely often. -/
theorem attemptGrant_iff_attempt :
    AttemptGrant i A G σ ↔ (MissHit.InfOften (attempt i A σ) → MissHit.InfOften (hit i A G σ)) :=
  AttemptGrant.fair_iff_attempt

/-! ### Soundness: under own grant, `SF` gives the thread's counter -/

/-- **Soundness.**  Under own grant, `SF` gives the attempt–grant form.  It is layer 0's
restriction `AttemptGrant.fair_mono` applied to `Action.sf_iff_fair`: the thread's attempts are
among the positions where `A` holds, and under own grant they contain every granted one. -/
theorem attemptGrant_of_sf (hown : OwnGrant i G) (hsf : Action.SF A G σ) :
    AttemptGrant i A G σ :=
  AttemptGrant.fair_mono (fun _ ha => ha.2) (fun _ hA hg => ⟨hown hg, hA⟩)
    (Action.sf_iff_fair.1 hsf)

/-- Under own grant, the response form gives the attempt–grant form. -/
theorem attemptGrant_of_response (hown : OwnGrant i G) (h : Action.Response A G σ) :
    AttemptGrant i A G σ :=
  attemptGrant_of_sf hown (Action.sf_of_response h)

/-- Under own grant, the trusted form gives the thread's counter. -/
theorem counter_of_sf (hown : OwnGrant i G) (hsf : Action.SF A G σ) :
    ∃ δ, IsCounter i A G σ δ :=
  AttemptGrant.counter_of_fair (attemptGrant_of_sf hown hsf)

/-- Stay: at every step that is not the thread's the counter is unchanged. -/
theorem counter_stay_of_other (hδ : IsCounter i A G σ δ) (hs : ¬ Steps i σ n) :
    δ n = δ (n + 1) :=
  AttemptGrant.counter_stay_of_other ownStep hδ hs

/-! ### Completeness: under persistence and fair scheduling, the view gives `SF` back

Past the last grant, `A` holding at a position persists to the thread's next step, which is then
a refused attempt.  So infinitely many positions where `A` holds give infinitely many misses of the
thread, and the attempt–grant form gives infinitely many grants.  Persistence follows from
stability under the other threads' steps on any run of the pool (`persists_of_stable`). -/

/-- Stability gives persistence on any run of the pool. -/
theorem persists_of_stable (hrun : PoolRun σ) (hstab : Stable i A) : Persists i A σ := by
  intro n hA
  obtain ⟨j, hs⟩ := hrun n
  by_cases hji : j = i
  · subst hji
    exact Or.inl hs
  · exact Or.inr (Or.inl (hstab hji hs hA))

/-- A pending attempt survives the other threads' steps: if `A` is stable and holds at `n`, it
holds at every later position reached by other threads' steps only, in particular at the
thread's next step. -/
theorem attempt_pending (hstab : Stable i A) (hA : A (σ n)) {k : Nat} (hnk : n ≤ k)
    (hothers : ∀ k', n ≤ k' → k' < k → ∃ j, j ≠ i ∧ Pool.Step j (σ k') (σ (k' + 1))) :
    A (σ k) := by
  induction k with
  | zero =>
    have h0 : n = 0 := Nat.le_zero.1 hnk
    subst h0
    exact hA
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le hnk with hlt | heq
    · have hk := ih (Nat.le_of_lt_succ hlt)
        (fun k' h1 h2 => hothers k' h1 (Nat.lt_succ_of_lt h2))
      obtain ⟨j, hji, hs⟩ := hothers k (Nat.le_of_lt_succ hlt) (Nat.lt_succ_self k)
      exact hstab hji hs hk
    · subst heq
      exact hA

/-- **Completeness.**  Under fair scheduling of the thread and persistence of `A`, the
attempt–grant form gives `SF`. -/
theorem sf_of_attemptGrant (hsched : StepsInfOften i σ) (hper : Persists i A σ)
    (hag : AttemptGrant i A G σ) : Action.SF A G σ := by
  intro hA
  apply Classical.byContradiction
  intro hno
  obtain ⟨N, hN⟩ := MissHit.eventually_not_of_not_infOften hno
  apply hno
  refine MissHit.infOften_mono (fun _ hh => ⟨hh.1.2, hh.2⟩) (hag fun n₀ => ?_)
  obtain ⟨n, hn, hAn⟩ := hA (n₀ + N)
  obtain ⟨m, hm, hsm⟩ := hsched n
  obtain ⟨m', ⟨hnm', hsm'⟩, hmin⟩ :=
    Nat.exists_min (p := fun m => n ≤ m ∧ Steps i σ m) m ⟨hm, hsm⟩
  have hAk : ∀ k, n ≤ k → k ≤ m' → A (σ k) := by
    intro k hnk hkm
    induction k with
    | zero =>
      have h0 : n = 0 := Nat.le_zero.1 hnk
      subst h0
      exact hAn
    | succ k ih =>
      rcases Nat.lt_or_eq_of_le hnk with hlt | heq
      · have hk := ih (Nat.le_of_lt_succ hlt) (Nat.le_of_succ_le hkm)
        rcases hper k hk with hs | hA' | hgone
        · exact absurd ⟨Nat.le_of_lt_succ hlt, hs⟩
            (hmin k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hkm))
        · exact hA'
        · obtain ⟨m'', hm'', hA''⟩ := hA (k + 1)
          exact absurd hA'' (hgone m'' (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hm''))
      · subst heq
        exact hAn
  have hAm := hAk m' hnm' (Nat.le_refl _)
  refine ⟨m', Nat.le_trans (Nat.le_add_right n₀ N) (Nat.le_trans hn hnm'), ⟨hsm', hAm⟩, ?_⟩
  intro hg
  exact hN m' (Nat.le_trans (Nat.le_add_left N n₀) (Nat.le_trans hn hnm')) ⟨hAm, hg⟩

/-- Under own grant, persistence and fair scheduling, the trusted form and the attempt–grant form
coincide. -/
theorem sf_iff_attemptGrant (hown : OwnGrant i G) (hsched : StepsInfOften i σ)
    (hper : Persists i A σ) : Action.SF A G σ ↔ AttemptGrant i A G σ :=
  ⟨attemptGrant_of_sf hown, sf_of_attemptGrant hsched hper⟩

/-! ### A grant certain at the thread's own attempts

When every attempt of the thread is granted, the thread's view has no misses.  Its attempt–grant
form holds outright and its counter is identically zero.  Weak fairness follows from fair
scheduling alone, and `SF` from fair scheduling and persistence.  The device task at a gate
(`Fairness.lean` 5.5) waits on whoever opens the gate, which is an obligation and not a fairness
assumption. -/

/-- With a grant certain at the thread's attempts there are no misses, so the attempt–grant form
holds outright. -/
theorem attemptGrant_of_certain (hc : Certain i A G σ) : AttemptGrant i A G σ :=
  AttemptGrant.fair_of_certain hc

/-- With a grant certain at the thread's attempts the zero function is a counter: reset at every
granted attempt, stay elsewhere, never a drop. -/
theorem counter_zero_of_certain (hc : Certain i A G σ) : IsCounter i A G σ (fun _ => 0) :=
  AttemptGrant.counter_zero_of_certain hc

/-- With a grant certain at the thread's attempts, weak fairness follows from fair scheduling
alone. -/
theorem wf_of_certain (hsched : StepsInfOften i σ) (hc : Certain i A G σ) : Action.WF A G σ := by
  rintro ⟨N, hN⟩ n
  obtain ⟨m, hm, hs⟩ := hsched (n + N)
  have hA : A (σ m) := hN m (Nat.le_trans (Nat.le_add_left N n) hm)
  exact ⟨m, Nat.le_trans (Nat.le_add_right n N) hm, hA, hc m ⟨hs, hA⟩⟩

/-- With a grant certain at the thread's attempts, `SF` follows from fair scheduling and
persistence. -/
theorem sf_of_certain (hsched : StepsInfOften i σ) (hper : Persists i A σ)
    (hc : Certain i A G σ) : Action.SF A G σ :=
  sf_of_attemptGrant hsched hper (attemptGrant_of_certain hc)

end Thread

end Lantana.Fairness
