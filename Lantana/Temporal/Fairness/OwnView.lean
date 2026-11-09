/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Fairness.Scheduling

/-! # The thread's view of an action (layer 2)

The thread's view of an action `a` is layer 0 with the thread's own attempts: a step of the
thread at `i` from a configuration where `a` is enabled.  Its attempts are the thread's steps
(`ownStep`), so its counter moves only at the thread's own steps (`counter_stay_of_other`): the
cheap path.  The view is sound under own grant (`OwnGrant`: every grant is a step of the thread;
`attemptGrant_of_sf`), and it loses nothing under persistence of the enabling condition
(`Persists`, from stability `Stable` on a behavior) and fair scheduling of the thread
(`sf_of_attemptGrant`), so with own grant the two forms coincide (`sf_iff_attemptGrant`).  A
grant certain at the thread's attempts (`Certain`) gives the view outright and `WF` from fair
scheduling alone.
-/

@[expose] public section

namespace Lantana.Fairness

open scoped Lantana.TrProp

/-! ## 5. Layer 2: the thread's view of an action (`Thread`) -/

namespace Thread

variable {C : Type} [ThreadSystem C]

/-! ### Definitions -/

/-- The thread at `i` attempts: it steps from a configuration where the action is enabled. -/
abbrev attempt (i : ThreadId) (a : Action C) : TrProp C := threadStep i ∧ₜ a.enabledNow

/-- The thread's attempt is granted: it steps from a configuration where the action is enabled,
and its step is a grant. -/
abbrev hit (i : ThreadId) (a : Action C) : TrProp C :=
  AttemptGrant.hit (attempt i a) a.granted

/-- The thread's attempt is refused. -/
abbrev miss (i : ThreadId) (a : Action C) : TrProp C :=
  AttemptGrant.miss (attempt i a) a.granted

/-- The attempt–grant form of the thread's view: infinitely many refused attempts force infinitely
many granted ones.  The form the logic consumes on the cheap path. -/
abbrev AttemptGrant (i : ThreadId) (a : Action C) : TrProp C :=
  AttemptGrant.Fair (attempt i a) a.granted

/-- The counter of the thread's view: zero at a granted attempt, one more at a refused attempt
than at the next position, unchanged where the thread does not attempt. -/
abbrev IsCounter (i : ThreadId) (a : Action C) (δ : Nat → Nat) : TrProp C :=
  AttemptGrant.IsCounter (attempt i a) a.granted δ

/-- The grant is certain at the thread's attempts: every attempt of the thread at `i` is
granted. -/
abbrev Certain (i : ThreadId) (a : Action C) : TrProp C :=
  AttemptGrant.Certain (attempt i a) a.granted

/-- Own grant: the grant is one of the thread's transitions.  The property that makes the thread's
view sound. -/
def OwnGrant (i : ThreadId) (a : Action C) : Prop :=
  ∀ {c c' : C}, a.grant c c' → ThreadSystem.step i c c'

/-- The enabling condition is stable under every other thread's step. -/
def Stable (i : ThreadId) (a : Action C) : Prop :=
  ∀ {j : ThreadId} {c c' : C}, j ≠ i → ThreadSystem.step j c c' → a.enabled c → a.enabled c'

/-- The enabling condition persists along the run: where it holds, the thread steps now, or it
still holds at the next position, or it never holds again.  The general interface: it says
nothing about how the condition can be lost. -/
def Persists (i : ThreadId) (a : Action C) : TrProp C :=
  □ₜ (a.enabledNow →ₜ threadStep i ∨ₜ ○ₜ a.enabledNow ∨ₜ ○ₜ □ₜ ¬ₜ a.enabledNow)

variable {i : ThreadId} {a : Action C} {δ : Nat → Nat} {τ : Trace C}

/-! ### The pair is the thread's, and the action's at the thread's steps -/

/-- The attempts are steps of the thread, for every action. -/
theorem ownStep : AttemptGrant.OwnStep i (attempt i a) := fun _ h => h.1

/-- A miss is a step of the thread from a configuration where the action is enabled that is not a
grant. -/
theorem miss_iff : miss i a τ ↔ threadStep i τ ∧ a.enabled τ.now ∧ ¬ a.grant τ.now τ.next.now :=
  and_assoc

/-- A hit of the thread is a step of the thread at a granted position of the action. -/
theorem hit_iff_steps_action_hit : hit i a τ ↔ threadStep i τ ∧ a.hit τ := and_assoc

/-- A miss of the thread is a step of the thread at a refused position of the action. -/
theorem miss_iff_steps_action_miss : miss i a τ ↔ threadStep i τ ∧ a.miss τ :=
  miss_iff

/-- The meaning of the attempt–grant form: a thread that attempts infinitely often is granted
infinitely often. -/
theorem attemptGrant_iff_attempt :
    AttemptGrant i a τ ↔ ((□ₜ ◇ₜ attempt i a) τ → (□ₜ ◇ₜ hit i a) τ) :=
  AttemptGrant.fair_iff_attempt

/-! ### Soundness: under own grant, `SF` gives the thread's counter -/

/-- **Soundness.**  Under own grant, `SF` gives the attempt–grant form: layer 0's restriction
`AttemptGrant.fair_mono_of_le` applied to `Action.sf_iff_fair`. -/
theorem attemptGrant_of_sf (hown : OwnGrant i a) : a.SF ⊆ AttemptGrant i a :=
  fun τ hsf => AttemptGrant.fair_mono_of_le (fun _ ha => ha.2)
    (fun _ ⟨hA, hg⟩ => ⟨hown hg, hA⟩) τ (Action.sf_iff_fair.1 hsf)

/-- Under own grant, the response form gives the attempt–grant form. -/
theorem attemptGrant_of_response (hown : OwnGrant i a) : a.Response ⊆ AttemptGrant i a :=
  TrProp.le_trans Action.sf_of_response (attemptGrant_of_sf hown)

/-- Under own grant, the trusted form gives the thread's counter. -/
theorem counter_of_sf (hown : OwnGrant i a) (hsf : a.SF τ) : ∃ δ, IsCounter i a δ τ :=
  AttemptGrant.counter_of_fair (attemptGrant_of_sf hown τ hsf)

/-- Stay: at every step that is not the thread's the counter is unchanged. -/
theorem counter_stay_of_other (hδ : IsCounter i a δ τ) (hs : ¬ threadStep i τ) :
    δ τ.pos = δ (τ.pos + 1) :=
  AttemptGrant.counter_stay_of_other ownStep hδ hs

/-! ### Completeness: under persistence and fair scheduling, the view gives `SF` back -/

/-- Stability gives persistence on any behavior. -/
theorem persists_of_stable (hstab : Stable i a) : IsBehavior ⊆ Persists i a := by
  intro τ hrun m hm hA
  obtain ⟨j, hs⟩ := hrun m hm
  by_cases hji : j = i
  · subst hji
    exact Or.inl hs
  · exact Or.inr (Or.inl (hstab hji hs hA))

/-- A pending attempt survives the other threads' steps: if the enabling condition is stable and
holds now, it holds at every later position reached by other threads' steps only, in particular at
the thread's next step. -/
theorem attempt_pending (hstab : Stable i a) (hA : a.enabled τ.now) {k : Nat} (hk : τ.pos ≤ k)
    (hothers : ∀ k', τ.pos ≤ k' → k' < k →
      ∃ j, j ≠ i ∧ ThreadSystem.step j (τ.seq k') (τ.seq (k' + 1))) :
    a.enabled (τ.seq k) := by
  induction k with
  | zero =>
    rw [← Nat.le_zero.1 hk]
    exact hA
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · have hk' := ih (Nat.le_of_lt_succ hlt)
        (fun k' h1 h2 => hothers k' h1 (Nat.lt_succ_of_lt h2))
      obtain ⟨j, hji, hs⟩ := hothers k (Nat.le_of_lt_succ hlt) (Nat.lt_succ_self k)
      exact hstab hji hs hk'
    · rw [← heq]
      exact hA

/-- **Completeness.**  Under fair scheduling of the thread and persistence of the enabling
condition, the attempt–grant form gives `SF`. -/
theorem sf_of_attemptGrant :
    (ThreadStepInfOften i ∧ₜ Persists i a ∧ₜ AttemptGrant i a) ⊆ a.SF := by
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
    Nat.exists_min (p := fun m => n ≤ m ∧ threadStep i { τ with pos := m }) m ⟨hm, hsm⟩
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

/-- Under own grant, persistence and fair scheduling, the trusted form and the attempt–grant form
coincide. -/
theorem sf_iff_attemptGrant (hown : OwnGrant i a) (hsched : ThreadStepInfOften i τ)
    (hper : Persists i a τ) : a.SF τ ↔ AttemptGrant i a τ :=
  ⟨attemptGrant_of_sf hown τ, fun hag => sf_of_attemptGrant τ ⟨hsched, hper, hag⟩⟩

/-! ### A grant certain at the thread's own attempts -/

/-- With a grant certain at the thread's attempts there are no misses, so the attempt–grant form
holds outright. -/
theorem attemptGrant_of_certain : Certain i a ⊆ AttemptGrant i a :=
  AttemptGrant.fair_of_certain

/-- With a grant certain at the thread's attempts the zero function is a counter. -/
theorem counter_zero_of_certain (hc : Certain i a τ) : IsCounter i a (fun _ => 0) τ :=
  AttemptGrant.counter_zero_of_certain hc

/-- With a grant certain at the thread's attempts, weak fairness follows from fair scheduling
alone. -/
theorem wf_of_certain : (ThreadStepInfOften i ∧ₜ Certain i a) ⊆ a.WF := by
  rintro τ ⟨hsched, hc⟩ hwf
  obtain ⟨N, -, hNA⟩ := TrProp.eventually_always_iff.mp hwf
  refine TrProp.always_eventually_iff.mpr fun n hn => ?_
  obtain ⟨m, hm, hs⟩ :=
    TrProp.always_eventually_iff.mp hsched (max n N) (Nat.le_trans hn (Nat.le_max_left _ _))
  have hAm : a.enabled (τ.seq m) := hNA m (Nat.le_trans (Nat.le_max_right _ _) hm)
  exact ⟨m, Nat.le_trans (Nat.le_max_left _ _) hm, hAm,
    hc m (Nat.le_trans hn (Nat.le_trans (Nat.le_max_left _ _) hm)) ⟨hs, hAm⟩⟩

/-- With a grant certain at the thread's attempts, `SF` follows from fair scheduling and
persistence. -/
theorem sf_of_certain : (ThreadStepInfOften i ∧ₜ Persists i a ∧ₜ Certain i a) ⊆ a.SF :=
  fun τ ⟨hsched, hper, hc⟩ => sf_of_attemptGrant τ ⟨hsched, hper, attemptGrant_of_certain τ hc⟩

end Thread

end Lantana.Fairness
