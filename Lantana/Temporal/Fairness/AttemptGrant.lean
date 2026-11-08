/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Fairness.MissHit

/-! # The attempt–grant pair (layer 0)

Layer 0 of the attempt–grant model of fairness, over trace properties: two predicates on traces,
the *attempts* and the *grants*; a hit is a granted attempt, a miss a refused one; attempt–grant
fairness says that infinitely many misses force infinitely many hits (`Fair`), and it is the
existence of a counter, the budget of refusals before the next grant (`fair_iff_counter`).  The
counter's rules (`counter_reset`, `counter_drop`, `counter_stay`) are stated here once, for every
layer; restriction (`fair_mono`, with the inclusions holding from the current position on, and
`fair_mono_of_le`, with entailments) and a certain grant (`fair_of_certain`) too.

The statements are trace properties read at the current position of a trace `τ`; every formula
is a `□ₜ`, `◇ₜ` or an implication between such, so it is the same at every position of the run
(`TrProp.Absolute`).  They are proved from the engine `MissHit`
(`Lantana.Temporal.Fairness.MissHit`), arithmetic on positions that is not part of the theory's
interface, through the bridge `always_eventually_iff_infOften`.
-/

@[expose] public section

namespace Lantana.Fairness

open scoped Lantana.TrProp

/-! ## 1. Layer 0: the attempt–grant pair over trace properties (`AttemptGrant`) -/

namespace AttemptGrant

variable {C : Type}

/-! ### Definitions -/

/-- A granted attempt. -/
def hit (attempt grant : TrProp C) : TrProp C := attempt ∧ₜ grant

/-- A refused attempt. -/
def miss (attempt grant : TrProp C) : TrProp C := attempt ∧ₜ ¬ₜ grant

/-- Attempt–grant fairness: infinitely many refused attempts force infinitely many granted
ones. -/
def Fair (attempt grant : TrProp C) : TrProp C :=
  □ₜ ◇ₜ miss attempt grant →ₜ □ₜ ◇ₜ hit attempt grant

/-- The counter: zero at a granted attempt, one more at a refused attempt than at the next
position, unchanged where there is no attempt; from the current position on. -/
def IsCounter (attempt grant : TrProp C) (δ : Nat → Nat) : TrProp C :=
  □ₜ ((hit attempt grant →ₜ TrProp.atPos fun n => δ n = 0) ∧ₜ
    (miss attempt grant →ₜ TrProp.atPos fun n => δ n = δ (n + 1) + 1) ∧ₜ
    (¬ₜ attempt →ₜ TrProp.atPos fun n => δ n = δ (n + 1)))

/-- Every attempt is granted, from the current position on. -/
def Certain (attempt grant : TrProp C) : TrProp C := □ₜ (attempt →ₜ grant)

variable {attempt grant : TrProp C} {δ : Nat → Nat} {τ : Trace C}

/-! ### Hits, misses and the meaning of fairness -/

/-- No position is both a granted and a refused attempt. -/
theorem hit_miss_exclusive : ¬ (hit attempt grant τ ∧ miss attempt grant τ) :=
  fun ⟨hh, hm⟩ => hm.2 hh.2

/-- The attempts are exactly the granted and the refused attempts. -/
theorem attempt_iff : attempt τ ↔ hit attempt grant τ ∨ miss attempt grant τ :=
  ⟨fun ha => (Classical.em (grant τ)).imp (And.intro ha) (And.intro ha),
    fun h => h.elim And.left And.left⟩

/-- Fairness is the same at every position of the run. -/
theorem fair_absolute : TrProp.Absolute (Fair attempt grant) :=
  TrProp.absolute_imp TrProp.absolute_always_eventually TrProp.absolute_always_eventually

/-- The meaning: infinitely many attempts force infinitely many granted ones. -/
theorem fair_iff_attempt :
    Fair attempt grant τ ↔ ((□ₜ ◇ₜ attempt) τ → (□ₜ ◇ₜ hit attempt grant) τ) := by
  change ((□ₜ ◇ₜ miss attempt grant) τ → _) ↔ _
  simp only [always_eventually_iff_infOften]
  constructor
  · intro hag hinf
    apply Classical.byContradiction
    intro hno
    obtain ⟨N, hN⟩ := MissHit.eventually_not_of_not_infOften hno
    apply hno
    apply hag
    intro n
    obtain ⟨m, hm, ham⟩ := hinf (n + N)
    have hhm : ¬ TrProp.along (hit attempt grant) τ m :=
      hN m (Nat.le_trans (Nat.le_add_left N n) hm)
    exact ⟨m, Nat.le_trans (Nat.le_add_right n N) hm, (attempt_iff.1 ham).resolve_left hhm⟩
  · intro h hinf
    exact h (MissHit.infOften_mono (fun _ hm => hm.1) hinf)

/-- A response property gives fairness: every attempt is followed by a granted attempt, at it or
later. -/
theorem fair_of_response : (□ₜ (attempt →ₜ ◇ₜ hit attempt grant)) ⊆ Fair attempt grant := by
  intro τ h hmiss
  refine TrProp.always_eventually_iff.mpr fun n hn => ?_
  obtain ⟨m, hm, ha, -⟩ := TrProp.always_eventually_iff.mp hmiss n hn
  obtain ⟨k, hk, hhit⟩ := TrProp.eventually_iff.mp (h m (Nat.le_trans hn hm) ha)
  exact ⟨k, Nat.le_trans hm hk, hhit⟩

/-! ### The counter and its rules

Attempt–grant fairness is the existence of a counter.  At a granted attempt the counter resets, at
a refused attempt it drops by one, and where there is no attempt it stays.  The three rules are
the counter's definition (`isCounter_iff`).  The rules are stated at the current position; a
counter from `τ` is a counter from every later position (`IsCounter.mono`). -/

/-- Attempt–grant fairness is the existence of a counter. -/
theorem fair_iff_counter : Fair attempt grant τ ↔ ∃ δ, IsCounter attempt grant δ τ := by
  constructor
  · intro hag
    have hmh : MissHit.Fair (TrProp.along (hit attempt grant) τ)
        (TrProp.along (miss attempt grant) τ) := fun hinf =>
      always_eventually_iff_infOften.1 (hag (always_eventually_iff_infOften.2 hinf))
    obtain ⟨hreset, hdrop, hstay⟩ := MissHit.counter_spec (fun _ => hit_miss_exclusive) hmh
    exact ⟨MissHit.budget _ _, fun m _ =>
      ⟨hreset m, hdrop m, fun ha => hstay m (fun h => ha h.1) fun h => ha h.1⟩⟩
  · rintro ⟨δ, hδ⟩ hmiss
    have hδ' : MissHit.IsCounter (fun n => TrProp.along (hit attempt grant) τ (τ.pos + n))
        (fun n => TrProp.along (miss attempt grant) τ (τ.pos + n)) fun n => δ (τ.pos + n) :=
      ⟨fun _ => (hδ _ (Nat.le_add_right _ _)).1, fun _ => (hδ _ (Nat.le_add_right _ _)).2.1,
        fun _ hh hm => (hδ _ (Nat.le_add_right _ _)).2.2 fun ha =>
          (attempt_iff.1 ha).elim hh hm⟩
    exact always_eventually_iff_infOften_from.2
      (MissHit.fair_of_counter hδ' (always_eventually_iff_infOften_from.1 hmiss))

/-- Attempt–grant fairness gives a counter. -/
theorem counter_of_fair (hag : Fair attempt grant τ) : ∃ δ, IsCounter attempt grant δ τ :=
  fair_iff_counter.1 hag

/-- A counter gives attempt–grant fairness. -/
theorem fair_of_counter (hδ : IsCounter attempt grant δ τ) : Fair attempt grant τ :=
  fair_iff_counter.2 ⟨δ, hδ⟩

/-- A counter from `τ` is a counter from every later position. -/
theorem IsCounter.mono (hδ : IsCounter attempt grant δ τ) {m : Nat} (hm : τ.pos ≤ m) :
    IsCounter attempt grant δ { τ with pos := m } :=
  TrProp.always_idemp τ hδ m hm

/-- Reset: the counter is zero at a granted attempt. -/
theorem counter_reset (hδ : IsCounter attempt grant δ τ) (ha : attempt τ) (hg : grant τ) :
    δ τ.pos = 0 :=
  (TrProp.always_elim τ hδ).1 ⟨ha, hg⟩

/-- Drop: at a refused attempt the counter is one more than at the next position. -/
theorem counter_drop (hδ : IsCounter attempt grant δ τ) (ha : attempt τ) (hg : ¬ grant τ) :
    δ τ.pos = δ (τ.pos + 1) + 1 :=
  (TrProp.always_elim τ hδ).2.1 ⟨ha, hg⟩

/-- Stay: where there is no attempt the counter is unchanged. -/
theorem counter_stay (hδ : IsCounter attempt grant δ τ) (ha : ¬ attempt τ) :
    δ τ.pos = δ (τ.pos + 1) :=
  (TrProp.always_elim τ hδ).2.2 ha

/-- The counter, by its three rules at every position from the current one on. -/
theorem isCounter_iff : IsCounter attempt grant δ τ ↔
    ∀ m, τ.pos ≤ m →
      (TrProp.along attempt τ m → TrProp.along grant τ m → δ m = 0) ∧
      (TrProp.along attempt τ m → ¬ TrProp.along grant τ m → δ m = δ (m + 1) + 1) ∧
      (¬ TrProp.along attempt τ m → δ m = δ (m + 1)) :=
  ⟨fun hδ m hm => ⟨fun ha hg => (hδ m hm).1 ⟨ha, hg⟩, fun ha hg => (hδ m hm).2.1 ⟨ha, hg⟩,
      (hδ m hm).2.2⟩,
    fun h m hm => ⟨fun hh => (h m hm).1 hh.1 hh.2, fun hmiss => (h m hm).2.1 hmiss.1 hmiss.2,
      (h m hm).2.2⟩⟩

/-! ### What a counter bounds -/

/-- A refused attempt has a positive counter. -/
theorem counter_pos_of_miss (hδ : IsCounter attempt grant δ τ) (h : miss attempt grant τ) :
    0 < δ τ.pos := by
  have := counter_drop hδ h.1 h.2
  omega

/-- The base case of a waiter's induction: an attempt made at counter zero is granted. -/
theorem grant_of_attempt_of_counter_zero (hδ : IsCounter attempt grant δ τ) (ha : attempt τ)
    (h0 : δ τ.pos = 0) : grant τ :=
  Classical.byContradiction fun hg => Nat.ne_of_gt (counter_pos_of_miss hδ ⟨ha, hg⟩) h0

/-- The bound: with no granted attempt in the next `k` positions, the refused attempts in that
window plus the counter at its end are at most the counter now. -/
theorem counter_bounds_misses (hδ : IsCounter attempt grant δ τ) (k : Nat)
    (hno : ∀ m, τ.pos ≤ m → m < τ.pos + k → ¬ TrProp.along (hit attempt grant) τ m) :
    δ (τ.pos + k) + MissHit.countMiss (TrProp.along (miss attempt grant) τ) τ.pos k ≤ δ τ.pos := by
  have hδ' := isCounter_iff.1 hδ
  suffices h : ∀ k n, τ.pos ≤ n →
      (∀ m, n ≤ m → m < n + k → ¬ TrProp.along (hit attempt grant) τ m) →
      δ (n + k) + MissHit.countMiss (TrProp.along (miss attempt grant) τ) n k ≤ δ n from
    h k τ.pos (Nat.le_refl _) hno
  intro k
  induction k with
  | zero =>
    intro n _ _
    simp
  | succ k ih =>
    intro n hn hno
    have ih' := ih (n + 1) (Nat.le_succ_of_le hn) fun m hm1 hm2 => hno m (by omega) (by omega)
    have e : n + (k + 1) = n + 1 + k := by omega
    rw [e]
    rcases Classical.em (TrProp.along attempt τ n) with ha | ha
    · have hg : ¬ TrProp.along grant τ n := fun hg => hno n (Nat.le_refl n) (by omega) ⟨ha, hg⟩
      rw [MissHit.countMiss_succ_of_miss (miss := TrProp.along (miss attempt grant) τ) ⟨ha, hg⟩]
      have := (hδ' n hn).2.1 ha hg
      omega
    · rw [MissHit.countMiss_succ_of_not_miss (miss := TrProp.along (miss attempt grant) τ)
        fun hm => ha hm.1]
      have := (hδ' n hn).2.2 ha
      omega

/-! ### Restriction -/

/-- Fairness survives shrinking the attempts to a subset that still contains every granted
attempt, the two inclusions holding from the current position on: the attempts of the smaller
pair are attempts of the larger one, and every granted attempt of the larger is an attempt of the
smaller. -/
theorem fair_mono {attempt' : TrProp C} :
    (□ₜ (attempt' →ₜ attempt) ∧ₜ □ₜ (attempt ∧ₜ grant →ₜ attempt') ∧ₜ Fair attempt grant) ⊆
      Fair attempt' grant := by
  rintro τ ⟨hatt, hgr, hag⟩ hmiss
  have hmiss' : (□ₜ ◇ₜ miss attempt grant) τ := TrProp.always_eventually_iff.mpr fun n hn => by
    obtain ⟨m, hnm, ha, hg⟩ := TrProp.always_eventually_iff.mp hmiss n hn
    exact ⟨m, hnm, hatt m (Nat.le_trans hn hnm) ha, hg⟩
  refine TrProp.always_eventually_iff.mpr fun n hn => ?_
  obtain ⟨m, hnm, hh⟩ := TrProp.always_eventually_iff.mp (hag hmiss') n hn
  exact ⟨m, hnm, hgr m (Nat.le_trans hn hnm) hh, hh.2⟩

/-- Restriction with the inclusions as entailments. -/
theorem fair_mono_of_le {attempt' : TrProp C} (hatt : attempt' ⊆ attempt)
    (hgr : (attempt ∧ₜ grant) ⊆ attempt') : Fair attempt grant ⊆ Fair attempt' grant :=
  fun τ hag => fair_mono τ ⟨fun _ _ => hatt _, fun _ _ => hgr _, hag⟩

/-! ### A certain grant -/

/-- A certain grant gives fairness outright. -/
theorem fair_of_certain : Certain attempt grant ⊆ Fair attempt grant := by
  intro τ hc hmiss
  obtain ⟨m, hm, ha, hg⟩ := TrProp.always_eventually_iff.mp hmiss τ.pos (Nat.le_refl _)
  exact absurd (hc m hm ha) hg

/-- With a certain grant the zero function is a counter: it resets at every granted attempt and
stays elsewhere, and never drops. -/
theorem counter_zero_of_certain (hc : Certain attempt grant τ) :
    IsCounter attempt grant (fun _ => 0) τ :=
  fun m hm => ⟨fun _ => rfl, fun hmiss => absurd (hc m hm hmiss.1) hmiss.2, fun _ => rfl⟩

end AttemptGrant

end Lantana.Fairness
