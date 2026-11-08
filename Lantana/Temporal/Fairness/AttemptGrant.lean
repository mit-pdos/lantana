/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.TracePropRules

/-! # The attempt–grant pair (layer 0)

Layer 0 of the attempt–grant model of fairness, over trace properties: two predicates on traces,
the *attempts* and the *grants*; a hit is a granted attempt, a miss a refused one; attempt–grant
fairness says that infinitely many misses force infinitely many hits (`Fair`), and it is the
existence of a counter, the budget of refusals before the next grant (`fair_iff_counter`).  The
counter's rules (`counter_reset`, `counter_drop`, `counter_stay`) are stated here once, for every
layer; restriction (`fair_mono`) and a certain grant (`fair_of_certain`) too.

The statements are trace properties read at the current position of a trace `τ`; every formula
is a `□ₜ`, `◇ₜ` or an implication between such, so it is the same at every position of the run
(`TrProp.Absolute`).  The engine underneath, `MissHit`, is arithmetic on positions: a budget
counting the misses before the next hit (copied from Lantana's ghost toy); it is not part of the
theory's interface, and the trace statements are proved from it through the bridge
`always_eventually_iff_infOften`.
-/

@[expose] public section

namespace Lantana.Fairness

open scoped Lantana.TrProp

/-! ## 1. Layer 0: the attempt–grant pair over trace properties (`AttemptGrant`) -/

/-! ### The engine: miss–hit fairness over two position predicates (`MissHit`)

Two position predicates, the hits and the misses.  Miss–hit fairness says that infinitely many
misses force infinitely many hits.  With hits and misses exclusive, it is the existence of a
counter that is zero at a hit, goes down by one at a miss and is unchanged otherwise
(`MissHit.fair_iff_counter`).  Arithmetic on `Nat`; the theory's statements are trace properties
and come after.  Copied from Lantana's ghost toy (`LantanaTest/GhostToy/Count.lean`,
`MissHit.lean`), as in the ported theory. -/

namespace MissHit

/-! #### Least witnesses

The least witnesses `Nat.exists_min`, `Nat.minWitness`, `Nat.minWitness_spec` and
`Nat.minWitness_min` are in `Lantana.Prelude.Nat`. -/

/-! #### Miss–hit fairness and counters -/

/-- `P` holds at infinitely many positions. -/
def InfOften (P : Nat → Prop) : Prop := ∀ n, ∃ m ≥ n, P m

/-- Miss–hit fairness: infinitely many misses force infinitely many hits (`□◇ miss → □◇ hit`). -/
def Fair (hit miss : Nat → Prop) : Prop := InfOften miss → InfOften hit

/-- The miss–hit counter: zero at a hit, down by one at a miss, unchanged otherwise. -/
def IsCounter (hit miss : Nat → Prop) (δ : Nat → Nat) : Prop :=
  (∀ n, hit n → δ n = 0) ∧ (∀ n, miss n → δ n = δ (n + 1) + 1) ∧
  (∀ n, ¬ hit n → ¬ miss n → δ n = δ (n + 1))

/-- A predicate that does not hold infinitely often fails from some position on. -/
theorem eventually_not_of_not_infOften {P : Nat → Prop} (h : ¬ InfOften P) :
    ∃ N, ∀ m ≥ N, ¬ P m :=
  Classical.byContradiction fun hc =>
    h fun n => Classical.byContradiction fun hn => hc ⟨n, fun m hm hP => hn ⟨m, hm, hP⟩⟩

/-- A predicate that does not fail from some position on holds infinitely often. -/
theorem infOften_of_not_eventually {P : Nat → Prop} (h : ¬ ∃ N, ∀ m ≥ N, ¬ P m) :
    InfOften P :=
  fun n => Classical.byContradiction fun hn => h ⟨n, fun m hm hP => hn ⟨m, hm, hP⟩⟩

/-! #### The oracle budget (`Count`) -/

section Defs

variable (hit miss : Nat → Prop)

open Classical in
/-- The first hit at or after `n`, if any. -/
noncomputable def firstHit? (n : Nat) : Option Nat :=
  if h : ∃ H, n ≤ H ∧ hit H then some (Nat.minWitness h) else none

open Classical in
/-- The number of misses in `[n, n + k)`. -/
noncomputable def countMiss (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (if miss n then 1 else 0) + countMiss (n + 1) k

open Classical in
/-- The least time after which there are no misses, if there is one; `0` otherwise. -/
noncomputable def missBound : Nat :=
  if h : ∃ N, ∀ m ≥ N, ¬ miss m then Nat.minWitness h else 0

/-- The end of the counting window from `n`: the first hit at or after `n` if there is one,
else `max n (missBound miss)`. -/
noncomputable def horizon (n : Nat) : Nat :=
  match firstHit? hit n with
  | some H => H
  | none => max n (missBound miss)

/-- The oracle budget at `n`: the number of misses in `[n, horizon hit miss n)`. -/
noncomputable def budget (n : Nat) : Nat := countMiss miss n (horizon hit miss n - n)

end Defs

section Budget

variable {hit miss : Nat → Prop}

/-- `firstHit? hit n` is `H` exactly when `H` is the first hit at or after `n`. -/
theorem firstHit?_eq_some_iff {n H : Nat} :
    firstHit? hit n = some H ↔ n ≤ H ∧ hit H ∧ ∀ m, n ≤ m → m < H → ¬ hit m := by
  unfold firstHit?
  split
  · rename_i h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨(Nat.minWitness_spec h).1, (Nat.minWitness_spec h).2,
        fun _ hm hmH hhit => Nat.minWitness_min h hmH ⟨hm, hhit⟩⟩
    · rintro ⟨hnH, hH, hmin⟩
      apply Nat.le_antisymm
      · exact Nat.le_of_not_lt fun hlt => Nat.minWitness_min h hlt ⟨hnH, hH⟩
      · exact Nat.le_of_not_lt fun hlt =>
          hmin _ (Nat.minWitness_spec h).1 hlt (Nat.minWitness_spec h).2
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨hnH, hH, -⟩
    exact h ⟨H, hnH, hH⟩

/-- `firstHit? hit n` is `none` exactly when there is no hit at or after `n`. -/
theorem firstHit?_eq_none_iff {n : Nat} :
    firstHit? hit n = none ↔ ∀ m ≥ n, ¬ hit m := by
  unfold firstHit?
  split
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    obtain ⟨H, hnH, hH⟩ := h
    exact fun hno => hno H hnH hH
  · rename_i h
    simp only [true_iff]
    exact fun m hm hhit => h ⟨m, hm, hhit⟩

/-- At a hit, the first hit is the position itself. -/
theorem firstHit?_of_hit {n : Nat} (h : hit n) : firstHit? hit n = some n :=
  firstHit?_eq_some_iff.2 ⟨Nat.le_refl n, h, fun _ hm hmn => absurd hm (Nat.not_le.2 hmn)⟩

/-- Where there is no hit, the first hit comes strictly later. -/
theorem lt_of_firstHit?_eq_some {n H : Nat} (hn : ¬ hit n) (h : firstHit? hit n = some H) :
    n < H := by
  obtain ⟨hnH, hH, -⟩ := firstHit?_eq_some_iff.1 h
  exact Nat.lt_of_le_of_ne hnH fun e => hn (e ▸ hH)

/-- Past a position that is not a hit, the first hit is the same. -/
theorem firstHit?_succ_of_some {n H : Nat} (hn : ¬ hit n) (h : firstHit? hit n = some H) :
    firstHit? hit (n + 1) = some H := by
  obtain ⟨-, hH, hmin⟩ := firstHit?_eq_some_iff.1 h
  exact firstHit?_eq_some_iff.2 ⟨lt_of_firstHit?_eq_some hn h, hH,
    fun m hm hmH => hmin m (Nat.le_of_succ_le hm) hmH⟩

/-- With no hit at or after `n`, there is none at or after `n + 1` either. -/
theorem firstHit?_succ_of_none {n : Nat} (h : firstHit? hit n = none) :
    firstHit? hit (n + 1) = none :=
  firstHit?_eq_none_iff.2 fun m hm => firstHit?_eq_none_iff.1 h m (Nat.le_of_succ_le hm)

/-- An empty window has no misses. -/
@[simp] theorem countMiss_zero (n : Nat) : countMiss miss n 0 = 0 := rfl

/-- A window that starts at a miss counts it and the rest. -/
theorem countMiss_succ_of_miss {n : Nat} (h : miss n) (k : Nat) :
    countMiss miss n (k + 1) = countMiss miss (n + 1) k + 1 := by
  rw [countMiss, ite_eq_left h, Nat.add_comm]

/-- A window that starts at a position that is not a miss counts the rest only. -/
theorem countMiss_succ_of_not_miss {n : Nat} (h : ¬ miss n) (k : Nat) :
    countMiss miss n (k + 1) = countMiss miss (n + 1) k := by
  rw [countMiss, ite_eq_right h, Nat.zero_add]

/-- When the misses stop, there is none at or after `missBound miss`. -/
theorem missBound_spec (h : ∃ N, ∀ m ≥ N, ¬ miss m) {m : Nat} (hm : missBound miss ≤ m) :
    ¬ miss m := by
  unfold missBound at hm
  rw [dite_eq_left h] at hm
  exact Nat.minWitness_spec h m hm

/-- When the misses stop, every miss is before `missBound miss`. -/
theorem lt_missBound_of_miss (h : ∃ N, ∀ m ≥ N, ¬ miss m) {n : Nat} (hn : miss n) :
    n < missBound miss :=
  Nat.lt_of_not_le fun hle => missBound_spec h hle hn

/-- At a hit, the window ends where it starts. -/
theorem horizon_of_hit {n : Nat} (h : hit n) : horizon hit miss n = n := by
  simp only [horizon, firstHit?_of_hit h]

/-- Past a position that is not a hit and before the horizon, the horizon is the same. -/
theorem horizon_succ_of_lt {n : Nat} (hn : ¬ hit n) (hlt : n < horizon hit miss n) :
    horizon hit miss (n + 1) = horizon hit miss n := by
  rcases hfh : firstHit? hit n with _ | H
  · simp only [horizon, hfh, firstHit?_succ_of_none hfh] at hlt ⊢
    omega
  · simp only [horizon, hfh, firstHit?_succ_of_some hn hfh]

/-- Past a position that is not a hit and at or past the horizon, the window from the next position
is empty. -/
theorem horizon_succ_of_le {n : Nat} (hn : ¬ hit n) (hle : horizon hit miss n ≤ n) :
    horizon hit miss (n + 1) = n + 1 := by
  rcases hfh : firstHit? hit n with _ | H
  · simp only [horizon, hfh, firstHit?_succ_of_none hfh] at hle ⊢
    omega
  · simp only [horizon, hfh] at hle
    exact absurd hle (Nat.not_le.2 (lt_of_firstHit?_eq_some hn hfh))

/-- With hits and misses exclusive and the misses stopping where the hits stop, a miss is before the
horizon. -/
theorem lt_horizon_of_miss (hex : ∀ n, ¬ (hit n ∧ miss n))
    (hfin : ∀ n, (∀ m ≥ n, ¬ hit m) → ∃ N, ∀ m ≥ N, ¬ miss m)
    {n : Nat} (hm : miss n) : n < horizon hit miss n := by
  have hn : ¬ hit n := fun hh => hex n ⟨hh, hm⟩
  rcases hfh : firstHit? hit n with _ | H
  · simp only [horizon, hfh]
    have hN := lt_missBound_of_miss (hfin n (firstHit?_eq_none_iff.1 hfh)) hm
    omega
  · simp only [horizon, hfh]
    exact lt_of_firstHit?_eq_some hn hfh

/-- The budget is zero at a hit. -/
theorem budget_hit {n : Nat} (h : hit n) : budget hit miss n = 0 := by
  simp only [budget, horizon_of_hit h, Nat.sub_self, countMiss_zero]

/-- The budget's window from `n` and from `n + 1` end at the same horizon when `n` is not a hit
and the window is nonempty. -/
theorem budget_succ_of_lt {n : Nat} (hn : ¬ hit n) (hlt : n < horizon hit miss n) :
    budget hit miss n = countMiss miss n (horizon hit miss (n + 1) - (n + 1) + 1) := by
  rw [budget, horizon_succ_of_lt hn hlt]
  congr 1
  omega

/-- Under the same hypotheses, the budget drops by one at a miss. -/
theorem budget_miss (hex : ∀ n, ¬ (hit n ∧ miss n))
    (hfin : ∀ n, (∀ m ≥ n, ¬ hit m) → ∃ N, ∀ m ≥ N, ¬ miss m)
    {n : Nat} (hm : miss n) : budget hit miss n = budget hit miss (n + 1) + 1 := by
  have hn : ¬ hit n := fun hh => hex n ⟨hh, hm⟩
  rw [budget_succ_of_lt hn (lt_horizon_of_miss hex hfin hm), countMiss_succ_of_miss hm]
  rfl

/-- The budget is unchanged at a position that is neither a hit nor a miss. -/
theorem budget_step {n : Nat} (hn : ¬ hit n) (hm : ¬ miss n) :
    budget hit miss n = budget hit miss (n + 1) := by
  rcases Nat.lt_or_ge n (horizon hit miss n) with hlt | hle
  · rw [budget_succ_of_lt hn hlt, countMiss_succ_of_not_miss hm]
    rfl
  · rw [budget, budget, horizon_succ_of_le hn hle, Nat.sub_self,
      Nat.sub_eq_zero_of_le hle, countMiss_zero, countMiss_zero]

/-! #### Miss–hit fairness is the existence of a counter: the two main theorems -/

/-- Under miss–hit fairness, with hits and misses exclusive, `budget hit miss` is a miss–hit
counter. -/
theorem counter_spec (hex : ∀ n, ¬ (hit n ∧ miss n)) (hmh : Fair hit miss) :
    IsCounter hit miss (budget hit miss) := by
  refine ⟨fun n h => budget_hit h, fun n hm => budget_miss hex ?_ hm,
    fun n hh hm => budget_step hh hm⟩
  intro k hno
  apply Classical.byContradiction
  intro hfin
  obtain ⟨m, hm, hh⟩ := hmh (infOften_of_not_eventually hfin) k
  exact hno m hm hh

/-- A miss–hit counter gives miss–hit fairness. -/
theorem fair_of_counter {δ : Nat → Nat} (hδ : IsCounter hit miss δ) : Fair hit miss := by
  obtain ⟨-, hdec, hconst⟩ := hδ
  intro hinf
  apply Classical.byContradiction
  intro hno
  obtain ⟨N, hN⟩ := eventually_not_of_not_infOften hno
  have hmono : ∀ a k, N ≤ a → δ (a + k) ≤ δ a := by
    intro a k ha
    induction k with
    | zero => exact Nat.le_refl _
    | succ k ih =>
      have hhit : ¬ hit (a + k) := hN _ (Nat.le_trans ha (Nat.le_add_right a k))
      rw [← Nat.add_assoc]
      by_cases hm : miss (a + k)
      · have := hdec _ hm
        omega
      · have := hconst _ hhit hm
        omega
  have key : ∀ j, ∃ k, δ (N + k) + j ≤ δ N := by
    intro j
    induction j with
    | zero => exact ⟨0, Nat.le_refl _⟩
    | succ j ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨m, hm, hmiss⟩ := hinf (N + k)
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
      have h₁ := hdec _ hmiss
      have h₂ := hmono (N + k) d (Nat.le_add_right N k)
      have e : N + (k + d + 1) = N + k + d + 1 := by omega
      refine ⟨k + d + 1, ?_⟩
      rw [e]
      omega
  obtain ⟨k, hk⟩ := key (δ N + 1)
  omega

/-- Miss–hit fairness, with hits and misses exclusive, is the existence of a miss–hit
counter. -/
theorem fair_iff_counter (hex : ∀ n, ¬ (hit n ∧ miss n)) :
    Fair hit miss ↔ ∃ δ, IsCounter hit miss δ :=
  ⟨fun hmh => ⟨budget hit miss, counter_spec hex hmh⟩, fun ⟨_, hδ⟩ => fair_of_counter hδ⟩

end Budget

/-! #### Holding infinitely often is monotone -/

/-- Holding infinitely often is monotone in the predicate. -/
theorem infOften_mono {P Q : Nat → Prop} (h : ∀ n, P n → Q n) (hP : InfOften P) : InfOften Q :=
  fun n => let ⟨m, hm, hPm⟩ := hP n; ⟨m, hm, h m hPm⟩

end MissHit

/-! ### The bridge: a trace property along a run is a position predicate -/

/-- The trace property `P` read along the run of `τ`, as a predicate on positions. -/
def _root_.Lantana.TrProp.along {C : Type} (P : TrProp C) (τ : Trace C) (n : Nat) : Prop := P { τ with pos := n }

/-- `□ₜ ◇ₜ P` at `τ` is `P` infinitely often along its run (positions before `τ.pos` do not
matter). -/
theorem always_eventually_iff_infOften {C : Type} {P : TrProp C} {τ : Trace C} :
    (□ₜ ◇ₜ P) τ ↔ MissHit.InfOften (TrProp.along P τ) := by
  rw [TrProp.always_eventually_iff]
  constructor
  · intro h n
    obtain ⟨m, hm, hP⟩ := h (max n τ.pos) (Nat.le_max_right _ _)
    exact ⟨m, Nat.le_trans (Nat.le_max_left _ _) hm, hP⟩
  · intro h n _
    exact h n

/-- `□ₜ ◇ₜ P` at `τ` is `P` infinitely often along its run counted from the current position:
the positions are shifted by `τ.pos`. -/
theorem always_eventually_iff_infOften_from {C : Type} {P : TrProp C} {τ : Trace C} :
    (□ₜ ◇ₜ P) τ ↔ MissHit.InfOften fun n => TrProp.along P τ (τ.pos + n) := by
  rw [TrProp.always_eventually_iff]
  constructor
  · intro h n
    obtain ⟨m, hm, hP⟩ := h (τ.pos + n) (Nat.le_add_right _ _)
    refine ⟨m - τ.pos, by omega, ?_⟩
    change TrProp.along P τ (τ.pos + (m - τ.pos))
    rwa [Nat.add_sub_cancel' (Nat.le_trans (Nat.le_add_right _ _) hm)]
  · intro h n hn
    obtain ⟨m, hm, hP⟩ := h (n - τ.pos)
    exact ⟨τ.pos + m, by omega, hP⟩

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
attempt. -/
theorem fair_mono {attempt' : TrProp C} (hatt : attempt' ⊆ attempt)
    (hgr : (attempt ∧ₜ grant) ⊆ attempt') : Fair attempt grant ⊆ Fair attempt' grant :=
  fun τ hag hmiss =>
    TrProp.always_eventually_mono (fun τ' hh => ⟨hgr τ' hh, hh.2⟩) τ
      (hag (TrProp.always_eventually_mono (fun τ' hm => ⟨hatt τ' hm.1, hm.2⟩) τ hmiss))

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
