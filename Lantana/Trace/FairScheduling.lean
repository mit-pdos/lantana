/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TracePropRules

/-! # Fair scheduling

Every active thread is eventually scheduled (Rocq `fair_scheduling.v`). The fairness counter
that the adequacy proof threads (Rocq `beh_fscnt`, a coinductive predicate on the counters of
one position, obtained by choice) is an explicit sequence of counters along the trace (D18):
`BehFscnt τ γ` says that while a thread is active and not scheduled its counter strictly
decreases. A fair trace has one (`fairScheduling_behFscnt`, classical: the distance to the next
turn), and the counters of consecutive positions are related by `fscntNextRel`.
-/

@[expose] public section

namespace Lantana


variable {Expr : Type} {State : Type} {Val : Type} [Λ : Language Expr State Val]

open scoped TrProp

/-- Fair scheduling: at every position, every thread is inactive or active and eventually
scheduled. -/
@[lantana_alias fair_scheduling]
def fairScheduling : TrProp Expr State :=
  □ₜ (∀ₜ i : ThreadId, TrProp.now (TraceState.inactive i) ∨ₜ
    (TrProp.now (TraceState.active i) ∧ₜ ◇ₜ TrProp.now (TraceState.turn i)))

@[lantana_alias fair_scheduling_next]
theorem fairScheduling_next {τ : Trace Expr State} (h : fairScheduling τ) :
    fairScheduling τ.next :=
  fun m hm => h m (Nat.le_of_succ_le hm)

/-! ## The fairness counter (D18) -/

/-- A minimal witness of a satisfiable predicate on `Nat` (classical). -/
theorem Nat.exists_min {p : Nat → Prop} : ∀ n, p n → ∃ m, p m ∧ ∀ k, k < m → ¬ p k
  | n, hn => by
    classical
    by_cases h : ∃ k, k < n ∧ p k
    · obtain ⟨k, hk, hpk⟩ := h
      exact Nat.exists_min k hpk
    · exact ⟨n, hn, fun k hk hpk => h ⟨k, hk, hpk⟩⟩
termination_by n => n

/-- The least witness of a satisfiable predicate on `Nat`. -/
noncomputable def Nat.minWitness {p : Nat → Prop} (h : ∃ n, p n) : Nat :=
  Classical.choose (Nat.exists_min h.choose h.choose_spec)

theorem Nat.minWitness_spec {p : Nat → Prop} (h : ∃ n, p n) : p (Nat.minWitness h) :=
  (Classical.choose_spec (Nat.exists_min h.choose h.choose_spec)).1

theorem Nat.minWitness_min {p : Nat → Prop} (h : ∃ n, p n) {k : Nat}
    (hk : k < Nat.minWitness h) : ¬ p k :=
  (Classical.choose_spec (Nat.exists_min h.choose h.choose_spec)).2 k hk

/-- Fairness counters along a trace (Rocq `beh_fscnt`): from the current position on, every
thread is inactive, or active and either scheduled or with a strictly decreasing counter. -/
@[lantana_alias beh_fscnt]
def BehFscnt (τ : Trace Expr State) (γ : Nat → ThreadId → Nat) : Prop :=
  ∀ m, τ.pos ≤ m → ∀ i, (τ.seq m).inactive i ∨
    ((τ.seq m).active i ∧ ((τ.seq m).turn i ∨ γ (m + 1) i < γ m i))

theorem BehFscnt.next {τ : Trace Expr State} {γ : Nat → ThreadId → Nat} (h : BehFscnt τ γ) :
    BehFscnt τ.next γ :=
  fun m hm => h m (Nat.le_of_succ_le hm)

/-- The counters of a thread at a position and at the next one (Rocq `fscnt_next_rel_th`):
unconstrained if the thread is scheduled or inactive, otherwise strictly decreasing. -/
@[lantana_alias fscnt_next_rel_th]
def fscntNextRelTh (τ : Trace Expr State) (i : ThreadId) (c₁ c₂ : Nat) : Prop :=
  τ.now.turn i ∨ τ.now.inactive i ∨ c₂ < c₁

@[lantana_alias fscnt_next_rel]
def fscntNextRel (τ : Trace Expr State) (γ₁ γ₂ : ThreadId → Nat) : Prop :=
  ∀ i, fscntNextRelTh τ i (γ₁ i) (γ₂ i)

/-- The counters of the next position are related to the current ones
(Rocq `exists_fscnt_next`, without choice: the sequence is given). -/
@[lantana_alias exists_fscnt_next]
theorem BehFscnt.nextRel {τ : Trace Expr State} {γ : Nat → ThreadId → Nat} (h : BehFscnt τ γ) :
    fscntNextRel τ (γ τ.pos) (γ (τ.pos + 1)) := by
  intro i
  rcases h τ.pos (Nat.le_refl _) i with hna | ⟨-, hturn | hlt⟩
  · exact .inr (.inl hna)
  · exact .inl hturn
  · exact .inr (.inr hlt)

open Classical in
/-- The distance from position `m` to the next turn of the thread `i` if it is active there,
`0` otherwise, given that active threads are eventually scheduled. -/
noncomputable def turnDist (τ : Trace Expr State)
    (hex : ∀ m, τ.pos ≤ m → ∀ i, (τ.seq m).active i → ∃ s, (τ.seq (m + s)).turn i)
    (m : Nat) (i : ThreadId) : Nat :=
  if hmi : τ.pos ≤ m ∧ (τ.seq m).active i then Nat.minWitness (hex m hmi.1 i hmi.2) else 0

theorem turnDist_eq (τ : Trace Expr State)
    (hex : ∀ m, τ.pos ≤ m → ∀ i, (τ.seq m).active i → ∃ s, (τ.seq (m + s)).turn i)
    {m : Nat} {i : ThreadId} (hm : τ.pos ≤ m) (hact : (τ.seq m).active i) :
    turnDist τ hex m i = Nat.minWitness (hex m hm i hact) := by
  simp only [turnDist, hm, hact, and_self, dite_true]

theorem turnDist_eq_zero (τ : Trace Expr State)
    (hex : ∀ m, τ.pos ≤ m → ∀ i, (τ.seq m).active i → ∃ s, (τ.seq (m + s)).turn i)
    {m : Nat} {i : ThreadId} (hna : (τ.seq m).inactive i) : turnDist τ hex m i = 0 := by
  have hn : ¬ (τ.pos ≤ m ∧ (τ.seq m).active i) := fun hmi =>
    TraceState.not_active_and_inactive i _ ⟨hmi.2, hna⟩
  simp only [turnDist, hn, dite_false]

/-- A fair trace has fairness counters: the distance of each active thread to its next turn
(Rocq `fair_scheduling_fscnt`; classical). -/
@[lantana_alias fair_scheduling_fscnt]
theorem fairScheduling_behFscnt {τ : Trace Expr State} (h : fairScheduling τ) :
    ∃ γ : Nat → ThreadId → Nat, BehFscnt τ γ := by
  classical
  have hex : ∀ m, τ.pos ≤ m → ∀ i, (τ.seq m).active i → ∃ s, (τ.seq (m + s)).turn i := by
    intro m hm i hact
    rcases h m hm i with hna | ⟨-, k, hmk, hturn, -⟩
    · exact absurd ⟨hact, hna⟩ (TraceState.not_active_and_inactive i _)
    · exact ⟨k - m, by rw [Nat.add_sub_cancel' hmk]; exact hturn⟩
  refine ⟨turnDist τ hex, ?_⟩
  intro m hm i
  rcases TraceState.active_or_inactive i (τ.seq m) with hact | hna
  · refine .inr ⟨hact, ?_⟩
    by_cases hturn : (τ.seq m).turn i
    · exact .inl hturn
    · right
      rw [turnDist_eq τ hex hm hact]
      have hs₀ := Nat.minWitness_spec (hex m hm i hact)
      have hpos : 0 < Nat.minWitness (hex m hm i hact) := by
        rcases Nat.eq_zero_or_pos (Nat.minWitness (hex m hm i hact)) with h0 | h0
        · rw [h0] at hs₀
          exact absurd hs₀ hturn
        · exact h0
      rcases TraceState.active_or_inactive i (τ.seq (m + 1)) with hact' | hna'
      · rw [turnDist_eq τ hex (Nat.le_succ_of_le hm) hact']
        have hle : Nat.minWitness (hex (m + 1) (Nat.le_succ_of_le hm) i hact') ≤
            Nat.minWitness (hex m hm i hact) - 1 := by
          apply Nat.le_of_not_lt
          intro hlt
          apply Nat.minWitness_min _ hlt
          have heq : m + 1 + (Nat.minWitness (hex m hm i hact) - 1) =
              m + Nat.minWitness (hex m hm i hact) := by omega
          rw [heq]
          exact hs₀
        omega
      · rw [turnDist_eq_zero τ hex hna']
        exact hpos
  · exact .inl hna

end Lantana
