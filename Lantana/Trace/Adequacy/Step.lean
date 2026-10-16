/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.BaseLogic.Model
public import Lantana.Trace.FairScheduling

/-! # Adequacy: facts about one step

Rocq `lantana/trace/adequacy_step.v`, the pure part: after the progress round of the scheduled
thread, witnesses that strictly decrease and keep both witness invariants exist
(`mprog_exists_step`). The witness of an assigned obligation with fuel `a` and owner `o` is the
fair-scheduler measure `fairMeasure (γ (τ.pos + 1)) o a` of the next position: the fuel of the
scheduled thread's obligations dropped, the fairness counter of every other active owner dropped
(D18: the counters are an explicit sequence `γ`, so no choice is needed for them).

The ghost-state part of the Rocq file (`get_obls_thread_active`, from the model interpretation
and the `Th.done` tokens of finished threads) comes with the adequacy proof (M6).
-/

@[expose] public section

namespace Lantana

open Lantana.Model Iris.Std LawfulPartialMap

variable {Expr : Type} {State : Type} {Val : Type} [Λ : Language Expr State Val]

/-- Every assigned obligation is owned by a thread that is active at the current position
(Rocq `obls_thread_active`). -/
@[lantana_alias obls_thread_active]
def oblsThreadActive (Ω : Obls) (τ : Trace Expr State) : Prop :=
  ∀ k a i, get? Ω k = some (.assigned a i) → τ.now.active i

/-- The fair-scheduler measures of the next position are strictly below those of the current
one for the scheduled thread's obligations (whose fuel dropped) and for the other active
owners (whose counter dropped). -/
theorem fairMeasure_next_lt {τ : Trace Expr State} {γ : Nat → ThreadId → Nat}
    (hcnt : BehFscnt τ γ) {i o o' : ThreadId} {a a' : Fuel} (hi : i = τ.thread)
    (hact : τ.now.active o) (h : (o = i ∧ a' < a) ∨ (o ≠ i ∧ a' = a ∧ o' = o)) :
    fairMeasure (γ (τ.pos + 1)) o' a' < fairMeasure (γ τ.pos) o a := by
  rcases h with ⟨-, hlt⟩ | ⟨hne, ha, ho⟩
  · exact fairMeasure_lt_mono hlt
  · rw [ha, ho]
    have hdec : γ (τ.pos + 1) o < γ τ.pos o := by
      rcases hcnt τ.pos (Nat.le_refl _) o with hna | ⟨-, hturn | hlt⟩
      · exact absurd ⟨hact, hna⟩ (TraceState.not_active_and_inactive o _)
      · exact absurd (hturn.symm.trans hi.symm) hne
      · exact hlt
    unfold fairMeasure
    exact Ordinals.Ordinal.nadd_lt_nadd_left (Ordinals.Ordinal.ofNat_lt_ofNat_iff.mpr hdec) _

/-- After the progress round of the scheduled thread `i` (Rocq `mprog_exists_step`): the
witnesses `fairMeasure (γ (τ.pos + 1))` of the new obligations strictly decrease the assigned
witnesses and keep the witness invariant and its lower bound. -/
@[lantana_alias mprog_exists_step]
theorem mprog_exists_step {τ : Trace Expr State} {γ : Nat → ThreadId → Nat} {i : ThreadId}
    {Ω₁ Ω₂ : Obls} {W₁ : Witnesses} (hi : i = τ.thread) (hact : oblsThreadActive Ω₁ τ)
    (hI : owitInvFair Ω₁ W₁) (hLb : owitInvLb (fairMeasure (γ τ.pos)) Ω₁ W₁)
    (hcnt : BehFscnt τ γ) (hprog : Obls.condProgress (Obl.condOwner i) Ω₁ Ω₂) :
    ∃ W₂ : Witnesses, Witnesses.condProgress Witness.condAssigned W₁ W₂ ∧ owitInvFair Ω₂ W₂ ∧
      owitInvLb (fairMeasure (γ (τ.pos + 1))) Ω₂ W₂ := by
  obtain ⟨W₂, hW₂⟩ := mapForall2_choice (B := Witness)
    (P := fun _ g₂ w₂ => w₂ = witOf (fairMeasure (γ (τ.pos + 1))) g₂) Ω₂
    (fun _ g₂ _ => ⟨_, rfl⟩)
  -- the new obligation of every old one
  have hnew : ∀ k g₁, get? Ω₁ k = some g₁ → ∃ g₂, get? Ω₂ k = some g₂ ∧ Obl.keep g₁ g₂ ∧
      ((Obl.condOwner i k g₁ ∧ Obl.progress g₁ g₂) ∨ (¬Obl.condOwner i k g₁ ∧ g₁ = g₂)) := by
    intro k g₁ e₁
    obtain ⟨g₂, e₂, hr⟩ := mapForall2.lookup_left hprog.1 e₁
    have hkeep : Obl.keep g₁ g₂ := mapForall2.lookup hprog.2 e₁ e₂
    refine ⟨g₂, e₂, hkeep, ?_⟩
    rcases hr with ⟨hc, hs | hs⟩ | hn
    · exact .inl ⟨hc, hs⟩
    · exfalso
      cases g₁ <;> cases g₂ <;> first | exact hs.elim | exact hkeep.elim
    · exact .inr hn
  refine ⟨W₂, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- the assigned witnesses decrease strictly, the discharged ones stay
    refine mapForall2_intro fun k => ?_
    rcases e₁ : get? W₁ k with _ | w₁
    · left
      refine ⟨rfl, ?_⟩
      rcases e₂ : get? W₂ k with _ | w₂
      · rfl
      · obtain ⟨g₂, eg₂, -⟩ := mapForall2.lookup_right hW₂ e₂
        obtain ⟨g₁, eg₁, -⟩ := mapForall2.lookup_right hprog.2 eg₂
        obtain ⟨w₁', ew₁', -⟩ := mapForall2.lookup_left hI eg₁
        rw [e₁] at ew₁'
        cases ew₁'
    · right
      obtain ⟨g₁, eg₁, hr₁⟩ := mapForall2.lookup_right hI e₁
      obtain ⟨g₂, eg₂, hkeep, hstep⟩ := hnew k g₁ eg₁
      obtain ⟨w₂, ew₂, rfl⟩ := mapForall2.lookup_left hW₂ eg₂
      refine ⟨w₁, _, rfl, ew₂, ?_⟩
      cases g₁ with
      | discharged =>
        cases w₁ with
        | assigned b => simp [owitRel] at hr₁
        | discharged =>
          cases g₂ with
          | assigned a' o' => simp [Obl.keep] at hkeep
          | discharged => exact .inr ⟨fun h => h, rfl⟩
      | assigned a o =>
        cases w₁ with
        | discharged => simp [owitRel] at hr₁
        | assigned b =>
          cases g₂ with
          | discharged => simp [Obl.keep] at hkeep
          | assigned a' o' =>
            left
            refine ⟨trivial, .inl ?_⟩
            change fairMeasure (γ (τ.pos + 1)) o' a' < b
            have hlb : fairMeasure (γ τ.pos) o a ≤ b := mapForall2.lookup hLb eg₁ e₁
            refine Ordinals.Ordinal.lt_of_lt_of_le ?_ hlb
            refine fairMeasure_next_lt hcnt hi (hact k a o eg₁) ?_
            rcases hstep with ⟨ho, hlt⟩ | ⟨hno, heq⟩
            · exact .inl ⟨ho, hlt⟩
            · cases heq
              exact .inr ⟨fun h => hno h, rfl, rfl⟩
  · -- statuses are kept
    refine mapForall2_intro fun k => ?_
    rcases e₁ : get? W₁ k with _ | w₁
    · left
      refine ⟨rfl, ?_⟩
      rcases e₂ : get? W₂ k with _ | w₂
      · rfl
      · obtain ⟨g₂, eg₂, -⟩ := mapForall2.lookup_right hW₂ e₂
        obtain ⟨g₁, eg₁, -⟩ := mapForall2.lookup_right hprog.2 eg₂
        obtain ⟨w₁', ew₁', -⟩ := mapForall2.lookup_left hI eg₁
        rw [e₁] at ew₁'
        cases ew₁'
    · right
      obtain ⟨g₁, eg₁, hr₁⟩ := mapForall2.lookup_right hI e₁
      obtain ⟨g₂, eg₂, hkeep, -⟩ := hnew k g₁ eg₁
      obtain ⟨w₂, ew₂, rfl⟩ := mapForall2.lookup_left hW₂ eg₂
      refine ⟨w₁, _, rfl, ew₂, ?_⟩
      cases g₁ <;> cases g₂ <;> cases w₁ <;> simp_all [owitRel, Obl.keep, Witness.keep, witOf]
  · -- the witness invariant
    exact hW₂.impl fun _ g₂ w₂ h => by
      subst h
      cases g₂ with
      | assigned a o => exact fairMeasure_le_ub _ o a
      | discharged => trivial
  · -- the lower bound
    exact hW₂.impl fun _ g₂ w₂ h => by
      subst h
      cases g₂ with
      | assigned a o => exact Ordinals.Ordinal.le_rfl
      | discharged => trivial

/-! ## The drop of the fair-scheduler measures across a step -/

/-- The measures of all obligations drop from `Ω` to `Ω'` (Rocq `obls_drop`). -/
@[lantana_alias obls_drop]
def oblsDrop (m m' : ThreadId → Fuel → Fuel) (Ω Ω' : Obls) : Prop :=
  ∀ k fu o fu' o', get? Ω k = some (.assigned fu o) → get? Ω' k = some (.assigned fu' o') →
    m' o' fu' < m o fu

/-- A step of the scheduled thread `i` drops every measure (Rocq `obls_drop_step`): through the
pre-step model update `Ω ≤ Ω₀`, the progress round `Ω₀ → Ω₂` of `i` and the post-step update
`Ω₂ ≤ Ω'`, the obligations of `i` lose fuel and the other active owners lose a counter. -/
@[lantana_alias obls_drop_step]
theorem oblsDrop_step {τ : Trace Expr State} {γ : Nat → ThreadId → Nat} {i : ThreadId}
    (hi : i = τ.thread) (hcnt : BehFscnt τ γ) {Ω Ω₀ Ω₂ Ω' : Obls} (h₀ : Obls.le Ω Ω₀)
    (hprog : Obls.condProgress (Obl.condOwner i) Ω₀ Ω₂) (h₂ : Obls.le Ω₂ Ω')
    (hact : oblsThreadActive Ω₂ τ) :
    oblsDrop (fairMeasure (γ τ.pos)) (fairMeasure (γ (τ.pos + 1))) Ω Ω' := by
  intro k fu o fu' o' hk hk'
  obtain ⟨g₀, hk₀⟩ : ∃ g₀, get? Ω₀ k = some g₀ :=
    Option.isSome_iff_exists.mp (h₀.1 k (by rw [hk]; rfl))
  have hle₀ : Obl.le (.assigned fu o) g₀ := h₀.2 k _ _ hk hk₀
  obtain ⟨g₂, hk₂, hr⟩ := mapForall2.lookup_left hprog.1 hk₀
  have hkeep : Obl.keep g₀ g₂ := mapForall2.lookup hprog.2 hk₀ hk₂
  have hle₂ : Obl.le g₂ (.assigned fu' o') := h₂.2 k _ _ hk₂ hk'
  cases g₂ with
  | discharged => exact hle₂.elim
  | assigned fu₂ o₂ =>
    cases g₀ with
    | discharged => exact hkeep.elim
    | assigned fu₀ o₀ =>
      have hfu₀ : fu₀ ≤ fu := by
        rcases hle₀ with ⟨h, -⟩ | h
        · exact h
        · exact Ordinals.Ordinal.le_of_lt h
      have hfu' : fu' ≤ fu₂ := by
        rcases hle₂ with ⟨h, -⟩ | h
        · exact h
        · exact Ordinals.Ordinal.le_of_lt h
      rcases hr with ⟨-, hs | hs⟩ | ⟨hno, heq⟩
      · exact fairMeasure_lt_mono
          (Ordinals.Ordinal.lt_of_le_of_lt hfu' (Ordinals.Ordinal.lt_of_lt_of_le hs hfu₀))
      · exact hs.elim
      · injection heq with hf ho
        subst hf
        subst ho
        rcases Ordinals.Ordinal.lt_or_eq_of_le (Ordinals.Ordinal.le_trans hfu' hfu₀)
          with hlt | heq'
        · exact fairMeasure_lt_mono hlt
        · have hfu₀' : fu₀ = fu := Ordinals.Ordinal.le_antisymm hfu₀ (heq' ▸ hfu')
          have ho₀ : o = o₀ := by
            rcases hle₀ with ⟨-, h⟩ | h
            · exact h
            · exact absurd (hfu₀' ▸ h) (Ordinals.Ordinal.lt_irrefl _)
          have ho' : o₀ = o' := by
            rcases hle₂ with ⟨-, h⟩ | h
            · exact h
            · exact absurd ((heq'.trans hfu₀'.symm) ▸ h) (Ordinals.Ordinal.lt_irrefl _)
          subst ho₀
          subst ho'
          exact fairMeasure_next_lt hcnt hi (hact k fu₀ o hk₂) (.inr ⟨fun h => hno h, heq', rfl⟩)

/-- A stutter of a finished thread drops every measure through the fairness counters
(Rocq `obls_drop_na`). -/
@[lantana_alias obls_drop_na]
theorem oblsDrop_na {τ : Trace Expr State} {γ : Nat → ThreadId → Nat} (hcnt : BehFscnt τ γ)
    (hna : τ.now.inactive τ.thread) {Ω : Obls} (hact : oblsThreadActive Ω τ) :
    oblsDrop (fairMeasure (γ τ.pos)) (fairMeasure (γ (τ.pos + 1))) Ω Ω := by
  intro k fu o fu' o' hk hk'
  rw [hk] at hk'
  cases hk'
  refine fairMeasure_next_lt hcnt rfl (hact k fu o hk) (.inr ⟨?_, rfl, rfl⟩)
  intro ho
  exact TraceState.not_active_and_inactive o _ ⟨hact k fu o hk, by rw [ho]; exact hna⟩

end Lantana
