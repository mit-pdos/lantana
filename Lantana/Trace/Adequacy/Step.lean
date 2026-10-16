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

end Lantana
