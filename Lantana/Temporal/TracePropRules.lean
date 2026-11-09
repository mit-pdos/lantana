/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Trace

/-! # Rules of trace entailment

The rules of `R ⊆ S` (Rocq `trace/trace_prop_rules.v`): introduction, elimination and
monotonicity for the connectives and the atoms, coinduction for `□ₜ` and induction for `Uₜ`, the
classical dualities, infinitely often and eventually always read at positions, the absolute
properties (`Absolute`, the same at every position of a run), and the fixpoint rules.
See `docs/temporal.md`.
-/

@[expose] public section

namespace Lantana.TrProp

variable {C : Type}
variable {R S X A B P Q R' S' A' : TrProp C}

open scoped Lantana.TrProp

#lantana_ignore tr_unfold "the definitions are a local simp set"

attribute [local simp] le HasSubset.Subset pure and or imp all ex always strongUntil eventually next
  atomic step not atPos

@[simp] theorem pos_set_pos (τ : Trace C) (m : Nat) :
    ({ τ with pos := m } : Trace C).pos = m := rfl
@[simp] theorem seq_set_pos (τ : Trace C) (m : Nat) :
    ({ τ with pos := m } : Trace C).seq = τ.seq := rfl
theorem next_eq_set_pos (τ : Trace C) :
    τ.next = { τ with pos := τ.pos + 1 } := rfl

/-! ## Entailment -/

@[lantana_alias tr_le_preorder, refl]
theorem le_refl (R : TrProp C) : R ⊆ R := fun _ h => h

theorem le_trans (h₁ : R ⊆ S) (h₂ : S ⊆ X) : R ⊆ X := fun τ h => h₂ τ (h₁ τ h)

instance : Trans (α := TrProp C) (· ⊆ ·) (· ⊆ ·) (· ⊆ ·) := ⟨le_trans⟩

/-! ## Pure -/

@[lantana_alias tr_pure_intro]
theorem pure_intro {φ : Prop} (h : φ) : R ⊆ ⌜φ⌝ₜ := fun _ _ => h

@[lantana_alias tr_pure_elim]
theorem pure_elim {φ : Prop} (h : φ → ∀ τ, S τ) : ⌜φ⌝ₜ ⊆ S := fun τ hφ => h hφ τ

@[lantana_alias tr_pure_mono]
theorem pure_mono {φ ψ : Prop} (h : φ → ψ) : (⌜φ⌝ₜ : TrProp C) ⊆ ⌜ψ⌝ₜ := fun _ => h

@[lantana_alias tr_true_intro]
theorem true_intro : R ⊆ ⌜True⌝ₜ := fun _ _ => trivial

@[lantana_alias tr_false_elim]
theorem false_elim : (⌜False⌝ₜ : TrProp C) ⊆ S := fun _ h => h.elim

@[lantana_alias tr_pure_elim_l]
theorem pure_elim_l {φ : Prop} (h : φ → R ⊆ S) : (⌜φ⌝ₜ ∧ₜ R) ⊆ S :=
  fun τ ⟨hφ, hR⟩ => h hφ τ hR

/-! ## Conjunction and disjunction -/

@[lantana_alias tr_and_intro]
theorem and_intro (h₁ : R ⊆ S) (h₂ : R ⊆ X) : R ⊆ (S ∧ₜ X) := fun τ h => ⟨h₁ τ h, h₂ τ h⟩

@[lantana_alias tr_and_elim_l]
theorem and_elim_l : (R ∧ₜ S) ⊆ R := fun _ h => h.1

@[lantana_alias tr_and_elim_r]
theorem and_elim_r : (R ∧ₜ S) ⊆ S := fun _ h => h.2

@[lantana_alias tr_and_mono]
theorem and_mono (h₁ : R ⊆ R') (h₂ : S ⊆ S') : (R ∧ₜ S) ⊆ (R' ∧ₜ S') :=
  fun τ h => ⟨h₁ τ h.1, h₂ τ h.2⟩

@[lantana_alias tr_and_comm]
theorem and_comm : (R ∧ₜ S) ⊆ (S ∧ₜ R) := fun _ h => ⟨h.2, h.1⟩

@[lantana_alias tr_and_assoc]
theorem and_assoc : ((R ∧ₜ S) ∧ₜ X) ⊆ (R ∧ₜ (S ∧ₜ X)) := fun _ h => ⟨h.1.1, h.1.2, h.2⟩

@[lantana_alias tr_and_assoc']
theorem and_assoc' : (R ∧ₜ (S ∧ₜ X)) ⊆ ((R ∧ₜ S) ∧ₜ X) := fun _ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩

@[lantana_alias tr_exist_elim_l]
theorem ex_elim_l {α : Sort _} {P : α → TrProp C} (h : ∀ a, (P a ∧ₜ R) ⊆ S) :
    ((∃ₜ a, P a) ∧ₜ R) ⊆ S := fun τ ⟨⟨a, ha⟩, hR⟩ => h a τ ⟨ha, hR⟩

@[lantana_alias tr_or_intro_l]
theorem or_intro_l : R ⊆ (R ∨ₜ S) := fun _ h => .inl h

@[lantana_alias tr_or_intro_r]
theorem or_intro_r : S ⊆ (R ∨ₜ S) := fun _ h => .inr h

@[lantana_alias tr_or_elim]
theorem or_elim (h₁ : R ⊆ X) (h₂ : S ⊆ X) : (R ∨ₜ S) ⊆ X :=
  fun τ h => h.elim (h₁ τ) (h₂ τ)

@[lantana_alias tr_or_mono]
theorem or_mono (h₁ : R ⊆ R') (h₂ : S ⊆ S') : (R ∨ₜ S) ⊆ (R' ∨ₜ S') :=
  fun τ h => h.imp (h₁ τ) (h₂ τ)

@[lantana_alias tr_and_or_distr]
theorem and_or_distr : (R ∧ₜ (S ∨ₜ X)) ⊆ ((R ∧ₜ S) ∨ₜ (R ∧ₜ X)) :=
  fun _ ⟨hR, h⟩ => h.imp (⟨hR, ·⟩) (⟨hR, ·⟩)

/-! ## Implication -/

@[lantana_alias tr_impl_intro]
theorem imp_intro (h : (R ∧ₜ A) ⊆ S) : R ⊆ (A →ₜ S) := fun τ hR hA => h τ ⟨hR, hA⟩

@[lantana_alias tr_impl_elim]
theorem imp_elim : ((A →ₜ S) ∧ₜ A) ⊆ S := fun _ h => h.1 h.2

@[lantana_alias tr_impl_mono]
theorem imp_mono (h₁ : A' ⊆ A) (h₂ : S ⊆ S') : (A →ₜ S) ⊆ (A' →ₜ S') :=
  fun τ h hA => h₂ τ (h (h₁ τ hA))

/-! ## Quantifiers -/

@[lantana_alias tr_forall_intro]
theorem all_intro {α : Sort _} {P : α → TrProp C} (h : ∀ a, R ⊆ P a) :
    R ⊆ (∀ₜ a, P a) := fun τ hR a => h a τ hR

@[lantana_alias tr_forall_elim]
theorem all_elim {α : Sort _} {P : α → TrProp C} (a : α) : (∀ₜ a, P a) ⊆ P a :=
  fun _ h => h a

@[lantana_alias tr_forall_mono]
theorem all_mono {α : Sort _} {P Q : α → TrProp C} (h : ∀ a, P a ⊆ Q a) :
    (∀ₜ a, P a) ⊆ (∀ₜ a, Q a) := fun τ hP a => h a τ (hP a)

@[lantana_alias tr_exist_intro]
theorem ex_intro {α : Sort _} {P : α → TrProp C} (a : α) : P a ⊆ (∃ₜ a, P a) :=
  fun _ h => ⟨a, h⟩

@[lantana_alias tr_exist_elim]
theorem ex_elim {α : Sort _} {P : α → TrProp C} (h : ∀ a, P a ⊆ S) :
    (∃ₜ a, P a) ⊆ S := fun τ ⟨a, ha⟩ => h a τ ha

@[lantana_alias tr_exist_mono]
theorem ex_mono {α : Sort _} {P Q : α → TrProp C} (h : ∀ a, P a ⊆ Q a) :
    (∃ₜ a, P a) ⊆ (∃ₜ a, Q a) := fun τ ⟨a, ha⟩ => ⟨a, h a τ ha⟩

/-! ## Atoms and negation -/

theorem step_mono {T T' : C → C → Prop} (h : ∀ c c', T c c' → T' c c') : step T ⊆ step T' :=
  fun _ hT => h _ _ hT

theorem atomic_mono {φ ψ : AProp C} (h : ∀ c, φ c → ψ c) : atomic φ ⊆ atomic ψ :=
  fun _ hφ => h _ hφ

theorem not_intro (h : (R ∧ₜ A) ⊆ ⌜False⌝ₜ) : R ⊆ ¬ₜ A := fun τ hR hA => h τ ⟨hR, hA⟩

theorem not_elim : ((¬ₜ A) ∧ₜ A) ⊆ S := fun _ h => (h.1 h.2).elim

theorem not_mono (h : A' ⊆ A) : (¬ₜ A) ⊆ ¬ₜ A' := fun τ hn hA => hn (h τ hA)

/-- Double negation (classical). -/
theorem not_not_elim : (¬ₜ ¬ₜ A) ⊆ A := fun _ h => Classical.byContradiction h

theorem atPos_mono {f g : Nat → Prop} (h : ∀ n, f n → g n) : (atPos f : TrProp C) ⊆ atPos g :=
  fun τ => h τ.pos

/-! ## Next -/

@[lantana_alias tr_next_mono]
theorem next_mono (h : R ⊆ S) : (○ₜ R) ⊆ (○ₜ S) := fun τ hR => h τ.next hR

/-! ## Always -/

@[lantana_alias tr_always_elim]
theorem always_elim : (□ₜ R) ⊆ R := fun τ h => by simpa using h τ.pos (Nat.le_refl _)

@[lantana_alias tr_always_next]
theorem always_next : (□ₜ R) ⊆ (○ₜ □ₜ R) :=
  fun _ h m hm => h m (Nat.le_of_succ_le hm)

@[lantana_alias tr_always_idemp]
theorem always_idemp : (□ₜ R) ⊆ (□ₜ □ₜ R) :=
  fun _ h m hm l hl => by simpa using h l (Nat.le_trans hm hl)

@[lantana_alias tr_always_mono]
theorem always_mono (h : R ⊆ S) : (□ₜ R) ⊆ (□ₜ S) := fun _ hR m hm => h _ (hR m hm)

@[lantana_alias tr_always_and]
theorem always_and : (□ₜ (R ∧ₜ S)) ⊆ ((□ₜ R) ∧ₜ (□ₜ S)) :=
  fun _ h => ⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2⟩

@[lantana_alias tr_and_always]
theorem and_always : ((□ₜ R) ∧ₜ (□ₜ S)) ⊆ (□ₜ (R ∧ₜ S)) :=
  fun _ h m hm => ⟨h.1 m hm, h.2 m hm⟩

@[lantana_alias tr_always_impl]
theorem always_imp : ((□ₜ (R →ₜ S)) ∧ₜ (□ₜ R)) ⊆ (□ₜ S) :=
  fun _ h m hm => h.1 m hm (h.2 m hm)

/-- Coinduction for `□ₜ`: a property that holds now and is preserved by `○ₜ` holds always. -/
@[lantana_alias tr_always_coind]
theorem always_coind (h : X ⊆ (R ∧ₜ ○ₜ X)) : X ⊆ (□ₜ R) := by
  intro τ hX m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k generalizing τ with
  | zero => simpa using (h τ hX).1
  | succ k ih =>
    have := ih τ.next (h τ hX).2 (Nat.le_add_right _ _)
    simpa [Trace.next, Nat.add_assoc, (Nat.add_comm 1 k)] using this

/-! ## Until and eventually -/

@[lantana_alias tr_until_now]
theorem until_now : S ⊆ (R Uₜ S) :=
  fun τ h => ⟨τ.pos, Nat.le_refl _, by simpa using h, fun _ h₁ h₂ => absurd h₁ (Nat.not_le.mpr h₂)⟩

@[lantana_alias tr_until_step]
theorem until_step : (R ∧ₜ ○ₜ (R Uₜ S)) ⊆ (R Uₜ S) := by
  intro τ ⟨hR, m, hm, hS, hbefore⟩
  refine ⟨m, Nat.le_of_succ_le hm, hS, fun l hl hlm => ?_⟩
  rcases Nat.eq_or_lt_of_le hl with rfl | hl
  · simpa using hR
  · exact hbefore l hl hlm

@[lantana_alias tr_until_unfold]
theorem until_unfold : (R Uₜ S) ⊆ (S ∨ₜ (R ∧ₜ ○ₜ (R Uₜ S))) := by
  intro τ ⟨m, hm, hS, hbefore⟩
  rcases Nat.eq_or_lt_of_le hm with rfl | hm
  · exact .inl (by simpa using hS)
  · exact .inr ⟨by simpa using hbefore τ.pos (Nat.le_refl _) hm,
      m, hm, hS, fun l hl hlm => hbefore l (Nat.le_of_succ_le hl) hlm⟩

/-- Induction for `Uₜ`: a property implied by `S` and preserved backwards by `R ∧ₜ ○ₜ ·`
contains `R Uₜ S`. -/
@[lantana_alias tr_until_ind]
theorem until_ind (h₁ : S ⊆ X) (h₂ : (R ∧ₜ ○ₜ X) ⊆ X) : (R Uₜ S) ⊆ X := by
  intro τ ⟨m, hm, hS, hbefore⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k generalizing τ with
  | zero => simpa using h₁ _ hS
  | succ k ih =>
    have hlt : τ.pos < τ.pos + (k + 1) := by omega
    refine h₂ τ ⟨hbefore τ.pos (Nat.le_refl _) hlt, ?_⟩
    refine ih τ.next (Nat.le_add_right _ _)
      (by simpa [Trace.next, Nat.add_assoc, (Nat.add_comm 1 k)] using hS) fun l hl hlm => ?_
    exact hbefore l (by simp [Trace.next] at hl; omega) (by simp [Trace.next] at hlm; omega)

@[lantana_alias tr_until_mono]
theorem until_mono (h₁ : R ⊆ R') (h₂ : S ⊆ S') : (R Uₜ S) ⊆ (R' Uₜ S') :=
  fun _ ⟨m, hm, hS, hb⟩ => ⟨m, hm, h₂ _ hS, fun l hl hlm => h₁ _ (hb l hl hlm)⟩

@[lantana_alias tr_until_finally]
theorem until_eventually : (R Uₜ S) ⊆ (◇ₜ S) := until_mono true_intro (le_refl _)

@[lantana_alias tr_finally_intro]
theorem eventually_intro : S ⊆ (◇ₜ S) := until_now

@[lantana_alias tr_finally_mono]
theorem eventually_mono (h : S ⊆ S') : (◇ₜ S) ⊆ (◇ₜ S') := until_mono (le_refl _) h

@[lantana_alias tr_finally_idemp]
theorem eventually_idemp : (◇ₜ ◇ₜ S) ⊆ (◇ₜ S) := by
  intro τ ⟨m, hm, ⟨m', hm', hS, _⟩, _⟩
  exact ⟨m', Nat.le_trans hm (by simpa using hm'), by simpa using hS, fun _ _ _ => trivial⟩

@[lantana_alias tr_finally_or]
theorem eventually_or : (◇ₜ (R ∨ₜ S)) ⊆ ((◇ₜ R) ∨ₜ (◇ₜ S)) := by
  intro τ ⟨m, hm, h, _⟩
  exact h.imp (⟨m, hm, ·, fun _ _ _ => trivial⟩) (⟨m, hm, ·, fun _ _ _ => trivial⟩)

/-- `□ₜ (R →ₜ ◇ₜ S)` and `◇ₜ R` give `◇ₜ S`. -/
@[lantana_alias tr_always_finally_resp]
theorem always_eventually_resp : ((□ₜ (R →ₜ ◇ₜ S)) ∧ₜ (◇ₜ R)) ⊆ (◇ₜ S) := by
  intro τ ⟨hA, m, hm, hR, _⟩
  obtain ⟨m', hm', hS, _⟩ := hA m hm hR
  exact ⟨m', Nat.le_trans hm (by simpa using hm'), by simpa using hS, fun _ _ _ => trivial⟩

@[lantana_alias tr_always_finally_mono]
theorem always_eventually_mono (h : R ⊆ S) : (□ₜ ◇ₜ R) ⊆ (□ₜ ◇ₜ S) :=
  always_mono (eventually_mono h)

/-! ## Duality (classical) -/

@[lantana_alias tr_not_finally]
theorem not_eventually : ((◇ₜ R) →ₜ ⌜False⌝ₜ) ⊆ (□ₜ (R →ₜ ⌜False⌝ₜ)) :=
  fun _ h m hm hR => h ⟨m, hm, hR, fun _ _ _ => trivial⟩

@[lantana_alias tr_not_always]
theorem not_always : (◇ₜ (R →ₜ ⌜False⌝ₜ)) ⊆ ((□ₜ R) →ₜ ⌜False⌝ₜ) :=
  fun _ ⟨m, hm, hn, _⟩ hA => hn (hA m hm)

@[lantana_alias tr_not_always_finally]
theorem not_always_eventually : ((□ₜ R) →ₜ ⌜False⌝ₜ) ⊆ (◇ₜ (R →ₜ ⌜False⌝ₜ)) :=
  fun _ h => Classical.byContradiction fun hn =>
    h fun m hm => Classical.byContradiction fun hR => hn ⟨m, hm, hR, fun _ _ _ => trivial⟩

/-! ## Infinitely often and eventually always

`□ₜ ◇ₜ R` (infinitely often) and `◇ₜ □ₜ R` (eventually always) read through positions, are
invariant under `○ₜ` (and under any shift of the position, `absolute_always_eventually`,
`absolute_eventually_always`), and are dual under negation. -/

theorem eventually_iff {τ : Trace C} : (◇ₜ R) τ ↔ ∃ m, τ.pos ≤ m ∧ R { τ with pos := m } :=
  ⟨fun ⟨m, hm, hR, _⟩ => ⟨m, hm, hR⟩, fun ⟨m, hm, hR⟩ => ⟨m, hm, hR, fun _ _ _ => trivial⟩⟩

/-- `□ₜ ◇ₜ P` at positions: from every position on, `P` holds at some later one. -/
theorem always_eventually_iff {τ : Trace C} :
    (□ₜ ◇ₜ P) τ ↔ ∀ n, τ.pos ≤ n → ∃ m, n ≤ m ∧ P { τ with pos := m } :=
  forall_congr' fun _ => imp_congr_right fun _ => eventually_iff

/-- `◇ₜ □ₜ P` at positions: from some position on, `P` holds at every one. -/
theorem eventually_always_iff {τ : Trace C} :
    (◇ₜ □ₜ P) τ ↔ ∃ n, τ.pos ≤ n ∧ ∀ m, n ≤ m → P { τ with pos := m } :=
  eventually_iff

theorem always_eventually_next : (□ₜ ◇ₜ R) ⊆ (○ₜ □ₜ ◇ₜ R) := always_next

theorem next_always_eventually : (○ₜ □ₜ ◇ₜ R) ⊆ (□ₜ ◇ₜ R) := by
  intro τ h
  refine always_eventually_iff.mpr fun n hn => ?_
  obtain ⟨m, hm, hR⟩ := always_eventually_iff.mp h (n + 1) (by simpa using hn)
  exact ⟨m, Nat.le_of_succ_le hm, hR⟩

theorem eventually_always_next : (◇ₜ □ₜ R) ⊆ (○ₜ ◇ₜ □ₜ R) := by
  intro τ h
  obtain ⟨n, hn, hR⟩ := eventually_always_iff.mp h
  exact eventually_always_iff.mpr
    ⟨n + 1, by simpa using hn, fun m hm => hR m (Nat.le_of_succ_le hm)⟩

theorem next_eventually_always : (○ₜ ◇ₜ □ₜ R) ⊆ (◇ₜ □ₜ R) := by
  intro τ h
  obtain ⟨n, hn, hR⟩ := eventually_always_iff.mp h
  exact eventually_always_iff.mpr ⟨n, Nat.le_of_succ_le (by simpa using hn), hR⟩

/-- Eventually always gives infinitely often. -/
theorem eventually_always_le : (◇ₜ □ₜ R) ⊆ (□ₜ ◇ₜ R) := by
  intro τ h
  obtain ⟨n, -, hR⟩ := eventually_always_iff.mp h
  exact always_eventually_iff.mpr fun m _ =>
    ⟨max m n, Nat.le_max_left _ _, hR _ (Nat.le_max_right _ _)⟩

/-- Not infinitely often is eventually never (classical). -/
theorem not_always_eventually_le : (¬ₜ □ₜ ◇ₜ R) ⊆ (◇ₜ □ₜ ¬ₜ R) := by
  intro τ h
  refine eventually_always_iff.mpr (Classical.byContradiction fun hn => h ?_)
  refine always_eventually_iff.mpr fun n hn' => Classical.byContradiction fun hm => hn ?_
  exact ⟨n, hn', fun m hnm hR => hm ⟨m, hnm, hR⟩⟩

/-- Not eventually always is infinitely often not (classical). -/
theorem not_eventually_always_le : (¬ₜ ◇ₜ □ₜ R) ⊆ (□ₜ ◇ₜ ¬ₜ R) := by
  intro τ h
  refine always_eventually_iff.mpr fun n hn => Classical.byContradiction fun hm => h ?_
  exact eventually_always_iff.mpr ⟨n, hn, fun m hnm =>
    Classical.byContradiction fun hR => hm ⟨m, hnm, hR⟩⟩

theorem eventually_always_not_le : (◇ₜ □ₜ ¬ₜ R) ⊆ (¬ₜ □ₜ ◇ₜ R) := by
  intro τ h hR
  obtain ⟨n, hn, hnR⟩ := eventually_always_iff.mp h
  obtain ⟨m, hnm, hm⟩ := always_eventually_iff.mp hR n hn
  exact hnR m hnm hm

theorem always_eventually_not_le : (□ₜ ◇ₜ ¬ₜ R) ⊆ (¬ₜ ◇ₜ □ₜ R) := by
  intro τ h hR
  obtain ⟨n, hn, hnR⟩ := eventually_always_iff.mp hR
  obtain ⟨m, hnm, hm⟩ := always_eventually_iff.mp h n hn
  exact hm (hnR m hnm)

/-! ## Absolute properties

A property is absolute when it is the same at every position of a run: it depends on the
sequence of configurations only. `□ₜ ◇ₜ P` and `◇ₜ □ₜ P` are, and the absolute properties are
closed under the propositional connectives and the quantifiers. -/

/-- A property the same at every position of a run. -/
def Absolute (P : TrProp C) : Prop := ∀ τ m, P τ ↔ P { τ with pos := m }

/-- An absolute property is the same one position later. -/
theorem Absolute.next (h : Absolute P) {τ : Trace C} : P τ ↔ P τ.next := h τ (τ.pos + 1)

/-- An absolute property, once true, is true at every position. -/
theorem Absolute.le_always (h : Absolute P) : P ⊆ (□ₜ P) := fun τ hP m _ => (h τ m).mp hP

theorem absolute_always_eventually : Absolute (□ₜ ◇ₜ P) := by
  intro τ k
  rw [always_eventually_iff, always_eventually_iff]
  constructor
  · intro h n hn
    obtain ⟨m, hm, hP⟩ := h (max n τ.pos) (Nat.le_max_right _ _)
    exact ⟨m, Nat.le_trans (Nat.le_max_left _ _) hm, hP⟩
  · intro h n _
    obtain ⟨m, hm, hP⟩ := h (max n k) (Nat.le_max_right _ _)
    exact ⟨m, Nat.le_trans (Nat.le_max_left _ _) hm, hP⟩

theorem absolute_eventually_always : Absolute (◇ₜ □ₜ P) := by
  intro τ k
  rw [eventually_always_iff, eventually_always_iff]
  constructor
  · rintro ⟨n, -, hP⟩
    exact ⟨max n k, Nat.le_max_right _ _,
      fun m hm => hP m (Nat.le_trans (Nat.le_max_left _ _) hm)⟩
  · rintro ⟨n, -, hP⟩
    exact ⟨max n τ.pos, Nat.le_max_right _ _,
      fun m hm => hP m (Nat.le_trans (Nat.le_max_left _ _) hm)⟩

theorem absolute_pure {φ : Prop} : Absolute (⌜φ⌝ₜ : TrProp C) := fun _ _ => Iff.rfl

theorem absolute_imp (hP : Absolute P) (hQ : Absolute Q) : Absolute (P →ₜ Q) :=
  fun τ m => imp_congr (hP τ m) (hQ τ m)

theorem absolute_and (hP : Absolute P) (hQ : Absolute Q) : Absolute (P ∧ₜ Q) :=
  fun τ m => and_congr (hP τ m) (hQ τ m)

theorem absolute_or (hP : Absolute P) (hQ : Absolute Q) : Absolute (P ∨ₜ Q) :=
  fun τ m => or_congr (hP τ m) (hQ τ m)

theorem absolute_not (hP : Absolute P) : Absolute (¬ₜ P) := absolute_imp hP absolute_pure

theorem absolute_all {α : Sort _} {P : α → TrProp C} (h : ∀ a, Absolute (P a)) :
    Absolute (∀ₜ a, P a) := fun τ m => forall_congr' fun a => h a τ m

theorem absolute_ex {α : Sort _} {P : α → TrProp C} (h : ∀ a, Absolute (P a)) :
    Absolute (∃ₜ a, P a) := fun τ m => exists_congr fun a => h a τ m

/-! ## Fixpoints -/

@[lantana_alias tr_gfp_coind]
theorem gfp_coind {Φ : TrProp C → TrProp C} (h : ∀ τ, R τ → Φ R τ) :
    ∀ τ, R τ → gfp Φ τ := fun _ hR => ⟨R, h, hR⟩

@[lantana_alias tr_gfp_unfold_l]
theorem gfp_unfold_l {Φ : TrProp C → TrProp C} (hΦ : Mono Φ) :
    ∀ τ, gfp Φ τ → Φ (gfp Φ) τ :=
  fun τ ⟨R, hR, hτ⟩ => hΦ R (gfp Φ) (fun _ h => ⟨R, hR, h⟩) τ (hR τ hτ)

@[lantana_alias tr_gfp_unfold_r]
theorem gfp_unfold_r {Φ : TrProp C → TrProp C} (hΦ : Mono Φ) :
    ∀ τ, Φ (gfp Φ) τ → gfp Φ τ :=
  fun _ h => ⟨Φ (gfp Φ), fun τ' h' => hΦ _ _ (gfp_unfold_l hΦ) τ' h', h⟩

@[lantana_alias tr_lfp_ind]
theorem lfp_ind {Φ : TrProp C → TrProp C} (h : ∀ τ, Φ R τ → R τ) :
    ∀ τ, lfp Φ τ → R τ := fun _ hτ => hτ R h

@[lantana_alias tr_lfp_unfold_r]
theorem lfp_unfold_r {Φ : TrProp C → TrProp C} (hΦ : Mono Φ) :
    ∀ τ, Φ (lfp Φ) τ → lfp Φ τ :=
  fun τ h R hR => hR τ (hΦ _ _ (fun _ h' => h' R hR) τ h)

@[lantana_alias tr_lfp_unfold_l]
theorem lfp_unfold_l {Φ : TrProp C → TrProp C} (hΦ : Mono Φ) :
    ∀ τ, lfp Φ τ → Φ (lfp Φ) τ :=
  fun _ h => h (Φ (lfp Φ)) fun τ' h' => hΦ _ _ (lfp_unfold_r hΦ) τ' h'

end Lantana.TrProp
