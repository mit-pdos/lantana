/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TraceProp

/-! # Rules of trace entailment

The rules of `R ⊆ S` (Rocq `trace_prop_rules.v`): connectives, state atoms, the laws of LTL
and the fixpoint rules. Everything is provable by unfolding; `TrProp.unfold` is the escape
hatch.
-/

@[expose] public section

namespace Lantana.TrProp


variable {Expr : Type} {State : Type}
variable {R S X A B P Q R' S' A' : TrProp Expr State}

open scoped Lantana.TrProp

/-- The definitions, for `simp` (Rocq `tr_unfold`). -/
@[lantana_alias tr_unfold]
theorem unfold : True := trivial

attribute [local simp] le HasSubset.Subset pure and or imp all ex always strongUntil eventually next
  state now

@[simp] theorem pos_set_pos (τ : Trace Expr State) (m : Nat) :
    ({ τ with pos := m } : Trace Expr State).pos = m := rfl
@[simp] theorem seq_set_pos (τ : Trace Expr State) (m : Nat) :
    ({ τ with pos := m } : Trace Expr State).seq = τ.seq := rfl
theorem next_eq_set_pos (τ : Trace Expr State) :
    τ.next = { τ with pos := τ.pos + 1 } := rfl

/-! ## Entailment -/

@[lantana_alias tr_le_preorder, refl]
theorem le_refl (R : TrProp Expr State) : R ⊆ R := fun _ h => h

theorem le_trans (h₁ : R ⊆ S) (h₂ : S ⊆ X) : R ⊆ X := fun τ h => h₂ τ (h₁ τ h)

instance : Trans (α := TrProp Expr State) (· ⊆ ·) (· ⊆ ·) (· ⊆ ·) := ⟨le_trans⟩

/-! ## Pure -/

@[lantana_alias tr_pure_intro]
theorem pure_intro {φ : Prop} (h : φ) : R ⊆ ⌜φ⌝ₜ := fun _ _ => h

@[lantana_alias tr_pure_elim]
theorem pure_elim {φ : Prop} (h : φ → ∀ τ, S τ) : ⌜φ⌝ₜ ⊆ S := fun τ hφ => h hφ τ

@[lantana_alias tr_pure_mono]
theorem pure_mono {φ ψ : Prop} (h : φ → ψ) : (⌜φ⌝ₜ : TrProp Expr State) ⊆ ⌜ψ⌝ₜ := fun _ => h

@[lantana_alias tr_true_intro]
theorem true_intro : R ⊆ ⌜True⌝ₜ := fun _ _ => trivial

@[lantana_alias tr_false_elim]
theorem false_elim : (⌜False⌝ₜ : TrProp Expr State) ⊆ S := fun _ h => h.elim

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
theorem ex_elim_l {α : Sort _} {P : α → TrProp Expr State} (h : ∀ a, (P a ∧ₜ R) ⊆ S) :
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
theorem all_intro {α : Sort _} {P : α → TrProp Expr State} (h : ∀ a, R ⊆ P a) :
    R ⊆ (∀ₜ a, P a) := fun τ hR a => h a τ hR

@[lantana_alias tr_forall_elim]
theorem all_elim {α : Sort _} {P : α → TrProp Expr State} (a : α) : (∀ₜ a, P a) ⊆ P a :=
  fun _ h => h a

@[lantana_alias tr_forall_mono]
theorem all_mono {α : Sort _} {P Q : α → TrProp Expr State} (h : ∀ a, P a ⊆ Q a) :
    (∀ₜ a, P a) ⊆ (∀ₜ a, Q a) := fun τ hP a => h a τ (hP a)

@[lantana_alias tr_exist_intro]
theorem ex_intro {α : Sort _} {P : α → TrProp Expr State} (a : α) : P a ⊆ (∃ₜ a, P a) :=
  fun _ h => ⟨a, h⟩

@[lantana_alias tr_exist_elim]
theorem ex_elim {α : Sort _} {P : α → TrProp Expr State} (h : ∀ a, P a ⊆ S) :
    (∃ₜ a, P a) ⊆ S := fun τ ⟨a, ha⟩ => h a τ ha

@[lantana_alias tr_exist_mono]
theorem ex_mono {α : Sort _} {P Q : α → TrProp Expr State} (h : ∀ a, P a ⊆ Q a) :
    (∃ₜ a, P a) ⊆ (∃ₜ a, Q a) := fun τ ⟨a, ha⟩ => ⟨a, h a τ ha⟩

/-! ## State atoms -/

@[lantana_alias tr_state_mono]
theorem state_mono {φ ψ : State → ThreadPool Expr → Prop} (h : ∀ σ tp, φ σ tp → ψ σ tp) :
    state φ ⊆ state ψ := fun _ hφ => h _ _ hφ

@[lantana_alias tr_state_and]
theorem state_and {φ ψ : State → ThreadPool Expr → Prop} :
    (state φ ∧ₜ state ψ) ⊆ state fun σ tp => φ σ tp ∧ ψ σ tp := fun _ h => h

@[lantana_alias tr_and_state]
theorem and_state {φ ψ : State → ThreadPool Expr → Prop} :
    state (fun σ tp => φ σ tp ∧ ψ σ tp) ⊆ (state φ ∧ₜ state ψ) := fun _ h => h

@[lantana_alias tr_state_pure]
theorem state_pure {φ : State → ThreadPool Expr → Prop} {ψ : Prop} (h : ∀ σ tp, φ σ tp → ψ) :
    state φ ⊆ ⌜ψ⌝ₜ := fun _ hφ => h _ _ hφ

@[lantana_alias tr_pure_state]
theorem pure_state {φ : Prop} {ψ : State → ThreadPool Expr → Prop} (h : φ → ∀ σ tp, ψ σ tp) :
    (⌜φ⌝ₜ : TrProp Expr State) ⊆ state ψ := fun _ hφ => h hφ _ _

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
theorem until_now : S ⊆ (R 𝒰ₜ S) :=
  fun τ h => ⟨τ.pos, Nat.le_refl _, by simpa using h, fun _ h₁ h₂ => absurd h₁ (Nat.not_le.mpr h₂)⟩

@[lantana_alias tr_until_step]
theorem until_step : (R ∧ₜ ○ₜ (R 𝒰ₜ S)) ⊆ (R 𝒰ₜ S) := by
  intro τ ⟨hR, m, hm, hS, hbefore⟩
  refine ⟨m, Nat.le_of_succ_le hm, hS, fun l hl hlm => ?_⟩
  rcases Nat.eq_or_lt_of_le hl with rfl | hl
  · simpa using hR
  · exact hbefore l hl hlm

@[lantana_alias tr_until_unfold]
theorem until_unfold : (R 𝒰ₜ S) ⊆ (S ∨ₜ (R ∧ₜ ○ₜ (R 𝒰ₜ S))) := by
  intro τ ⟨m, hm, hS, hbefore⟩
  rcases Nat.eq_or_lt_of_le hm with rfl | hm
  · exact .inl (by simpa using hS)
  · exact .inr ⟨by simpa using hbefore τ.pos (Nat.le_refl _) hm,
      m, hm, hS, fun l hl hlm => hbefore l (Nat.le_of_succ_le hl) hlm⟩

/-- Induction for `𝒰ₜ`: a property implied by `S` and preserved backwards by `R ∧ₜ ○ₜ ·`
contains `R 𝒰ₜ S`. -/
@[lantana_alias tr_until_ind]
theorem until_ind (h₁ : S ⊆ X) (h₂ : (R ∧ₜ ○ₜ X) ⊆ X) : (R 𝒰ₜ S) ⊆ X := by
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
theorem until_mono (h₁ : R ⊆ R') (h₂ : S ⊆ S') : (R 𝒰ₜ S) ⊆ (R' 𝒰ₜ S') :=
  fun _ ⟨m, hm, hS, hb⟩ => ⟨m, hm, h₂ _ hS, fun l hl hlm => h₁ _ (hb l hl hlm)⟩

@[lantana_alias tr_until_finally]
theorem until_eventually : (R 𝒰ₜ S) ⊆ (◇ₜ S) := until_mono true_intro (le_refl _)

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

/-! ## Fixpoints -/

@[lantana_alias tr_gfp_coind]
theorem gfp_coind {Φ : TrProp Expr State → TrProp Expr State} (h : ∀ τ, R τ → Φ R τ) :
    ∀ τ, R τ → gfp Φ τ := fun _ hR => ⟨R, h, hR⟩

@[lantana_alias tr_gfp_unfold_l]
theorem gfp_unfold_l {Φ : TrProp Expr State → TrProp Expr State} (hΦ : Mono Φ) :
    ∀ τ, gfp Φ τ → Φ (gfp Φ) τ :=
  fun τ ⟨R, hR, hτ⟩ => hΦ R (gfp Φ) (fun _ h => ⟨R, hR, h⟩) τ (hR τ hτ)

@[lantana_alias tr_gfp_unfold_r]
theorem gfp_unfold_r {Φ : TrProp Expr State → TrProp Expr State} (hΦ : Mono Φ) :
    ∀ τ, Φ (gfp Φ) τ → gfp Φ τ :=
  fun _ h => ⟨Φ (gfp Φ), fun τ' h' => hΦ _ _ (gfp_unfold_l hΦ) τ' h', h⟩

@[lantana_alias tr_lfp_ind]
theorem lfp_ind {Φ : TrProp Expr State → TrProp Expr State} (h : ∀ τ, Φ R τ → R τ) :
    ∀ τ, lfp Φ τ → R τ := fun _ hτ => hτ R h

@[lantana_alias tr_lfp_unfold_r]
theorem lfp_unfold_r {Φ : TrProp Expr State → TrProp Expr State} (hΦ : Mono Φ) :
    ∀ τ, Φ (lfp Φ) τ → lfp Φ τ :=
  fun τ h R hR => hR τ (hΦ _ _ (fun _ h' => h' R hR) τ h)

@[lantana_alias tr_lfp_unfold_l]
theorem lfp_unfold_l {Φ : TrProp Expr State → TrProp Expr State} (hΦ : Mono Φ) :
    ∀ τ, lfp Φ τ → Φ (lfp Φ) τ :=
  fun _ h => h (Φ (lfp Φ)) fun τ' h' => hΦ _ _ (lfp_unfold_r hΦ) τ' h'

end Lantana.TrProp
