/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.HeapLang.Instances

/-! # The evaluation contexts of HeapLang

`lWP` quantifies over every evaluation context `K : Exp → Exp` (`Language.Context K`), and the laws
of HeapLang hold a thread's expression under a list `C` of context items.
`context_eq_fill_of_primStep` relates the two: a context that agrees with `fill C` before a step
agrees with it after the step.  See `docs/program-logic.md`, §4.
-/

@[expose] public section

namespace Lantana.HeapLang

open Iris.Std
open Iris.ProgramLogic
open Iris.ProgramLogic.PrimStep (primStep)

/-! ## Context items -/

theorem eq_or_eq_of_fillItem_eq {Ki Ki' : ECtxItem} {x₁ x₂ y₁ y₂ : Exp}
    (h₁ : fillItem Ki x₁ = fillItem Ki' y₁) (h₂ : fillItem Ki x₂ = fillItem Ki' y₂) :
    Ki = Ki' ∨ x₁ = x₂ := by
  cases Ki <;> cases Ki' <;> cases h₁ <;> cases h₂ <;> first | exact .inl rfl | exact .inr rfl

/-- Two lists of context items that agree on two pairs of values, with distinct values on the
left, are equal. -/
theorem eq_of_fill_ofVal_eq {C C' : List ECtxItem} {v₁ v₂ w₁ w₂ : Val}
    (h₁ : fill C (Exp.ofVal v₁ : Exp) = fill C' (Exp.ofVal w₁ : Exp))
    (h₂ : fill C (Exp.ofVal v₂ : Exp) = fill C' (Exp.ofVal w₂ : Exp)) (hne : v₁ ≠ v₂) :
    C = C' := by
  induction C using FromMathlib.List.reverseRec generalizing C' with
  | nil =>
    cases C' using FromMathlib.List.reverseCases with
    | nil => rfl
    | append_singleton C' Ki' =>
      simpa using congrArg toVal h₁
  | append_singleton C Ki ih =>
    cases C' using FromMathlib.List.reverseCases with
    | nil => simpa using congrArg toVal h₁
    | append_singleton C' Ki' =>
      simp only [EctxItemLanguage.fill_append, EctxItemLanguage.fill_cons,
        EctxItemLanguage.fill_nil] at h₁ h₂
      rcases eq_or_eq_of_fillItem_eq h₁ h₂ with rfl | h
      · rw [ih (EctxItemLanguage.fillItem_inj h₁) (EctxItemLanguage.fillItem_inj h₂)]
      · exact absurd (ToVal.TovVal.ofVal_inj (EvContext.fill_inj h)) hne

/-! ## Determinism of the base step -/

/-- A fresh block that initialises a state to the same heap as another fresh block of the same
length is that block. -/
theorem State.eq_of_initHeap_eq {σ : State} {l l' : Loc} {n : Int} {v : Option Val}
    (hn : 0 < n) (hl : ∀ i : Int, 0 ≤ i → i < n → σ.get? (l + i) = none)
    (hl' : ∀ i : Int, 0 ≤ i → i < n → σ.get? (l' + i) = none)
    (h : σ.initHeap l n v = σ.initHeap l' n v) : l = l' := by
  have hmem : ∀ {l l' : Loc}, (∀ i : Int, 0 ≤ i → i < n → σ.get? (l + i) = none) →
      σ.initHeap l n v = σ.initHeap l' n v → ∃ i : Nat, l = l' + (i : Int) := by
    intro l l' hl h
    have hget := congrArg (fun σ' : State => σ'.get? l) h
    simp only [State.get?, get?_foldl_insert] at hget
    have h0 := hl 0 (Int.le_refl 0) hn
    rw [Loc.add_zero] at h0
    rw [ite_eq_left ⟨0, by omega, by simp⟩] at hget
    split at hget
    · next hex => exact hex.elim fun i ⟨_, he⟩ => ⟨i, he⟩
    · exact absurd (hget.trans h0) (by simp)
  obtain ⟨i, hi⟩ := hmem hl h
  obtain ⟨j, hj⟩ := hmem hl' h.symm
  have hi := congrArg Loc.n hi
  have hj := congrArg Loc.n hj
  simp only [Loc.add_n] at hi hj
  ext
  omega

/-- Two base steps of `e` from one state to one state have the same result, unless `e` is
`chooseNat`. -/
theorem BaseStep.eq_or_eq_chooseNat {e e₁ e₂ : Exp} {σ σ₁ σ₂ : State} {efs₁ efs₂ : List Exp}
    (h₁ : BaseStep e σ e₁ σ₁ efs₁) (h₂ : BaseStep e σ e₂ σ₂ efs₂) (hσ : σ₁ = σ₂) :
    e₁ = e₂ ∨ e = .chooseNat := by
  -- With one result state for both steps, `cases h₂` fails on `allocNS`, `cmpXchgS`, `faaS`.
  cases h₁ <;> cases h₂
  case allocNS.allocNS hn hl _ _ hl' => exact .inl (by rw [State.eq_of_initHeap_eq hn hl hl' hσ])
  all_goals first | exact .inr rfl | (left; clear hσ; simp_all)

/-- Two base steps of one expression with different results return values. -/
theorem BaseStep.exists_eq_ofVal_of_ne {e e₁ e₂ : Exp} {σ₁ σ₂ σ₁' σ₂' : State}
    {efs₁ efs₂ : List Exp} (h₁ : BaseStep e σ₁ e₁ σ₁' efs₁) (h₂ : BaseStep e σ₂ e₂ σ₂' efs₂)
    (hne : e₁ ≠ e₂) : ∃ v, e₁ = Exp.ofVal v := by
  cases h₁ <;> cases h₂ <;> first | exact ⟨_, rfl⟩ | (subst_vars; exact absurd rfl hne)

/-! ## `chooseNat` -/

private def singletonState (n : Nat) : State :=
  ⟨PartialMap.singleton (M := HeapF) ⟨0⟩ (some (.lit (.int n)))⟩

private theorem get?_singletonState {n : Nat} {l : Loc} {w : Option Val} :
    (singletonState n).get? l = some w ↔ l = ⟨0⟩ ∧ w = some (.lit (.int n)) := by
  simp only [singletonState, State.get?, LawfulPartialMap.get?_singleton]
  split <;> simp_all [eq_comm]

private theorem baseStep_load_singletonState (n : Nat) :
    BaseStep (.load (.ofVal (.lit (.loc ⟨0⟩)))) (singletonState n) (.ofVal (.lit (.int n)))
      (singletonState n) [] :=
  .loadS _ _ _ (get?_singletonState.mpr ⟨rfl, rfl⟩)

private theorem eq_of_primStep_load_singletonState {n : Nat} {obs : List Empty} {e' : Exp}
    {σ' : State} {efs : List Exp}
    (h : primStep (.load (.ofVal (.lit (.loc ⟨0⟩))), singletonState n) obs (e', σ', efs)) :
    e' = .ofVal (.lit (.int n)) := by
  have hb : BaseStep _ _ _ _ _ := EctxLanguage.baseStep_of_primStep h
    (subredexesAreValues_of_baseStep (baseStep_load_singletonState n))
  cases hb with
  | loadS _ _ _ hget => simp_all [get?_singletonState]

private theorem exists_eq_of_primStep_chooseNat {σ σ' : State} {obs : List Empty} {e' : Exp}
    {efs : List Exp} (h : primStep (.chooseNat, σ) obs (e', σ', efs)) :
    ∃ n : Nat, e' = .ofVal (.lit (.int n)) := by
  have hb : BaseStep _ _ _ _ _ := EctxLanguage.baseStep_of_primStep h
    (subredexesAreValues_of_baseStep (.chooseNatS 0 σ))
  cases hb
  exact ⟨_, rfl⟩

private theorem exists_baseStep_of_primStep {e e' : Exp} {σ σ' : State} {obs : List Empty}
    {efs : List Exp} (h : primStep (e, σ) obs (e', σ', efs)) :
    ∃ (D : List ECtxItem) (r r' : Exp),
      e = fill D r ∧ e' = fill D r' ∧ BaseStep r σ r' σ' efs := by
  obtain ⟨hb⟩ := h
  exact ⟨_, _, _, rfl, rfl, hb⟩

private theorem BaseStep.eq_of_singletonState {q a₀ a₁ a : Exp} {k₀ k₁ n : Nat}
    {σ₀ σ₁ σ' : State} {efs₀ efs₁ efs : List Exp}
    (h₀ : BaseStep q (singletonState k₀) a₀ σ₀ efs₀) (ha₀ : a₀ = .ofVal (.lit (.int (0 : Nat))))
    (h₁ : BaseStep q (singletonState k₁) a₁ σ₁ efs₁) (ha₁ : a₁ = .ofVal (.lit (.int (1 : Nat))))
    (h : BaseStep q (singletonState n) a σ' efs) (hq : q ≠ .chooseNat) :
    a = .ofVal (.lit (.int n)) := by
  cases h₀ <;> cases h₁ <;> cases h <;>
    simp_all [get?_singletonState, ToVal.TovVal.ofVal_inj.eq_iff]

private theorem context_ofVal_eq_fill_of_chooseNat {K : Exp → Exp} [Language.Context K]
    {C : List ECtxItem} (heq : K .chooseNat = fill C .chooseNat) (n : Nat) :
    K (.ofVal (.lit (.int n))) = fill C (.ofVal (.lit (.int n))) := by
  have hsurj : ∀ m : Nat,
      ∃ k : Nat, K (.ofVal (.lit (.int k))) = fill C (.ofVal (.lit (.int m))) := by
    intro m
    obtain ⟨e', he', hs⟩ := Lantana.Language.Context.exists_eq_of_primStep (fill C) K heq.symm
      (EctxLanguage.primStep_of_baseStep (obs := []) (BaseStep.chooseNatS m default))
    obtain ⟨k, rfl⟩ := exists_eq_of_primStep_chooseNat hs
    exact ⟨k, he'.symm⟩
  have hstep : ∀ k : Nat, ∃ (D : List ECtxItem) (q a : Exp),
      K (.load (.ofVal (.lit (.loc ⟨0⟩)))) = fill D q ∧ K (.ofVal (.lit (.int k))) = fill D a ∧
        BaseStep q (singletonState k) a (singletonState k) [] :=
    fun k => exists_baseStep_of_primStep (Language.Context.primStep_fill (K := K)
      (EctxLanguage.primStep_of_baseStep (obs := []) (baseStep_load_singletonState k)))
  obtain ⟨D, q, a₀, hr, -, hb₀⟩ := hstep 0
  have hall : ∀ k : Nat, ∃ a, K (.ofVal (.lit (.int k))) = fill D a ∧
      BaseStep q (singletonState k) a (singletonState k) [] := by
    intro k
    obtain ⟨D', q', a, hr', ha, hb⟩ := hstep k
    obtain ⟨hD, rfl⟩ := EctxLanguage.base_redex_unique (hr'.symm.trans hr)
      ⟨[], _, _, _, hb⟩ ⟨[], _, _, _, hb₀⟩
    obtain rfl : D' = D := hD.trans (List.nil_append _)
    exact ⟨a, ha, hb⟩
  have hdet : ∀ k y σ' efs, BaseStep q (singletonState k) y σ' efs →
      fill D y = K (.ofVal (.lit (.int k))) := by
    intro k y σ' efs hb
    have hs : primStep (K (.load (.ofVal (.lit (.loc ⟨0⟩)))), singletonState k) []
        (fill D y, σ', efs) := by
      rw [hr]
      exact BaseStep.ContextStep.ofBaseStep D hb
    obtain ⟨e', he', hs⟩ := Language.Context.primStep_fill_inv (K := K) rfl hs
    rw [he', eq_of_primStep_load_singletonState hs]
  obtain ⟨k₀, hk₀⟩ := hsurj 0
  obtain ⟨k₁, hk₁⟩ := hsurj 1
  obtain ⟨a₀, ha₀, hb₀⟩ := hall k₀
  obtain ⟨a₁, ha₁, hb₁⟩ := hall k₁
  have hne : a₀ ≠ a₁ := by
    rintro rfl
    have := EvContext.fill_inj (hk₀.symm.trans (ha₀.trans (ha₁.symm.trans hk₁)))
    simp [ToVal.TovVal.ofVal_inj.eq_iff] at this
  obtain ⟨v₀, rfl⟩ := BaseStep.exists_eq_ofVal_of_ne hb₀ hb₁ hne
  obtain ⟨v₁, rfl⟩ := BaseStep.exists_eq_ofVal_of_ne hb₁ hb₀ (Ne.symm hne)
  obtain rfl := eq_of_fill_ofVal_eq (ha₀.symm.trans hk₀) (ha₁.symm.trans hk₁)
    fun h => hne (h ▸ rfl)
  have hq : q ≠ .chooseNat := by
    rintro rfl
    have := EvContext.fill_inj ((hdet k₀ _ _ _ (.chooseNatS 0 _)).trans
      (hdet k₀ _ _ _ (.chooseNatS 1 _)).symm)
    simp [ToVal.TovVal.ofVal_inj.eq_iff] at this
  obtain ⟨a, ha, hb⟩ := hall n
  rw [ha, BaseStep.eq_of_singletonState hb₀ (EvContext.fill_inj (ha₀.symm.trans hk₀)) hb₁
    (EvContext.fill_inj (ha₁.symm.trans hk₁)) hb hq]

/-! ## Contexts and steps -/

/-- An evaluation context that agrees with the items `C` on `e₁` agrees with them on the result of
a step of `e₁`. -/
theorem context_eq_fill_of_primStep {K : Exp → Exp} [Language.Context K] {C : List ECtxItem}
    {e₁ e₂ : Exp} {σ₁ σ₂ : State} {obs : List Empty} {efs : List Exp}
    (heq : K e₁ = fill C e₁) (hs : primStep (e₁, σ₁) obs (e₂, σ₂, efs)) :
    K e₂ = fill C e₂ := by
  obtain ⟨D, r₁, r₂, rfl, rfl, hb⟩ := exists_baseStep_of_primStep hs
  have heq' : (K ∘ fill D) r₁ = fill (D ++ C) r₁ := by
    simpa only [Function.comp_apply, EctxItemLanguage.fill_append] using heq
  rw [← Function.comp_apply (f := K), ← EctxItemLanguage.fill_append]
  obtain ⟨r₂', h, hs'⟩ := Lantana.Language.Context.exists_eq_of_primStep (K ∘ fill D)
    (fill (D ++ C)) heq' (EctxLanguage.primStep_of_baseStep (obs := obs) hb)
  have hb' : BaseStep r₁ σ₁ r₂' σ₂ efs :=
    EctxLanguage.baseStep_of_primStep_of_baseStep_reducible ⟨obs, _, _, _, hb⟩ hs'
  rcases BaseStep.eq_or_eq_chooseNat hb hb' rfl with rfl | rfl
  · exact h
  · cases hb
    exact context_ofVal_eq_fill_of_chooseNat heq' _

end Lantana.HeapLang
