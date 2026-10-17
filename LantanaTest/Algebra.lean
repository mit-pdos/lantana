/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests of the cameras of `Lantana.Algebra` at their instances: the bank and the bounded
credits over fuel (`Fuel = Ordinal.{1}` with the natural sum `+ₕ`), and authoritative monotone
knowledge of layers. The generic lemmas, instantiated at `Fuel`, state `+ₕ` literally, so that
the lemmas of the ordinals rewrite them. -/

namespace LantanaTest.Algebra

open Iris Lantana Ordinals Ordinal

/-! ## Fuel is a well-founded ordered commutative monoid -/

example : WFOCM Fuel nadd := inferInstance
example : WFOCM Layer nadd := inferInstance

example (a b : Fuel) : a ≤ a +ₕ b := OCM.le_self_add a b
example (a b : Fuel) : b ≤ a +ₕ b := OCM.le_add_self a b
example (a b : Fuel) (h : 0 < b) : a < a +ₕ b := WFOCM.lt_add_of_pos_right a h
example (a c : Fuel) : (∃ b, 0 < b ∧ a +ₕ b ≤ c) ↔ a < c := WFOCM.lt_exists_left
example (a : Fuel) : 0 ≤ a := OCM.zero_le (add := nadd) a

/-! ## The bank over fuel -/

section Bank

open Bank

example (a c : Fuel) (q : Qp) : ✓ (debtOf a q • cash c : Bank Fuel) ↔ c ≤ a ∧ q ≤ 1 :=
  valid_debtOf_cash

example (a b : Fuel) (q : Qp) : ✓ (debtOf a 1 • debtOf b q : Bank Fuel) ↔ False :=
  valid_debt_exclusive a b 0 0 q

example (a₀ a₁ : Fuel) : (debtOf a₀ 1 : Bank Fuel) ~~> debtOf (a₀ +ₕ a₁) 1 • cash a₁ :=
  debtOf_owe a₀ a₁

example (a₀ a₁ : Fuel) (q : Qp) :
    (debtOf a₀ q • cash a₁ : Bank Fuel) ~~>: fun k => ∃ a₂, k = debtOf a₂ q ∧ a₁ +ₕ a₂ ≤ a₀ :=
  debtOf_pay a₀ a₁ q

example (a₀ a₁ : Fuel) (h : a₀ ≤ a₁) : (cash a₁ : Bank Fuel) ~~> cash a₀ := cash_update h

example (a₀ a₁ : Fuel) (q : Qp) (h : a₀ ≤ a₁) : (debtOf a₀ q : Bank Fuel) ~~> debtOf a₁ q :=
  debtOf_update h

/-- The instantiated statements mention `+ₕ`: the ordinal lemmas rewrite them. -/
example (a b : Fuel) : (cash a • cash b : Bank Fuel) = cash (b +ₕ a) := by
  rw [cash_add, nadd_comm]

example (a : Fuel) (q : Qp) : (debtOf a q : Bank Fuel) = debtOf a q.half • debtOf a q.half := by
  rw [← debt_split, Qp.half_add_half]

/-- The proof-mode instances split a debt along its fraction and cash along `+ₕ`. -/
example (a : Fuel) (q : Qp) :
    IsOp .split (debtOf a q : Bank Fuel) (debtOf a q.half) (debtOf a q.half) := inferInstance

example (a b : Fuel) : IsOp .merge (cash (a +ₕ b) : Bank Fuel) (cash a) (cash b) :=
  inferInstance

/-- Borrowing and paying back: from the full debt `a`, borrow `b`, then pay `b` back. -/
example (a b : Fuel) :
    (debtOf a 1 : Bank Fuel) ~~>: fun k => ∃ a₂, k = debtOf a₂ 1 ∧ b +ₕ a₂ ≤ a +ₕ b :=
  Update.transP (debtOf_owe a b) (debtOf_pay (a +ₕ b) b 1)

end Bank

/-! ## Bounded credits over fuel -/

section BCred

open BCred

example (a₀ a₁ : Fuel) : ✓ (creditBound a₀ • credit a₁) ↔ a₁ ≤ a₀ :=
  creditBound_credit_valid_compare

example (a : Fuel) : ✓ (creditBound a • credit a) := creditBound_credit_valid_eq a

example (a : Fuel) : ORA.CoreId (creditBound a) := inferInstance

example (a₀ a₁ : Fuel) : credit (a₀ +ₕ a₁) = credit a₀ • credit a₁ := credit_split a₀ a₁

example (a₀ a₁ : Fuel) (h : a₀ ≤ a₁) : creditBound a₁ ≼ creditBound a₀ :=
  creditBound_included h

example (a₀ a₁ : Fuel) :
    creditBound a₀ • credit a₁ ~~>: fun k => ∃ a₂, k = creditBound a₂ ∧ a₁ +ₕ a₂ ≤ a₀ :=
  credit_spend a₀ a₁

example (a₀ a₁ a₂ : Fuel) (h : a₀ +ₕ a₁ ≤ a₂) : credit a₂ ~~> credit a₀ • credit a₁ :=
  credit_update_split h

/-- Spending one credit from a bound `ω` lowers the bound below `ω`. -/
example : creditBound (ω : Fuel) • credit (1 : Fuel) ~~>:
    fun k => ∃ a₂, k = creditBound a₂ ∧ a₂ < ω :=
  (credit_spend ω 1).weaken fun _ ⟨a₂, hk, h⟩ =>
    ⟨a₂, hk, Ordinal.lt_of_lt_of_le (by rw [nadd_comm, nadd_one]; exact lt_succ a₂) h⟩

end BCred

/-! ## Authoritative monotone knowledge of layers -/

section AuthMra

open AuthMra

example (a b : Layer) : ✓ ((●AM[(· ≤ ·)] a) • (◯AM[(· ≤ ·)] b)) ↔ b ≤ a := both_valid

example (dq : DFrac) (a b : Layer) :
    ✓ ((●AM{dq}[(· ≤ ·)] a) • (◯AM[(· ≤ ·)] b)) ↔ ✓ dq ∧ b ≤ a :=
  both_dfrac_valid

example (a₁ a₂ : Layer) : ✓ ((●AM[(· ≤ ·)] a₁) • (●AM[(· ≤ ·)] a₂)) ↔ False := auth_op_valid

example (a₁ a₂ : Layer) :
    ✓ ((●AM□[(· ≤ ·)] a₁) • (●AM□[(· ≤ ·)] a₂)) ↔ ✓ (DFrac.discard • DFrac.discard) ∧ a₁ = a₂ :=
  auth_dfrac_op_valid

example (a a' : Layer) (h : a ≤ a') :
    (●AM[(· ≤ · : Layer → Layer → Prop)] a) ~~> (●AM[(· ≤ ·)] a') :=
  update h

example (a : Layer) : ORA.CoreId (◯AM[(· ≤ · : Layer → Layer → Prop)] a) := inferInstance

example (a : Layer) : ORA.CoreId (●AM□[(· ≤ · : Layer → Layer → Prop)] a) := inferInstance

example (a₁ a₂ : Layer) (h : a₁ ≤ a₂) :
    (◯AM[(· ≤ · : Layer → Layer → Prop)] a₁) ≼ (◯AM[(· ≤ ·)] a₂) :=
  know_mono h

/-- The lexicographic order on pairs of layers. -/
example (a b : Layer × Layer) :
    ✓ ((●AM[lex (· ≤ ·) (· ≤ ·)] a) • (◯AM[lex (· ≤ ·) (· ≤ ·)] b)) ↔
      lex (· ≤ ·) (· ≤ ·) b a :=
  both_valid

example (a₁ a₂ : Layer × Layer) :
    ✓ ((●AM[lex (· ≤ · : Layer → Layer → Prop) (· ≤ ·)] a₁) •
      (●AM[lex (· ≤ ·) (· ≤ ·)] a₂)) ↔ False :=
  auth_op_valid

example (ℓ : Layer) (n m : Layer) (h : n ≤ m) :
    (●AM[lex (· ≤ · : Layer → Layer → Prop) (· ≤ ·)] (ℓ, n)) ~~>
      (●AM[lex (· ≤ ·) (· ≤ ·)] (ℓ, m)) :=
  update (lex.right ℓ h)

end AuthMra

end LantanaTest.Algebra
