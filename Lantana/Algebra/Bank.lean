/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Algebra.OCM
public import Iris.Algebra.Frac
public import Iris.Algebra.Updates
public import Iris.Algebra.IsOp

/-! # The bank camera

The camera of obligation fuel over an ordered commutative monoid (Rocq `bank.v`, after
"Module Fuel" of Lilo and FOS): `debtOf a q` (a fraction `q` of the debt) bounds by `a` the
`cash` in circulation. Cash can be borrowed with the full fraction of the debt, raising the debt
(`debtOf_owe`), and paid back with any fraction, lowering it (`debtOf_pay`).

An element is either cash `cash s` or a debt `debt e s q`: a fraction `q` of the debt with
bound `e`, together with cash `s`. Debts compose by taking the minimum of the bounds and adding
the cash and the fractions; a debt is valid when its cash is below its bound and its fraction is
at most `1`. The core is constant (`cash 0`): nothing is persistent.

Following decision D6, the carrier is defined directly on the `OCM` (Rocq: on its quotient), and
Rocq's `quotient.meet` is `min`. The camera is discrete and Leibniz.

Naming: the constructors `cash` and `debt` are Rocq's `BankCash` and `BankDebt`, and `debtOf a q`
is Rocq's `debt a q` (Rocq's `cash a` is the constructor `cash a`). Lemmas about the constructor
`debt` (`debt_update`, `debt_owe`, `debt_pay`) are Rocq's `bank_debt_*`; those about `debtOf`
(`debtOf_update`, `debtOf_owe`, `debtOf_pay`) are Rocq's `debt_*`.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris ORA

universe u

/-- The bank (Rocq `bank`): cash `cash s`, or a debt `debt e s q` with bound `e`, cash `s` and
fraction `q`. -/
@[lantana_alias bank]
inductive Bank (α : Type u) where
  /-- Cash `s` (Rocq `BankCash`; Rocq's `cash a` is the same). -/
  | cash (s : α)
  /-- A fraction `q` of a debt with bound `e`, with cash `s` (Rocq `BankDebt`). -/
  | debt (e s : α) (q : Qp)

attribute [lantana_alias BankCash, lantana_alias cash] Bank.cash
attribute [lantana_alias BankDebt] Bank.debt

namespace Bank

/-- A fraction `q` of the debt `a` (Rocq `debt a q`). -/
@[lantana_alias debt]
def debtOf {α : Type u} [Zero α] (a : α) (q : Qp) : Bank α :=
  debt a 0 q

@[lantana_alias bank_inhabited]
instance {α : Type u} [Zero α] : Inhabited (Bank α) := ⟨cash 0⟩

#lantana_ignore BankCash_inj "`Bank.cash.inj`"
#lantana_ignore bank_unit "the unit of the camera, `cash 0` (`Bank.unit_eq`)"
#lantana_ignore bankO "`COFE.ofDiscrete`: the OFE is Leibniz"
#lantana_ignore bank_unit_instance "the `unit` field of `Bank.instUCMRA`"
#lantana_ignore bank_pcore_instance "the core of `Bank.instCMRA`"
#lantana_ignore bank_ra_mixin "`CMRA.ofDiscreteTotal` (`Bank.instCMRA`)"
#lantana_ignore bank_ucmra_mixin "`Bank.instUCMRA`"
#lantana_ignore bank_opM "the camera is total: use `UpdateP.discrete_total`"
#lantana_ignore cash_eq "Leibniz equality"
#lantana_ignore debt_eq "Leibniz equality"

/-! ## The camera -/

/-- Validity (Rocq `bank_valid_instance`): the cash of a debt is below its bound, and its
fraction is at most `1`. -/
@[lantana_alias bank_valid_instance]
protected def Valid {α : Type u} [LE α] : Bank α → Prop
  | cash _ => True
  | debt e s q => s ≤ e ∧ q ≤ 1

variable {α : Type u} [LE α] [LT α] [Min α] [Zero α] {add : α → α → α}

/-- The operation (Rocq `bank_op_instance`). -/
@[lantana_alias bank_op_instance]
protected def op [OCM α add] : Bank α → Bank α → Bank α
  | cash s₀, cash s₁ => cash (add s₀ s₁)
  | cash s₀, debt e₁ s₁ q₁ => debt e₁ (add s₀ s₁) q₁
  | debt e₀ s₀ q₀, cash s₁ => debt e₀ (add s₀ s₁) q₀
  | debt e₀ s₀ q₀, debt e₁ s₁ q₁ => debt (min e₀ e₁) (add s₀ s₁) (q₀ + q₁)

variable [OCM α add]

set_option hygiene false in
/-- The operation of the monoid. -/
local infixl:65 " +ₒ " => add

private theorem qp_add_assoc (p q r : Qp) : p + q + r = p + (q + r) :=
  Subtype.ext (Rat.add_assoc p.val q.val r.val)

private theorem qp_add_comm (p q : Qp) : p + q = q + p :=
  Subtype.ext (Rat.add_comm p.val q.val)

private theorem qp_le_of_add_le {p q r : Qp} (h : p + q ≤ r) : p ≤ r := by
  have := q.2
  simp only [Qp.le_iff, Qp.val_add] at *
  grind

private theorem qp_one_add_le_one (q : Qp) : ¬(1 : Qp) + q ≤ 1 := by
  have := q.2
  simp only [Qp.le_iff, Qp.val_add, Qp.val_one]
  grind

theorem raw_op_assoc (x y z : Bank α) :
    Bank.op x (Bank.op y z) = Bank.op (Bank.op x y) z := by
  rcases x with s₀ | ⟨e₀, s₀, q₀⟩ <;> rcases y with s₁ | ⟨e₁, s₁, q₁⟩ <;>
    rcases z with s₂ | ⟨e₂, s₂, q₂⟩ <;>
    simp only [Bank.op, OCM.add_assoc (add := add), OCM.min_assoc (α := α), qp_add_assoc]

theorem raw_op_comm (x y : Bank α) : Bank.op x y = Bank.op y x := by
  rcases x with s₀ | ⟨e₀, s₀, q₀⟩ <;> rcases y with s₁ | ⟨e₁, s₁, q₁⟩ <;>
    simp only [Bank.op, OCM.add_comm (add := add), OCM.min_comm (α := α), qp_add_comm]

theorem raw_zero_op (x : Bank α) : Bank.op (cash 0) x = x := by
  rcases x with s | ⟨e, s, q⟩ <;> simp only [Bank.op, OCM.zero_add (add := add)]

theorem raw_valid_op_left (x y : Bank α) : Bank.Valid (Bank.op x y) → Bank.Valid x := by
  rcases x with s₀ | ⟨e₀, s₀, q₀⟩
  · exact fun _ => trivial
  rcases y with s₁ | ⟨e₁, s₁, q₁⟩
  · exact fun h => ⟨OCM.le_of_add_le_left h.1, h.2⟩
  · exact fun h =>
      ⟨Std.le_trans (OCM.le_of_add_le_left h.1) (OCM.min_le_left e₀ e₁), qp_le_of_add_le h.2⟩

instance : COFE (Bank α) := COFE.ofDiscrete _

instance instOFEDiscrete : OFE.Discrete (Bank α) := ⟨fun h => h⟩

/-- The bank camera (Rocq `bankR`): discrete, total, with the constant core `cash 0`. -/
@[lantana_alias bankR]
instance instCMRA : CMRA (Bank α) :=
  CMRA.ofDiscreteTotal (fun _ => cash 0) Bank.op Bank.Valid raw_op_assoc raw_op_comm raw_zero_op
    (fun _ => rfl) raw_valid_op_left (fun _ _ => ⟨cash 0, (raw_zero_op _).symm⟩)

@[lantana_alias bank_cmra_discrete]
instance instCMRADiscrete : ORA.Discrete (Bank α) where
  discrete_valid := id

instance instIsTotal : IsTotal (Bank α) where
  total _ := ⟨cash 0, rfl⟩

/-- The unital bank camera (Rocq `bankUR`). -/
@[lantana_alias bankUR]
instance instUCMRA : UCMRA (Bank α) := UORA.ofUCMRAData {
  unit := cash 0
  unit_valid := trivial
  unit_left_id := raw_zero_op _
  pcore_unit := rfl }

@[lantana_alias bank_unit_core_id]
instance : CoreId (cash 0 : Bank α) := ⟨rfl⟩

/-! ## Unfolding lemmas -/

@[lantana_alias bank_unit_unfold]
theorem unit_eq : (UORA.unit : Bank α) = cash 0 := rfl

@[lantana_alias bank_op_cash, lantana_alias cash_add]
theorem cash_add (a b : α) : (cash a • cash b : Bank α) = cash (a +ₒ b) := rfl

@[lantana_alias bank_op_debt]
theorem debt_op_debt (e₀ e₁ s₀ s₁ : α) (q₀ q₁ : Qp) :
    (debt e₀ s₀ q₀ • debt e₁ s₁ q₁ : Bank α) = debt (min e₀ e₁) (s₀ +ₒ s₁) (q₀ + q₁) := rfl

@[lantana_alias bank_op_cash_debt]
theorem cash_op_debt (a e s : α) (q : Qp) :
    (cash a • debt e s q : Bank α) = debt e (a +ₒ s) q := rfl

@[lantana_alias bank_op_debt_cash]
theorem debt_op_cash (a e s : α) (q : Qp) :
    (debt e s q • cash a : Bank α) = debt e (s +ₒ a) q := rfl

@[lantana_alias bank_core]
theorem core_eq (x : Bank α) : core x = cash 0 := rfl

/-! ## Validity -/

@[lantana_alias bank_valid_cash]
theorem valid_cash (s : α) : ✓ (cash s : Bank α) := trivial

@[lantana_alias bank_valid_debt]
theorem valid_debt {e s : α} {q : Qp} : ✓ (debt e s q : Bank α) ↔ s ≤ e ∧ q ≤ 1 := .rfl

@[lantana_alias bank_valid_debt_exclusive]
theorem valid_debt_exclusive (e₀ e₁ s₀ s₁ : α) (q : Qp) :
    ✓ (debt e₀ s₀ 1 • debt e₁ s₁ q : Bank α) ↔ False :=
  ⟨fun h => qp_one_add_le_one q h.2, False.elim⟩

@[lantana_alias bank_valid_debt_cash_raw]
theorem valid_debt_cash {e s c : α} {q : Qp} :
    ✓ (debt e s q • cash c : Bank α) ↔ s +ₒ c ≤ e ∧ q ≤ 1 := .rfl

@[lantana_alias bank_valid_debt_cash]
theorem valid_debtOf_cash {a c : α} {q : Qp} :
    ✓ (debtOf a q • cash c : Bank α) ↔ c ≤ a ∧ q ≤ 1 := by
  rw [debtOf, valid_debt_cash, OCM.zero_add (add := add)]

/-! ## Inclusion -/

@[lantana_alias bank_cash_included]
theorem cash_included {a b : α} : (cash a : Bank α) ≼ cash b ↔ ∃ c, b = a +ₒ c := by
  refine ⟨fun ⟨z, hz⟩ => ?_, fun ⟨c, hc⟩ => ⟨cash c, hc ▸ rfl⟩⟩
  rcases z with c | ⟨e, s, q⟩
  · exact ⟨c, Bank.cash.inj hz⟩
  · cases hz

@[lantana_alias bank_debt_included]
theorem debt_included {e₀ e₁ s₀ s₁ : α} {q₀ q₁ : Qp} :
    (debt e₀ s₀ q₀ : Bank α) ≼ debt e₁ s₁ q₁ ↔
      (∃ s, e₀ = e₁ ∧ s₁ = s₀ +ₒ s ∧ q₀ = q₁) ∨
      (∃ e s q, e₁ = min e₀ e ∧ s₁ = s₀ +ₒ s ∧ q₁ = q₀ + q) := by
  constructor
  · rintro ⟨z, hz⟩
    rcases z with s | ⟨e, s, q⟩
    · obtain ⟨he, hs, hq⟩ := Bank.debt.inj hz
      exact .inl ⟨s, he.symm, hs, hq.symm⟩
    · obtain ⟨he, hs, hq⟩ := Bank.debt.inj hz
      exact .inr ⟨e, s, q, he, hs, hq⟩
  · rintro (⟨s, rfl, rfl, rfl⟩ | ⟨e, s, q, rfl, rfl, rfl⟩)
    · exact ⟨cash s, rfl⟩
    · exact ⟨debt e s q, rfl⟩

@[lantana_alias bank_cash_debt_included]
theorem cash_debt_included {a e s : α} {q : Qp} :
    (cash a : Bank α) ≼ debt e s q ↔ ∃ b, s = a +ₒ b := by
  refine ⟨fun ⟨z, hz⟩ => ?_, fun ⟨b, hb⟩ => ⟨debt e b q, hb ▸ rfl⟩⟩
  rcases z with c | ⟨e', s', q'⟩
  · cases hz
  · exact ⟨s', (Bank.debt.inj hz).2.1⟩

@[lantana_alias bank_debt_cash_included]
theorem debt_cash_included {a e s : α} {q : Qp} :
    (debt e s q : Bank α) ≼ cash a ↔ False := by
  refine ⟨fun ⟨z, hz⟩ => ?_, False.elim⟩
  rcases z with c | ⟨e', s', q'⟩ <;> cases hz

/-! ## Updates -/

@[lantana_alias bank_cash_update, lantana_alias cash_update]
theorem cash_update {a₀ a₁ : α} (h : a₀ ≤ a₁) : (cash a₁ : Bank α) ~~> cash a₀ := by
  refine Update.discrete_total.mpr fun z hz => ?_
  rcases z with c | ⟨e, s, q⟩
  · exact trivial
  · exact ⟨Std.le_trans (OCM.add_le_add_right h s) hz.1, hz.2⟩

@[lantana_alias bank_debt_update]
theorem debt_update {a₀ a₁ s₀ s₁ : α} {q : Qp} (ha : a₀ ≤ a₁) (hs : s₀ ≤ s₁) :
    (debt a₀ s₁ q : Bank α) ~~> debt a₁ s₀ q := by
  refine Update.discrete_total.mpr fun z hz => ?_
  rcases z with c | ⟨e, s, q'⟩
  · exact ⟨Std.le_trans (OCM.add_le_add_right hs c) (Std.le_trans hz.1 ha), hz.2⟩
  · refine ⟨OCM.le_min ?_ ?_, hz.2⟩
    · exact Std.le_trans (OCM.add_le_add_right hs s)
        (Std.le_trans hz.1 (Std.le_trans (OCM.min_le_left a₀ e) ha))
    · exact Std.le_trans (OCM.add_le_add_right hs s) (Std.le_trans hz.1 (OCM.min_le_right a₀ e))

@[lantana_alias debt_update]
theorem debtOf_update {a₀ a₁ : α} {q : Qp} (h : a₀ ≤ a₁) :
    (debtOf a₀ q : Bank α) ~~> debtOf a₁ q :=
  debt_update h OCM.le_rfl

/-- Borrowing cash with the full fraction of the debt raises the debt. -/
@[lantana_alias bank_debt_owe]
theorem debt_owe (a₀ a₁ s : α) : (debt a₀ s 1 : Bank α) ~~> debt (a₀ +ₒ a₁) s 1 • cash a₁ := by
  refine Update.discrete_total.mpr fun z hz => ?_
  rcases z with c | ⟨e, s', q'⟩
  · refine ⟨?_, hz.2⟩
    change s +ₒ a₁ +ₒ c ≤ a₀ +ₒ a₁
    rw [OCM.add_right_comm s a₁ c]
    exact OCM.add_le_add_right hz.1 a₁
  · exact (qp_one_add_le_one q' hz.2).elim

/-- Borrowing cash with the full fraction of the debt raises the debt. -/
@[lantana_alias debt_owe]
theorem debtOf_owe (a₀ a₁ : α) : (debtOf a₀ 1 : Bank α) ~~> debtOf (a₀ +ₒ a₁) 1 • cash a₁ :=
  debt_owe a₀ a₁ 0

/-- Paying back cash with any fraction of the debt lowers the debt. -/
@[lantana_alias bank_debt_pay]
theorem debt_pay (a₀ a₁ s : α) (q : Qp) :
    (debt a₀ s q • cash a₁ : Bank α) ~~>: fun k => ∃ a₂, k = debt a₂ s q ∧ a₁ +ₒ a₂ ≤ a₀ := by
  refine UpdateP.discrete_total.mpr fun z hz => ?_
  rcases z with c | ⟨e, s', q'⟩
  · -- `hz : s +ₒ a₁ +ₒ c ≤ a₀ ∧ q ≤ 1`
    refine ⟨debt (s +ₒ c) s q, ⟨s +ₒ c, rfl, ?_⟩, OCM.le_rfl, hz.2⟩
    rw [← OCM.add_assoc a₁ s c, OCM.add_comm a₁ s]
    exact hz.1
  · -- `hz : s +ₒ a₁ +ₒ s' ≤ min a₀ e ∧ q + q' ≤ 1`
    have h : a₁ +ₒ (s +ₒ s') ≤ s +ₒ a₁ +ₒ s' := by
      rw [← OCM.add_assoc a₁ s s', OCM.add_comm a₁ s]
      exact OCM.le_rfl
    refine ⟨debt (s +ₒ s') s q, ⟨s +ₒ s', rfl, ?_⟩, ?_, hz.2⟩
    · exact Std.le_trans h (Std.le_trans hz.1 (OCM.min_le_left a₀ e))
    · refine OCM.le_min OCM.le_rfl ?_
      exact Std.le_trans (OCM.add_le_add_right (OCM.le_self_add s a₁) s')
        (Std.le_trans hz.1 (OCM.min_le_right a₀ e))

/-- Paying back cash with any fraction of the debt lowers the debt. -/
@[lantana_alias debt_pay]
theorem debtOf_pay (a₀ a₁ : α) (q : Qp) :
    (debtOf a₀ q • cash a₁ : Bank α) ~~>: fun k => ∃ a₂, k = debtOf a₂ q ∧ a₁ +ₒ a₂ ≤ a₀ :=
  debt_pay a₀ a₁ 0 q

/-! ## The algebra of debts -/

omit [LE α] [LT α] [Min α] in
@[lantana_alias debt_raw]
theorem debt_raw (e : α) (q : Qp) : (debt e 0 q : Bank α) = debtOf e q := rfl

@[lantana_alias debt_add_raw]
theorem debtOf_op (a₀ a₁ : α) (q₀ q₁ : Qp) :
    (debtOf a₀ q₀ • debtOf a₁ q₁ : Bank α) = debtOf (min a₀ a₁) (q₀ + q₁) := by
  rw [debtOf, debtOf, debt_op_debt, OCM.zero_add (add := add)]
  rfl

@[lantana_alias debt_add]
theorem debt_add (a₀ a₁ : α) (q₀ q₁ : Qp) :
    ∃ b, (debtOf a₀ q₀ • debtOf a₁ q₁ : Bank α) = debtOf b (q₀ + q₁) ∧ b ≤ a₀ ∧ b ≤ a₁ :=
  ⟨min a₀ a₁, debtOf_op a₀ a₁ q₀ q₁, OCM.min_le_left a₀ a₁, OCM.min_le_right a₀ a₁⟩

@[lantana_alias debt_split]
theorem debt_split (a : α) (q₀ q₁ : Qp) :
    (debtOf a (q₀ + q₁) : Bank α) = debtOf a q₀ • debtOf a q₁ := by
  rw [debtOf_op, OCM.min_self]

/-! ## Proof-mode instances -/

set_option synthInstance.checkSynthOrder false in
instance cash_isOp {d} (a b : α) : IsOp d (cash (a +ₒ b) : Bank α) (cash a) (cash b) where
  is_op := rfl

set_option synthInstance.checkSynthOrder false in
instance debtOf_isOp {d} (a : α) {q q₁ q₂ : Qp} [h : IsOp d q q₁ q₂] :
    IsOp d (debtOf a q : Bank α) (debtOf a q₁) (debtOf a q₂) where
  is_op := by rw [h.is_op]; exact debt_split a q₁ q₂

end Bank

end Lantana
