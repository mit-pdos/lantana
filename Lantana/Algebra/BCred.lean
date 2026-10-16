/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Algebra.OCM
public import Iris.Algebra.Updates
public import Iris.Algebra.IsOp

/-! # Bounded credits

The camera of bounded credits over an ordered commutative monoid (Rocq `bcred.v`, after
"Module CounterRA" of Lilo and FOS), used for the credits of witnesses: the persistent
`creditBound a` bounds by `a` the `credit`s in circulation, and spending credits lowers the bound
(`credit_spend`).

An element is a pair of a bound and credits. The bound is `none` (no bound) or `some a`: Rocq's
bound is a down-closed set (`partition.t`), of which only the principal ones `[!a]` and `top` are
ever constructed, and `Option α` with `none` as the top is a faithful representation of them
(decision D6). Elements compose by taking the minimum of the bounds (`boundMin`) and adding the
credits; an element is valid when its credits are below its bound. The core keeps the bound and
drops the credits, so bounds are persistent.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris CMRA

universe u

/-- Bounded credits (Rocq `bcred`): a bound and credits. -/
@[lantana_alias bcred]
structure BCred (α : Type u) where
  /-- The bound on the credits, `none` if there is none (Rocq: a down-closed set). -/
  bound : Option α
  /-- The credits (Rocq: an up-closed set). -/
  cred : α

attribute [lantana_alias BCred] BCred.mk

namespace BCred

/-- The bound `a` on the credits in circulation (Rocq `credit_bound`). -/
@[lantana_alias credit_bound]
def creditBound {α : Type u} [Zero α] (a : α) : BCred α :=
  ⟨some a, 0⟩

/-- The credits `a` (Rocq `credit`). -/
@[lantana_alias credit]
def credit {α : Type u} (a : α) : BCred α :=
  ⟨none, a⟩

@[lantana_alias bcred_inhabited]
instance {α : Type u} [Zero α] : Inhabited (BCred α) := ⟨⟨none, 0⟩⟩

#lantana_ignore BCred_inj "`BCred.mk.inj`"
#lantana_ignore bcred_unit "the unit of the camera, `⟨none, 0⟩` (`BCred.unit_eq`)"
#lantana_ignore bcredO "`COFE.ofDiscrete`: the OFE is Leibniz"
#lantana_ignore bcred_unit_instance "the `unit` field of `BCred.instUCMRA`"
#lantana_ignore bcred_pcore_instance "the core of `BCred.instCMRA`"
#lantana_ignore bcred_ra_mixin "`CMRA.ofDiscreteTotal` (`BCred.instCMRA`)"
#lantana_ignore bcred_ucmra_mixin "`BCred.instUCMRA`"
#lantana_ignore bcred_opM "the camera is total: use `UpdateP.discrete_total`"
#lantana_ignore credit_eq "Leibniz equality"

/-! ## Bounds -/

/-- The minimum of two bounds, `none` being the top (Rocq `partition.meet`). -/
def boundMin {α : Type u} [Min α] : Option α → Option α → Option α
  | none, b => b
  | some a, none => some a
  | some a, some b => some (min a b)

section Bounds

variable {α : Type u} [LE α] [LT α] [Min α] [Zero α] {add : α → α → α} [OCM α add]

omit [LE α] [LT α] [Zero α] [OCM α add] in
@[simp] theorem boundMin_none_left (b : Option α) : boundMin none b = b := rfl

omit [LE α] [LT α] [Zero α] [OCM α add] in
@[simp] theorem boundMin_none_right (a : Option α) : boundMin a none = a := by
  cases a <;> rfl

omit [LE α] [LT α] [Zero α] [OCM α add] in
@[simp] theorem boundMin_some_some (a b : α) : boundMin (some a) (some b) = some (min a b) := rfl

include add in
theorem boundMin_self (a : Option α) : boundMin a a = a := by
  cases a with
  | none => rfl
  | some a => exact congrArg some (OCM.min_self a)

include add in
theorem boundMin_comm (a b : Option α) : boundMin a b = boundMin b a := by
  cases a <;> cases b <;> simp only [boundMin, OCM.min_comm (α := α)]

include add in
theorem boundMin_assoc (a b c : Option α) :
    boundMin (boundMin a b) c = boundMin a (boundMin b c) := by
  cases a <;> cases b <;> cases c <;> simp only [boundMin, OCM.min_assoc (α := α)]

include add in
/-- Credits `c` are below the bound `boundMin (some a) p` iff they are below `a` and `p`. -/
theorem below_boundMin_some {a c : α} {p : Option α} :
    (∀ b, boundMin (some a) p = some b → c ≤ b) ↔ c ≤ a ∧ ∀ b, p = some b → c ≤ b := by
  cases p with
  | none =>
    simp only [boundMin, Option.some.injEq, forall_eq', reduceCtorEq, false_imp_iff,
      implies_true, and_true]
  | some b =>
    simp only [boundMin, Option.some.injEq, forall_eq']
    exact Std.le_min_iff

end Bounds

/-! ## The camera -/

/-- Validity (Rocq `bcred_valid_instance`): the credits are below the bound. -/
@[lantana_alias bcred_valid_instance]
protected def Valid {α : Type u} [LE α] (x : BCred α) : Prop :=
  ∀ b, x.bound = some b → x.cred ≤ b

variable {α : Type u} [LE α] [LT α] [Min α] [Zero α] {add : α → α → α}

/-- The operation (Rocq `bcred_op_instance`): the minimum of the bounds and the sum of the
credits. -/
@[lantana_alias bcred_op_instance]
protected def op [OCM α add] (x y : BCred α) : BCred α :=
  ⟨boundMin x.bound y.bound, add x.cred y.cred⟩

variable [OCM α add]

set_option hygiene false in
/-- The operation of the monoid. -/
local infixl:65 " +ₒ " => add

theorem raw_op_assoc (x y z : BCred α) :
    BCred.op x (BCred.op y z) = BCred.op (BCred.op x y) z := by
  simp only [BCred.op, boundMin_assoc (add := add), OCM.add_assoc (add := add)]

theorem raw_op_comm (x y : BCred α) : BCred.op x y = BCred.op y x := by
  simp only [BCred.op, boundMin_comm (add := add) x.bound, OCM.add_comm (add := add) x.cred]

theorem raw_core_op (x : BCred α) : BCred.op ⟨x.bound, 0⟩ x = x := by
  simp only [BCred.op, boundMin_self (add := add), OCM.zero_add (add := add)]

theorem raw_valid_op_left (x y : BCred α) : BCred.Valid (BCred.op x y) → BCred.Valid x := by
  rcases x with ⟨_ | a, c⟩
  · exact fun _ _ h => nomatch h
  · intro h b hb
    cases Option.some.inj hb
    exact OCM.le_of_add_le_left (below_boundMin_some.mp h).1

instance : COFE (BCred α) := COFE.ofDiscrete _

instance instOFEDiscrete : OFE.Discrete (BCred α) := ⟨fun h => h⟩

/-- The camera of bounded credits (Rocq `bcredR`): discrete, total, with the core `⟨p, 0⟩`. -/
@[lantana_alias bcredR]
instance instCMRA : CMRA (BCred α) :=
  CMRA.ofDiscreteTotal (fun x => ⟨x.bound, 0⟩) BCred.op BCred.Valid raw_op_assoc raw_op_comm
    raw_core_op (fun _ => rfl)
    (fun _ _ ⟨z, hz⟩ => ⟨⟨z.bound, 0⟩, by
      rw [hz]; simp only [BCred.op, OCM.zero_add (add := add)]⟩)
    raw_valid_op_left

@[lantana_alias bcred_cmra_discrete]
instance instCMRADiscrete : CMRA.Discrete (BCred α) where
  discrete_valid := id

instance instIsTotal : CMRA.IsTotal (BCred α) where
  total x := ⟨⟨x.bound, 0⟩, rfl⟩

/-- The unital camera of bounded credits (Rocq `bcredUR`). -/
@[lantana_alias bcredUR]
instance instUCMRA : UCMRA (BCred α) where
  unit := ⟨none, 0⟩
  unit_valid _ h := nomatch h
  unit_left_id {x} := by
    change BCred.op ⟨none, 0⟩ x = x
    simp only [BCred.op, boundMin_none_left, OCM.zero_add (add := add)]
  pcore_unit := rfl

/-- Bounds are persistent. -/
@[lantana_alias bcred_unit_core_id]
instance creditBound_coreId (a : α) : CoreId (creditBound a) := ⟨rfl⟩

/-! ## Unfolding lemmas -/

@[lantana_alias bcred_unit_unfold]
theorem unit_eq : (UCMRA.unit : BCred α) = ⟨none, 0⟩ := rfl

@[lantana_alias bcred_op]
theorem op_eq (p₀ p₁ : Option α) (q₀ q₁ : α) :
    (⟨p₀, q₀⟩ : BCred α) • (⟨p₁, q₁⟩ : BCred α) = ⟨boundMin p₀ p₁, q₀ +ₒ q₁⟩ := rfl

@[lantana_alias bcred_core]
theorem core_eq (p : Option α) (q : α) : core (⟨p, q⟩ : BCred α) = ⟨p, 0⟩ := rfl

@[lantana_alias bcred_valid]
theorem valid_iff {p : Option α} {q : α} : ✓ (⟨p, q⟩ : BCred α) ↔ ∀ b, p = some b → q ≤ b :=
  .rfl

@[lantana_alias bcred_included]
theorem included_iff {p₀ p₁ : Option α} {q₀ q₁ : α} :
    (⟨p₀, q₀⟩ : BCred α) ≼ ⟨p₁, q₁⟩ ↔ ∃ p₂ q₂, p₁ = boundMin p₀ p₂ ∧ q₁ = q₀ +ₒ q₂ := by
  constructor
  · rintro ⟨⟨p₂, q₂⟩, hz⟩
    exact ⟨p₂, q₂, congrArg BCred.bound hz, congrArg BCred.cred hz⟩
  · rintro ⟨p₂, q₂, rfl, rfl⟩
    exact ⟨⟨p₂, q₂⟩, rfl⟩

/-! ## Validity -/

@[lantana_alias credit_bound_valid]
theorem creditBound_valid (a : α) : ✓ creditBound a :=
  fun _ h => Option.some.inj h ▸ OCM.zero_le (add := add) a

@[lantana_alias credit_valid]
theorem credit_valid (a : α) : ✓ credit a :=
  fun _ h => nomatch h

theorem creditBound_credit_valid_compare {a₀ a₁ : α} :
    ✓ (creditBound a₀ • credit a₁) ↔ a₁ ≤ a₀ := by
  change (∀ b, boundMin (some a₀) none = some b → 0 +ₒ a₁ ≤ b) ↔ a₁ ≤ a₀
  rw [OCM.zero_add a₁, below_boundMin_some]
  exact ⟨And.left, fun h => ⟨h, fun _ h => nomatch h⟩⟩

attribute [lantana_alias credit_bound_credit_valid_compare] creditBound_credit_valid_compare

@[lantana_alias credit_bound_credit_valid]
theorem creditBound_credit_valid {a b : α} :
    ✓ (creditBound a • credit b) ↔ ∃ c, c ≤ a ∧ b ≤ c := by
  rw [creditBound_credit_valid_compare]
  exact ⟨fun h => ⟨a, OCM.le_rfl, h⟩, fun ⟨_, hca, hbc⟩ => Std.le_trans hbc hca⟩

@[lantana_alias credit_bound_credit_valid_eq]
theorem creditBound_credit_valid_eq (a : α) : ✓ (creditBound a • credit a) :=
  creditBound_credit_valid_compare.mpr OCM.le_rfl

/-! ## Inclusion and composition of bounds -/

theorem creditBound_op_creditBound (a₁ a₂ : α) :
    creditBound a₁ • creditBound a₂ = creditBound (min a₁ a₂) := by
  change (⟨boundMin (some a₁) (some a₂), 0 +ₒ 0⟩ : BCred α) = ⟨some (min a₁ a₂), 0⟩
  rw [OCM.zero_add (0 : α), boundMin_some_some]

@[lantana_alias credit_bound_included]
theorem creditBound_included {a₀ a₁ : α} (h : a₀ ≤ a₁) : creditBound a₁ ≼ creditBound a₀ :=
  ⟨creditBound a₀, by rw [creditBound_op_creditBound, OCM.min_eq_right h]⟩

@[lantana_alias credit_bound_op]
theorem creditBound_op (a₁ a₂ : α) :
    ∃ a₃, creditBound a₁ • creditBound a₂ = creditBound a₃ ∧ a₃ ≤ a₁ ∧ a₃ ≤ a₂ :=
  ⟨min a₁ a₂, creditBound_op_creditBound a₁ a₂, OCM.min_le_left a₁ a₂, OCM.min_le_right a₁ a₂⟩

/-! ## Credits -/

@[lantana_alias credit_split]
theorem credit_split (a₀ a₁ : α) : credit (a₀ +ₒ a₁) = credit a₀ • credit a₁ := rfl

@[lantana_alias credit_update]
theorem credit_update {a₀ a₁ : α} (h : a₀ ≤ a₁) : credit a₁ ~~> credit a₀ := by
  refine Update.discrete_total.mpr fun ⟨p, c⟩ hz b hb => ?_
  exact Std.le_trans (OCM.add_le_add_right h c) (hz b hb)

@[lantana_alias credit_update_split]
theorem credit_update_split {a₀ a₁ a₂ : α} (h : a₀ +ₒ a₁ ≤ a₂) :
    credit a₂ ~~> credit a₀ • credit a₁ :=
  credit_split a₀ a₁ ▸ credit_update h

/-- Spending credits `a₁` lowers the (persistent) bound `a₀` to some `a₂` with
`a₁ +ₒ a₂ ≤ a₀`. -/
@[lantana_alias credit_spend]
theorem credit_spend (a₀ a₁ : α) :
    creditBound a₀ • credit a₁ ~~>: fun k => ∃ a₂, k = creditBound a₂ ∧ a₁ +ₒ a₂ ≤ a₀ := by
  refine UpdateP.discrete_total.mpr fun ⟨p, c⟩ hz => ?_
  -- `hz : 0 + a₁ + c` is below `a₀` and `p`
  replace hz : a₁ +ₒ c ≤ a₀ ∧ ∀ b, p = some b → a₁ +ₒ c ≤ b := by
    have hz' : ∀ b, boundMin (some a₀) p = some b → 0 +ₒ a₁ +ₒ c ≤ b := hz
    rw [OCM.zero_add a₁] at hz'
    exact below_boundMin_some.mp hz'
  refine ⟨creditBound c, ⟨c, rfl, hz.1⟩, ?_⟩
  change ∀ b, boundMin (some c) p = some b → 0 +ₒ c ≤ b
  rw [OCM.zero_add c, below_boundMin_some]
  exact ⟨OCM.le_rfl, fun b hb => OCM.le_of_add_le_right (hz.2 b hb)⟩

/-! ## Proof-mode instances -/

set_option synthInstance.checkSynthOrder false in
instance credit_isOp {d} (a b : α) : IsOp d (credit (a +ₒ b) : BCred α) (credit a) (credit b) where
  is_op := rfl

end BCred

end Lantana
