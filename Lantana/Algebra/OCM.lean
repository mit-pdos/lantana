/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Prelude.Ordinal

/-! # Ordered commutative monoids

Ordered commutative monoids (`OCM`, Rocq `ocm.v`) and well-founded ones (`WFOCM`, Rocq
`wfocm.v`), and the instance on the ordinals with the natural sum (Rocq `ordinal_wfocm.v`). They
are the carriers of the bank (`Lantana.Bank`) and of the bounded credits (`Lantana.BCred`).

## Leibniz order (decision D6)

Rocq's `OCM.t` is a total *pre*order whose monoid laws hold up to the preorder; its modules
`quotient` and `partition` quotient it to obtain Leibniz equality for the cameras. Here the order
is a linear order with Leibniz equality (`Std.IsLinearOrder`) and the monoid laws hold for `=`,
so the cameras are defined directly on the carrier: Rocq's `quotient.join`/`quotient.meet` are
`max`/`min`, and the only principal down-sets and `top` that `partition` is used for are
`some a` and `none` in `Option`. The only instance, the ordinals, is antisymmetric.

## The operation is a parameter (the `Add`/`+ₕ` question)

The operation of the monoid is an `outParam` of the class, `OCM α add`, not an `Add α` instance.
Fuel is `Ordinal.{1}`, whose global `Add` is the ordinal sum, while its monoid operation is the
natural sum `+ₕ` (`Ordinal.nadd`): with the operation as a parameter, the instance
`OCM Ordinal nadd` is global, conflicts with nothing, and the generic lemmas instantiated at
`Fuel` state literally `a +ₕ b` (so `rw` with the ordinal lemmas works), without a type synonym
(see `Lantana.BaseLogic.LaterCredits` for the trouble with `NatOrdinal`) and without a scoped
`Add Ordinal`. In the generic files the operation is written `a +ₒ b` (a local notation for the
`add` of the section).

The order data `LE`, `LT`, `Min`, `Zero` are the type's own instances; the class requires them
to form a linear order (`Std.IsLinearOrder`) with `<` its strict part (`Std.LawfulOrderLT`) and
`min` its minimum (`Std.LawfulOrderMin`). The ordinals have all of these.
-/

@[expose] public section

namespace Lantana

universe u v

/-- An ordered commutative monoid (Rocq `OCM.t`): a linear order with Leibniz equality, a
commutative monoid operation `add` with unit `0`, such that `a ≤ add a b` and `add a` is
monotone. -/
@[lantana_alias OCM.t]
class OCM (α : Type u) [LE α] [LT α] [Min α] [Zero α] (add : outParam (α → α → α)) : Prop
    extends Std.IsLinearOrder α, Std.LawfulOrderLT α, Std.LawfulOrderMin α where
  add_assoc (a b c : α) : add (add a b) c = add a (add b c)
  add_comm (a b : α) : add a b = add b a
  zero_add (a : α) : add 0 a = a
  le_self_add (a b : α) : a ≤ add a b
  add_le_add_left {b c : α} (h : b ≤ c) (a : α) : add a b ≤ add a c

attribute [lantana_alias OCM.add_assoc_eq] OCM.add_assoc
attribute [lantana_alias OCM.add_comm_eq] OCM.add_comm
attribute [lantana_alias OCM.add_unit_left_eq] OCM.zero_add
attribute [lantana_alias OCM.add_base_left_le] OCM.le_self_add
attribute [lantana_alias OCM.add_left_le_proper] OCM.add_le_add_left

#lantana_ignore OCM.unit "the `0` of `Zero α`"
#lantana_ignore OCM.le_PreOrder "`Std.IsLinearOrder`, a parent of `OCM`"
#lantana_ignore OCM.le_total "`Std.IsLinearOrder`, a parent of `OCM` (`Std.le_total`)"
#lantana_ignore OCM.add_assoc_le "Leibniz equality: `OCM.add_assoc`"
#lantana_ignore OCM.add_comm_le "Leibniz equality: `OCM.add_comm`"
#lantana_ignore OCM.add_unit_left_le "Leibniz equality: `OCM.zero_add`"
#lantana_ignore OCM.add_unit_right_le "Leibniz equality: `OCM.add_zero`"
#lantana_ignore OCM.eq_def "Leibniz equality"
#lantana_ignore OCM.eq "Leibniz equality"
#lantana_ignore OCM.eq_Equivalence "Leibniz equality"
#lantana_ignore OCM.add_left_eq_proper "Leibniz equality"
#lantana_ignore OCM.add_right_eq_proper "Leibniz equality"
#lantana_ignore OCM.add_eq_proper "Leibniz equality"
#lantana_ignore OCM.eq_le_antisymm "`Std.le_antisymm` (Leibniz equality)"
#lantana_ignore OCM.eq_le_proper "Leibniz equality"
#lantana_ignore OCM.pack "the operation is an `outParam` of `OCM`, found from the carrier"

namespace OCM

variable {α : Type u} [LE α] [LT α] [Min α] [Zero α] {add : α → α → α} [OCM α add]

set_option hygiene false in
/-- The operation of the monoid. -/
local infixl:65 " +ₒ " => add

include add

/-! ## The order

The laws of the linear order are those of `Std.IsLinearOrder` (`Std.le_refl`, `Std.le_trans`,
`Std.le_antisymm`, `Std.le_total`); the following facts about `<` and `min` are stated for an
`OCM`, so that they need no further instances. -/

protected theorem le_rfl {a : α} : a ≤ a :=
  Std.le_refl a

protected theorem le_of_eq {a b : α} (h : a = b) : a ≤ b :=
  h ▸ Std.le_refl a

protected theorem lt_iff_le_not_le {a b : α} : a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  Std.LawfulOrderLT.lt_iff a b

protected theorem le_of_lt {a b : α} (h : a < b) : a ≤ b :=
  (OCM.lt_iff_le_not_le.mp h).1

protected theorem not_le {a b : α} : ¬a ≤ b ↔ b < a :=
  ⟨fun h => OCM.lt_iff_le_not_le.mpr ⟨(Std.le_total (a := a) (b := b)).resolve_left h, h⟩,
   fun h => (OCM.lt_iff_le_not_le.mp h).2⟩

protected theorem not_lt {a b : α} : ¬a < b ↔ b ≤ a := by
  rw [← OCM.not_le, Classical.not_not]

protected theorem lt_irrefl (a : α) : ¬a < a :=
  fun h => (OCM.lt_iff_le_not_le.mp h).2 (Std.le_refl a)

protected theorem lt_of_le_of_lt {a b c : α} (hab : a ≤ b) (hbc : b < c) : a < c :=
  OCM.not_le.mp fun hca => OCM.not_le.mpr hbc (Std.le_trans hca hab)

protected theorem lt_of_lt_of_le {a b c : α} (hab : a < b) (hbc : b ≤ c) : a < c :=
  OCM.not_le.mp fun hca => OCM.not_le.mpr hab (Std.le_trans hbc hca)

protected theorem lt_trans {a b c : α} (hab : a < b) (hbc : b < c) : a < c :=
  OCM.lt_of_lt_of_le hab (OCM.le_of_lt hbc)

protected theorem ne_of_lt {a b : α} (h : a < b) : a ≠ b :=
  fun e => OCM.lt_irrefl a (e ▸ h)

protected theorem lt_of_le_of_ne {a b : α} (hab : a ≤ b) (hne : a ≠ b) : a < b :=
  OCM.not_le.mp fun hba => hne (Std.le_antisymm hab hba)

/-! ## The minimum (Rocq `quotient.meet`) -/

protected theorem min_le_left (a b : α) : min a b ≤ a :=
  Std.min_le_left

protected theorem min_le_right (a b : α) : min a b ≤ b :=
  Std.min_le_right

protected theorem le_min {a b c : α} (hb : a ≤ b) (hc : a ≤ c) : a ≤ min b c :=
  Std.le_min_iff.mpr ⟨hb, hc⟩

protected theorem min_eq_left {a b : α} (h : a ≤ b) : min a b = a :=
  Std.le_antisymm (OCM.min_le_left a b) (OCM.le_min OCM.le_rfl h)

protected theorem min_eq_right {a b : α} (h : b ≤ a) : min a b = b :=
  Std.le_antisymm (OCM.min_le_right a b) (OCM.le_min h OCM.le_rfl)

protected theorem min_self (a : α) : min a a = a :=
  OCM.min_eq_left OCM.le_rfl

protected theorem min_comm (a b : α) : min a b = min b a :=
  Std.le_antisymm (OCM.le_min (OCM.min_le_right a b) (OCM.min_le_left a b))
    (OCM.le_min (OCM.min_le_right b a) (OCM.min_le_left b a))

protected theorem min_assoc (a b c : α) : min (min a b) c = min a (min b c) := by
  refine Std.le_antisymm (OCM.le_min ?_ (OCM.le_min ?_ ?_)) (OCM.le_min (OCM.le_min ?_ ?_) ?_)
  · exact Std.le_trans (OCM.min_le_left _ _) (OCM.min_le_left a b)
  · exact Std.le_trans (OCM.min_le_left _ _) (OCM.min_le_right a b)
  · exact OCM.min_le_right _ c
  · exact OCM.min_le_left a _
  · exact Std.le_trans (OCM.min_le_right a _) (OCM.min_le_left b c)
  · exact Std.le_trans (OCM.min_le_right a _) (OCM.min_le_right b c)

/-! ## The monoid -/

@[lantana_alias OCM.add_unit_right_eq]
theorem add_zero (a : α) : a +ₒ 0 = a := by
  rw [OCM.add_comm a 0, OCM.zero_add a]

theorem add_left_comm (a b c : α) : a +ₒ (b +ₒ c) = b +ₒ (a +ₒ c) := by
  rw [← OCM.add_assoc a b c, OCM.add_comm a b, OCM.add_assoc b a c]

theorem add_right_comm (a b c : α) : a +ₒ b +ₒ c = a +ₒ c +ₒ b := by
  rw [OCM.add_assoc a b c, OCM.add_comm b c, ← OCM.add_assoc a c b]

theorem add_add_add_comm (a b c d : α) : a +ₒ b +ₒ (c +ₒ d) = a +ₒ c +ₒ (b +ₒ d) := by
  rw [OCM.add_assoc a b, add_left_comm b c d, ← OCM.add_assoc a c]

@[lantana_alias OCM.add_base_right_le]
theorem le_add_self (a b : α) : b ≤ a +ₒ b :=
  OCM.add_comm a b ▸ OCM.le_self_add b a

@[lantana_alias OCM.add_right_le_proper]
theorem add_le_add_right {b c : α} (h : b ≤ c) (a : α) : b +ₒ a ≤ c +ₒ a := by
  rw [OCM.add_comm b a, OCM.add_comm c a]
  exact OCM.add_le_add_left h a

@[lantana_alias OCM.add_le_proper]
theorem add_le_add {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a +ₒ c ≤ b +ₒ d :=
  Std.le_trans (OCM.add_le_add_left h₂ a) (add_le_add_right h₁ d)

@[lantana_alias OCM.unit_le]
theorem zero_le (a : α) : 0 ≤ a :=
  OCM.zero_add a ▸ OCM.le_self_add 0 a

theorem le_add_of_le_left {a b : α} (h : a ≤ b) (c : α) : a ≤ b +ₒ c :=
  Std.le_trans h (OCM.le_self_add b c)

theorem le_add_of_le_right {a b : α} (h : a ≤ b) (c : α) : a ≤ c +ₒ b :=
  Std.le_trans h (le_add_self c b)

theorem le_of_add_le_left {a b c : α} (h : a +ₒ b ≤ c) : a ≤ c :=
  Std.le_trans (OCM.le_self_add a b) h

theorem le_of_add_le_right {a b c : α} (h : a +ₒ b ≤ c) : b ≤ c :=
  Std.le_trans (le_add_self a b) h

end OCM

/-! ## Rocq's `quotient` and `partition` modules -/

section Quotient

#lantana_ignore quotient.t "Leibniz order: the cameras are defined on the carrier (decision D6)"
#lantana_ignore quotient.from_monoid "Leibniz order: the identity"
#lantana_ignore quotient.le "Leibniz order: `≤`"
#lantana_ignore quotient.le_PreOrder "Leibniz order: `Std.IsLinearOrder`"
#lantana_ignore quotient.le_antisymm "Leibniz order: `Std.le_antisymm`"
#lantana_ignore quotient.ext "Leibniz order"
#lantana_ignore quotient.from_monoid_exist "Leibniz order"
#lantana_ignore quotient.from_monoid_iff "Leibniz order"
#lantana_ignore quotient.from_monoid_le "Leibniz order"
#lantana_ignore quotient.from_monoid_eq "Leibniz order"
#lantana_ignore quotient.add "Leibniz order: the operation of the `OCM`"
#lantana_ignore quotient.join "Leibniz order: `max`"
#lantana_ignore quotient.meet "Leibniz order: `min`"
#lantana_ignore quotient.from_monoid_add "Leibniz order"
#lantana_ignore quotient.from_monoid_join_right "Leibniz order"
#lantana_ignore quotient.from_monoid_join_left "Leibniz order"
#lantana_ignore quotient.from_monoid_meet_left "Leibniz order: `OCM.min_eq_left`"
#lantana_ignore quotient.from_monoid_meet_right "Leibniz order: `OCM.min_eq_right`"
#lantana_ignore quotient.add_comm "Leibniz order: `OCM.add_comm`"
#lantana_ignore quotient.join_comm "Leibniz order: `max` is unused"
#lantana_ignore quotient.meet_comm "Leibniz order: `OCM.min_comm`"
#lantana_ignore quotient.add_assoc "Leibniz order: `OCM.add_assoc`"
#lantana_ignore quotient.join_assoc "Leibniz order: `max` is unused"
#lantana_ignore quotient.meet_assoc "Leibniz order: `OCM.min_assoc`"
#lantana_ignore quotient.unit "Leibniz order: `0`"
#lantana_ignore quotient.unit_le "Leibniz order: `OCM.zero_le`"
#lantana_ignore quotient.add_unit_left_eq "Leibniz order: `OCM.zero_add`"
#lantana_ignore quotient.add_unit_left_le "Leibniz order: `OCM.zero_add`"
#lantana_ignore quotient.add_unit_right_eq "Leibniz order: `OCM.add_zero`"
#lantana_ignore quotient.add_unit_right_le "Leibniz order: `OCM.add_zero`"
#lantana_ignore quotient.join_unit_left_eq "Leibniz order: `max` is unused"
#lantana_ignore quotient.join_unit_left_le "Leibniz order: `max` is unused"
#lantana_ignore quotient.join_unit_right_eq "Leibniz order: `max` is unused"
#lantana_ignore quotient.join_unit_right_le "Leibniz order: `max` is unused"
#lantana_ignore quotient.meet_unit_left_eq "Leibniz order: `min` with `0`"
#lantana_ignore quotient.meet_left_le "Leibniz order: `OCM.min_le_left`"
#lantana_ignore quotient.meet_unit_right_eq "Leibniz order: `min` with `0`"
#lantana_ignore quotient.meet_right_le "Leibniz order: `OCM.min_le_right`"
#lantana_ignore quotient.add_le_proper "Leibniz order: `OCM.add_le_add`"
#lantana_ignore quotient.add_eq_proper "Leibniz order"
#lantana_ignore quotient.add_left_le_proper "Leibniz order: `OCM.add_le_add_left`"
#lantana_ignore quotient.add_left_eq_proper "Leibniz order"
#lantana_ignore quotient.add_right_le_proper "Leibniz order: `OCM.add_le_add_right`"
#lantana_ignore quotient.add_right_eq_proper "Leibniz order"
#lantana_ignore quotient.join_le_proper "Leibniz order: `max` is unused"
#lantana_ignore quotient.join_eq_proper "Leibniz order: `max` is unused"
#lantana_ignore quotient.join_left_le_proper "Leibniz order: `max` is unused"
#lantana_ignore quotient.join_left_eq_proper "Leibniz order: `max` is unused"
#lantana_ignore quotient.join_right_le_proper "Leibniz order: `max` is unused"
#lantana_ignore quotient.join_right_eq_proper "Leibniz order: `max` is unused"
#lantana_ignore quotient.meet_le_proper "Leibniz order: monotonicity of `min`"
#lantana_ignore quotient.meet_eq_proper "Leibniz order"
#lantana_ignore quotient.meet_left_le_proper "Leibniz order: monotonicity of `min`"
#lantana_ignore quotient.meet_left_eq_proper "Leibniz order"
#lantana_ignore quotient.meet_right_le_proper "Leibniz order: monotonicity of `min`"
#lantana_ignore quotient.meet_right_eq_proper "Leibniz order"
#lantana_ignore quotient.join_supremum "Leibniz order: `max` is unused"
#lantana_ignore quotient.meet_infimum "Leibniz order: `OCM.le_min`"
#lantana_ignore quotient.join_left_le "Leibniz order: `max` is unused"
#lantana_ignore quotient.join_right_le "Leibniz order: `max` is unused"
#lantana_ignore quotient.join_idemp_le "Leibniz order: `max` is unused"
#lantana_ignore quotient.join_idemp_eq "Leibniz order: `max` is unused"
#lantana_ignore quotient.meet_idemp_le "Leibniz order: `OCM.min_self`"
#lantana_ignore quotient.meet_idemp_eq "Leibniz order: `OCM.min_self`"

#lantana_ignore partition.t
  "Leibniz order: a bound is `Option α`, `none` for `top` (decision D6, `Lantana.BCred`)"
#lantana_ignore partition.ext "Leibniz order"
#lantana_ignore partition.meet "Leibniz order: `BCred.boundMin`"
#lantana_ignore partition.top "Leibniz order: `none`"
#lantana_ignore partition.from_monoid "Leibniz order: `some`"
#lantana_ignore partition.from_monoid_iff "Leibniz order"
#lantana_ignore partition.from_monoid_eq "Leibniz order: injectivity of `some`"
#lantana_ignore partition.from_monoid_meet_left "Leibniz order: `OCM.min_eq_left`"
#lantana_ignore partition.from_monoid_meet_right "Leibniz order: `OCM.min_eq_right`"
#lantana_ignore partition.meet_comm "Leibniz order: `BCred.boundMin_comm`"
#lantana_ignore partition.meet_assoc "Leibniz order: `BCred.boundMin_assoc`"
#lantana_ignore partition.meet_top_left_eq "Leibniz order: `BCred.boundMin_none_left`"
#lantana_ignore partition.meet_top_right_eq "Leibniz order: `BCred.boundMin_none_right`"
#lantana_ignore partition.meet_left_eq_proper "Leibniz order"
#lantana_ignore partition.meet_right_eq_proper "Leibniz order"
#lantana_ignore partition.meet_eq_proper "Leibniz order"
#lantana_ignore partition.meet_idemp_eq "Leibniz order: `BCred.boundMin_self`"

end Quotient

/-! ## Well-founded ordered commutative monoids -/

/-- A well-founded ordered commutative monoid (Rocq `WFOCM.t`): `<` is well-founded, and
`a < c` iff `add a b ≤ c` for some positive `b`. -/
@[lantana_alias WFOCM.t]
class WFOCM (α : Type u) [LE α] [LT α] [Min α] [Zero α] (add : outParam (α → α → α)) : Prop
    extends OCM α add where
  lt_wf : WellFounded (α := α) (· < ·)
  lt_exists_left {a c : α} : (∃ b, 0 < b ∧ add a b ≤ c) ↔ a < c
  exists_pos : ∃ a : α, 0 < a

attribute [lantana_alias WFOCM.ocm] WFOCM.toOCM
attribute [lantana_alias WFOCM.lt_wf] WFOCM.lt_wf
attribute [lantana_alias WFOCM.lt_exists_left] WFOCM.lt_exists_left
attribute [lantana_alias WFOCM.exists_pos] WFOCM.exists_pos

#lantana_ignore WFOCM.pack "the operation is an `outParam` of `WFOCM`, found from the carrier"
#lantana_ignore WFOCM.eq_Proper "Leibniz equality"

namespace WFOCM

variable {α : Type u} [LE α] [LT α] [Min α] [Zero α] {add : α → α → α} [WFOCM α add]

set_option hygiene false in
/-- The operation of the monoid. -/
local infixl:65 " +ₒ " => add

include add

@[lantana_alias WFOCM.lt_exists_right]
theorem lt_exists_right {a c : α} : (∃ b, 0 < b ∧ b +ₒ a ≤ c) ↔ a < c := by
  rw [← lt_exists_left]
  exact exists_congr fun b => and_congr_right fun _ => by rw [OCM.add_comm a b]

@[lantana_alias WFOCM.lt_le]
theorem lt_le {a b : α} (h : a < b) : a ≤ b :=
  OCM.le_of_lt h

@[lantana_alias WFOCM.lt_le_lt]
theorem lt_le_lt {a b c : α} (hab : a < b) (hbc : b ≤ c) : a < c :=
  OCM.lt_of_lt_of_le hab hbc

@[lantana_alias WFOCM.le_lt_lt]
theorem le_lt_lt {a b c : α} (hab : a ≤ b) (hbc : b < c) : a < c :=
  OCM.lt_of_le_of_lt hab hbc

@[lantana_alias WFOCM.lt_Transitive]
protected theorem lt_trans {a b c : α} (hab : a < b) (hbc : b < c) : a < c :=
  OCM.lt_trans hab hbc

@[lantana_alias WFOCM.lt_Irreflexive]
protected theorem lt_irrefl (a : α) : ¬a < a :=
  OCM.lt_irrefl a

@[lantana_alias WFOCM.lt_le_false]
theorem lt_le_false {a b : α} (hab : a < b) (hba : b ≤ a) : False :=
  OCM.not_le.mpr hab hba

/-- Well-founded induction on `<`. -/
@[elab_as_elim, lantana_alias WFOCM.induction_type, lantana_alias WFOCM.induction_set,
  lantana_alias WFOCM.ind]
noncomputable def induction {motive : α → Sort v} (a : α)
    (ind : ∀ x, (∀ y, y < x → motive y) → motive x) : motive a :=
  (lt_wf (α := α)).fix ind a

theorem lt_add_of_pos_right (a : α) {b : α} (h : 0 < b) : a < a +ₒ b :=
  lt_exists_left.mp ⟨b, h, OCM.le_rfl⟩

end WFOCM

/-! ## The ordinals with the natural sum (Rocq `ordinal_wfocm.v`) -/

section Ordinal

open Ordinals Ordinal

/-- The ordinals with the natural sum `+ₕ` are an ordered commutative monoid. -/
@[lantana_alias ord_OCM]
instance instOCMOrdinal : OCM Ordinal.{u} nadd where
  toIsLinearOrder := inferInstance
  toLawfulOrderLT := inferInstance
  toLawfulOrderMin := inferInstance
  add_assoc := nadd_assoc
  add_comm := nadd_comm
  zero_add := zero_nadd
  le_self_add := le_self_nadd
  add_le_add_left h _ := nadd_le_nadd Ordinal.le_rfl h

/-- The ordinals with the natural sum `+ₕ` are a well-founded ordered commutative monoid. -/
@[lantana_alias ord_wfocm]
instance instWFOCMOrdinal : WFOCM Ordinal.{u} nadd where
  lt_wf := Ordinal.lt_wf
  lt_exists_left := Ordinal.lt_exists_left
  exists_pos := ⟨1, Ordinal.zero_lt_one⟩

#lantana_ignore ord_OCM_eq "Leibniz equality"
#lantana_ignore ord_wfocm_pack "the operation is an `outParam` of `WFOCM`, found from the carrier"

end Ordinal

end Lantana
