/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Init
public import Ordinals.Ordinal.Jacobsthal
public import Ordinals.Ordinal.WellFounded

/-! # Ordinals: layers, fuel and the fair-scheduler bound

Lantana-Rocq uses two copies of the snu-sf ordinal library to avoid a universe inconsistency
(`lantana/algebra/layer.v`): the layers live one universe below the fuel ordinals. The ordinals
of the `Ordinals` package are universe-polymorphic, so one library serves both (decision D4):

* `Layer := Ordinal.{0}` (`: Type 1`), the layers of obligations;
* `Fuel := Ordinal.{1}` (`: Type 2`), fuel, witness credits, later credits and ranks;
* the well-founded relations embedded in measures are on types in `Type 0`.

This file also proves the small ordinal facts of `ordinal_facts.v` and `ordinal_copy_facts.v`
used by measures and the model (for every universe, so for both copies at once), and defines
`fairMeasureUb` (Rocq `fair_measure_ub`), the inflationary function `η` used by `▽`
(decision D5: a concrete function, no class).

Lemmas stated in both Rocq files carry two aliases, the second one prefixed by
`ordinal_copy_facts`.
-/

@[expose] public section

namespace Ordinals.Ordinal

universe u

/-! ## Small facts on the natural sum -/

theorem zero_lt_one : (0 : Ordinal.{u}) < 1 :=
  zero_lt_succ 0

theorem nadd_one (a : Ordinal.{u}) : a +ₕ 1 = succ a := by
  rw [one_eq_succ_zero, nadd_succ, nadd_zero]

@[lantana_alias ord_S_add, lantana_alias ordinal_copy_facts.ord_S_add]
theorem succ_eq_one_nadd (a : Ordinal.{u}) : succ a = 1 +ₕ a := by
  rw [nadd_comm, nadd_one]

theorem lt_iff_nadd_one_le {a b : Ordinal.{u}} : a < b ↔ a +ₕ 1 ≤ b := by
  rw [nadd_one, succ_le_iff]

@[lantana_alias ord_lt_one, lantana_alias ordinal_copy_facts.ord_lt_one]
theorem nadd_one_le_of_lt {a b : Ordinal.{u}} (h : a < b) : a +ₕ 1 ≤ b :=
  lt_iff_nadd_one_le.mp h

/-- The axiom `lt_exists_left` of well-founded ordered commutative monoids. -/
@[lantana_alias ord_lt_exists_left, lantana_alias ordinal_copy_facts.ord_lt_exists_left]
theorem lt_exists_left {a c : Ordinal.{u}} : (∃ b, 0 < b ∧ a +ₕ b ≤ c) ↔ a < c :=
  ⟨fun ⟨_, hb, h⟩ => Ordinal.lt_of_lt_of_le (lt_nadd_of_pos_right a hb) h,
   fun h => ⟨1, zero_lt_one, nadd_one_le_of_lt h⟩⟩

/-! ## `ω` and the Jacobsthal product -/

@[lantana_alias omega_lt_zero, lantana_alias ordinal_copy_facts.omega_lt_zero]
theorem zero_lt_omega : (0 : Ordinal.{u}) < ω :=
  ofNat_lt_omega 0

@[lantana_alias omega_lt_one, lantana_alias ordinal_copy_facts.omega_lt_one]
theorem one_lt_omega : (1 : Ordinal.{u}) < ω :=
  ofNat_lt_omega 1

@[lantana_alias ordinal_copy_facts.mult_base_l]
theorem le_jmul_of_pos (a : Ordinal.{u}) {b : Ordinal.{u}} (hb : 0 < b) : a ≤ a ×ⱼ b := by
  conv => lhs; rw [← jmul_one a]
  exact jmul_le_jmul Ordinal.le_rfl (succ_le_of_lt hb)

theorem le_jmul_of_pos_left {a : Ordinal.{u}} (b : Ordinal.{u}) (ha : 0 < a) : b ≤ a ×ⱼ b := by
  conv => lhs; rw [← one_jmul b]
  exact jmul_le_jmul (succ_le_of_lt ha) Ordinal.le_rfl

/-! ## Ranks of well-founded relations -/

section ofWf

variable {A : Type u} {r : A → A → Prop}

@[lantana_alias ordinal_copy_facts.ord_from_wf_lt_one]
theorem ofWf_lt_one (hwf : WellFounded r) {a0 a1 : A} (h : r a0 a1) :
    ofWf hwf a0 +ₕ 1 ≤ ofWf hwf a1 :=
  nadd_one_le_of_lt (ofWf_lt_ofWf hwf h)

@[lantana_alias ordinal_copy_facts.ord_from_wf_set_one]
theorem ofWf_nadd_one_le_type (hwf : WellFounded r) (a : A) : ofWf hwf a +ₕ 1 ≤ type hwf :=
  nadd_one_le_of_lt (ofWf_lt_type hwf a)

end ofWf

/-- The rank of `n` for `<` on `Nat` is `n` (snu-sf: `Ord.from_nat_from_peano_lt`). -/
theorem ofWf_nat (hwf : WellFounded (α := Nat) (· < ·)) (n : Nat) : ofWf hwf n = ofNat n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    refine Ordinal.ext fun c => ⟨fun hc => ?_, fun hc => ?_⟩
    · obtain ⟨m, hm, hc⟩ := (lt_ofWf_iff hwf).mp hc
      rw [ih m hm] at hc
      exact Ordinal.lt_of_le_of_lt hc (ofNat_lt_ofNat_iff.mpr hm)
    · obtain ⟨m, rfl⟩ := lt_omega_iff.mp (Ordinal.lt_trans hc (ofNat_lt_omega n))
      have hm := ofNat_lt_ofNat_iff.mp hc
      exact (lt_ofWf_iff hwf).mpr ⟨m, hm, Ordinal.le_of_eq (ih m hm).symm⟩

end Ordinals.Ordinal

namespace Lantana

open Ordinals Ordinal

/-- The layers of obligations (Rocq `layer`, the copy `ord.t`). -/
abbrev Layer := Ordinal.{0}

/-- Fuel, credits and ranks (Rocq `Ord.t`). -/
abbrev Fuel := Ordinal.{1}

/-! ## The fair-scheduler bound -/

/-- The bound `(ω ×ⱼ a) +ₕ ω` of the fair-scheduler measure: the inflationary function `η` of
`▽`. -/
@[lantana_alias fair_measure_ub]
def fairMeasureUb (a : Fuel) : Fuel :=
  ω ×ⱼ a +ₕ ω

theorem lt_fairMeasureUb (a : Fuel) : a < fairMeasureUb a :=
  Ordinal.lt_of_le_of_lt (le_jmul_of_pos_left a zero_lt_omega)
    (lt_nadd_of_pos_right _ zero_lt_omega)

@[lantana_alias fair_measure_ub_mono]
theorem le_fairMeasureUb (a : Fuel) : a ≤ fairMeasureUb a :=
  Ordinal.le_of_lt (lt_fairMeasureUb a)

@[lantana_alias fair_measure_ub_lt_proper]
theorem fairMeasureUb_lt_mono {a b : Fuel} (h : a < b) : fairMeasureUb a < fairMeasureUb b :=
  nadd_lt_nadd_right (jmul_lt_jmul_of_pos_left h zero_lt_omega) ω

@[lantana_alias fair_measure_ub_le_proper]
theorem fairMeasureUb_le_mono {a b : Fuel} (h : a ≤ b) : fairMeasureUb a ≤ fairMeasureUb b :=
  nadd_le_nadd (jmul_le_jmul Ordinal.le_rfl h) Ordinal.le_rfl

/-- The measure of thread `i` for a fair scheduler whose counters are `γ`. -/
@[lantana_alias fair_measure]
def fairMeasure (γ : Nat → Nat) (i : Nat) (a : Fuel) : Fuel :=
  ω ×ⱼ a +ₕ ofNat (γ i)

@[lantana_alias fair_measure_mon_gen]
theorem fairMeasure_lt_mono {γ1 γ2 : Nat → Nat} {i j : Nat} {a b : Fuel} (h : a < b) :
    fairMeasure γ1 i a < fairMeasure γ2 j b := by
  refine Ordinal.lt_of_lt_of_le (nadd_lt_nadd_left (ofNat_lt_omega (γ1 i)) (ω ×ⱼ a)) ?_
  refine Ordinal.le_trans ?_ (le_self_nadd (ω ×ⱼ b) _)
  rw [nadd_comm, ← jmul_succ]
  exact jmul_le_jmul Ordinal.le_rfl (succ_le_of_lt h)

@[lantana_alias fair_measure_le_ub]
theorem fairMeasure_le_ub (γ : Nat → Nat) (i : Nat) (a : Fuel) :
    fairMeasure γ i a ≤ fairMeasureUb a :=
  nadd_le_nadd Ordinal.le_rfl (Ordinal.le_of_lt (ofNat_lt_omega (γ i)))

#lantana_ignore fair_measure_mon "special case of `fairMeasure_lt_mono`"
#lantana_ignore ord_mono_fun_class "decision D5: `fairMeasureUb` is used directly, no class"
#lantana_ignore ordinal_copy_facts.ord_mono_fun_class
  "decision D5: `fairMeasureUb` is used directly, no class"
#lantana_ignore fair_measure_ub_ord_mono_fun_class
  "decision D5: `fairMeasureUb` is used directly, no class"
#lantana_ignore ordinal_copy_facts.limit_fun "`Ordinal.sup`"
#lantana_ignore ordinal_copy_facts.limit_fun_upperbound "`Ordinal.le_sup`"
#lantana_ignore ordinal_copy_facts.limit_fun_supremum "`Ordinal.sup_le`"
#lantana_ignore ordinal_copy_facts.jacobsthal_expn_omega "unused in Lantana-Rocq"
#lantana_ignore ordinal_copy_facts.jacobsthal_expn_square "unused in Lantana-Rocq"
#lantana_ignore ordinal_copy_facts.unit_mult_omega_lt_one "unused in Lantana-Rocq"
#lantana_ignore ordinal_copy_facts.unit_mult_omega_lt_zero "unused in Lantana-Rocq"
#lantana_ignore ordinal_copy_facts.unit_mult_omega_le_omega "unused in Lantana-Rocq"
#lantana_ignore ordinal_copy_facts.jacobsthal_expn_nat "unused in Lantana-Rocq"
#lantana_ignore ordinal_copy_facts.jacobsthal_expn_nat_spec "unused in Lantana-Rocq"

end Lantana
