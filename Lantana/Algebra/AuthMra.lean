/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Prelude.Ordinal
public import Iris.Algebra.Auth
public import Iris.Algebra.Mra
public import Iris.Algebra.Updates
public import Iris.Algebra.IsOp

/-! # Authoritative monotone knowledge

The camera `AuthMra R` of authoritative monotone knowledge (Rocq `auth_mra.v`): `●AM[R] a` owns
the current value `a`, and `◯AM[R] b` knows that `R b a`. The value can only grow along `R`
(`AuthMra.update`). It is the authoritative camera over Iris-Lean's monotone camera `Mra R`, and
the lemmas follow Iris-Lean's `MonoNat` (`Iris.Algebra.Lib.MonoNat`).

Rocq's class `auth_mra_class` of the properties of `R` (a preorder, antisymmetric for an
equivalence, proper) becomes the side conditions `[Std.Refl R]`, `[Trans R R R]` and
`[Antisymmetric (· = ·) R]` of each lemma, with Leibniz equality. Rocq's lexicographic order
`lex_R EA RA RB` is `AuthMra.lex RA RB` with `EA := Eq` (a `Prod.Lex` of the strict part of `RA`
and `RB`), and the instance for ordinals is `≤` on `Ordinal` (used with `Layer`).
-/

@[expose] public noncomputable section

namespace Lantana

open Iris CMRA Mra Auth
open Iris.Std (Antisymmetric)

universe u v

/-- `toMra a • toMra b ≼ toMra a` gives `R b a` for a preorder `R`. -/
@[lantana_alias to_mra_op_included_R]
theorem toMra_op_included {α : Type u} {R : α → α → Prop} [Std.Refl R] [Trans R R R] {a b : α}
    (h : toMra (R := R) a • toMra b ≼ toMra a) : R b a :=
  (toMra_inc_iff b a).mp (inc_trans (inc_op_right _ _) h)

/-- The camera of authoritative monotone knowledge over `R` (Rocq `auth_mra`). -/
@[lantana_alias auth_mra]
abbrev AuthMra {α : Type u} (R : α → α → Prop) := Auth (Mra R)

#lantana_ignore auth_mraR "Use the `AuthMra` type and its `CMRA` instance"
#lantana_ignore auth_mraUR "Use the `AuthMra` type and its `UCMRA` instance"

namespace AuthMra

variable {α : Type u}

/-- The authoritative value `a`, with fraction `dq` (Rocq `auth_mra_auth`). It includes the
knowledge of `a`. -/
@[lantana_alias auth_mra_auth]
def auth (R : α → α → Prop) (dq : DFrac) (a : α) : AuthMra R :=
  (●{dq} toMra a) • ◯ toMra a

/-- The knowledge that the authoritative value is above `a` (Rocq `auth_mra_know`). -/
@[lantana_alias auth_mra_know]
def know (R : α → α → Prop) (a : α) : AuthMra R :=
  ◯ toMra a

@[inherit_doc auth] scoped notation "●AM{" dq "}[" R "] " a => auth R dq a
@[inherit_doc auth] scoped notation "●AM[" R "] " a => auth R (DFrac.own 1) a
@[inherit_doc auth] scoped notation "●AM□[" R "] " a => auth R DFrac.discard a
@[inherit_doc know] scoped notation "◯AM[" R "] " a => know R a

#lantana_ignore auth_mra_class "the side conditions `[Std.Refl R] [Trans R R R]` and \
  `[Antisymmetric (· = ·) R]` of each lemma (Leibniz equality)"
#lantana_ignore auth_mra_R_PreOrder "`[Std.Refl R] [Trans R R R]`"
#lantana_ignore auth_mra_equiv_Reflexive "Leibniz equality"
#lantana_ignore auth_mra_AntiSymm "`[Antisymmetric (· = ·) R]`"
#lantana_ignore auth_mra_Proper "Leibniz equality"
#lantana_ignore auth_mra_eq_class "the side conditions `[Std.Refl R] [Trans R R R]` and \
  `[Antisymmetric (· = ·) R]` of each lemma (Leibniz equality)"
#lantana_ignore auth_mra_eq_R_PreOrder "`[Std.Refl R] [Trans R R R]`"
#lantana_ignore auth_mra_eq_AntiSymm "`[Antisymmetric (· = ·) R]`"
#lantana_ignore auth_mra_eq_Proper "Leibniz equality"
#lantana_ignore auth_mra_eq_instance "Leibniz equality"

variable {R : α → α → Prop} {a a' a₁ a₂ b : α} {dq dq₁ dq₂ : DFrac}

/-! ## Core and composition -/

@[lantana_alias auth_mra_know_core_id]
instance know_coreId : CoreId (◯AM[R] a) := by
  unfold know
  infer_instance

@[lantana_alias auth_mra_auth_core_id]
instance auth_coreId : CoreId (●AM□[R] a) := by
  unfold auth
  infer_instance

@[lantana_alias auth_mra_auth_dfrac_op]
theorem auth_dfrac_op (dq₁ dq₂ : DFrac) (a : α) :
    (●AM{dq₁ • dq₂}[R] a) = (●AM{dq₁}[R] a) • (●AM{dq₂}[R] a) := by
  unfold auth
  rw [← CMRA.assoc', CMRA.op_core_right_of_inc (CMRA.inc_op_right ..), CMRA.assoc',
    ← Auth.auth_dfrac_op]

/-- Knowledge of a value includes the knowledge of the values below it. -/
@[lantana_alias auth_mra_know_op, lantana_alias auth_mra_know_op_R_l]
theorem know_op [Trans R R R] (h : R a₁ a₂) : (◯AM[R] a₂) = (◯AM[R] a₁) • (◯AM[R] a₂) := by
  unfold know
  rw [← Auth.frag_op, toMra_op_of_rel a₁ a₂ h]

@[lantana_alias auth_mra_auth_know_op]
theorem auth_know_op (dq : DFrac) (a : α) : (●AM{dq}[R] a) = (●AM{dq}[R] a) • (◯AM[R] a) :=
  (CMRA.op_core_left_of_inc (CMRA.inc_op_right ..)).symm

set_option synthInstance.checkSynthOrder false in
@[lantana_alias auth_mra_auth_dfrac_is_op]
instance auth_isOp {d} [h : IsOp d dq dq₁ dq₂] :
    IsOp d (●AM{dq}[R] a) (●AM{dq₁}[R] a) (●AM{dq₂}[R] a) where
  is_op := by rw [h.is_op]; exact auth_dfrac_op ..

set_option synthInstance.checkSynthOrder false in
@[lantana_alias auth_mra_know_R_is_op]
instance know_isOp {d} [h : IsOp d (toMra (R := R) a) (toMra a₁) (toMra a₂)] :
    IsOp d (◯AM[R] a) (◯AM[R] a₁) (◯AM[R] a₂) where
  is_op := by unfold know; rw [h.is_op]; exact Auth.frag_op

/-! ## Validity -/

@[lantana_alias auth_mra_auth_dfrac_valid]
theorem auth_dfrac_valid : ✓ (●AM{dq}[R] a) ↔ ✓ dq :=
  Auth.both_dfrac_valid_discrete.trans ⟨And.left, fun h => ⟨h, CMRA.inc_refl _, trivial⟩⟩

@[lantana_alias auth_mra_auth_valid]
theorem auth_valid : ✓ (●AM[R] a) :=
  auth_dfrac_valid.mpr DFrac.valid_own_one

@[lantana_alias auth_mra_auth_dfrac_op_valid]
theorem auth_dfrac_op_valid [Std.Refl R] [Antisymmetric (· = ·) R] :
    ✓ ((●AM{dq₁}[R] a₁) • (●AM{dq₂}[R] a₂)) ↔ ✓ (dq₁ • dq₂) ∧ a₁ = a₂ := by
  constructor
  · intro h
    unfold auth at h
    have ⟨hdq, heq, _⟩ := Auth.auth_dfrac_op_valid.mp <|
      CMRA.valid_of_inc (CMRA.op_mono (CMRA.inc_op_left ..) (CMRA.inc_op_left ..)) h
    exact ⟨hdq, toMra_injective heq⟩
  · rintro ⟨hdq, rfl⟩
    exact auth_dfrac_op dq₁ dq₂ a₁ ▸ auth_dfrac_valid.mpr hdq

@[lantana_alias auth_mra_auth_op_valid]
theorem auth_op_valid [Std.Refl R] [Antisymmetric (· = ·) R] :
    ✓ ((●AM[R] a₁) • (●AM[R] a₂)) ↔ False :=
  auth_dfrac_op_valid.trans
    ⟨fun ⟨h, _⟩ => DFrac.own_whole_exclusive.exclusive0_l _ h.validN, False.elim⟩

@[lantana_alias auth_mra_both_dfrac_valid]
theorem both_dfrac_valid [Std.Refl R] [Trans R R R] :
    ✓ ((●AM{dq}[R] a) • (◯AM[R] b)) ↔ ✓ dq ∧ R b a := by
  unfold auth know
  rw [← CMRA.assoc', ← Auth.frag_op, Auth.both_dfrac_valid_discrete]
  refine ⟨fun ⟨hdq, hinc, _⟩ => ⟨hdq, toMra_op_included hinc⟩, fun ⟨hdq, h⟩ => ⟨hdq, ?_, trivial⟩⟩
  rw [CMRA.comm', toMra_op_of_rel b a h]
  exact CMRA.inc_refl _

@[lantana_alias auth_mra_both_valid]
theorem both_valid [Std.Refl R] [Trans R R R] : ✓ ((●AM[R] a) • (◯AM[R] b)) ↔ R b a :=
  both_dfrac_valid.trans ⟨And.right, fun h => ⟨DFrac.valid_own_one, h⟩⟩

/-! ## Inclusion and updates -/

@[lantana_alias auth_mra_know_mono]
theorem know_mono [Trans R R R] (h : R a₁ a₂) : (◯AM[R] a₁) ≼ (◯AM[R] a₂) :=
  ⟨◯AM[R] a₂, know_op h⟩

@[lantana_alias auth_mra_included]
theorem included (dq : DFrac) (a : α) : (◯AM[R] a) ≼ (●AM{dq}[R] a) :=
  CMRA.inc_op_right ..

/-- The authoritative value grows along `R`. -/
@[lantana_alias auth_mra_update]
theorem update [Trans R R R] (h : R a a') : (●AM[R] a) ~~> (●AM[R] a') :=
  Auth.auth_update (local_update_grow a _ a' h)

@[lantana_alias auth_mra_auth_persist]
theorem auth_persist (a : α) (dq : DFrac) : (●AM{dq}[R] a) ~~> (●AM□[R] a) :=
  Update.op Auth.auth_update_auth_persist (fun _ _ h => h)

@[lantana_alias auth_mra_auth_unpersist]
theorem auth_unpersist (a : α) :
    (●AM□[R] a) ~~>: fun k => ∃ q, k = (●AM{DFrac.own q}[R] a) :=
  Auth.auth_updateP_both_unpersist


/-! ## The lexicographic order -/

section Lex

variable {β : Type v}

/-- The lexicographic order on pairs (Rocq `lex_R` with `EA := Eq`): the first components are
strictly ordered by `RA`, or equal with the second ones ordered by `RB`. -/
@[lantana_alias lex_R]
def lex (RA : α → α → Prop) (RB : β → β → Prop) : α × β → α × β → Prop :=
  Prod.Lex (fun a₀ a₁ => RA a₀ a₁ ∧ a₀ ≠ a₁) RB

variable {RA : α → α → Prop} {RB : β → β → Prop}

theorem lex_iff {x y : α × β} :
    lex RA RB x y ↔ (RA x.1 y.1 ∧ x.1 ≠ y.1) ∨ (x.1 = y.1 ∧ RB x.2 y.2) :=
  Prod.lex_def

@[lantana_alias lex_R_left]
theorem lex.left {a₀ a₁ : α} (b₀ b₁ : β) (h : RA a₀ a₁) (hne : a₀ ≠ a₁) :
    lex RA RB (a₀, b₀) (a₁, b₁) :=
  Prod.Lex.left b₀ b₁ ⟨h, hne⟩

@[lantana_alias lex_R_right]
theorem lex.right (a : α) {b₀ b₁ : β} (h : RB b₀ b₁) : lex RA RB (a, b₀) (a, b₁) :=
  Prod.Lex.right a h

@[lantana_alias lex_R_Reflexive]
instance lex_refl [Std.Refl RB] : Std.Refl (lex RA RB) where
  refl x := Prod.Lex.right x.1 (Std.Refl.refl x.2)

@[lantana_alias lex_R_Transitive]
instance lex_trans [Trans RA RA RA] [Antisymmetric (· = ·) RA] [Trans RB RB RB] :
    Trans (lex RA RB) (lex RA RB) (lex RA RB) where
  trans {x y z} hxy hyz := by
    rw [lex_iff] at hxy hyz ⊢
    rcases hxy with ⟨hxy, nxy⟩ | ⟨exy, hxy⟩ <;> rcases hyz with ⟨hyz, nyz⟩ | ⟨eyz, hyz⟩
    · refine .inl ⟨Trans.trans hxy hyz, fun exz => nxy ?_⟩
      exact Antisymmetric.antisymm hxy (exz ▸ hyz)
    · exact .inl ⟨eyz ▸ hxy, eyz ▸ nxy⟩
    · exact .inl ⟨exy ▸ hyz, exy ▸ nyz⟩
    · exact .inr ⟨exy.trans eyz, Trans.trans hxy hyz⟩

@[lantana_alias lex_R_AntiSymm]
instance lex_antisymm [Antisymmetric (· = ·) RA] [Antisymmetric (· = ·) RB] :
    Antisymmetric (· = ·) (lex RA RB) where
  antisymm {x y} hxy hyx := by
    rw [lex_iff] at hxy hyx
    rcases hxy with ⟨hxy, nxy⟩ | ⟨exy, hxy⟩
    · rcases hyx with ⟨hyx, _⟩ | ⟨eyx, _⟩
      · exact (nxy (Antisymmetric.antisymm hxy hyx)).elim
      · exact (nxy eyx.symm).elim
    · rcases hyx with ⟨_, nyx⟩ | ⟨_, hyx⟩
      · exact (nyx exy.symm).elim
      · exact Prod.ext exy (Antisymmetric.antisymm hxy hyx)

#lantana_ignore lex_R_auth_mra_instance
  "the instances `lex_refl`, `lex_trans` and `lex_antisymm` (with `EA := Eq`)"

end Lex

/-! ## Ordinals (Rocq `ordinal_auth_mra_class`) -/

open Ordinals in
/-- `≤` on ordinals is antisymmetric for `=` (with `Std.Refl` and `Trans` from the linear
order, the conditions for the rules of `AuthMra (· ≤ ·)`). -/
@[lantana_alias ordinal_auth_mra_class]
instance ordinal_le_antisymm : Antisymmetric (α := Ordinal.{u}) (· = ·) (· ≤ ·) where
  antisymm := Ordinal.le_antisymm

end AuthMra

end Lantana
