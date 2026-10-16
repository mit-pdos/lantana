/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Prelude.Ordinal

/-! # Measures

A `Measure` is a syntax for a subset of the ordinals, interpreted *at a layer* by `Measure.rep`
(Rocq `measure.v` and `layer.v`). All constructors but `▽` are interpreted independently of the
layer; `▽` at layer `ℓ` is `fairMeasureUb` of the supremum of all measures at all layers below
`ℓ`, so that a measure at a higher layer dominates every measure at a lower layer.

## Universes (decision D4)

* `embed` takes a well-founded relation on a type in `Type 0`, so `Measure : Type 1`, and its
  rank `ofWf hwf a : Ordinal.{0}` is lifted to `Fuel = Ordinal.{1}` with `lift.{0, 1}`. This is
  the only `lift`.
* `large` is `Ordinal.large.{0} : Ordinal.{1}`, above the lifted ranks of all well-founded
  relations on types in `Type 0` (`lift_type_lt_large` replaces Rocq's `A : SmallT`).
* `Ordinal.sup` takes an index type in the universe of the ordinals, here `Type 1`. Both index
  types of `▽` are there without lifting: `Measure : Type 1` and
  `{ℓ' : Layer // ℓ' < ℓ} : Type 1` (because `Layer = Ordinal.{0} : Type 1`). This is why layers
  sit exactly one universe below fuel.

`rep` is defined by well-founded recursion on the layer (`WellFounded.fix`) with an inner
structural recursion on the measure (`repAt`); `rep_unfold` is `WellFounded.fix_eq`, so Rocq's
`measure_rep_rec_proof_irrelevance` is not needed. `rep` is irreducible (decision D25): use the
reduction lemmas.
-/

@[expose] public section

noncomputable section

namespace Lantana

open Ordinals Ordinal

universe u

/-- A syntax for a subset of the ordinals (Rocq `measure`). -/
@[lantana_alias measure]
inductive Measure : Type 1 where
  /-- The rank of `a` for a well-founded relation `r` (Rocq `ms_embed`, notation `⟪hwf, a⟫`). -/
  | embed {A : Type} {r : A → A → Prop} (hwf : WellFounded r) (a : A)
  /-- An ordinal above all embedded ranks (Rocq `ms_large`, notation `ℵ`). -/
  | large
  /-- The natural sum (Rocq `ms_add`, notation `+`). -/
  | add (s1 s2 : Measure)
  /-- The Jacobsthal product (Rocq `ms_mult`, notation `*`). -/
  | mul (s1 s2 : Measure)
  /-- The Jacobsthal power (Rocq `ms_expn`, notation `^`). -/
  | pow (s1 s2 : Measure)
  /-- Above all measures at lower layers (Rocq `ms_extend`, notation `▽`). -/
  | extend

attribute [lantana_alias ms_embed] Measure.embed
attribute [lantana_alias ms_large] Measure.large
attribute [lantana_alias ms_add] Measure.add
attribute [lantana_alias ms_mult] Measure.mul
attribute [lantana_alias ms_expn] Measure.pow
attribute [lantana_alias ms_extend] Measure.extend

namespace Measure

/-- The natural number `n`: its rank for `<` (Rocq `ms_nat`). -/
@[lantana_alias ms_nat]
def ofNat (n : Nat) : Measure :=
  embed (r := (· < ·)) Nat.lt_wfRel.wf n

instance : Add Measure := ⟨add⟩
instance : Mul Measure := ⟨mul⟩
instance : Pow Measure Measure := ⟨pow⟩
instance : NatCast Measure := ⟨ofNat⟩
instance (n : Nat) : OfNat Measure n := ⟨ofNat n⟩

@[inherit_doc] scoped notation "ℵ" => Measure.large
@[inherit_doc] scoped notation "▽" => Measure.extend
@[inherit_doc] scoped notation "⟪" hwf ", " a "⟫" => Measure.embed hwf a

/-- Induction on measures, with the cases written in notation (`s1 + s2` rather than
`add s1 s2`), so that the lemmas about the notation apply. -/
@[elab_as_elim, induction_eliminator]
protected def recAux {motive : Measure → Sort u}
    (embed : ∀ {A : Type} {r : A → A → Prop} (hwf : WellFounded r) (a : A), motive ⟪hwf, a⟫)
    (large : motive ℵ)
    (add : ∀ s1 s2, motive s1 → motive s2 → motive (s1 + s2))
    (mul : ∀ s1 s2, motive s1 → motive s2 → motive (s1 * s2))
    (pow : ∀ s1 s2, motive s1 → motive s2 → motive (s1 ^ s2))
    (extend : motive ▽) (μ : Measure) : motive μ :=
  Measure.rec embed large add mul pow extend μ

/-! ## Interpretation -/

/-- The interpretation at layer `ℓ`, given the interpretation `rec` at the layers below `ℓ`. -/
def repAt (ℓ : Layer) (rec : ∀ ℓ' : Layer, ℓ' < ℓ → Measure → Fuel) : Measure → Fuel
  | embed hwf a => lift.{0, 1} (ofWf hwf a)
  | large => Ordinal.large.{0}
  | add s1 s2 => repAt ℓ rec s1 +ₕ repAt ℓ rec s2
  | mul s1 s2 => repAt ℓ rec s1 ×ⱼ repAt ℓ rec s2
  | pow s1 s2 => repAt ℓ rec s1 ^ⱼ repAt ℓ rec s2
  | extend => fairMeasureUb (sup fun ℓ' : {ℓ' : Layer // ℓ' < ℓ} => sup (rec ℓ'.1 ℓ'.2))

/-- The interpretation of a measure at a layer (Rocq `measure_rep`). -/
@[lantana_alias measure_rep, irreducible]
def rep : Layer → Measure → Fuel :=
  Ordinal.lt_wf.fix repAt

/-- The supremum of all measures at a layer (Rocq `measure_rep_top`). -/
@[lantana_alias measure_rep_top]
def repTop (ℓ : Layer) : Fuel :=
  sup (rep ℓ)

variable {ℓ ℓ1 ℓ2 : Layer}

@[lantana_alias measure_rep_unfold]
theorem rep_unfold (ℓ : Layer) (μ : Measure) : rep ℓ μ = repAt ℓ (fun ℓ' _ => rep ℓ') μ := by
  unfold rep
  rw [WellFounded.fix_eq]

/-! ### Reduction rules -/

@[lantana_alias measure_rep_embed]
theorem rep_embed (ℓ : Layer) {A : Type} {r : A → A → Prop} (hwf : WellFounded r) (a : A) :
    rep ℓ ⟪hwf, a⟫ = lift.{0, 1} (ofWf hwf a) := by
  rw [rep_unfold]; rfl

@[lantana_alias measure_rep_large]
theorem rep_large (ℓ : Layer) : rep ℓ ℵ = Ordinal.large.{0} := by
  rw [rep_unfold]; rfl

@[lantana_alias measure_rep_add]
theorem rep_add (ℓ : Layer) (s1 s2 : Measure) : rep ℓ (s1 + s2) = rep ℓ s1 +ₕ rep ℓ s2 := by
  rw [rep_unfold, rep_unfold ℓ s1, rep_unfold ℓ s2]; rfl

@[lantana_alias measure_rep_mult]
theorem rep_mul (ℓ : Layer) (s1 s2 : Measure) : rep ℓ (s1 * s2) = rep ℓ s1 ×ⱼ rep ℓ s2 := by
  rw [rep_unfold, rep_unfold ℓ s1, rep_unfold ℓ s2]; rfl

@[lantana_alias measure_rep_expn]
theorem rep_pow (ℓ : Layer) (s1 s2 : Measure) : rep ℓ (s1 ^ s2) = rep ℓ s1 ^ⱼ rep ℓ s2 := by
  rw [rep_unfold, rep_unfold ℓ s1, rep_unfold ℓ s2]; rfl

theorem rep_extend_eq (ℓ : Layer) :
    rep ℓ ▽ = fairMeasureUb (sup fun ℓ' : {ℓ' : Layer // ℓ' < ℓ} => repTop ℓ'.1) := by
  rw [rep_unfold]; rfl

/-! ### The top of a layer and `▽` -/

@[lantana_alias measure_rep_top_upperbound]
theorem le_repTop (ℓ : Layer) (μ : Measure) : rep ℓ μ ≤ repTop ℓ :=
  le_sup (rep ℓ) μ

@[lantana_alias measure_rep_top_lt_extend]
theorem repTop_lt_extend (h : ℓ1 < ℓ2) : fairMeasureUb (repTop ℓ1) ≤ rep ℓ2 ▽ := by
  rw [rep_extend_eq]
  exact fairMeasureUb_le_mono (le_sup (fun ℓ' : {ℓ' // ℓ' < ℓ2} => repTop ℓ'.1) ⟨ℓ1, h⟩)

@[lantana_alias measure_rep_top_lt]
theorem repTop_lt (h : ℓ1 < ℓ2) : fairMeasureUb (repTop ℓ1) ≤ repTop ℓ2 :=
  Ordinal.le_trans (repTop_lt_extend h) (le_repTop ℓ2 ▽)

@[lantana_alias measure_rep_extend]
theorem rep_extend (h : ℓ1 < ℓ2) (t : Measure) : fairMeasureUb (rep ℓ1 t) ≤ rep ℓ2 ▽ :=
  Ordinal.le_trans (fairMeasureUb_le_mono (le_repTop ℓ1 t)) (repTop_lt_extend h)

@[lantana_alias measure_rep_extend_alt]
theorem rep_extend_alt {o : Fuel} (h : ℓ1 < ℓ2) (t : Measure) (ho : o ≤ fairMeasureUb (rep ℓ1 t)) :
    o ≤ rep ℓ2 ▽ :=
  Ordinal.le_trans ho (rep_extend h t)

/-! ### Properties -/

@[lantana_alias measure_rep_embed_lt]
theorem rep_embed_lt (ℓ : Layer) {A : Type} {r : A → A → Prop} (hwf : WellFounded r) {a1 a2 : A}
    (h : r a1 a2) : rep ℓ ⟪hwf, a1⟫ < rep ℓ ⟪hwf, a2⟫ := by
  rw [rep_embed, rep_embed]
  exact lift_lt_lift_iff.mpr (ofWf_lt_ofWf hwf h)

@[lantana_alias measure_rep_large_lt]
theorem rep_large_lt (ℓ : Layer) {A : Type} {r : A → A → Prop} (hwf : WellFounded r) (a : A) :
    rep ℓ ⟪hwf, a⟫ < rep ℓ ℵ := by
  rw [rep_embed, rep_large]
  exact Ordinal.lt_trans (lift_lt_lift_iff.mpr (ofWf_lt_type hwf a)) (lift_type_lt_large hwf)

@[lantana_alias measure_rep_layer_le]
theorem rep_layer_le (h : ℓ1 ≤ ℓ2) (μ : Measure) : rep ℓ1 μ ≤ rep ℓ2 μ := by
  induction μ with
  | embed => rw [rep_embed, rep_embed]
  | large => rw [rep_large, rep_large]
  | add s1 s2 ih1 ih2 => rw [rep_add, rep_add]; exact nadd_le_nadd ih1 ih2
  | mul s1 s2 ih1 ih2 => rw [rep_mul, rep_mul]; exact jmul_le_jmul ih1 ih2
  | pow s1 s2 ih1 ih2 => rw [rep_pow, rep_pow]; exact jpow_le_jpow ih1 ih2
  | extend =>
    rw [rep_extend_eq, rep_extend_eq]
    refine fairMeasureUb_le_mono (sup_le_sup_of_forall_exists fun ℓ' => ?_)
    exact ⟨⟨ℓ'.1, Ordinal.lt_of_lt_of_le ℓ'.2 h⟩, Ordinal.le_rfl⟩

/-! ### Natural numbers -/

@[lantana_alias measure_rep_nat]
theorem rep_nat (ℓ : Layer) (n : Nat) : rep ℓ (n : Measure) = (n : Fuel) := by
  rw [show (n : Measure) = ⟪Nat.lt_wfRel.wf, n⟫ from rfl, rep_embed, ofWf_nat, lift_ofNat]
  rfl

theorem rep_ofNat (ℓ : Layer) (n : Nat) :
    rep ℓ (no_index (OfNat.ofNat n) : Measure) = (OfNat.ofNat n : Fuel) :=
  rep_nat ℓ n

@[lantana_alias measure_rep_nat_add]
theorem rep_nat_add (ℓ : Layer) (n1 n2 : Nat) :
    rep ℓ ((n1 + n2 : Nat) : Measure) = rep ℓ (n1 : Measure) +ₕ rep ℓ (n2 : Measure) := by
  rw [rep_nat, rep_nat, rep_nat]
  exact (nadd_ofNat n1 n2).symm

@[lantana_alias measure_rep_nat_S]
theorem rep_nat_succ (ℓ : Layer) (n : Nat) :
    rep ℓ ((n + 1 : Nat) : Measure) = rep ℓ (1 : Measure) +ₕ rep ℓ (n : Measure) := by
  rw [Nat.add_comm]
  exact rep_nat_add ℓ 1 n

/-! ### Layers dominate (Rocq `opreds.v`) -/

/-- A `▽` at a higher layer dominates every measure at a lower layer. -/
@[lantana_alias omodel.layer_dominates]
theorem layer_dominates {ℓq ℓ : Layer} (μq : Measure) (h : ℓq < ℓ) : rep ℓq μq < rep ℓ ▽ :=
  Ordinal.lt_of_le_of_lt (le_repTop ℓq μq)
    (Ordinal.lt_of_lt_of_le (lt_fairMeasureUb _) (repTop_lt_extend h))

@[lantana_alias omodel.layer_le_bound]
theorem layer_le_bound {ℓq ℓ : Layer} (μq : Measure) (h : ℓq ≤ ℓ) : rep ℓq μq < rep ℓ (μq + 1) := by
  rw [rep_add, rep_ofNat]
  exact Ordinal.lt_of_le_of_lt (rep_layer_le h μq) (lt_nadd_of_pos_right _ zero_lt_one)

end Measure

#lantana_ignore layer_class "layers are `Layer = Ordinal.{0}`"
#lantana_ignore layer_layer_class "layers are `Layer = Ordinal.{0}`"
#lantana_ignore L_sub "the subtype `{ℓ' : Layer // ℓ' < ℓ}`"
#lantana_ignore measure_rep_rec "`Measure.repAt` under `WellFounded.fix`"
#lantana_ignore measure_rep_rec_oblig "the subtype's property"
#lantana_ignore measure_rep_rec_proof_irrelevance
  "`Measure.rep_unfold` follows from `WellFounded.fix_eq`"
#lantana_ignore measure_rep_layer_eq "layers have Leibniz equality: rewrite"
#lantana_ignore measure_rep_layer_le_proper "`Measure.rep_layer_le` (layers are a linear order)"

end Lantana
