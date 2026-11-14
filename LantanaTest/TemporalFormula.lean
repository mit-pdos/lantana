/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for the temporal formulas: `iinv` opens an `alwaysI`, fractions of an until, the
guarantees inferred from the shape of a formula, the opening of a set of untils, and the axioms
of the guarantees. -/

namespace LantanaTest.TemporalFormula

open Iris Iris.BI Lantana
open Iris.ProgramLogic (Language)
open scoped Lantana.TrProp Lantana.TrSpec

variable {Expr State Obs Val : Type} {GF : BundledGFunctors} [Language Expr State Obs Val]
  [Crash Expr State Obs Val] [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF]

/-- `iinv` opens an `alwaysI` like an invariant. -/
example (N : Namespace) (P : IProp GF) [Persistent P] : alwaysI N P ⊢ |={⊤}=> ▷ P := by
  iintro #H
  iinv H with #HP Hclose
  imod Hclose $$ [] with -
  · iexact HP
  imodintro
  iexact HP

/-- An until splits into halves. -/
example (N : Namespace) (k : Oid) (P Q : IProp GF) :
    untilI N k 1 P Q ⊢ untilI N k (Qp.half 1) P Q ∗ untilI N k (Qp.half 1) P Q :=
  untilI_frac_split (Qp.half_add_half 1).symm

/-- The guarantee of a formula is inferred through `alwaysI` and `untilI`. -/
example (N : Namespace) (k : Oid) (q : Qp) (φ ψ : Prop) :
    ⊢@{IProp GF} iprop(alwaysI N iprop(⌜φ⌝) ∗ untilI N k q iprop(⌜φ⌝) iprop(⌜ψ⌝)) ⊨ₜ
      ((□ₛ ⌜φ⌝ₛ) ∧ₛ (⌜φ⌝ₛ Uₛ ⌜ψ⌝ₛ) : TrSpec Expr State GF) :=
  IntoGuar.into_guar

/-- A done until guarantees a finally. -/
example (k : Oid) (ψ : Prop) :
    ⊢@{IProp GF} untilIDone k iprop(⌜ψ⌝) ⊨ₜ (◇ₛ ⌜ψ⌝ₛ : TrSpec Expr State GF) :=
  IntoGuar.into_guar

section Sets
open Iris.ProofMode BigSepS

/-- Two untils with the namespaces `N₀.@k` open at once; after a later, the contents go back
and the halves of the assignments kept rebuild the untils. -/
example (N₀ : Namespace) (k₁ k₂ : Oid) (hk : k₁ ≠ k₂) (P Q : Oid → IProp GF) :
    untilI (N₀.@k₁) k₁ 1 (P k₁) (Q k₁) ∗ untilI (N₀.@k₂) k₂ 1 (P k₂) (Q k₂) ⊢
      |={⊤, ⊤ \ ↑N₀}=> ▷ |={⊤ \ ↑N₀, ⊤}=>
        untilI (N₀.@k₁) k₁ 1 (P k₁) (Q k₁) ∗ untilI (N₀.@k₂) k₂ 1 (P k₂) (Q k₂) := by
  have h : k₁ ∉ ({k₂} : Oids) := by simpa using hk.symm
  iintro ⟨U₁, U₂⟩
  imod untilI_acc_assigned_set_ndot (E := ⊤) CoPset.subseteq_top $$ [U₁ U₂] with ⟨H, Hclose⟩
  · iapply (bigSepS_insert h).2
    iframe U₁
    iapply bigSepS_singleton.2
    iexact U₂
  imodintro
  ihave H := bigSepS_later_2 $$ H
  inext
  icases (bigSepS_mono_of_forall fun k =>
      (sep_mono_left (Obl.assigned_halves k).1).trans sep_assoc.1).trans bigSepS_sep.1 $$ H
    with ⟨Ha, Hv⟩
  imod Hclose $$ [Hv] with Ws
  · iapply bigSepS_mono_of_forall (fun k => (or_intro_l.trans
      (Obl.variant_unfold k (P k) _).2).trans later_intro) $$ Hv
  ihave Us := bigSepS_wand $$ Ha Ws
  icases (bigSepS_insert h).1 $$ Us with ⟨U₁, Us⟩
  icases bigSepS_singleton.1 $$ Us with U₂
  imodintro
  iframe U₁ U₂

/-- A set of finallys with the namespaces `N₀.@k` opens with the whole assignments, and the
closing rebuilds them at once. -/
example (N₀ : Namespace) (S : Oids) (Q : Oid → IProp GF) :
    ([∗set] k ∈ S, finallyI (N₀.@k) k 1 (Q k)) ⊢
      |={⊤}=> [∗set] k ∈ S, finallyI (N₀.@k) k 1 (Q k) := by
  iintro Us
  imod finallyI_acc_assigned_set_ndot (E := ⊤) CoPset.subseteq_top $$ Us with ⟨H, Hclose⟩
  icases (bigSepS_mono_of_forall fun k => (Obl.assigned_halves k).1).trans bigSepS_sep.1 $$ H
    with ⟨Ha, Hv⟩
  imod Hclose $$ [Hv] with Ws
  · iapply bigSepS_mono_of_forall (fun k => (sep_true.2.trans (or_intro_l.trans
      (Obl.variant_unfold k iprop(True) _).2)).trans later_intro) $$ Hv
  imodintro
  iapply bigSepS_wand $$ Ha Ws

end Sets

/-- info: 'Lantana.guar_alwaysI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guar_alwaysI

/-- info: 'Lantana.guar_untilI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guar_untilI

end LantanaTest.TemporalFormula
