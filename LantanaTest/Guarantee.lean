/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for temporal guarantees: the opacity of the one-step property and the bundle for
`inext`, and small uses of the rules and of the canonical specification. -/

namespace LantanaTest.Guarantee

open Iris Iris.BI Lantana
open scoped Lantana.TrProp Lantana.TrSpec

variable {Expr State Val : Type} {GF : BundledGFunctors} [Language Expr State Val]
  [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF]

/-- `inext` keeps the one-step property and the bundle as they are: their certificates'
laters are not stripped. -/
example (Sys : SysT Expr State GF) (l : List (Nat × RegEntry)) (n : Nat) :
    sysStep Sys ∗ bundle (Expr := Expr) (State := State) l n ⊢
      ▷ (sysStep Sys ∗ bundle (Expr := Expr) (State := State) l n) := by
  iintro ⟨#ST, #B⟩
  inext
  isplitl []
  · iexact ST
  · iexact B

/-- Pure facts combine. -/
example (φ ψ : Prop) :
    ⊢@{IProp GF} iprop(⌜φ⌝ ∗ ⌜ψ⌝) ⊨ₜ (⌜φ⌝ₛ ∧ₛ ⌜ψ⌝ₛ : TrSpec Expr State GF) := by
  iapply guar_sep $$ [] []
  · iapply guar_pure
  · iapply guar_pure

/-- An until is fulfilled by its right formula at once. -/
example (G : TrSpec Expr State GF) (φ : Prop) :
    ⊢@{IProp GF} iprop(⌜φ⌝) ⊨ₜ (G 𝒰ₛ ⌜φ⌝ₛ) := by
  iapply guar_until_now
  inext
  iapply guar_pure

/-- The canonical specification is below every guaranteed one. An application of a lemma
whose conclusion is `⊑ₛ` has its trailing instance arguments (those of `⊑ₛ`) filled with the
ambient instances, so the expected `⊑ₛ` must be matched without elaborating the application
against it (here with `@`). -/
example (Q : IProp GF) : TrSpec.canon Q ⊑ₛ (TrSpec.true : TrSpec Expr State GF) :=
  @TrSpec.canon_le _ _ _ _ _ _ _ _ _ _ guar_true

example (Q : IProp GF) : TrSpec.canon Q ⊑ₛ (TrSpec.true : TrSpec Expr State GF) :=
  @Iff.mp _ _ (guar_canon_complete Q TrSpec.true) guar_true

example (Q : IProp GF) : trCanon (Expr := Expr) (State := State) Q ⊆ ⌜True⌝ₜ :=
  (trCanon_le Q _).mpr ⟨TrSpec.true, guar_true, fun _ h => h⟩

end LantanaTest.Guarantee
