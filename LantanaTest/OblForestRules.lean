/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for the derived rules of the obligation-forest interface (M5): the proof-mode
instances of the model update `|={E₁,E₂}=>m P`, and a few derived rules in use. -/

namespace LantanaTest.OblForestRules

open Iris Iris.BI Iris.ProofMode Lantana
open scoped Lantana.Measure

section

variable {Expr State : Type} {GF : BundledGFunctors} [ModelGS GF]
variable [TemporalGS Expr State GF] [StateInterp Expr State GF] [TemporalInterp Expr State GF]
variable {E E₁ E₂ : CoPset} {P Q R : IProp GF}

/-! Eliminating basic, fancy and model updates into a model update (`ElimModal`). -/

example : (|==> P) ∗ (P -∗ |={E}=>m Q) ⊢ |={E}=>m Q := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

example : (|={E₁,E₂}=> P) ∗ (P -∗ |={E₂,E₁}=>m Q) ⊢ |={E₁}=>m Q := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

example : (|={E₁,E₂}=>m P) ∗ (P -∗ |={E₂,E₁}=>m Q) ⊢ |={E₁}=>m Q := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

/-! Introduction (`FromModal`), framing (`Frame`), pure goals (`FromPure`), assumptions
(`FromAssumption`), separating conjunctions (`FromSep`), disjunctions (`FromOr`) and
existentials (`FromExists`). -/

example : P ∗ Q ⊢ |={E}=>m (Q ∗ P) := by
  iintro ⟨HP, HQ⟩
  imodintro
  iframe HP HQ

example : (|={E₁,E₂}=>m R) ∗ P ∗ Q ⊢ |={E₁,E₂}=>m (Q ∗ P ∗ R) := by
  iintro ⟨H, HP, HQ⟩
  iframe HP HQ
  iexact H

example : ⊢@{IProp GF} |={E}=>m ⌜1 + 1 = 2⌝ := by
  ipureintro
  rfl

example : (|={E}=> P) ⊢ |={E}=>m P := by
  iintro HP
  iexact HP

example : (|={E}=>m P) ∗ (|={E}=>m Q) ⊢ |={E}=>m (P ∗ Q) := by
  iintro ⟨HP, HQ⟩
  isplitl [HP]
  · iexact HP
  · iexact HQ

example : P ⊢ |={E}=>m (Q ∨ P) := by
  iintro HP
  iright
  iexact HP

example (Φ : Nat → IProp GF) : Φ 3 ⊢ |={E}=>m ∃ n, Φ n := by
  iintro H
  iexists 3
  iexact H

/-! A wand under a model update (`IntoWand`) and an update added by `ihave` (`AddModal`). -/

example : (|={E}=>m (P -∗ Q)) ∗ (|={E}=>m P) ⊢ |={E}=>m Q := by
  iintro ⟨H, HP⟩
  iapply H $$ HP

example : (P ={E}=∗m Q) ∗ P ⊢ |={E}=>m Q := by
  iintro ⟨H, HP⟩
  imod H $$ HP with HQ
  iexact HQ

/-! Except-0 (`IsExcept0`). -/

example : ◇ (|={E₁,E₂}=>m P) ⊢ |={E₁,E₂}=>m P := by
  iintro HP
  imod HP
  iexact HP

/-- A timeless hypothesis under a later is stripped in front of a model update. -/
example [Timeless P] : ▷ P ⊢ |={E}=>m P := by
  iintro HP
  imod HP
  iexact HP

/-! Later credits strip a later in front of a model update. -/

example : £ₙ 1 ∗ ▷ (|={E}=>m P) ⊢ |={E}=>m P := by
  iintro ⟨Hc, HP⟩
  iapply lc_mupd_add_later $$ Hc HP

end

/-! Derived rules of the interface in use. -/

section

variable {Expr State : Type} {GF : BundledGFunctors} [ModelGS GF]
variable [TemporalGS Expr State GF] [StateInterp Expr State GF] [TemporalInterp Expr State GF]

/-- Allocating an obligation below a thread, and checking its witness. -/
example (E : CoPset) (i : ThreadId) (K : Oids) (ℓ : Layer) (μ : Measure) :
    (thKids i K : IProp GF) ⊢ |={E}=>m ∃ k : Oid, thKids i (K.insert k) ∗
      Obl.assigned k (Qp.half 1) ∗ (Wit.cred k 0 ∨ Obl.discharged k) := by
  iintro T
  ihave B := parLe_thread (GF := GF) i ℓ
  imod obl_alloc_assigned E (.thread i) K ℓ μ $$ B T with ⟨%k, %_, T, -, A, -, #W, -⟩
  imod Obl.check_witness E k ℓ $$ W with C
  imodintro
  iexists k
  iframe T A C

/-- Witness-layer induction with an empty set of fuels. -/
example (k : Oid) (ℓ l : Layer) (hl : ℓ < l) (P : IProp GF)
    (IND : ⊢ (Wit.cred k 1 ==∗ ([∗set] g ∈ (∅ : Oids), Obl.fuel g l 1) ∗ P) ==∗ P) :
    Wit.layer k ℓ ⊢ |==> P := by
  iintro #W
  iapply Wit.layer_ind k ℓ ∅ l 1 P hl
  isplitl []
  · imodintro
    iapply IND
  isplitl []
  · iexact W
  · iapply BigSepS.bigSepS_empty.2
    iempintro

end

end LantanaTest.OblForestRules
