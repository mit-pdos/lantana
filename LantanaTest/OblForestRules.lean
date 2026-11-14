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

/-- Allocating an obligation below a thread and into its bill, and checking its witness. -/
example (E : CoPset) (i : ThreadId) (K G : Oids) (ℓ : Layer) (μ : Measure) :
    (thKids i K ∗ thCarriers i G : IProp GF) ⊢ |={E}=>m ∃ k : Oid, thKids i (K.insert k) ∗
      thCarriers i (G.insert k) ∗ Obl.assigned k (Qp.half 1) ∗
      (Wit.cred k 0 ∨ Obl.discharged k) := by
  iintro ⟨T, HG⟩
  ihave B := parLe_thread (GF := GF) i ℓ
  imod obl_alloc_assigned E (.thread i) K G ℓ μ $$ B T HG with ⟨%k, %_, T, HG, -, A, -, #W, -⟩
  imod Obl.check_witness E k ℓ $$ W with C
  imodintro
  iexists k
  iframe T HG A C

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

open Iris.Std LawfulSet in
/-- Discharging the whole forest below thread `i` in one model update: a chain of two
obligations (`b` a child of `a`, a child of `i`) and a second child `c` of `i`. -/
example (E : CoPset) (i : ThreadId) (a b c : Oid) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (thKids i ({a} ∪ {c}) ∗ oblKids a {b} ∗ oblKids b ∅ ∗ oblKids c ∅ ∗ Obl.assigned a 1 ∗
      Obl.assigned b 1 ∗ Obl.assigned c 1 : IProp GF) ⊢
      |={E}=>m thKids i ∅ ∗ Obl.discharged a ∗ Obl.discharged b ∗ Obl.discharged c := by
  let S : Oids := {a} ∪ ({b} ∪ {c})
  let kids : Oid → Oids := fun k => if k = a then {b} else ∅
  have hka : kids a = {b} := by simp [kids]
  have hkb : kids b = ∅ := by simp [kids, Ne.symm hab]
  have hkc : kids c = ∅ := by simp [kids, Ne.symm hac]
  have hS : ∀ x, x ∈ S ↔ x = a ∨ x = b ∨ x = c := fun x => by
    simp only [S, mem_union, mem_singleton]
  have h₁ : ({a} : Oids) ## ({b} ∪ {c}) := fun x ⟨hx, hx'⟩ => by
    rw [mem_singleton] at hx
    rw [mem_union, mem_singleton, mem_singleton] at hx'
    grind
  have h₂ : ({b} : Oids) ## {c} := fun x ⟨hx, hx'⟩ => by
    rw [mem_singleton] at hx hx'
    exact hbc (hx.symm.trans hx')
  have hK : ∀ j, j ∈ [i] → ({a} ∪ {c} : Oids) ⊆ S := fun _ _ x hx => by
    rw [mem_union, mem_singleton, mem_singleton] at hx
    rw [hS]
    grind
  have hclosed : ∀ k, k ∈ S → kids k ⊆ S := fun k _ x hx => by
    by_cases hk : k = a
    · rw [hk, hka, mem_singleton] at hx
      rw [hS]
      exact .inr (.inl hx)
    · simp only [kids, hk, ite_false] at hx
      exact (mem_empty hx).elim
  have hcovered : ∀ x, x ∈ S → (∃ j, j ∈ [i] ∧ x ∈ ({a} ∪ {c} : Oids)) ∨
      ∃ k, k ∈ S ∧ x ∈ kids k := fun x hx => by
    rcases (hS x).1 hx with rfl | rfl | rfl
    · exact .inl ⟨_, List.mem_singleton_self _, mem_union.2 (.inl (mem_singleton.2 rfl))⟩
    · exact .inr ⟨a, (hS a).2 (.inl rfl), by rw [hka]; exact mem_singleton.2 rfl⟩
    · exact .inl ⟨_, List.mem_singleton_self _, mem_union.2 (.inr (mem_singleton.2 rfl))⟩
  iintro ⟨T, Ka, Kb, Kc, Aa, Ab, Ac⟩
  imod obl_discharge_forest_threads E [i] (fun _ => {a} ∪ {c}) S kids hK hclosed hcovered
    $$ [T] [Ka Kb Kc Aa Ab Ac] with ⟨T, D⟩
  · iapply BigSepL.bigSepL_singleton.2
    iexact T
  · iapply (BigSepS.bigSepS_union h₁).2
    isplitl [Ka Aa]
    · iapply BigSepS.bigSepS_singleton.2
      rw [hka]
      iframe Ka Aa
    · iapply (BigSepS.bigSepS_union h₂).2
      isplitl [Kb Ab]
      · iapply BigSepS.bigSepS_singleton.2
        rw [hkb]
        iframe Kb Ab
      · iapply BigSepS.bigSepS_singleton.2
        rw [hkc]
        iframe Kc Ac
  icases BigSepL.bigSepL_singleton.1 $$ T with T
  icases (BigSepS.bigSepS_union h₁).1 $$ D with ⟨Da, D⟩
  icases (BigSepS.bigSepS_union h₂).1 $$ D with ⟨Db, Dc⟩
  icases BigSepS.bigSepS_singleton.1 $$ Da with Da
  icases BigSepS.bigSepS_singleton.1 $$ Db with Db
  icases BigSepS.bigSepS_singleton.1 $$ Dc with Dc
  imodintro
  iframe T Da Db Dc

/-- The nodes of the threads `< 3` that satisfy `φ` are the nodes of the threads `0` and `2`. -/
example : ([∗list] j ∈ [0, 2], (thActive j ∗ thKids j ∅ : IProp GF)) ⊣⊢
    Th.nodes 3 (fun j => j = 0 ∨ j = 2) :=
  Th.nodes_list 3 (by decide) fun j => by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    grind

end

end LantanaTest.OblForestRules
