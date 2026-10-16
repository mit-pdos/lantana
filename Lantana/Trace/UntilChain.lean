/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TemporalFormula
public import Lantana.BaseLogic.MonoListP

/-! # Chains of untils

Rocq `lantana/trace/until_chain.v`: `untilIChain N k o P Q` is `P` until `Q` or until the next
link of the chain, whose ordinal is smaller, so every chain is finite. It is defined by
well-founded recursion on the ordinal (`WellFounded.fix` on `Fuel`), so a chain is a plain
`IProp`, with no guarded fixpoint; its unfolding is `WellFounded.fix_eq`, so Rocq's proof
irrelevance of the accessibility argument is not needed. `untilChainLog` keeps the discharged
links of a chain in a monotone ghost log (`uchainAuth`, `uchainPin`) over `Oid × Fuel`, which
lives in `Type 2`: the log uses Lantana's universe-polymorphic `MonoListGP`. This is a
definitions file; the rules live with the clients.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open Lantana.Model

/-! ## Well-formed logs -/

/-- The ordinals of a log increase along it. -/
@[lantana_alias uchain_log_wf]
def uchainLogWf (l : List (Oid × Fuel)) : Prop :=
  ∀ (i : Nat) (e₁ e₂ : Oid × Fuel), l[i]? = some e₁ → l[i + 1]? = some e₂ → e₁.2 < e₂.2

section LogWf
variable {l l₁ l₂ : List (Oid × Fuel)}

@[lantana_alias uchain_log_wf_lookup_1]
theorem uchainLogWf_lookup_1 (hl : uchainLogWf l) {i j : Nat} {e₁ e₂ : Oid × Fuel}
    (h₁ : l[i]? = some e₁) (h₂ : l[j]? = some e₂) (hij : i < j) : e₁.2 < e₂.2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  induction d generalizing e₂ with
  | zero => exact hl i e₁ e₂ h₁ h₂
  | succ d ih =>
    have hlt : i + d + 1 < l.length := by
      have := (List.getElem?_eq_some_iff.mp h₂).1
      omega
    obtain ⟨e, he⟩ : ∃ e, l[i + d + 1]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    have h₂' : l[i + d + 1 + 1]? = some e₂ := by
      rw [show i + d + 1 + 1 = i + (d + 1) + 1 by omega]
      exact h₂
    exact Ordinals.Ordinal.lt_trans (ih he (by omega)) (hl _ e e₂ he h₂')

@[lantana_alias uchain_log_wf_cons]
theorem uchainLogWf_cons (e : Oid × Fuel) (l : List (Oid × Fuel)) :
    uchainLogWf (e :: l) ↔
      uchainLogWf l ∧ ∀ (i : Nat) (a : Oid × Fuel), l[i]? = some a → e.2 < a.2 := by
  constructor
  · intro h
    refine ⟨fun i e₁ e₂ h₁ h₂ => h (i + 1) e₁ e₂ (by simpa using h₁) (by simpa using h₂),
      fun i a ha => ?_⟩
    exact uchainLogWf_lookup_1 h (i := 0) (j := i + 1) (by simp) (by simpa using ha)
      (Nat.succ_pos i)
  · rintro ⟨hl, he⟩ i e₁ e₂ h₁ h₂
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁
      subst h₁
      exact he 0 e₂ (by simpa using h₂)
    | succ i => exact hl i e₁ e₂ (by simpa using h₁) (by simpa using h₂)

@[lantana_alias uchain_log_wf_app]
theorem uchainLogWf_app (l₁ l₂ : List (Oid × Fuel)) :
    (uchainLogWf l₁ ∧ uchainLogWf l₂ ∧
      ∀ (i : Nat) (e a : Oid × Fuel), l₁[i]? = some e → l₂.head? = some a → e.2 < a.2) ↔
      uchainLogWf (l₁ ++ l₂) := by
  constructor
  · rintro ⟨h₁, h₂, h₁₂⟩ i e₁ e₂ he₁ he₂
    by_cases hi : i + 1 < l₁.length
    · rw [List.getElem?_append_left (by omega)] at he₁
      rw [List.getElem?_append_left hi] at he₂
      exact h₁ i e₁ e₂ he₁ he₂
    · by_cases hi' : i < l₁.length
      · rw [List.getElem?_append_left hi'] at he₁
        rw [List.getElem?_append_right (by omega), show i + 1 - l₁.length = 0 by omega] at he₂
        exact h₁₂ i e₁ e₂ he₁ (by rw [List.head?_eq_getElem?]; exact he₂)
      · rw [List.getElem?_append_right (by omega)] at he₁
        rw [List.getElem?_append_right (by omega),
          show i + 1 - l₁.length = i - l₁.length + 1 by omega] at he₂
        exact h₂ _ e₁ e₂ he₁ he₂
  · intro h
    refine ⟨fun i e₁ e₂ he₁ he₂ => ?_, fun i e₁ e₂ he₁ he₂ => ?_, fun i e a he ha => ?_⟩
    · have hi : i + 1 < l₁.length := (List.getElem?_eq_some_iff.mp he₂).1
      exact h i e₁ e₂ (by rw [List.getElem?_append_left (by omega)]; exact he₁)
        (by rw [List.getElem?_append_left hi]; exact he₂)
    · refine h (l₁.length + i) e₁ e₂ ?_ ?_
      · rw [List.getElem?_append_right (by omega), show l₁.length + i - l₁.length = i by omega]
        exact he₁
      · rw [List.getElem?_append_right (by omega),
          show l₁.length + i + 1 - l₁.length = i + 1 by omega]
        exact he₂
    · have hi : i < l₁.length := (List.getElem?_eq_some_iff.mp he).1
      refine uchainLogWf_lookup_1 h (i := i) (j := l₁.length) ?_ ?_ hi
      · rw [List.getElem?_append_left hi]; exact he
      · rw [List.getElem?_append_right (by omega), Nat.sub_self, ← List.head?_eq_getElem?]
        exact ha

@[lantana_alias uchain_log_wf_lookup_2]
theorem uchainLogWf_lookup_2 (hl : uchainLogWf l) {i j : Nat} {e₁ e₂ : Oid × Fuel}
    (h₁ : l[i]? = some e₁) (h₂ : l[j]? = some e₂) (hlt : e₁.2 < e₂.2) : i < j := by
  rcases Nat.lt_or_ge i j with hij | hji
  · exact hij
  · rcases Nat.eq_or_lt_of_le hji with rfl | hji
    · rw [h₁, Option.some.injEq] at h₂
      subst h₂
      exact absurd hlt (Ordinals.Ordinal.lt_irrefl _)
    · exact absurd (Ordinals.Ordinal.lt_trans hlt (uchainLogWf_lookup_1 hl h₂ h₁ hji))
        (Ordinals.Ordinal.lt_irrefl _)

end LogWf

/-! ## Ghost state: the log of a chain -/

/-- The world's ghost state for chain logs (Rocq `uchainGS.uchainGpreS`). -/
@[lantana_alias uchainGS.uchainGpreS]
class UchainGpreS (GF : BundledGFunctors) where
  [logG : MonoListGP GF (Oid × Fuel)]

attribute [reducible, instance] UchainGpreS.logG
attribute [lantana_alias uchainGS.uchainGpreS_log] UchainGpreS.logG

set_option linter.iris.dupNamespace false in
/-- The ghost state of a chain log: the world's ghost state and the name of the log
(Rocq `uchainGS.uchainGS`). -/
@[lantana_alias uchainGS.uchainGS]
class UchainGS (GF : BundledGFunctors) extends UchainGpreS GF where
  /-- The ghost name of the log. -/
  logName : GName

attribute [lantana_alias uchainGS.uchain_inG] UchainGS.toUchainGpreS
attribute [lantana_alias uchainGS.log_name] UchainGS.logName

#lantana_ignore uchainGS.«uchainΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#lantana_ignore uchainGS.«subG_uchainΣ» "Subsumed by BundledGFunctors typeclass synthesis"

section Log
variable {GF : BundledGFunctors} [UchainGS GF]

/-- The authoritative log, with the fraction `q` (sealed). -/
@[lantana_alias uchain_auth, irreducible]
def uchainAuth (q : Qp) (l : List (Oid × Fuel)) : IProp GF :=
  iprop(⌜uchainLogWf l⌝ ∗ MonoListP.auth_own (UchainGS.logName GF) (.own q) l)

@[lantana_alias uchain_auth_unseal]
theorem uchainAuth_unfold (q : Qp) (l : List (Oid × Fuel)) :
    uchainAuth (GF := GF) q l =
      iprop(⌜uchainLogWf l⌝ ∗ MonoListP.auth_own (UchainGS.logName GF) (.own q) l) := by
  unfold uchainAuth; rfl

#lantana_ignore uchain_auth_def "`uchainAuth`, irreducible."
#lantana_ignore uchain_auth_aux "`uchainAuth`, irreducible."

/-- The log ends, at some point, with the entry `e` (sealed). -/
@[lantana_alias uchain_pin, irreducible]
def uchainPin (e : Oid × Fuel) : IProp GF :=
  iprop(∃ l : List (Oid × Fuel), ⌜l.getLast? = some e ∧ uchainLogWf l⌝ ∧
    MonoListP.lb_own (UchainGS.logName GF) l)

@[lantana_alias uchain_pin_unseal]
theorem uchainPin_unfold (e : Oid × Fuel) :
    uchainPin (GF := GF) e = iprop(∃ l : List (Oid × Fuel), ⌜l.getLast? = some e ∧ uchainLogWf l⌝ ∧
      MonoListP.lb_own (UchainGS.logName GF) l) := by
  unfold uchainPin; rfl

#lantana_ignore uchain_pin_def "`uchainPin`, irreducible."
#lantana_ignore uchain_pin_aux "`uchainPin`, irreducible."

end Log

/-! ## Chains -/

section Chain
variable {Expr State Val : Type} {GF : BundledGFunctors} [Language Expr State Val]
variable [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF]

/-- `untilIChain N k o P Q`: `P` until `Q` or until a next link `untilIChain N k' o' P Q` with
`o' < o`, on the obligation `k` (half of the until). By well-founded recursion on `o`. -/
@[lantana_alias untilI_chain]
def untilIChain (N : Namespace) (k : Oid) (o : Fuel) (P Q : IProp GF) : IProp GF :=
  Ordinals.Ordinal.lt_wf.fix (C := fun _ => Oid → IProp GF)
    (fun o rec k => untilI (Expr := Expr) (State := State) N k (1 : Qp).half P
      iprop(Q ∨ ∃ (k' : Oid) (o' : Fuel) (h : o' < o), rec o' h k')) o k

#lantana_ignore untilI_chain_rec "`untilIChain`, by `WellFounded.fix`."
#lantana_ignore untilI_chain_rec_proof_irrelevance "`untilIChain` is defined by `WellFounded.fix`."

@[lantana_alias untilI_chain_unfold]
theorem untilIChain_unfold (N : Namespace) (k : Oid) (o : Fuel) (P Q : IProp GF) :
    untilIChain (Expr := Expr) (State := State) N k o P Q =
      untilI (Expr := Expr) (State := State) N k (1 : Qp).half P
        iprop(Q ∨ ∃ (k' : Oid) (o' : Fuel) (_ : o' < o),
          untilIChain (Expr := Expr) (State := State) N k' o' P Q) := by
  unfold untilIChain
  rw [WellFounded.fix_eq]

/-- The log of a chain: the discharged links `l`, each with an ordinal below some measure at
layer `0`, the current link `(k, o)`, and either the chain from it or, once it is
discharged, `R` (sealed, Rocq `locked`). -/
@[lantana_alias until_chain_log, irreducible]
def untilChainLog [UchainGS GF] (N : Namespace) (P Q R : IProp GF) : IProp GF :=
  iprop(∃ (l : List (Oid × Fuel)) (k : Oid) (o : Fuel),
    ⌜∃ m : Measure, o ≤ Measure.rep 0 m⌝ ∗ uchainAuth (1 : Qp).half (l ++ [(k, o)]) ∗
    ([∗list] ko ∈ l, Obl.discharged ko.1 ∗ ⌜∃ m : Measure, ko.2 ≤ Measure.rep 0 m⌝) ∗
    (untilIChain (Expr := Expr) (State := State) N k o P Q ∨
      ((uchainAuth (1 : Qp).half (l ++ [(k, o)]) ∗ Obl.discharged k) ∗ R)))

theorem untilChainLog_unfold [UchainGS GF] (N : Namespace) (P Q R : IProp GF) :
    untilChainLog (Expr := Expr) (State := State) N P Q R =
      iprop(∃ (l : List (Oid × Fuel)) (k : Oid) (o : Fuel),
        ⌜∃ m : Measure, o ≤ Measure.rep 0 m⌝ ∗ uchainAuth (1 : Qp).half (l ++ [(k, o)]) ∗
        ([∗list] ko ∈ l, Obl.discharged ko.1 ∗ ⌜∃ m : Measure, ko.2 ≤ Measure.rep 0 m⌝) ∗
        (untilIChain (Expr := Expr) (State := State) N k o P Q ∨
          ((uchainAuth (1 : Qp).half (l ++ [(k, o)]) ∗ Obl.discharged k) ∗ R))) := by
  unfold untilChainLog; rfl

end Chain

end Lantana
