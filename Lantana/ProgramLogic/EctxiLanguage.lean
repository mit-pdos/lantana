/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from Iris-Lean's `Iris.ProgramLogic.EctxiLanguage`, whose header reads:
  Copyright (c) The Iris-Lean Contributors
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Fernando Leal
Modified by the Lantana-Lean Contributors; the module documentation describes the changes.
-/
module

public import Lantana.ProgramLogic.EctxLanguage
public import Iris.Std.FromMathlib

/-! # Languages with evaluation context items

Rocq `lantana/program_logic/ectxi_language.v`, adapted from Iris-Lean's
`Iris.ProgramLogic.EctxiLanguage`: a language given by context items `Item` (contexts of depth
one) and a base step is an `EctxLanguage` whose contexts are lists of items, innermost first.
-/

@[expose] public section

namespace Lantana

open Iris.ProgramLogic (ToVal toVal)
open FromMathlib


/-- A language with evaluation context items: `fillItem Ki e` plugs `e` into the item `Ki`. -/
@[lantana_alias ectxiLanguage, lantana_alias EctxiLanguageMixin]
class EctxItemLanguage (Expr : Type) (Item : outParam (Type)) (State : outParam (Type))
    (Val : outParam (Type)) extends ToVal Expr Val where
  /-- Plug an expression into a context item. -/
  fillItem : Item → Expr → Expr
  /-- The base step: one step of a redex, forking the threads `efs`. -/
  baseStep : Expr → State → Expr → State → List Expr → Prop
  /-- Values are not redexes. -/
  val_base_stuck {e₁ : Expr} {σ₁ : State} {e₂ σ₂ efs} :
    baseStep e₁ σ₁ e₂ σ₂ efs → toVal e₁ = none
  fillItem_val (Ki : Item) (e : Expr) : (toVal (fillItem Ki e)).isSome → (toVal e).isSome
  fillItem_inj {Ki : Item} : Function.Injective (fillItem Ki)
  fillItem_no_val_inj {Ki₁ Ki₂ : Item} {e₁ e₂ : Expr} :
    toVal e₁ = none → toVal e₂ = none → fillItem Ki₁ e₁ = fillItem Ki₂ e₂ → Ki₁ = Ki₂
  /-- Unlike in `EctxLanguage`, the context cannot be empty: `e` is a value. -/
  base_ctx_step_val {Ki : Item} {e : Expr} {σ₁ : State} {e₂ σ₂ efs} :
    baseStep (fillItem Ki e) σ₁ e₂ σ₂ efs → (toVal e).isSome

export EctxItemLanguage (fillItem)

attribute [lantana_alias fill_item] EctxItemLanguage.fillItem
attribute [lantana_alias ectxi_language.base_step] EctxItemLanguage.baseStep
attribute [lantana_alias fill_item_val] EctxItemLanguage.fillItem_val
attribute [lantana_alias fill_item_inj] EctxItemLanguage.fillItem_inj
attribute [lantana_alias fill_item_no_val_inj] EctxItemLanguage.fillItem_no_val_inj
attribute [lantana_alias ectxi_language.base_ctx_step_val] EctxItemLanguage.base_ctx_step_val

namespace EctxItemLanguage

open EvContext (fill_empty fill_comp fill_inj)

variable {Expr : Type} {Item : Type} {State : Type} {Val : Type}
  [Λ : EctxItemLanguage Expr Item State Val]

/-- Contexts are lists of items, innermost first; `compEctx K₁ K₂` is `K₂ ++ K₁`. -/
@[lantana_alias ectxi_language.fill]
instance instEvContext : EvContext Expr (List Item) where
  emptyEctx := []
  compEctx K₁ K₂ := K₂ ++ K₁
  fill K e := K.foldl (fun e Ki => fillItem Ki e) e
  fill_empty _ := rfl
  fill_comp _ _ _ := (List.foldl_append ..).symm
  fill_inj {K} := by
    induction K with
    | nil => exact fun _ _ h => h
    | cons Ki K ih => exact fun _ _ h => fillItem_inj (ih h)

@[simp]
theorem fill_nil (e : Expr) : fill ([] : List Item) e = e := rfl

@[simp]
theorem fill_cons (Ki : Item) (K : List Item) (e : Expr) :
    fill (Ki :: K) e = fill K (fillItem Ki e) := rfl

@[lantana_alias fill_app, simp]
theorem fill_append (K₁ K₂ : List Item) (e : Expr) : fill (K₁ ++ K₂) e = fill K₂ (fill K₁ e) :=
  List.foldl_append ..

theorem fill_singleton (Ki : Item) (e : Expr) : fill [Ki] e = fillItem Ki e := rfl

theorem fill_val {K : List Item} {e : Expr} (h : (toVal (fill K e)).isSome) :
    (toVal e).isSome := by
  induction K generalizing e with
  | nil => exact h
  | cons Ki K ih => exact fillItem_val Ki e (ih (e := fillItem Ki e) h)

/-- A base redex under a context is not a value. -/
theorem baseStep_fill_eq_val_absurd {K : List Item} {e e' : Expr} {σ σ' : State}
    {efs : List Expr} {v : Val} (hbase : Λ.baseStep e σ e' σ' efs)
    (heq : ToVal.ofVal v = fill K e) : False := by
  have h : (toVal e).isSome := fill_val (K := K) (by simp [← heq])
  simp [Λ.val_base_stuck hbase] at h

@[lantana_alias ectxi_language.fill_not_val]
theorem fill_not_val (K : List Item) {e : Expr} (h : toVal e = none) :
    toVal (fill K e) = none := by
  cases hK : toVal (fill K e) with
  | none => rfl
  | some _ => simpa [h] using fill_val (K := K) (e := e) (by simp [hK])

/-- The `EctxLanguage` of an `EctxItemLanguage`, whose contexts are lists of items. -/
@[lantana_alias ectxi_lang_ectx, lantana_alias ectxi_lang_ectx_mixin,
  lantana_alias EctxLanguageOfEctxi]
instance instEctxLanguage : EctxLanguage Expr State Val (List Item) where
  toEvContext := instEvContext
  baseStep := Λ.baseStep
  val_base_stuck := Λ.val_base_stuck
  fill_val _ _ := fill_val
  step_by_val {K K' e₁ e₁' σ₁ e₂ σ₂ efs} hfill hred hstep := by
    induction K using List.reverseRec generalizing K' e₁ with
    | nil => exact ⟨K', (List.append_nil K').symm⟩
    | append_singleton Ks Ki ih =>
      cases K' using List.reverseCases with
      | nil =>
        rw [fill_append, fill_singleton, fill_nil] at hfill
        subst hfill
        have := fill_val (Λ.base_ctx_step_val hstep)
        simp [hred] at this
      | append_singleton Ks' Ki' =>
        rw [fill_append, fill_append, fill_singleton, fill_singleton] at hfill
        obtain rfl : Ki = Ki' :=
          fillItem_no_val_inj (fill_not_val Ks hred)
            (fill_not_val Ks' (Λ.val_base_stuck hstep)) hfill
        obtain ⟨K'', rfl⟩ := ih (fillItem_inj hfill) hred
        exact ⟨K'', List.append_assoc K'' Ks [Ki]⟩
  base_ctx_step_val {K e _ _ _ _} hstep := by
    cases K using List.reverseCases with
    | nil => exact .inr rfl
    | append_singleton Ks Ki =>
      rw [fill_append, fill_singleton] at hstep
      exact .inl (fill_val (Λ.base_ctx_step_val hstep))

attribute [lantana_alias ectxi_lang] EctxLanguage.instLanguage

@[lantana_alias ectxi_language_sub_redexes_are_values]
theorem subredexesAreValues {e : Expr}
    (hsub : ∀ Ki e', e = fillItem Ki e' → (toVal e').isSome) :
    EctxLanguage.SubredexesAreValues e := by
  intro K e' heq hv
  rcases List.eq_nil_or_concat K with rfl | ⟨K', Ki, rfl⟩
  · rfl
  · rw [List.concat_eq_append, fill_append, fill_singleton] at heq
    simpa [hv] using fill_val (hsub _ _ heq)

#lantana_ignore ectxi_lang_ctx_item "`EctxLanguage.instContextFill [Ki]`"

/-- A reducible expression determines its context. -/
@[lantana_alias fill_ctx_step_inj]
theorem fill_ctx_step_inj {K₁ K₂ : List Item} {e : Expr} {σ : State} {e' σ' efs}
    (h : primStep e σ e' σ' efs) (heq : fill K₁ e = fill K₂ e) : K₁ = K₂ := by
  obtain ⟨R, r, r', rfl, -, hs⟩ := h
  rw [← fill_append, ← fill_append] at heq
  have hK := (EctxLanguage.base_redex_unique heq ⟨_, _, _, hs⟩ ⟨_, _, _, hs⟩).1
  exact List.append_cancel_left (hK.trans (List.nil_append _))

end EctxItemLanguage
end Lantana
