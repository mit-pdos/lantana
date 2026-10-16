/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.HeapLang.Syntax
public import Lantana.HeapLang.Notation
public import Lantana.HeapLang.Semantics
public import Lantana.ProgramLogic.EctxiLanguage

/-! # HeapLang: the language instance and its class instances

HeapLang as a `Lantana.EctxItemLanguage` (Rocq `lantana_heap_lang/lang.v:676-780`), whence an
`EctxLanguage` and a `Language`, and the `IntoVal`, `AsVal`, `Atomic` and `PureExec` instances
(Rocq `class_instances.v`). A fork of Iris-Lean's `Iris.HeapLang.Instances` (D22), without the
prophecy lemmas (D15).
-/

@[expose] public section
namespace Lantana.HeapLang

open Iris.ProgramLogic (toVal coe_of_toVal_eq_some)
open Iris.ProgramLogic.Language (Atomicity)
open Language EctxItemLanguage EctxLanguage

@[lantana_alias heap_lang.heap_lang_mixin]
instance instEctxItemLanguageExp : EctxItemLanguage Exp ECtxItem State Val where
  fillItem := ECtxItem.fill
  baseStep := BaseStep
  val_base_stuck h := by cases h <;> rfl
  fillItem_val Ki e h := by
    cases Ki <;> simp_all [ECtxItem.fill, toVal]
  fillItem_inj {Ki} e₁ e₂ h := by
    cases Ki <;> simp_all [ECtxItem.fill]
  fillItem_no_val_inj {Ki₁ Ki₂ _ _} hv₁ hv₂ heq := by
    cases Ki₁ <;> cases Ki₂ <;>
      simp_all only [ECtxItem.fill, Exp.ofVal, toVal, reduceCtorEq, Exp.app.injEq] <;> grind
  base_ctx_step_val {Ki} _ _ _ _ _ h := by
    cases Ki <;> cases h <;> rfl

-- The `EctxItemLanguage` instance above bundles what Rocq states as separate HeapLang lemmas and
-- then packages into `heap_lang_mixin`.
#lantana_ignore heap_lang.fill_item_inj "The `fillItem_inj` field of `instEctxItemLanguageExp`."
#lantana_ignore heap_lang.fill_item_val "The `fillItem_val` field of `instEctxItemLanguageExp`."
#lantana_ignore heap_lang.fill_item_no_val_inj
  "The `fillItem_no_val_inj` field of `instEctxItemLanguageExp`."
#lantana_ignore heap_lang.val_base_stuck
  "The `val_base_stuck` field of `instEctxItemLanguageExp`."
#lantana_ignore heap_lang.base_ctx_step_val
  "The `base_ctx_step_val` field of `instEctxItemLanguageExp`."
#lantana_ignore heap_ectxi_lang
  "`instEctxItemLanguageExp` is at once the mixin and the canonical structure it builds."
#lantana_ignore heap_ectx_lang
  "The generic `EctxItemLanguage.instEctxLanguage` (`EctxLanguageOfEctxi`) at `Exp`."
#lantana_ignore heap_lang.heap_lang
  "The generic `EctxLanguage.instLanguage` (`LanguageOfEctx`) at `Exp`."
#lantana_ignore heap_lang.irreducible_resolve "prophecies dropped (D15)"
#lantana_ignore heap_lang.new_proph_atomic "prophecies dropped (D15)"
#lantana_ignore heap_lang.resolve_atomic "prophecies dropped (D15)"
#lantana_ignore heap_lang.AsRecV
  "As in Iris-Lean, `instPureExecBeta` matches a `rec` value syntactically."
#lantana_ignore heap_lang.AsRecV_recv
  "As in Iris-Lean, `instPureExecBeta` matches a `rec` value syntactically."

@[simp]
theorem fillItem_expToVal_none (Ki : ECtxItem) (e : Exp) : toVal (fillItem Ki e) = none := by
  cases Ki <;> rfl

theorem fill_isSome_empty {K : List ECtxItem} {e : Exp}
    (h : (toVal (fill K e)).isSome) : K = [] := by
  cases K with
  | nil => rfl
  | cons Ki K' =>
    rw [fill_cons] at h
    simpa using EctxItemLanguage.fill_val h

/-- Specific to HeapLang: `fillItem Ki e` is never a value. -/
@[lantana_alias heap_lang.to_val_fill_some]
theorem toVal_fill_some {K : List ECtxItem} {e : Exp} {v : Val}
    (h : toVal (fill K e) = some v) : K = [] ∧ e = Exp.ofVal v := by
  obtain rfl := fill_isSome_empty (K := K) (e := e) (by simp [h])
  exact ⟨rfl, (coe_of_toVal_eq_some (by simpa using h)).symm⟩

theorem threadExprSat_iff {i : Nat} {C : List ECtxItem} {e : Exp} {σ : State} {tp : List Exp} :
    threadExprSat i C e σ tp ↔ tp[i]? = some (fill C e) :=
  .rfl

/-! ## Values -/

@[lantana_alias heap_lang.into_val_val]
instance instIntoValVal (v : Val) : IntoVal (Exp.ofVal v : Exp) v := ⟨rfl⟩

@[lantana_alias heap_lang.as_val_val]
instance instAsValVal (v : Val) : AsVal (Exp.ofVal v : Exp) := ⟨⟨v, rfl⟩⟩

/-! ## Steps to values -/

@[lantana_alias heap_lang.prim_step_to_val_is_base_step]
theorem primStep_val_baseStep {e : Exp} {σ : State} {v : Val} {σ' : State} {efs : List Exp}
    (h : primStep e σ (Exp.ofVal v) σ' efs) : BaseStep e σ (Exp.ofVal v) σ' efs := by
  obtain ⟨K, e₁, e₂, rfl, hv, hs⟩ := h
  obtain ⟨rfl, rfl⟩ := toVal_fill_some (K := K) (e := e₂) (v := v) (by rw [← hv]; simp)
  exact hs

/-- If one base step of `e₁` returns a value, every base step of `e₁` does. -/
@[lantana_alias heap_lang.base_step_to_val]
theorem base_step_to_val {e₁ : Exp} {σ₁ : State} {e₂ : Exp} {σ₂ : State} {efs : List Exp}
    {σ₁' : State} {e₂' : Exp} {σ₂' : State} {efs' : List Exp}
    (h : BaseStep e₁ σ₁ e₂ σ₂ efs) (h' : BaseStep e₁ σ₁' e₂' σ₂' efs')
    (hv : (toVal e₂).isSome) : (toVal e₂').isSome := by
  cases h <;> cases h' <;> simp_all

theorem prim_step_to_val_always_to_val {e₁ : Exp} {σ₁ : State} {v₂ : Val} {σ₂ : State}
    {efs : List Exp} {σ₁' : State} {e₂' : Exp} {σ₂' : State} {efs' : List Exp}
    (h : primStep e₁ σ₁ (Exp.ofVal v₂) σ₂ efs) (h' : primStep e₁ σ₁' e₂' σ₂' efs') :
    (toVal e₂').isSome :=
  have hb := primStep_val_baseStep h
  base_step_to_val hb (baseStep_of_primStep h' (subredexesAreValues_of_baseStep hb)) (by simp)

/-- Not an instance: `BaseStep` is not a class (Rocq has a `Hint Extern`). -/
theorem base_step_to_val_atomic {e₁ : Exp} {σ₁ : State} {v₂ : Val} {σ₂ : State}
    {efs : List Exp} (a : Atomicity) (h : BaseStep e₁ σ₁ (Exp.ofVal v₂) σ₂ efs) :
    Atomic a e₁ :=
  Atomic.of_stronglyAtomic
    ⟨fun h' => prim_step_to_val_always_to_val (primStep_of_baseStep h) h'⟩ a

/-! ## Atomicity -/

/-- An expression whose subexpressions under items are values, and whose base steps all end in
values, is atomic. -/
theorem atomic_of_subredexes {e : Exp} (a : Atomicity)
    (hsub : ∀ Ki e', e = fillItem Ki e' → (toVal e').isSome)
    (hval : ∀ σ e' σ' efs, BaseStep e σ e' σ' efs → (toVal e').isSome) : Atomic a e :=
  Atomic.of_stronglyAtomic (atomic_of_baseAtomic (a := .StronglyAtomic) hval
    (subredexesAreValues hsub)) a

/-- Proves `Atomic a e` with `atomic_of_subredexes`, by case analysis on the context item and
on the base step. -/
local macro "solve_atomic" : tactic =>
  `(tactic| (
    refine atomic_of_subredexes _ (fun Ki e' heq => ?_) (fun σ e' σ' efs h => ?_)
    · cases Ki <;> cases heq <;> rfl
    · cases h <;> rfl))

@[lantana_alias heap_lang.rec_atomic]
instance instAtomicRec {a : Atomicity} {f x : Binder} {e : Exp} :
    Atomic a hl(rec &f &x := &e) := by solve_atomic

@[lantana_alias heap_lang.pair_atomic]
instance instAtomicPair {a : Atomicity} {v1 v2 : Val} : Atomic a hl((&v1, &v2)) := by
  solve_atomic

@[lantana_alias heap_lang.injl_atomic]
instance instAtomicInjl {a : Atomicity} {v : Val} : Atomic a hl(injl(&v)) := by solve_atomic

@[lantana_alias heap_lang.injr_atomic]
instance instAtomicInjr {a : Atomicity} {v : Val} : Atomic a hl(injr(&v)) := by solve_atomic

/-- Generalizes `Skip`. -/
@[lantana_alias heap_lang.beta_atomic]
instance instAtomicBeta {a : Atomicity} {f x : Binder} {v1 v2 : Val} :
    Atomic a hl(v(rec &f &x := v(&v1)) &v2) := by
  refine atomic_of_subredexes _ (fun Ki e' heq => ?_) (fun σ e' σ' efs h => ?_)
  · cases Ki <;> cases heq <;> rfl
  · cases h with
    | betaS _ _ _ _ _ _ h => subst h; cases f <;> cases x <;> rfl

@[lantana_alias heap_lang.unop_atomic]
instance instAtomicUnOp {a : Atomicity} {op : UnOp} {v : Val} :
    Atomic a (Exp.unop op (.ofVal v)) := by solve_atomic

@[lantana_alias heap_lang.binop_atomic]
instance instAtomicBinOp {a : Atomicity} {op : BinOp} {v1 v2 : Val} :
    Atomic a (Exp.binop op (.ofVal v1) (.ofVal v2)) := by solve_atomic

@[lantana_alias heap_lang.if_true_atomic]
instance instAtomicIfTrue {a : Atomicity} {v1 : Val} {e2 : Exp} :
    Atomic a hl(if #true then &v1 else &e2) := by solve_atomic

@[lantana_alias heap_lang.if_false_atomic]
instance instAtomicIfFalse {a : Atomicity} {e1 : Exp} {v2 : Val} :
    Atomic a hl(if #false then &e1 else &v2) := by solve_atomic

@[lantana_alias heap_lang.fst_atomic]
instance instAtomicFst {a : Atomicity} {v : Val} : Atomic a hl(fst(&v)) := by solve_atomic

@[lantana_alias heap_lang.snd_atomic]
instance instAtomicSnd {a : Atomicity} {v : Val} : Atomic a hl(snd(&v)) := by solve_atomic

@[lantana_alias heap_lang.fork_atomic]
instance instAtomicFork {a : Atomicity} {e : Exp} : Atomic a hl(fork(&e)) := by solve_atomic

@[lantana_alias heap_lang.alloc_atomic]
instance instAtomicAllocN {a : Atomicity} {v1 v2 : Val} : Atomic a hl(allocn(&v1, &v2)) := by
  solve_atomic

@[lantana_alias heap_lang.free_atomic]
instance instAtomicFree {a : Atomicity} {v : Val} : Atomic a hl(free(&v)) := by solve_atomic

@[lantana_alias heap_lang.load_atomic]
instance instAtomicLoad {a : Atomicity} {v : Val} : Atomic a hl(!&v) := by solve_atomic

@[lantana_alias heap_lang.xchg_atomic]
instance instAtomicXchg {a : Atomicity} {v1 v2 : Val} : Atomic a hl(xchg(&v1, &v2)) := by
  solve_atomic

@[lantana_alias heap_lang.store_atomic]
instance instAtomicStore {a : Atomicity} {v1 v2 : Val} : Atomic a hl(&v1 ← &v2) := by
  solve_atomic

@[lantana_alias heap_lang.cmpxchg_atomic]
instance instAtomicCmpXchg {a : Atomicity} {v1 v2 v3 : Val} :
    Atomic a hl(cmpXchg(&v1, &v2, &v3)) := by solve_atomic

@[lantana_alias heap_lang.faa_atomic]
instance instAtomicFaa {a : Atomicity} {v1 v2 : Val} : Atomic a hl(faa(&v1, &v2)) := by
  solve_atomic

@[lantana_alias heap_lang.label_atomic]
instance instAtomicLabel {a : Atomicity} {t : String} {v : Val} :
    Atomic a hl(label(&t, &v)) := by solve_atomic

@[lantana_alias heap_lang.choosenat_atomic]
instance instAtomicChooseNat {a : Atomicity} : Atomic a hl(chooseNat()) := by
  solve_atomic

/-! ## Pure steps -/

/-- A base step that is always possible and deterministic is a pure step. -/
theorem pureStep_of_baseStep {e₁ e₂ : Exp} (hstep : ∀ σ, BaseStep e₁ σ e₂ σ [])
    (hdet : ∀ {σ e₂' σ' efs}, BaseStep e₁ σ e₂' σ' efs → σ' = σ ∧ e₂' = e₂ ∧ efs = []) :
    PureStep e₁ e₂ :=
  PureBaseStep.pureStep ⟨fun σ => ⟨_, _, _, hstep σ⟩, hdet⟩

/-- Proves `PureExec φ 1 e₁ e₂` from the base step `step` of `e₁`, given `φ`. -/
local macro "solve_pure_exec" step:term : tactic =>
  `(tactic| (
    intro _
    exact .once <| pureStep_of_baseStep (fun _ => $step) (fun h => by cases h <;> simp_all)))

@[lantana_alias heap_lang.pure_recc]
instance instPureExecRec {f x : Binder} {e : Exp} :
    PureExec True 1 hl(rec &f &x := &e) hl(v(rec &f &x := &e)) where
  pureExec := by solve_pure_exec .recS ..

@[lantana_alias heap_lang.pure_pairc]
instance instPureExecPair {v1 v2 : Val} : PureExec True 1 hl((&v1, &v2)) hl(v((&v1, &v2))) where
  pureExec := by solve_pure_exec .pairS ..

@[lantana_alias heap_lang.pure_injlc]
instance instPureExecInjl {v : Val} : PureExec True 1 hl(injl(&v)) hl(v(injl(&v))) where
  pureExec := by solve_pure_exec .injLS ..

@[lantana_alias heap_lang.pure_injrc]
instance instPureExecInjr {v : Val} : PureExec True 1 hl(injr(&v)) hl(v(injr(&v))) where
  pureExec := by solve_pure_exec .injRS ..

@[lantana_alias heap_lang.pure_beta]
instance instPureExecBeta {f x : Binder} {e : Exp} {v : Val} :
    PureExec True 1 hl(v(rec &f &x := &e) &v) ((e.subst f (.rec_ f x e)).subst x v) where
  pureExec := by solve_pure_exec .betaS _ _ _ _ _ _ rfl

set_option synthInstance.checkSynthOrder false in
@[lantana_alias heap_lang.pure_unop]
instance instPureExecUnOp {op : UnOp} {v v' : Val} :
    PureExec (op.eval v = some v') 1 (Exp.unop op (.ofVal v)) (.ofVal v') where
  pureExec h :=
    .once <| pureStep_of_baseStep (fun _ => .unOpS _ _ _ _ h) (fun hs => by cases hs; simp_all)

set_option synthInstance.checkSynthOrder false in
@[lantana_alias heap_lang.pure_binop]
instance instPureExecBinOp {op : BinOp} {v1 v2 v' : Val} :
    PureExec (op.eval v1 v2 = some v') 1 (Exp.binop op (.ofVal v1) (.ofVal v2)) (.ofVal v') where
  pureExec h :=
    .once <| pureStep_of_baseStep (fun _ => .binOpS _ _ _ _ _ h) (fun hs => by cases hs; simp_all)

/-- Higher priority than the generic `instPureExecBinOp`. -/
@[lantana_alias heap_lang.pure_eqop]
instance (priority := default + 10) instPureExecEqOp {v1 v2 : Val} :
    PureExec (v1.compareSafe v2) 1
      (Exp.binop .eq (.ofVal v1) (.ofVal v2)) (.ofVal (.lit (.bool (v1 == v2)))) where
  pureExec := by
    intro hφ
    refine .once <| pureStep_of_baseStep (fun _ => .binOpS _ _ _ _ _ ?_) (fun h => ?_)
    · simp [BinOp.eval, hφ]
    · cases h; simp_all [BinOp.eval]

@[lantana_alias heap_lang.pure_if_true]
instance instPureExecIfTrue {e1 e2 : Exp} : PureExec True 1 hl(if #true then &e1 else &e2) e1 where
  pureExec := by solve_pure_exec .ifTrueS ..

@[lantana_alias heap_lang.pure_if_false]
instance instPureExecIfFalse {e1 e2 : Exp} :
    PureExec True 1 hl(if #false then &e1 else &e2) e2 where
  pureExec := by solve_pure_exec .ifFalseS ..

@[lantana_alias heap_lang.pure_fst]
instance instPureExecFst {v1 v2 : Val} : PureExec True 1 hl(fst(v((&v1, &v2)))) v1 where
  pureExec := by solve_pure_exec .fstS ..

@[lantana_alias heap_lang.pure_snd]
instance instPureExecSnd {v1 v2 : Val} : PureExec True 1 hl(snd(v((&v1, &v2)))) v2 where
  pureExec := by solve_pure_exec .sndS ..

@[lantana_alias heap_lang.pure_case_inl]
instance instPureExecCaseInjl {v : Val} {e1 e2 : Exp} :
    PureExec True 1 (Exp.case hl(v(injl(&v))) e1 e2) (.app e1 (.ofVal v)) where
  pureExec := by solve_pure_exec .caseLS ..

@[lantana_alias heap_lang.pure_case_inr]
instance instPureExecCaseInjr {v : Val} {e1 e2 : Exp} :
    PureExec True 1 (Exp.case hl(v(injr(&v))) e1 e2) (.app e2 (.ofVal v)) where
  pureExec := by solve_pure_exec .caseRS ..

@[lantana_alias heap_lang.pure_label]
instance instPureExecLabel {t : String} {v : Val} : PureExec True 1 hl(label(&t, &v)) v where
  pureExec := by solve_pure_exec .labelS ..

end Lantana.HeapLang
