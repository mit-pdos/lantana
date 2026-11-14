/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from Iris-Lean's `Iris.HeapLang.Instances`, whose header reads:
  Copyright (c) The Iris-Lean Contributors
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Sergei Stepanenko, Markus de Medeiros
Modified by the Lantana-Lean Contributors; the module documentation describes the changes.
-/
module

public import Lantana.HeapLang.Syntax
public import Lantana.HeapLang.Notation
public import Lantana.HeapLang.Semantics
public import Lantana.ProgramLogic.Language

/-! # HeapLang: the language instance and its class instances

HeapLang as an Iris-Lean `EctxItemLanguage` (Rocq `lantana_heap_lang/lang.v:676-780`), from
which Iris-Lean derives the evaluation contexts `EvContext Exp (List ECtxItem)` (lists of items,
innermost first), the `EctxLanguage` and the `Language`; its crashed threads (none, `instCrash`);
and the `IntoVal`, `AsVal`, `Atomic` and `PureExec` instances (Rocq `class_instances.v`).
HeapLang has no observations (`Obs := Empty`): the base step ignores its observation argument,
which can only be `[]` (`obs_eq_nil`).  Adapted from Iris-Lean's `Iris.HeapLang.Instances`, for
the labels and `chooseNat` of Lantana's HeapLang and without the lemmas about prophecies, which it
lacks.
-/

@[expose] public section
namespace Lantana.HeapLang

open Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.PrimStep (primStep)

/-- A list of observations of HeapLang is empty. -/
theorem obs_eq_nil : ∀ obs : List Empty, obs = []
  | [] => rfl
  | o :: _ => o.elim

/-- HeapLang as a language with evaluation context items: the base step is `BaseStep`, with no
observation. -/
@[lantana_alias heap_lang.heap_lang_mixin]
instance instEctxItemLanguageExp : EctxItemLanguage Exp ECtxItem State Empty Val where
  baseStep | (e, σ), _, (e', σ', efs) => BaseStep e σ e' σ' efs
  fillItem := ECtxItem.fill
  fillItem_inj {Ki} e₁ e₂ h := by
    cases Ki <;> simp_all [ECtxItem.fill]
  fillItem_val e Ki h := by
    cases Ki <;> simp_all [ECtxItem.fill, toVal]
  -- `cases heq` tells the constructors apart and unifies the arguments: the same item, or a
  -- value on the other side (`cases hv₁`/`cases hv₂`); `simp_all` on the 729 pairs costs 6.5 s.
  fillItem_no_val_inj Ki₁ Ki₂ hv₁ hv₂ heq := by
    cases Ki₁ <;> cases Ki₂ <;> cases heq <;> first | rfl | cases hv₁ | cases hv₂
  val_stuck h := by
    cases h <;> rfl
  base_ctx_step_val {Ki} _ _ _ _ _ _ h := by
    cases Ki <;> cases h <;> rfl

-- The `EctxItemLanguage` instance above bundles what Rocq states as separate HeapLang lemmas and
-- then packages into `heap_lang_mixin`.
#lantana_ignore heap_lang.fill_item_inj "The `fillItem_inj` field of `instEctxItemLanguageExp`."
#lantana_ignore heap_lang.fill_item_val "The `fillItem_val` field of `instEctxItemLanguageExp`."
#lantana_ignore heap_lang.fill_item_no_val_inj
  "The `fillItem_no_val_inj` field of `instEctxItemLanguageExp`."
#lantana_ignore heap_lang.val_base_stuck
  "The `val_stuck` field of `instEctxItemLanguageExp`."
#lantana_ignore heap_lang.base_ctx_step_val
  "The `base_ctx_step_val` field of `instEctxItemLanguageExp`."
#lantana_ignore heap_ectxi_lang
  "`instEctxItemLanguageExp` is at once the mixin and the canonical structure it builds."
#lantana_ignore heap_ectx_lang
  "Iris-Lean's generic `EctxItemLanguage.instEctxLanguage` (`EctxLanguageOfEctxi`) at `Exp`."
#lantana_ignore heap_lang.heap_lang
  "Iris-Lean's generic `EctxLanguage.instLanguage` (`LanguageOfEctx`) at `Exp`."
#lantana_ignore heap_lang.irreducible_resolve "Lantana's HeapLang has no prophecies."
#lantana_ignore heap_lang.new_proph_atomic "Lantana's HeapLang has no prophecies."
#lantana_ignore heap_lang.resolve_atomic "Lantana's HeapLang has no prophecies."
#lantana_ignore heap_lang.AsRecV
  "As in Iris-Lean, `instPureExecBeta` matches a `rec` value syntactically."
#lantana_ignore heap_lang.AsRecV_recv
  "As in Iris-Lean, `instPureExecBeta` matches a `rec` value syntactically."

/-- No thread of HeapLang is ever crashed. -/
instance instCrash : Crash Exp State Empty Val where
  crashed _ _ := False
  crashed_not_val h := h.elim

/-- A thread of HeapLang is never crashed. -/
theorem not_crashed (e : Exp) (σ : State) : ¬ Crash.crashed e σ := id

@[simp]
theorem fillItem_expToVal_none (Ki : ECtxItem) (e : Exp) : toVal (fillItem Ki e) = none := by
  cases Ki <;> rfl

theorem fill_isSome_empty {K : List ECtxItem} {e : Exp}
    (h : (toVal (fill K e)).isSome) : K = [] := by
  cases K with
  | nil => rfl
  | cons Ki K' =>
    rw [EctxItemLanguage.fill_cons] at h
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

/-- A base redex has no subredex: its context items hold values. -/
theorem subredexesAreValues_of_baseStep {e : Exp} {σ : State} {e' : Exp} {σ' : State}
    {efs : List Exp} (h : BaseStep e σ e' σ' efs) : EctxLanguage.SubredexesAreValues e := by
  rintro K e₁ rfl hv
  rcases EctxLanguage.base_ctx_step_val (obs := []) (e₂ := e') (σ₂ := σ') (eₜ := efs) h with
    h | h
  · simp [hv] at h
  · exact h

@[lantana_alias heap_lang.prim_step_to_val_is_base_step]
theorem primStep_val_baseStep {e : Exp} {σ : State} {obs : List Empty} {v : Val} {σ' : State}
    {efs : List Exp} (h : primStep (e, σ) obs (Exp.ofVal v, σ', efs)) :
    BaseStep e σ (Exp.ofVal v) σ' efs := by
  generalize hg : (Exp.ofVal v : Exp) = g at h
  obtain ⟨hs⟩ := h
  rename_i e₁ e₂ K
  obtain ⟨rfl, rfl⟩ := toVal_fill_some (K := K) (e := e₂) (v := v) (by rw [← hg]; simp)
  exact hs

/-- If one base step of `e₁` returns a value, every base step of `e₁` does. -/
@[lantana_alias heap_lang.base_step_to_val]
theorem base_step_to_val {e₁ : Exp} {σ₁ : State} {e₂ : Exp} {σ₂ : State} {efs : List Exp}
    {σ₁' : State} {e₂' : Exp} {σ₂' : State} {efs' : List Exp}
    (h : BaseStep e₁ σ₁ e₂ σ₂ efs) (h' : BaseStep e₁ σ₁' e₂' σ₂' efs')
    (hv : (toVal e₂).isSome) : (toVal e₂').isSome := by
  cases h <;> cases h' <;> simp_all

theorem prim_step_to_val_always_to_val {e₁ : Exp} {σ₁ : State} {obs : List Empty} {v₂ : Val}
    {σ₂ : State} {efs : List Exp} {σ₁' : State} {obs' : List Empty} {e₂' : Exp} {σ₂' : State}
    {efs' : List Exp} (h : primStep (e₁, σ₁) obs (Exp.ofVal v₂, σ₂, efs))
    (h' : primStep (e₁, σ₁') obs' (e₂', σ₂', efs')) : (toVal e₂').isSome :=
  have hb := primStep_val_baseStep h
  base_step_to_val hb
    (EctxLanguage.baseStep_of_primStep h' (subredexesAreValues_of_baseStep hb)) (by simp)

/-- Not an instance: `BaseStep` is not a class (Rocq has a `Hint Extern`). -/
theorem base_step_to_val_atomic {e₁ : Exp} {σ₁ : State} {v₂ : Val} {σ₂ : State}
    {efs : List Exp} (a : Atomicity) (h : BaseStep e₁ σ₁ (Exp.ofVal v₂) σ₂ efs) :
    Atomic a e₁ :=
  stronglyAtomic_atomic ⟨fun h' =>
    prim_step_to_val_always_to_val (EctxLanguage.primStep_of_baseStep (obs := []) h) h'⟩

/-! ## Atomicity -/

/-- An expression whose subexpressions under items are values, and whose base steps all end in
values, is atomic. -/
theorem atomic_of_subredexes {e : Exp} (a : Atomicity)
    (hsub : ∀ Ki e', e = fillItem Ki e' → (toVal e').isSome)
    (hval : ∀ σ e' σ' efs, BaseStep e σ e' σ' efs → (toVal e').isSome) : Atomic a e :=
  stronglyAtomic_atomic <| EctxLanguage.Atomic.ofBaseAtomic .StronglyAtomic
    (fun σ _ e' σ' efs h => hval σ e' σ' efs h) (EctxItemLanguage.subredexes_are_values hsub)

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
    PurePrimStep e₁ e₂ :=
  EctxLanguage.purePrimStep_of_pureBaseStep ⟨fun σ => ⟨_, _, _, hstep σ⟩,
    fun {_ _ obs _ _} h => let ⟨h₁, h₂, h₃⟩ := hdet h; ⟨obs_eq_nil obs, h₁.symm, h₂.symm, h₃⟩⟩

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
