/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.BI.Lib.GenHeap
public import Iris.Instances.Lib.GhostMap
public import Lantana.HeapLang.Instances
public import Lantana.ProgramLogic.WeakestPre

/-! # The program logic of HeapLang: ghost state, assertions, primitive laws

Rocq `lantana_heap_lang/primitive_laws.v`. The ghost state `HeapGS` is the temporal layer plus
the heap (Iris-Lean's `genHeap`, locations to `Option Val`) and the *thread-expression map*
(a ghost map from thread ids to their expressions, D17): `threadExpr i C e` is exact
ownership of thread `i`'s whole expression `fill C e`, split into the caller context `C` and
the current subexpression `e`. Every step law takes and returns the token, the children
`thKids i G` of the thread with one unit of fuel each, and a witness set `R`; it returns `£ₒ o`
later credits and the witnesses' credits (the paper's STEP rules).

Points-to is Iris-Lean's `l ↦{dq} v` at value type `Option Val`: `l ↦ v` with `v : Val` means
`l ↦ some v` by coercion, and a freed location is `l ↦{q} none` (Rocq `freed l q`).

**Skeleton (M1):** definitions real where cheap, laws stated with `sorry` (M7).
-/

@[expose] public noncomputable section

namespace Lantana.HeapLang

open Iris Iris.BI Lantana Lantana.Language
open Iris.ProgramLogic (toVal)

/-- Finite maps from thread ids. -/
abbrev ThreadMapF := fun V => Std.ExtTreeMap ThreadId V compare

/-- The heap-specific ghost state: the heap and the thread-expression map. -/
@[lantana_alias heap_stateGS]
class HeapStateGS (GF : BundledGFunctors) where
  [genHeap : genHeapGS Loc (Option Val) GF HeapF]
  [threadMap : GhostMapG GF ThreadId Exp ThreadMapF]
  /-- The ghost name of the thread-expression map. -/
  threadMapName : GName

attribute [reducible, instance] HeapStateGS.genHeap HeapStateGS.threadMap

/-- The ghost state of HeapLang: the temporal layer and the heap state. -/
@[lantana_alias heapGS]
class HeapGS (GF : BundledGFunctors) extends TemporalGS Exp State GF, HeapStateGS GF

section
variable {GF : BundledGFunctors} [HeapStateGS GF]

/-- The thread pool as a finite map from thread ids. -/
def ThreadPool.toMap (tp : ThreadPool Exp) : ThreadMapF Exp :=
  tp.zipIdx.foldl (fun m ej => m.insert ej.2 ej.1) ∅

/-- Exact ownership of thread `i`'s expression: `e` in the context `C`. -/
@[lantana_alias thread_expr]
def threadExpr (i : ThreadId) (C : List ECtxItem) (e : Exp) : IProp GF :=
  HeapStateGS.threadMapName (GF := GF) ↪◯MAP[i]{DFrac.own 1} fill C e

/-- Thread `i` has exited with the value `v`. -/
scoped notation:20 "exits " v " @ " i => threadExpr i [] (Exp.val v)

/-- The state interpretation: the heap and the thread-expression map hold the state and the
pool. -/
@[lantana_alias state_interp]
def stateInterp (σ : State) (tp : ThreadPool Exp) : IProp GF :=
  iprop(genHeapInterp σ.heap ∗
    (HeapStateGS.threadMapName (GF := GF) ↪●MAP{DFrac.own 1} ThreadPool.toMap tp))

instance threadExpr_timeless (i : ThreadId) (C : List ECtxItem) (e : Exp) :
    Timeless (threadExpr (GF := GF) i C e) := by
  unfold threadExpr; infer_instance

@[lantana_alias thread_expr_fill]
theorem threadExpr_fill (i : ThreadId) (C D : List ECtxItem) (e : Exp) :
    threadExpr (GF := GF) i C (fill D e) ⊣⊢ threadExpr i (D ++ C) e := sorry

@[lantana_alias thread_expr_read]
theorem threadExpr_read (σ : State) (tp : ThreadPool Exp) (i : ThreadId) (C : List ECtxItem)
    (e : Exp) : stateInterp (GF := GF) σ tp ⊢ threadExpr i C e -∗ ⌜tp[i]? = some (fill C e)⌝ :=
  sorry

@[lantana_alias pointsto_state_interp]
theorem pointsTo_stateInterp (σ : State) (tp : ThreadPool Exp) (l : Loc) (dq : DFrac) (v : Val) :
    stateInterp (GF := GF) σ tp ∗ l ↦{dq} some v ⊢ ⌜pointstoSat l dq v σ tp⌝ := sorry

@[lantana_alias thread_expr_state_interp]
theorem threadExpr_stateInterp (σ : State) (tp : ThreadPool Exp) (i : ThreadId)
    (C : List ECtxItem) (e : Exp) :
    stateInterp (GF := GF) σ tp ∗ threadExpr i C e ⊢ ⌜threadExprSat i C e σ tp⌝ := sorry

end

/-- The state interpretation class of HeapLang. -/
instance instStateInterp {GF : BundledGFunctors} [HeapStateGS GF] : StateInterp Exp State GF :=
  ⟨stateInterp⟩

/-- HeapLang's instance of the program logic: forked threads have the postcondition `True`. -/
@[lantana_alias heapGS_lantanaGS]
instance instLantanaGS {GF : BundledGFunctors} [HeapGS GF] : LantanaGS Exp State Val GF where
  toTemporalGS := inferInstance
  toStateInterp := instStateInterp
  forkPost _ _ := iprop(True)

/-! ## The primitive laws -/

section Laws

variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]
  [TemporalInterp Exp State GF]
variable {s : Stuckness} {i : ThreadId} {E : CoPset} {C : List ECtxItem} {G R : Oids} {o : Fuel}

/-- What a step takes: the children of the thread with one unit of fuel each, and witnesses. -/
abbrev stepPre (i : ThreadId) (G R : Oids) : IProp GF :=
  iprop(thKids i G ∗ oblFuels G 1 ∗ witLayers R)

/-- What a step gives back: later credits, the children, the witnesses' credits. -/
abbrev stepPost (i : ThreadId) (G R : Oids) (o : Fuel) : IProp GF :=
  iprop(£ₒ o ∗ thKids i G ∗ witCreds R)

@[lantana_alias heap_lang.lwp_pure_step]
theorem lwp_pure_step (n : Nat) (e₁ e₂ : Exp) (φ : Prop) (Φ : Val → IProp GF)
    [PureExec φ n e₁ e₂] (hφ : φ) (hn : 0 < n) :
    threadExpr i C e₁ ∗ thKids i G ∗ oblFuels G n ∗ witLayers R ∗
      (threadExpr i C e₂ -∗ thKids i G -∗ witCreds R -∗ £ₒ o -∗ |={E}=>m lWP e₂ @ s; i; E {{ Φ }})
      ⊢ lWP e₁ @ s; i; E {{ Φ }} := sorry

/-- Fork: the children `K ⊆ G` move to the new thread, each paying one unit of fuel. -/
@[lantana_alias heap_lang.lwp_fork]
theorem lwp_fork (K : Oids) (P : IProp GF) (e : Exp) (hK : K ⊆ G) :
    (∀ j : ThreadId, l{{{ threadExpr j [] e ∗ thKids j K ∗ P }}} e @ s; j; ⊤
        l{{{ v, RET v; liftTerm j (fun _ _ => iprop(True)) v }}})
      ⊢@{IProp GF} l{{{ threadExpr i C (.fork e) ∗ stepPre i G R ∗ oblFuels K 1 ∗ P }}}
          (Exp.fork e) @ s; i; E
        l{{{ RET Val.lit .unit; threadExpr i C (.val (.lit .unit)) ∗
          (£ₒ o ∗ thKids i (G \ K) ∗ witCreds R) }}} := sorry

@[lantana_alias heap_lang.lwp_choosenat]
theorem lwp_chooseNat :
    ⊢@{IProp GF} l{{{ threadExpr i C .chooseNat ∗ stepPre i G R }}} Exp.chooseNat @ s; i; E
      l{{{ (n : Nat), RET Val.lit (.int n); threadExpr i C (.val (.lit (.int n))) ∗
        stepPost i G R o }}} := sorry

@[lantana_alias heap_lang.lwp_alloc]
theorem lwp_alloc (v : Val) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.allocN (.val (.lit (.int 1))) (.val v)) ∗ stepPre i G R }}}
        (Exp.allocN (.val (.lit (.int 1))) (.val v)) @ s; i; E
      l{{{ (l : Loc), RET Val.lit (.loc l); threadExpr i C (.val (.lit (.loc l))) ∗
        stepPost i G R o ∗ l ↦ some v }}} := sorry

@[lantana_alias heap_lang.lwp_free]
theorem lwp_free (l : Loc) (v : Val) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.free (.val (.lit (.loc l)))) ∗ stepPre i G R ∗ l ↦ some v }}}
        (Exp.free (.val (.lit (.loc l)))) @ s; i; E
      l{{{ RET Val.lit .unit; threadExpr i C (.val (.lit .unit)) ∗ stepPost i G R o ∗
        l ↦ (none : Option Val) }}} := sorry

@[lantana_alias heap_lang.lwp_load]
theorem lwp_load (l : Loc) (dq : DFrac) (v : Val) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.load (.val (.lit (.loc l)))) ∗ stepPre i G R ∗ l ↦{dq} some v }}}
        (Exp.load (.val (.lit (.loc l)))) @ s; i; E
      l{{{ RET v; threadExpr i C (.val v) ∗ stepPost i G R o ∗ l ↦{dq} some v }}} := sorry

@[lantana_alias heap_lang.lwp_store]
theorem lwp_store (l : Loc) (v' v : Val) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.store (.val (.lit (.loc l))) (.val v)) ∗ stepPre i G R ∗
          l ↦ some v' }}}
        (Exp.store (.val (.lit (.loc l))) (.val v)) @ s; i; E
      l{{{ RET Val.lit .unit; threadExpr i C (.val (.lit .unit)) ∗ stepPost i G R o ∗
        l ↦ some v }}} := sorry

@[lantana_alias heap_lang.lwp_xchg]
theorem lwp_xchg (l : Loc) (v' v : Val) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.xchg (.val (.lit (.loc l))) (.val v)) ∗ stepPre i G R ∗
          l ↦ some v' }}}
        (Exp.xchg (.val (.lit (.loc l))) (.val v)) @ s; i; E
      l{{{ RET v'; threadExpr i C (.val v') ∗ stepPost i G R o ∗ l ↦ some v }}} := sorry

@[lantana_alias heap_lang.lwp_cmpxchg_fail]
theorem lwp_cmpXchg_fail (l : Loc) (dq : DFrac) (v' v₁ v₂ : Val) (hne : v' ≠ v₁)
    (hsafe : Val.compareSafe v' v₁) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.cmpXchg (.val (.lit (.loc l))) (.val v₁) (.val v₂)) ∗
          stepPre i G R ∗ l ↦{dq} some v' }}}
        (Exp.cmpXchg (.val (.lit (.loc l))) (.val v₁) (.val v₂)) @ s; i; E
      l{{{ RET Val.pair v' (.lit (.bool false));
        threadExpr i C (.val (.pair v' (.lit (.bool false)))) ∗ stepPost i G R o ∗
        l ↦{dq} some v' }}} := sorry

@[lantana_alias heap_lang.lwp_cmpxchg_suc]
theorem lwp_cmpXchg_suc (l : Loc) (v' v₁ v₂ : Val) (heq : v' = v₁)
    (hsafe : Val.compareSafe v' v₁) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.cmpXchg (.val (.lit (.loc l))) (.val v₁) (.val v₂)) ∗
          stepPre i G R ∗ l ↦ some v' }}}
        (Exp.cmpXchg (.val (.lit (.loc l))) (.val v₁) (.val v₂)) @ s; i; E
      l{{{ RET Val.pair v' (.lit (.bool true));
        threadExpr i C (.val (.pair v' (.lit (.bool true)))) ∗ stepPost i G R o ∗
        l ↦ some v₂ }}} := sorry

@[lantana_alias heap_lang.lwp_faa]
theorem lwp_faa (l : Loc) (n₁ n₂ : Int) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.faa (.val (.lit (.loc l))) (.val (.lit (.int n₂)))) ∗
          stepPre i G R ∗ l ↦ some (Val.lit (.int n₁)) }}}
        (Exp.faa (.val (.lit (.loc l))) (.val (.lit (.int n₂)))) @ s; i; E
      l{{{ RET Val.lit (.int n₁); threadExpr i C (.val (.lit (.int n₁))) ∗ stepPost i G R o ∗
        l ↦ some (Val.lit (.int (n₁ + n₂))) }}} := sorry

end Laws

end Lantana.HeapLang
