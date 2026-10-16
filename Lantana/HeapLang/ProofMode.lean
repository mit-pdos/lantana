/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.HeapLang.PrimitiveLaws

/-! # Proof-mode support for HeapLang: paid pure steps

Rocq `lantana_heap_lang/proofmode.v` (`tac_lwp_pure_simple`, `lwp_pure`), D27. A pure step of
thread `i` needs its token `threadExpr i C e`, one unit of fuel of each child of the thread per
step, and the witness layers; it gives back the witnesses' credits and later credits.

* `PureExecCtx φ n e e'`: `e` reaches `e'` by `n` pure steps of the redex of `e` (in its
  evaluation context), found by instance search through the context items (Rocq
  `reshape_expr` and `PureExec` search) — the instances follow the right-to-left evaluation
  order, and the redex is found by the `PureExec` instances of `Instances`.
* `tac_lwp_pure`: the pure step of the redex of the goal's expression, with fuel `n + m` of the
  children `G`, of which `m` units are left.
* `lwp_pure H`: applies `tac_lwp_pure` with the token `H`, proves the side conditions it can
  (the pure condition and `0 < n`), and leaves the goal
  `∃ G m R o, (thKids i G ∗ oblFuels G (n + m) ∗ witLayers R) ∗ (thKids i G -∗ oblFuels G m -∗
  witCreds R -∗ £ₒ o -∗ threadExpr i C e' -∗ |={E}=>m lWP e' …)`, as Rocq's `lwp_pure` does.
* `PureExec` instances for the common operations with their results computed (`~#b`, `+`, `-`,
  `≤`, `<` on integers), which the generic ones of `Instances` cannot provide to instance search.
* `stepPre_nil`, `stepPre_wit`, `witLayers_empty`, `witCreds_singleton`: the bookkeeping of the
  witnesses of a step.
-/

@[expose] public noncomputable section

namespace Lantana.HeapLang

open Iris Iris.BI Iris.ProofMode Lantana Lantana.Language

/-- `e` reaches `e'` by `n` pure steps of its redex, under `φ`: the redex is found in the
evaluation context of `e` by instance search. -/
class PureExecCtx (φ : outParam Prop) (n : outParam Nat) (e : Exp) (e' : outParam Exp) :
    Prop where
  pureExecCtx : PureExec φ n e e'

/-- The items of HeapLang's contexts (for `simp`). -/
theorem fillItem_eq (Ki : ECtxItem) (e : Exp) : EctxItemLanguage.fillItem Ki e = Ki.fill e := rfl

namespace PureExecCtx

/-- The redex itself. -/
instance (priority := low) ofPureExec {φ : Prop} {n : Nat} {e e' : Exp} [h : PureExec φ n e e'] :
    PureExecCtx φ n e e' :=
  ⟨h⟩

/-- The redex is inside the item `Ki`. -/
theorem fillItem {φ : Prop} {n : Nat} {e e' : Exp} (Ki : ECtxItem) (h : PureExecCtx φ n e e') :
    PureExecCtx φ n (Ki.fill e) (Ki.fill e') :=
  ⟨EctxLanguage.pureExec_fill [Ki] h.pureExecCtx⟩

variable {φ : Prop} {n : Nat} {e e' e₀ e₁ e₂ : Exp} {v v₁ v₂ : Val}

instance appR [h : PureExecCtx φ n e e'] : PureExecCtx φ n (.app e₁ e) (.app e₁ e') :=
  fillItem (.appR e₁) h
instance appL [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.app e (.ofVal v₂)) (.app e' (.ofVal v₂)) :=
  fillItem (.appL v₂) h
instance unOp {op : UnOp} [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.unop op e) (.unop op e') :=
  fillItem (.unOp op) h
instance binOpR {op : BinOp} [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.binop op e₁ e) (.binop op e₁ e') :=
  fillItem (.binOpR op e₁) h
instance binOpL {op : BinOp} [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.binop op e (.ofVal v₂)) (.binop op e' (.ofVal v₂)) :=
  fillItem (.binOpL op v₂) h
instance «if» [h : PureExecCtx φ n e e'] : PureExecCtx φ n (.if e e₁ e₂) (.if e' e₁ e₂) :=
  fillItem (.if e₁ e₂) h
instance pairR [h : PureExecCtx φ n e e'] : PureExecCtx φ n (.pair e₁ e) (.pair e₁ e') :=
  fillItem (.pairR e₁) h
instance pairL [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.pair e (.ofVal v₂)) (.pair e' (.ofVal v₂)) :=
  fillItem (.pairL v₂) h
instance fst [h : PureExecCtx φ n e e'] : PureExecCtx φ n (.fst e) (.fst e') :=
  fillItem .fst h
instance snd [h : PureExecCtx φ n e e'] : PureExecCtx φ n (.snd e) (.snd e') :=
  fillItem .snd h
instance injL [h : PureExecCtx φ n e e'] : PureExecCtx φ n (.injL e) (.injL e') :=
  fillItem .injL h
instance injR [h : PureExecCtx φ n e e'] : PureExecCtx φ n (.injR e) (.injR e') :=
  fillItem .injR h
instance case [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.case e e₁ e₂) (.case e' e₁ e₂) :=
  fillItem (.case e₁ e₂) h
instance allocNR [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.allocN e₁ e) (.allocN e₁ e') :=
  fillItem (.allocNR e₁) h
instance allocNL [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.allocN e (.ofVal v₂)) (.allocN e' (.ofVal v₂)) :=
  fillItem (.allocNL v₂) h
instance free [h : PureExecCtx φ n e e'] : PureExecCtx φ n (.free e) (.free e') :=
  fillItem .free h
instance load [h : PureExecCtx φ n e e'] : PureExecCtx φ n (.load e) (.load e') :=
  fillItem .load h
instance storeR [h : PureExecCtx φ n e e'] : PureExecCtx φ n (.store e₁ e) (.store e₁ e') :=
  fillItem (.storeR e₁) h
instance storeL [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.store e (.ofVal v₂)) (.store e' (.ofVal v₂)) :=
  fillItem (.storeL v₂) h
instance xchgR [h : PureExecCtx φ n e e'] : PureExecCtx φ n (.xchg e₁ e) (.xchg e₁ e') :=
  fillItem (.xchgR e₁) h
instance xchgL [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.xchg e (.ofVal v₂)) (.xchg e' (.ofVal v₂)) :=
  fillItem (.xchgL v₂) h
instance cmpXchgR [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.cmpXchg e₀ e₁ e) (.cmpXchg e₀ e₁ e') :=
  fillItem (.cmpXchgR e₀ e₁) h
instance cmpXchgM [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.cmpXchg e₀ e (.ofVal v₂)) (.cmpXchg e₀ e' (.ofVal v₂)) :=
  fillItem (.cmpXchgM e₀ v₂) h
instance cmpXchgL [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.cmpXchg e (.ofVal v₁) (.ofVal v₂)) (.cmpXchg e' (.ofVal v₁) (.ofVal v₂)) :=
  fillItem (.cmpXchgL v₁ v₂) h
instance faaR [h : PureExecCtx φ n e e'] : PureExecCtx φ n (.faa e₁ e) (.faa e₁ e') :=
  fillItem (.faaR e₁) h
instance faaL [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.faa e (.ofVal v₂)) (.faa e' (.ofVal v₂)) :=
  fillItem (.faaL v₂) h
instance label {t : String} [h : PureExecCtx φ n e e'] :
    PureExecCtx φ n (.label t e) (.label t e') :=
  fillItem (.label t) h

end PureExecCtx

/-! ### Operations with a computed result

The generic `instPureExecUnOp` and `instPureExecBinOp` of `Instances` leave the result `v'` of
the operation to their pure condition `op.eval v = some v'`, so instance search cannot use them
(the result of `PureExec` is an `outParam`). These instances give the result of the common
operations directly. -/

section Ops

variable {b : Bool} {n₁ n₂ : Int}

/-- `~#b` (Rocq `pure_unop` for booleans). -/
instance instPureExecNegBool :
    PureExec True 1 (Exp.unop .neg (.ofVal (.lit (.bool b)))) (.ofVal (.lit (.bool !b))) :=
  ⟨fun _ => (instPureExecUnOp (op := .neg) (v := .lit (.bool b))
    (v' := .lit (.bool !b))).pureExec rfl⟩

/-- `#n₁ + #n₂`. -/
instance instPureExecPlusInt :
    PureExec True 1 (Exp.binop .plus (.ofVal (.lit (.int n₁))) (.ofVal (.lit (.int n₂))))
      (.ofVal (.lit (.int (n₁ + n₂)))) :=
  ⟨fun _ => (instPureExecBinOp (op := .plus) (v1 := .lit (.int n₁)) (v2 := .lit (.int n₂))
    (v' := .lit (.int (n₁ + n₂)))).pureExec rfl⟩

/-- `#n₁ - #n₂`. -/
instance instPureExecMinusInt :
    PureExec True 1 (Exp.binop .minus (.ofVal (.lit (.int n₁))) (.ofVal (.lit (.int n₂))))
      (.ofVal (.lit (.int (n₁ - n₂)))) :=
  ⟨fun _ => (instPureExecBinOp (op := .minus) (v1 := .lit (.int n₁)) (v2 := .lit (.int n₂))
    (v' := .lit (.int (n₁ - n₂)))).pureExec rfl⟩

/-- `#n₁ ≤ #n₂`. -/
instance instPureExecLeInt :
    PureExec True 1 (Exp.binop .le (.ofVal (.lit (.int n₁))) (.ofVal (.lit (.int n₂))))
      (.ofVal (.lit (.bool (decide (n₁ ≤ n₂))))) :=
  ⟨fun _ => (instPureExecBinOp (op := .le) (v1 := .lit (.int n₁)) (v2 := .lit (.int n₂))
    (v' := .lit (.bool (decide (n₁ ≤ n₂))))).pureExec rfl⟩

/-- `#n₁ < #n₂`. -/
instance instPureExecLtInt :
    PureExec True 1 (Exp.binop .lt (.ofVal (.lit (.int n₁))) (.ofVal (.lit (.int n₂))))
      (.ofVal (.lit (.bool (decide (n₁ < n₂))))) :=
  ⟨fun _ => (instPureExecBinOp (op := .lt) (v1 := .lit (.int n₁)) (v2 := .lit (.int n₂))
    (v' := .lit (.bool (decide (n₁ < n₂))))).pureExec rfl⟩

end Ops

/-- `e'` is a subexpression of `e` in evaluation position: `e = fill K e'`. The context is found
by instance search through the context items of `e`, outermost first. -/
class InCtx (e' : Exp) (e : Exp) (K : outParam (List ECtxItem)) : Prop where
  eq_fill : fill K e' = e

namespace InCtx

/-- The subexpression itself. -/
instance (priority := high) refl {e : Exp} : InCtx e e [] := ⟨rfl⟩

/-- The subexpression is inside the item `Ki`. -/
theorem fillItem {e' e : Exp} {K : List ECtxItem} (Ki : ECtxItem) (h : InCtx e' e K) :
    InCtx e' (Ki.fill e) (K ++ [Ki]) :=
  ⟨by rw [EctxItemLanguage.fill_append, ← h.eq_fill]; rfl⟩

variable {e e' e₀ e₁ e₂ : Exp} {K : List ECtxItem} {v₁ v₂ : Val}

instance appR [h : InCtx e' e K] : InCtx e' (.app e₁ e) (K ++ [.appR e₁]) :=
  fillItem (.appR e₁) h
instance appL [h : InCtx e' e K] : InCtx e' (.app e (.ofVal v₂)) (K ++ [.appL v₂]) :=
  fillItem (.appL v₂) h
instance unOp {op : UnOp} [h : InCtx e' e K] : InCtx e' (.unop op e) (K ++ [.unOp op]) :=
  fillItem (.unOp op) h
instance binOpR {op : BinOp} [h : InCtx e' e K] :
    InCtx e' (.binop op e₁ e) (K ++ [.binOpR op e₁]) :=
  fillItem (.binOpR op e₁) h
instance binOpL {op : BinOp} [h : InCtx e' e K] :
    InCtx e' (.binop op e (.ofVal v₂)) (K ++ [.binOpL op v₂]) :=
  fillItem (.binOpL op v₂) h
instance «if» [h : InCtx e' e K] : InCtx e' (.if e e₁ e₂) (K ++ [.if e₁ e₂]) :=
  fillItem (.if e₁ e₂) h
instance pairR [h : InCtx e' e K] : InCtx e' (.pair e₁ e) (K ++ [.pairR e₁]) :=
  fillItem (.pairR e₁) h
instance pairL [h : InCtx e' e K] : InCtx e' (.pair e (.ofVal v₂)) (K ++ [.pairL v₂]) :=
  fillItem (.pairL v₂) h
instance fst [h : InCtx e' e K] : InCtx e' (.fst e) (K ++ [.fst]) := fillItem .fst h
instance snd [h : InCtx e' e K] : InCtx e' (.snd e) (K ++ [.snd]) := fillItem .snd h
instance injL [h : InCtx e' e K] : InCtx e' (.injL e) (K ++ [.injL]) := fillItem .injL h
instance injR [h : InCtx e' e K] : InCtx e' (.injR e) (K ++ [.injR]) := fillItem .injR h
instance case [h : InCtx e' e K] : InCtx e' (.case e e₁ e₂) (K ++ [.case e₁ e₂]) :=
  fillItem (.case e₁ e₂) h
instance allocNR [h : InCtx e' e K] : InCtx e' (.allocN e₁ e) (K ++ [.allocNR e₁]) :=
  fillItem (.allocNR e₁) h
instance allocNL [h : InCtx e' e K] : InCtx e' (.allocN e (.ofVal v₂)) (K ++ [.allocNL v₂]) :=
  fillItem (.allocNL v₂) h
instance free [h : InCtx e' e K] : InCtx e' (.free e) (K ++ [.free]) := fillItem .free h
instance load [h : InCtx e' e K] : InCtx e' (.load e) (K ++ [.load]) := fillItem .load h
instance storeR [h : InCtx e' e K] : InCtx e' (.store e₁ e) (K ++ [.storeR e₁]) :=
  fillItem (.storeR e₁) h
instance storeL [h : InCtx e' e K] : InCtx e' (.store e (.ofVal v₂)) (K ++ [.storeL v₂]) :=
  fillItem (.storeL v₂) h
instance xchgR [h : InCtx e' e K] : InCtx e' (.xchg e₁ e) (K ++ [.xchgR e₁]) :=
  fillItem (.xchgR e₁) h
instance xchgL [h : InCtx e' e K] : InCtx e' (.xchg e (.ofVal v₂)) (K ++ [.xchgL v₂]) :=
  fillItem (.xchgL v₂) h
instance cmpXchgR [h : InCtx e' e K] :
    InCtx e' (.cmpXchg e₀ e₁ e) (K ++ [.cmpXchgR e₀ e₁]) :=
  fillItem (.cmpXchgR e₀ e₁) h
instance cmpXchgM [h : InCtx e' e K] :
    InCtx e' (.cmpXchg e₀ e (.ofVal v₂)) (K ++ [.cmpXchgM e₀ v₂]) :=
  fillItem (.cmpXchgM e₀ v₂) h
instance cmpXchgL [h : InCtx e' e K] :
    InCtx e' (.cmpXchg e (.ofVal v₁) (.ofVal v₂)) (K ++ [.cmpXchgL v₁ v₂]) :=
  fillItem (.cmpXchgL v₁ v₂) h
instance faaR [h : InCtx e' e K] : InCtx e' (.faa e₁ e) (K ++ [.faaR e₁]) :=
  fillItem (.faaR e₁) h
instance faaL [h : InCtx e' e K] : InCtx e' (.faa e (.ofVal v₂)) (K ++ [.faaL v₂]) :=
  fillItem (.faaL v₂) h
instance label {t : String} [h : InCtx e' e K] : InCtx e' (.label t e) (K ++ [.label t]) :=
  fillItem (.label t) h

end InCtx

section Tactic

variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TemporalInterp Exp State GF]
variable {s : Stuckness} {i : ThreadId} {E : CoPset} {C : List ECtxItem}

omit [HeapGS GF] [TemporalInterp Exp State GF] in
/-- `n + m` units of fuel are `n` units and `m` units. -/
theorem oblFuels_add (G : Oids) (n m : Nat) :
    oblFuels (GF := GF) G ((n + m : Nat) : Measure) ⊢
      oblFuels G (n : Measure) ∗ oblFuels G (m : Measure) := by
  unfold oblFuels
  refine (BigSepS.bigSepS_mono fun _ => ?_).trans BigSepS.bigSepS_sep.mp
  iintro ⟨%ℓ, H⟩
  ihave H := (Obl.fuel_eq _ (ℓ₁ := ℓ) (ℓ₂ := ℓ) (μ₂ := (n : Measure) + (m : Measure))
    (by rw [Measure.rep_nat_add, Measure.rep_add])).mp $$ H
  icases (Obl.fuel_add _ ℓ _ _).mp $$ H with ⟨H1, H2⟩
  isplitl [H1]
  · iexists ℓ
    iexact H1
  · iexists ℓ
    iexact H2

/-- The pure step of the redex of `e` (Rocq `tac_lwp_pure_simple`): the token, then the
children `G` with `n + m` units of fuel, of which `m` are left, the witnesses `R`, and the
later credits `o`. -/
@[lantana_alias heap_lang.tac_lwp_pure_simple]
theorem tac_lwp_pure {e e' : Exp} {φ : Prop} {n : Nat} [hpe : PureExecCtx φ n e e'] (hφ : φ)
    (hn : 0 < n) (Φ : Val → IProp GF) :
    threadExpr i C e ⊢
      (∃ (G : Oids) (m : Nat) (R : Oids) (o : Fuel),
        (thKids i G ∗ oblFuels G ((n + m : Nat) : Measure) ∗ witLayers R) ∗
        (thKids i G -∗ oblFuels G (m : Measure) -∗ witCreds R -∗ £ₒ o -∗ threadExpr i C e' -∗
          |={E}=>m lWP e' @ s; i; E {{ Φ }})) -∗
      lWP e @ s; i; E {{ Φ }} := by
  haveI := hpe.pureExecCtx
  iintro HT ⟨%G, %m, %R, %o, ⟨HG, HF, HR⟩, H⟩
  icases oblFuels_add G n m $$ HF with ⟨HF, HFm⟩
  iapply lwp_pure_step (o := o) n e e' φ Φ hφ hn
  iframe HT HG HF HR
  iintro HT HG HW Ho
  iapply H $$ HG HFm HW Ho HT

/-- Binding the subexpression `e'` of `e` (Rocq `tac_lwp_bind_gen`): the token moves its context
`K` from the expression to the context of the token. -/
@[lantana_alias heap_lang.tac_lwp_bind_gen]
theorem tac_lwp_bind (e' : Exp) {e : Exp} {K : List ECtxItem} [h : InCtx e' e K]
    (Φ : Val → IProp GF) :
    threadExpr i C e ⊢
      (threadExpr i (K ++ C) e' -∗
        lWP e' @ s; i; E {{ v, lWP (fill K (Exp.ofVal v : Exp)) @ s; i; E {{ Φ }} }}) -∗
      lWP e @ s; i; E {{ Φ }} := by
  iintro HT H
  rw [← h.eq_fill]
  iapply lwp_bind (fill K)
  iapply H
  iapply (threadExpr_fill i C K e').mp $$ HT

end Tactic

/-! ### The bookkeeping of a step -/

section Steps

variable {GF : BundledGFunctors}

/-- No witnesses. -/
theorem witLayers_empty [ModelGS GF] : ⊢ witLayers (GF := GF) ∅ := by
  unfold witLayers
  iapply BigSepS.bigSepS_empty.mpr
  iempintro

/-- The precondition of a step without witnesses. -/
theorem stepPre_nil [ModelGS GF] (i : ThreadId) (G : Oids) :
    thKids i G ⊢ oblFuels G ((1 : Nat) : Measure) -∗ stepPre (GF := GF) i G ∅ := by
  iintro HG HF
  simp only [stepPre]
  iframe HG HF
  iapply witLayers_empty

/-- The precondition of a step that observes the witness `k` (of layer `ℓ`). -/
theorem stepPre_wit [ModelGS GF] (i : ThreadId) (G : Oids) (k : Oid) (ℓ : Layer) :
    thKids i G ⊢ oblFuels G ((1 : Nat) : Measure) -∗ Wit.layer k ℓ -∗
      stepPre (GF := GF) i G {k} := by
  iintro HG HF Hk
  simp only [stepPre]
  iframe HG HF
  unfold witLayers
  iapply BigSepS.bigSepS_singleton.mpr
  iexists ℓ
  iexact Hk

/-- What a step that observes the witness `k` gives back: a credit of `k`, or its discharge. -/
theorem witCreds_singleton [ModelGS GF] (k : Oid) :
    witCreds (GF := GF) {k} ⊢ Wit.cred k 1 ∨ Obl.discharged k := by
  unfold witCreds
  exact BigSepS.bigSepS_singleton.mp

end Steps

/-- `lwp_pure H`: a pure step of the redex of the goal `lWP e @ s; i; E {{ Φ }}`, paid with the
token `H : threadExpr i C e` (Rocq `lwp_pure`). The pure condition is tried with `trivial`
and `decide`, and is left as the first goal if they fail; the goal left is the existential of
`tac_lwp_pure`. -/
syntax (name := lwpPure) "lwp_pure " ident : tactic

macro_rules
  | `(tactic| lwp_pure $H:ident) =>
    `(tactic| (iapply tac_lwp_pure ?hφ (by decide) $$ $H:ident
               try case hφ => first | trivial | decide))

/-- `lwp_bind e' H`: focus on the subexpression `e'` of the goal `lWP e @ s; i; E {{ Φ }}`
(Rocq `lwp_bind`); the token `H : threadExpr i C e` becomes `H : threadExpr i (K ++ C) e'`. -/
syntax (name := lwpBind) "lwp_bind " term:max ppSpace ident : tactic

macro_rules
  | `(tactic| lwp_bind $e $H:ident) =>
    `(tactic| (iapply tac_lwp_bind $e $$ $H:ident; iintro $H:ident))

/-- `lwp_expr_simp`: compute the substitutions, the contexts `fill K e` and the negations `!b` of
the goal (after `lwp_pure` of a `rec` application or of `~#b`, or after `lwp_bind`, Rocq
`lwp_expr_simpl`). The values are then written back as `Exp.ofVal v` (`val_to_ofVal`), the
form that the instances of `PureExecCtx`, `InCtx` and `Atomic` expect, so that `lwp_pure`,
`lwp_bind` and the opening of invariants around atomic expressions apply afterwards. -/
macro "lwp_expr_simp" : tactic =>
  `(tactic| (
    simp (config := {decide := true}) only
      [Exp.subst, Exp.substStr, Exp.ofVal, ↓reduceIte, List.nil_append, List.append_nil,
        List.cons_append, EctxItemLanguage.fill_append, EctxItemLanguage.fill_nil,
        EctxItemLanguage.fill_cons, fillItem_eq, ECtxItem.fill, Bool.not_true, Bool.not_false]
    try simp only [val_to_ofVal]))

end Lantana.HeapLang
