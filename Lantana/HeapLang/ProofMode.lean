/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
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
* `lwp_step`, `lwp_pure`, `lwp_bind e'` without hypothesis names, `lwp_expr_eval` and
  `lwp_pures` (the last section): the token, the children and the fuel found by their shape.
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
  ihave H := (Obl.fuel_eq _ (ℓ := ℓ) (μ₂ := (n : Measure) + (m : Measure))
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
  iapply lwp_bind_fill K
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

variable [ModelGS GF] [HeapGS GF] [TemporalInterp Exp State GF]
variable {s : Stuckness} {i : ThreadId} {E : CoPset} {C : List ECtxItem}

/-- A pure step of the redex of `e` that observes no witness (`tac_lwp_pure` with `R = ∅`),
paid with one of the `m + 1` units of fuel of the children `G`; it gives back `£ₒ o`. -/
theorem tac_lwp_step {e e' : Exp} {φ : Prop} [PureExecCtx φ 1 e e'] (hφ : φ) (o : Fuel)
    (Φ : Val → IProp GF) {G : Oids} {m : Nat} :
    threadExpr i C e ⊢ thKids i G -∗ oblFuels G ((m + 1 : Nat) : Measure) -∗
      (thKids i G -∗ oblFuels G (m : Measure) -∗ £ₒ o -∗ threadExpr i C e' -∗
        |={E}=>m lWP e' @ s; i; E {{ Φ }}) -∗
      lWP e @ s; i; E {{ Φ }} := by
  iintro HT HG HF H
  iapply tac_lwp_pure hφ Nat.one_pos Φ $$ HT
  iexists G, m, ∅, o
  isplitl [HG HF]
  · rw [Nat.add_comm 1 m]
    iframe HG HF
    iapply witLayers_empty
  iintro HG HF - Ho HT
  iapply H $$ HG HF Ho HT

end Steps

/-- `lwp_pure H`: a pure step of the redex of the goal `lWP e @ s; i; E {{ Φ }}`, paid with the
token `H : threadExpr i C e` (Rocq `lwp_pure`). The pure condition is tried with `trivial`
and `decide`, and is left as the first goal if they fail; the goal left is the existential of
`tac_lwp_pure`. -/
syntax (name := lwpPure) "lwp_pure " colGt ident : tactic

macro_rules
  | `(tactic| lwp_pure $H:ident) =>
    `(tactic| (iapply tac_lwp_pure ?hφ (by decide) $$ $H:ident
               try case hφ => first | trivial | decide))

/-- `lwp_step H HG HF`: a one-step pure reduction of the redex of the goal
`lWP e @ s; i; E {{ Φ }}` that observes no witness (`tac_lwp_step`), with the token
`H : threadExpr i C e`, the children `HG : thKids i G` and their fuel
`HF : oblFuels G ((m + 1 : Nat) : Measure)` (a numeral `oblFuels G 5` unifies too); the three
hypotheses are given back (`HF` with `m` units of fuel, `H` for the new expression) and the
goal is `lWP e' @ s; i; E {{ Φ }}`. `lwp_step H HG HF with Hc : o` also gives the later
credits `Hc : £ₒ o`. The pure condition is handled as by `lwp_pure`. -/
syntax (name := lwpStep) "lwp_step " colGt ident ppSpace colGt ident ppSpace colGt ident
  (" with " ident " : " term)? : tactic

macro_rules
  | `(tactic| lwp_step $H:ident $HG:ident $HF:ident) =>
    `(tactic| (iapply tac_lwp_step ?hφ 0 $$ $H:ident $HG:ident $HF:ident
               try case hφ => first | trivial | decide
               iintro $HG:ident $HF:ident - $H:ident
               imodintro))
  | `(tactic| lwp_step $H:ident $HG:ident $HF:ident with $Hc:ident : $o) =>
    `(tactic| (iapply tac_lwp_step ?hφ $o $$ $H:ident $HG:ident $HF:ident
               try case hφ => first | trivial | decide
               iintro $HG:ident $HF:ident $Hc:ident $H:ident
               imodintro))

/-- `lwp_bind e' H`: focus on the subexpression `e'` of the goal `lWP e @ s; i; E {{ Φ }}`
(Rocq `lwp_bind`); the token `H : threadExpr i C e` becomes `H : threadExpr i (K ++ C) e'`. -/
syntax (name := lwpBind) "lwp_bind " colGt term:max ppSpace colGt ident : tactic

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

/-! ## Finding the hypotheses of a step (D27, M10)

The tactics above take the token, the children and the fuel by name. The variants below find
them in the proof-mode context by their shape, for the thread `i` and the expression `e` of the
goal `lWP e @ s; i; E {{ Φ }}`: the token is the spatial hypothesis `threadExpr i C e` (with the
goal's expression), the children the spatial hypothesis `thKids i G`, and the fuel the spatial
hypothesis `oblFuels G n` of the same `G`; the most recent such hypothesis is taken.

* `lwp_step`, `lwp_step with Hc : o`, `lwp_pure` and `lwp_bind e'` are `lwp_step H HG HF`,
  `lwp_step H HG HF with Hc : o`, `lwp_pure H` and `lwp_bind e' H` with the hypotheses found.
  Before applying a step, `lwp_step` checks that the expression is not a value and finds the
  redex (`PureExecCtx φ 1 e e'`) itself, after `lwp_expr_eval` if there is none and the
  expression has something to compute. (The named tactic, applied to a value or to an
  unsimplified `Exp.subst`, fails its instance search with an error that elaboration recovers
  from; the search for a proof of the then unknown pure condition by `trivial` exceeds the
  maximum recursion depth, an exception that `try` and `repeat` do not catch.)
* `lwp_expr_eval` is `lwp_expr_simp` that also computes the comparisons `v₁ == v₂` of closed
  values (`reduceValBEq`; the result of `instPureExecEqOp`), `decide` of decided propositions
  (the results of `≤` and `<` on integer literals) and the arithmetic of integer literals.
* `lwp_pures` repeats `lwp_step`, giving back the token, the children and the fuel under their
  names and computing the expression with `lwp_expr_eval` when it has something to compute,
  until the expression is a value, has no one-step pure redex, or has one whose pure condition
  `trivial` and `decide` do not prove. It fails if it takes no step; a missing hypothesis or a
  lack of fuel is an error. The `lWP` of a value is left to the caller (`lwp_value'`).
-/

/-- Computes `v₁ == v₂` on closed values (the result of `instPureExecEqOp`), by evaluation. -/
simproc_decl reduceValBEq (@BEq.beq Val _ _ _) := fun e => do
  unless e.isAppOfArity ``BEq.beq 4 do return .continue
  if e.hasFVar || e.hasMVar then return .continue
  let r ← Lean.Meta.whnfD e
  if r.isConstOf ``true || r.isConstOf ``false then return .done { expr := r }
  return .continue

/-- `lwp_expr_eval`: `lwp_expr_simp`, which also computes the comparisons `v₁ == v₂` of closed
values, `decide` of decided propositions (`decide (1 < 2)`) and the arithmetic of integer
literals (`2 + 1`). -/
macro "lwp_expr_eval" : tactic =>
  `(tactic| (
    simp (config := {decide := true}) only
      [Exp.subst, Exp.substStr, Exp.ofVal, ↓reduceIte, List.nil_append, List.append_nil,
        List.cons_append, EctxItemLanguage.fill_append, EctxItemLanguage.fill_nil,
        EctxItemLanguage.fill_cons, fillItem_eq, ECtxItem.fill, Bool.not_true, Bool.not_false,
        reduceValBEq, _root_.decide_true, _root_.decide_false, Int.reduceAdd, Int.reduceSub,
        Int.reduceMul, Int.reduceNeg]
    try simp only [val_to_ofVal]))

section AutoStep

open Lean Elab Tactic Meta

/-- The parsed proof-mode goal `lWP e @ s; i; E {{ Φ }}`, its thread `i` and its expression
`e`. -/
meta def lwpGoal? (goal : Expr) : MetaM (Option (IrisGoal × Expr × Expr)) := do
  let some ig := parseIrisGoal? (← instantiateMVars goal) | return none
  let g := ig.goal.consumeMData
  unless g.isAppOfArity ``Lwp.lwp 11 do return none
  return some (ig, g.getArg! 7, g.getArg! 9)

/-- `a` and `b` are equal up to reducible unfolding (no metavariable is assigned). -/
meta def eqReducible (a b : Expr) : MetaM Bool :=
  withNewMCtxDepth <| withReducible <| isDefEq a b

/-- The last `k` arguments of an application of the constant `c`. -/
meta def lastArgs? (ty : Expr) (c : Name) (k : Nat) : Option (Array Expr) :=
  if ty.getAppFn.isConstOf c && ty.getAppNumArgs ≥ k then
    some (ty.getAppArgs.extract (ty.getAppNumArgs - k) ty.getAppNumArgs)
  else none

/-- The name and type of the most recent spatial hypothesis whose type satisfies `p`. -/
meta def findSpatialHyp {u : Level} {prop bi e : Expr} (hyps : @Hyps u prop bi e)
    (p : Expr → MetaM Bool) : MetaM (Option (Name × Expr)) := do
  let r ← hyps.findM? fun _ _ b ty => do
    if isTrue b then return false
    p ty.consumeMData
  return r.map fun (n, _, _, ty) => (n, ty.consumeMData)

/-- The token `threadExpr i C e` of the thread `i` with the expression `e`. -/
meta def findToken (tac : String) {u : Level} {prop bi e₀ : Expr} (hyps : @Hyps u prop bi e₀)
    (i e : Expr) : MetaM Name := do
  let some (n, _) ← findSpatialHyp hyps fun ty => do
      let some #[i', _, e'] := lastArgs? ty ``threadExpr 3 | return false
      eqReducible i' i <&&> eqReducible e' e
    | throwError "{tac}: no hypothesis threadExpr {i} _{indentExpr e}\n(the token of the thread)"
  return n

/-- The children `thKids i G` of the thread `i` and their fuel `oblFuels G n`. -/
meta def findKidsFuel (tac : String) {u : Level} {prop bi e₀ : Expr}
    (hyps : @Hyps u prop bi e₀) (i : Expr) : MetaM (Name × Name) := do
  let some (nG, tyG) ← findSpatialHyp hyps fun ty => do
      let some #[p, _] := lastArgs? ty ``Par.kids 2 | return false
      let some #[i'] := lastArgs? p ``Parent.thread 1 | return false
      eqReducible i' i
    | throwError "{tac}: no hypothesis thKids {i} _ (the children of the thread)"
  let G := tyG.getAppArgs.back!
  let some (nF, _) ← findSpatialHyp hyps fun ty => do
      let some #[G', _] := lastArgs? ty ``oblFuels 2 | return false
      eqReducible G' G
    | throwError "{tac}: no hypothesis oblFuels {G} _ (the fuel of the children of the thread)"
  return (nG, nF)

/-- The names of the hypotheses of a step: the token, the children and their fuel. -/
structure StepHyps where
  token : Name
  kids : Name
  fuel : Name

/-- `e` is a value: `Exp.val v` (`Exp.ofVal v`) up to instance unfolding. -/
meta def isValExp (e : Expr) : MetaM Bool :=
  return (← withTransparency .instances <| whnf e).isAppOf ``Exp.val

/-- `e` has something for `lwp_expr_eval` to compute: a substitution, a context, a negation, a
comparison, a `decide` or an arithmetic operation. -/
meta def needsEval (e : Expr) : Bool :=
  (e.find? fun x => x.isConst && [``Exp.subst, ``EvContext.fill, ``EctxItemLanguage.fillItem,
    ``ECtxItem.fill, ``BEq.beq, ``not, ``Decidable.decide, ``HAdd.hAdd, ``HSub.hSub,
    ``HMul.hMul, ``Neg.neg].contains x.constName!).isSome

/-- The pure condition `φ` of the one-step pure redex of `e` (`PureExecCtx φ 1 e e'`). -/
meta def findPureRedex? (e : Expr) : MetaM (Option Expr) := do
  let φ ← mkFreshExprMVar (mkSort .zero)
  let n ← mkFreshExprMVar (mkConst ``Nat)
  let e' ← mkFreshExprMVar (mkConst ``Exp)
  let some _ ← synthInstance? (mkAppN (mkConst ``PureExecCtx) #[φ, n, e, e']) | return none
  unless (← whnfD (← instantiateMVars n)).rawNatLit? == some 1 do return none
  return some (← instantiateMVars φ)

/-- The pure condition `φ` is proved by `trivial` or `decide` (nothing is assigned). -/
meta def provesPureCond (φ : Expr) : TacticM Bool := withMainContext do
  if φ.hasMVar then return false
  let saved ← saveState
  let m ← mkFreshExprMVar φ
  let ok ← try
      let gs ← Term.withoutErrToSorry <| Tactic.run m.mvarId! <|
        evalTactic (← `(tactic| first | trivial | decide))
      pure gs.isEmpty
    catch _ => pure false
  saved.restore
  return ok

/-- What a step finds in the main goal. -/
inductive StepView where
  /-- The goal is not an `lWP` of the proof mode. -/
  | notLwp
  /-- The expression is a value. -/
  | value
  /-- The expression `e` has no one-step pure redex. -/
  | noRedex (e : Expr)
  /-- A pure step with the pure condition `φ`, and the hypotheses that pay for it. -/
  | step (φ : Expr) (hyps : StepHyps)

/-- The view of the main goal; with `eval`, an expression without redex is computed with
`lwp_expr_eval` first (once) if it has something to compute. -/
meta partial def stepView (tac : String) (eval : Bool := true) : TacticM StepView :=
    withMainContext do
  let some (ig, i, e) ← lwpGoal? (← getMainTarget) | return .notLwp
  if ← isValExp e then return .value
  match ← findPureRedex? e with
  | some φ =>
    let token ← findToken tac ig.hyps i e
    let (kids, fuel) ← findKidsFuel tac ig.hyps i
    return .step φ { token, kids, fuel }
  | none =>
    if eval && needsEval e then
      let done ← try
          evalTactic (← `(tactic| lwp_expr_eval))
          pure true
        catch _ => pure false
      if done then return ← stepView tac (eval := false)
    return .noRedex e

/-- The named `lwp_step` with the hypotheses `h`, raising the errors of its elaboration. -/
meta def runStep (tac : String) (h : StepHyps) (with? : Option (TSyntax `ident × Term)) :
    TacticM Unit := do
  let (H, HG, HF) := (mkIdent h.token, mkIdent h.kids, mkIdent h.fuel)
  let stx ← match with? with
    | none => `(tactic| lwp_step $H $HG $HF)
    | some (Hc, o) => `(tactic| lwp_step $H $HG $HF with $Hc : $o)
  try Term.withoutErrToSorry <| evalTactic stx
  catch ex => throwError "{tac}: the step with {H} {HG} {HF} fails (is there fuel left in \
    {HF}?):{indentD ex.toMessageData}"

/-- The reason why the view `v` is not a step, as an error of the tactic `tac`. -/
meta def throwNoStep {α} (tac : String) : StepView → TacticM α
  | .notLwp => throwError "{tac}: the goal is not an lWP of the proof mode"
  | .value => throwError "{tac}: the expression is a value"
  | .noRedex e => throwError "{tac}: no one-step pure redex in{indentExpr e}"
  | .step φ _ => throwError "{tac}: the pure condition{indentExpr φ}\nis not proved by trivial \
      or decide"

/-- `lwp_step` with the hypotheses found. -/
meta def evalLwpStepAuto (with? : Option (TSyntax `ident × Term)) : TacticM Unit := do
  match ← stepView "lwp_step" with
  | .step _ h => runStep "lwp_step" h with?
  | v => throwNoStep "lwp_step" v

/-- The steps of `lwp_pures`, at most `bound`; the number of steps taken. -/
meta partial def lwpPuresLoop (bound : Nat) (taken : Nat := 0) : TacticM Nat := do
  if taken ≥ bound then return taken
  let .step φ h ← stepView "lwp_pures" | return taken
  unless ← provesPureCond φ do return taken
  runStep "lwp_pures" h none
  if let some (_, _, e) ← withMainContext do lwpGoal? (← getMainTarget) then
    if needsEval e then
      try evalTactic (← `(tactic| lwp_expr_eval)) catch _ => pure ()
  lwpPuresLoop bound (taken + 1)

/-- The token of the goal's thread and expression. -/
meta def findGoalToken (tac : String) : TacticM (TSyntax `ident) := withMainContext do
  let some (ig, i, e) ← lwpGoal? (← getMainTarget)
    | throwError "{tac}: the goal is not an lWP of the proof mode"
  return mkIdent (← findToken tac ig.hyps i e)


/-- `lwp_step`: `lwp_step H HG HF` with the token `H : threadExpr i C e` of the goal's thread and
expression, the children `HG : thKids i G` and their fuel `HF : oblFuels G n` found in the
context; `lwp_step with Hc : o` also gives the later credits `Hc : £ₒ o`. It fails with an error
on a value, or on an expression without a one-step pure redex (after `lwp_expr_eval`). -/
syntax (name := lwpStepAuto) "lwp_step" (" with " ident " : " term)? : tactic

elab_rules : tactic
  | `(tactic| lwp_step) => evalLwpStepAuto none
  | `(tactic| lwp_step with $Hc:ident : $o) => evalLwpStepAuto (some (Hc, o))

/-- `lwp_pure`: `lwp_pure H` with the token `H` of the goal's thread and expression. -/
syntax (name := lwpPureAuto) "lwp_pure" : tactic

elab_rules : tactic
  | `(tactic| lwp_pure) => do
    let H ← findGoalToken "lwp_pure"
    evalTactic (← `(tactic| lwp_pure $H))

/-- `lwp_bind e'`: `lwp_bind e' H` with the token `H` of the goal's thread and expression. -/
syntax (name := lwpBindAuto) "lwp_bind " colGt term:max : tactic

elab_rules : tactic
  | `(tactic| lwp_bind $e') => do
    let H ← findGoalToken "lwp_bind"
    evalTactic (← `(tactic| lwp_bind $e' $H))

/-- `lwp_pures`: `lwp_step` repeated (with `lwp_expr_eval` when the expression has something to
compute) until the expression is a value, has no one-step pure redex, or has one whose pure
condition `trivial` and `decide` do not prove; it fails if no step is taken. -/
syntax (name := lwpPures) "lwp_pures" : tactic

elab_rules : tactic
  | `(tactic| lwp_pures) => do
    if (← lwpPuresLoop 10000) == 0 then throwNoStep "lwp_pures" (← stepView "lwp_pures")

end AutoStep

end Lantana.HeapLang
