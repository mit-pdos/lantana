module

public import Lantana

/-! HeapLang smoke tests: programs written with the notation elaborate (the flag module of Rocq
`examples/flag.v` and the program of `examples/nondet.v`), the language instance is found,
redexes are atomic and pure steps are found by instance search. -/

namespace LantanaTest.HeapLang

open Lantana Lantana.HeapLang Lantana.Language

/-- Rocq `Flag.init`. -/
def flagInit : Val := hl_val(λ _, ref(#0))

/-- Rocq `Flag.set`. -/
def flagSet : Val := hl_val(λ x, x ← #1)

/-- Rocq `Flag.wait`. -/
def flagWait : Val := hl_val(rec wait x := if ~(!x = #1) then wait x else #1)

/-- Rocq `Nondet.nest`. -/
def nest : Val :=
  hl_val(rec fn x n :=
    if n ≤ #0 then v(&flagSet) x
    else
      let y := v(&flagInit) #();
      fork(fn y (n - #1));
      v(&flagWait) y;
      v(&flagSet) x)

/-- Rocq `Nondet.nondet`. -/
def nondet : Val :=
  hl_val(λ _,
    let n := chooseNat();
    let x := v(&flagInit) #();
    fork(v(&nest) x n);
    v(&flagWait) x)

/-- A labelled program. -/
def labelled : Exp := hl(label("start", v(&flagInit) #()))

example : Lantana.Language Exp State Val := inferInstance

example : EctxLanguage Exp State Val (List ECtxItem) := inferInstance

example (K : List ECtxItem) : Context (fill (Expr := Exp) K) := inferInstance

example : (emptyEctx : List ECtxItem) = [] := rfl

example (K₁ K₂ : List ECtxItem) : compEctx K₁ K₂ = K₂ ++ K₁ := rfl

example : hl(chooseNat()) = Exp.chooseNat := rfl

example : hl(label("t", #1)) = Exp.label "t" (.ofVal (.lit (.int 1))) := rfl

example : PureExec True 1 hl(v(λ x, x) #1) hl(#1) := inferInstance

example : PureExec True 1 hl(label("t", #1)) hl(#1) := inferInstance

example : PureExec True 1 hl(if #true then #1 else #2) hl(#1) := inferInstance

example (v1 v2 : Val) (h : v1.compareSafe v2) :
    Relation.Iterate PureStep 1 hl(&v1 = &v2) (Exp.ofVal (.lit (.bool (v1 == v2)))) :=
  PureExec.pureExec h

example : Atomic .StronglyAtomic hl(chooseNat()) := inferInstance

example (t : String) (v : Val) : Atomic .WeaklyAtomic hl(label(&t, &v)) := inferInstance

example (l : Loc) : Atomic .StronglyAtomic hl(!#l) := inferInstance

example (σ : State) : BaseStep hl(chooseNat()) σ hl(#(5 : Nat)) σ [] := .chooseNatS 5 σ

example (σ : State) :
    primStep hl(label("t", chooseNat())) σ hl(label("t", #(3 : Nat))) σ [] :=
  EctxLanguage.primStep_fill_of_baseStep [ECtxItem.label "t"] (.chooseNatS 3 σ)

example (σ : State) (e : Exp) :
    primStep hl(fork(&e)) σ hl(#()) σ [e] :=
  EctxLanguage.primStep_of_baseStep (.forkS e σ)

example (σ : State) (e : Exp) :
    threadExprSat 1 [ECtxItem.label "t"] e σ [hl(#()), hl(label("t", &e))] :=
  threadExprSat_iff.mpr rfl

set_option linter.deprecated false in
example : RocqLantana.heap_lang.ChooseNat = Exp.chooseNat := rfl

end LantanaTest.HeapLang
