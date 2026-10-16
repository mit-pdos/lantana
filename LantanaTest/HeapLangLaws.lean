module

public import Lantana

/-! Tests for the program logic of HeapLang (M7): the thread-expression token, the step laws
with the bookkeeping of children and witnesses, laws in an evaluation context, the tactics
`lwp_pure`, `lwp_bind`, `lwp_expr_simp`, contexts determined by a step, and the step tactics
that find their hypotheses (`lwp_step`, `lwp_pures`). -/

namespace LantanaTest.HeapLangLaws

open Iris Iris.BI Iris.ProofMode Lantana Lantana.HeapLang Lantana.Language

section

variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TemporalInterp Exp State GF]
variable {s : Stuckness} {i : ThreadId} {E : CoPset} {C : List ECtxItem} {G R : Oids} {o : Fuel}

/-! The token and the state interpretation. -/

example (C : List ECtxItem) : PureExecSI (GF := GF) (fun i e => threadExpr i C e) i :=
  inferInstance

example (σ : State) (tp : ThreadPool Exp) (e : Exp) :
    HeapLang.stateInterp (GF := GF) σ tp ∗ threadExpr i C e ⊢ ⌜tp[i]? = some (fill C e)⌝ := by
  iintro ⟨Hσ, HT⟩
  iapply threadExpr_read $$ Hσ HT

/-! A pure step: the children pay one unit of fuel, the witnesses get one credit. -/

example (Φ : Val → IProp GF) :
    threadExpr i C hl(if #true then #1 else #2) ∗ thKids i G ∗ oblFuels G ((1 : Nat) : Measure) ∗
      witLayers R ∗
      (threadExpr i C hl(#1) -∗ thKids i G -∗ witCreds R -∗ £ₒ o -∗
        |={E}=>m lWP hl(#1) @ s; i; E {{ Φ }})
      ⊢ lWP hl(if #true then #1 else #2) @ s; i; E {{ Φ }} :=
  lwp_pure_step 1 _ _ _ Φ trivial (by omega)

/-! A load, then the value. -/

example (l : Loc) (v : Val) :
    threadExpr i C hl(!#l) ∗ stepPre i G R ∗ l ↦ some v ⊢
      lWP hl(!#l) @ s; i; E {{ w, ⌜w = v⌝ ∗ threadExpr i C (.val v) ∗ stepPost i G R o ∗
        l ↦ some v }} := by
  iintro ⟨HT, Hpre, Hl⟩
  iapply lwp_load (o := o) l (DFrac.own 1) v $$ [HT Hpre Hl]
  · iframe
  · iintro ⟨HT, Hpost, Hl⟩
    iframe
    ipureintro
    rfl

/-! A load in an evaluation context: `lwp_bind` and `threadExpr_fill` move the context from
the expression to the token and back. -/

example (K : List ECtxItem) (l : Loc) (v : Val) (Φ : Val → IProp GF) :
    threadExpr i C (fill K hl(!#l)) ∗ stepPre i G R ∗ l ↦ some v ∗
      (threadExpr i C (fill K (Exp.val v)) -∗ stepPost i G R o -∗ l ↦ some v -∗
        lWP (fill K (Exp.val v)) @ s; i; E {{ Φ }})
      ⊢ lWP (fill K hl(!#l)) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, Hpre, Hl, HΦ⟩
  iapply lwp_bind (fill K)
  ihave HT := (threadExpr_fill i C K _).mp $$ HT
  iapply lwp_load (o := o) l (DFrac.own 1) v $$ [HT Hpre Hl]
  · iframe
  · iintro ⟨HT, Hpost, Hl⟩
    ihave HT := (threadExpr_fill i C K _).mpr $$ HT
    iapply HΦ $$ HT Hpost Hl

/-! A store, and the obligations of a fork. -/

example (l : Loc) (v w : Val) :
    threadExpr i C hl(#l ← &w) ∗ stepPre i G R ∗ l ↦ some v ⊢
      lWP hl(#l ← &w) @ s; i; E {{ _u, stepPost i G R o ∗ l ↦ some w }} := by
  iintro ⟨HT, Hpre, Hl⟩
  iapply lwp_store (o := o) l v w $$ [HT Hpre Hl]
  · iframe
  · iintro ⟨-, Hpost, Hl⟩
    iframe

/-! The tactics: a pure step in a context, then a load in a context. -/

example : PureExecCtx True 1 hl((if #true then #1 else #2) + #3) hl(#1 + #3) := inferInstance

example (Φ : Val → IProp GF) :
    threadExpr i C hl((if #true then #1 else #2) + #3) ∗ thKids i G ∗
      oblFuels G ((1 + 2 : Nat) : Measure) ∗
      (threadExpr i C hl(#1 + #3) -∗ thKids i G -∗ oblFuels G ((2 : Nat) : Measure) -∗
        |={E}=>m lWP hl(#1 + #3) @ s; i; E {{ Φ }})
      ⊢ lWP hl((if #true then #1 else #2) + #3) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, HG, HF, H⟩
  lwp_pure HT
  iexists G, 2, ∅, 0
  isplitl [HG HF]
  · iframe
    unfold witLayers
    iapply BigSepS.bigSepS_empty.mpr
    iempintro
  iintro HG HF - - HT
  iapply H $$ HT HG HF

example (Φ : Val → IProp GF) :
    threadExpr i C hl(v(λ x, x + #1) #2) ∗ thKids i G ∗ oblFuels G ((1 + 0 : Nat) : Measure) ∗
      (threadExpr i C hl(#2 + #1) -∗ |={E}=>m lWP hl(#2 + #1) @ s; i; E {{ Φ }})
      ⊢ lWP hl(v(λ x, x + #1) #2) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, HG, HF, H⟩
  lwp_pure HT
  lwp_expr_simp
  iexists G, 0, ∅, 0
  isplitl [HG HF]
  · iframe
    unfold witLayers
    iapply BigSepS.bigSepS_empty.mpr
    iempintro
  iintro - - - - HT
  iapply H $$ HT

example (l : Loc) (v : Val) (Φ : Val → IProp GF) :
    threadExpr i C hl(!#l + #1) ∗ stepPre i G R ∗ l ↦ some v ∗
      (threadExpr i C hl(&v + #1) -∗ stepPost i G R o -∗ l ↦ some v -∗
        lWP hl(&v + #1) @ s; i; E {{ Φ }})
      ⊢ lWP hl(!#l + #1) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, Hpre, Hl, HΦ⟩
  lwp_bind hl(!#l) HT
  iapply lwp_load (o := o) l (DFrac.own 1) v $$ [HT Hpre Hl]
  · iframe
  · iintro ⟨HT, Hpost, Hl⟩
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    iapply HΦ $$ HT Hpost Hl

example (K X : Oids) (j : ThreadId) (hX : X ⊆ K) :
    thKids i K ∗ thKids j ∅ ∗ oblFuels X 1 ⊢@{IProp GF}
      |={E}=>m (thKids i (K \ X) ∗ thKids j (X ∪ ∅)) :=
  obl_move_thread_set E (.thread i) j X K ∅ hX

/-! Operations with a computed result, `lwp_step` (a numeral fuel unifies with `m + 1`), and
`lwp_expr_simp` writing the values back as `Exp.ofVal`, so that `lwp_step` and `lwp_bind`
apply again. -/

example : PureExecCtx True 1 hl(if ~#false then #1 else #2) hl(if #(!false) then #1 else #2) :=
  inferInstance

example (n : Int) : PureExecCtx True 1 hl(#n - #1) hl(#(n - 1 : Int)) := inferInstance

example (n : Int) : PureExecCtx True 1 hl(#n ≤ #0) hl(#(decide (n ≤ 0))) := inferInstance

example (Φ : Val → IProp GF) :
    threadExpr i C hl(if ~#false then #1 else #2) ∗ thKids i G ∗ oblFuels G 2 ∗
      (threadExpr i C hl(#1) -∗ thKids i G -∗ lWP hl(#1) @ s; i; E {{ Φ }})
      ⊢ lWP hl(if ~#false then #1 else #2) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, HG, HF, H⟩
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  iapply H $$ HT HG

example (l : Loc) (v : Val) (Φ : Val → IProp GF) :
    threadExpr i C hl(v(λ x, !x + #1) #l) ∗ thKids i G ∗ oblFuels G 2 ∗ l ↦ some v ∗
      (threadExpr i C hl(&v + #1) -∗ lWP hl(&v + #1) @ s; i; E {{ Φ }})
      ⊢ lWP hl(v(λ x, !x + #1) #l) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, HG, HF, Hl, H⟩
  lwp_step HT HG HF with Hc : 1
  lwp_expr_simp
  lwp_bind hl(!#l) HT
  iapply lwp_load (o := 0) l (DFrac.own 1) v $$ [HT HG HF Hl]
  · iframe HT Hl
    iapply stepPre_nil $$ HG HF
  iintro ⟨HT, -, -⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  iapply H $$ HT

end

/-! Contexts are determined by a step, also for `chooseNat`. -/

example (K : Exp → Exp) [Context K] (C : List ECtxItem) (σ : State) (n : Nat)
    (h : K .chooseNat = fill C .chooseNat) :
    K (.val (.lit (.int n))) = fill C (.val (.lit (.int n))) :=
  Context.eq_fill_of_primStep h (EctxLanguage.primStep_of_baseStep (.chooseNatS n σ))

example (K : Exp → Exp) [Context K] (C : List ECtxItem) (σ : State) (l : Loc) (v : Val)
    (hl : σ.get? l = some (some v)) (h : K hl(!#l) = fill C hl(!#l)) :
    K (.val v) = fill C (.val v) :=
  Context.eq_fill_of_primStep h (EctxLanguage.primStep_of_baseStep (.loadS l v σ hl))

/-! The step tactics that find their hypotheses (D27, M10): `lwp_step`, `lwp_step with`,
`lwp_pure`, `lwp_bind e'` and `lwp_pures`; on a value they fail with an error that `try`,
`repeat` and `fail_if_success` catch. -/

section AutoStep

variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TemporalInterp Exp State GF]
variable {s : Stuckness} {i : ThreadId} {E : CoPset} {C : List ECtxItem} {G : Oids}

example (Φ : Val → IProp GF) :
    threadExpr i C hl(#1) ∗ thKids i G ∗ oblFuels G 2 ∗ (threadExpr i C hl(#1) -∗ Φ hl_val(#1))
      ⊢ lWP hl(#1) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, HG, HF, H⟩
  fail_if_success lwp_step
  fail_if_success lwp_pures
  repeat lwp_step
  iapply lwp_value'
  iapply H $$ HT

/-- A beta step, then an addition (`lwp_step` computes the substitution first). -/
example (Φ : Val → IProp GF) :
    threadExpr i C hl(v(λ x, x + #1) #2) ∗ thKids i G ∗ oblFuels G 2 ∗
      (threadExpr i C hl(#3) -∗ Φ hl_val(#3)) ⊢
      lWP hl(v(λ x, x + #1) #2) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, HG, HF, H⟩
  lwp_step
  lwp_step
  lwp_expr_eval
  iapply lwp_value'
  iapply H $$ HT

/-- The comparison of closed values is computed. -/
example (Φ : Val → IProp GF) :
    threadExpr i C hl(v(λ x, if x = #1 then #4 else x + #1) #2) ∗ thKids i G ∗ oblFuels G 5 ∗
      (threadExpr i C hl(#3) -∗ Φ hl_val(#3)) ⊢
      lWP hl(v(λ x, if x = #1 then #4 else x + #1) #2) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, HG, HF, H⟩
  lwp_pures
  iapply lwp_value'
  iapply H $$ HT

/-- `lwp_pures` stops at a load; `lwp_bind` finds the token. -/
example (l : Loc) (v : Val) (Φ : Val → IProp GF) :
    threadExpr i C hl(v(λ x, !x + #1) #l) ∗ thKids i G ∗ oblFuels G 2 ∗ l ↦ some v ∗
      (threadExpr i C hl(&v + #1) -∗ lWP hl(&v + #1) @ s; i; E {{ Φ }})
      ⊢ lWP hl(v(λ x, !x + #1) #l) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, HG, HF, Hl, H⟩
  lwp_pures
  lwp_bind hl(!#l)
  iapply lwp_load (o := 0) l (DFrac.own 1) v $$ [HT HG HF Hl]
  · iframe HT Hl
    iapply stepPre_nil $$ HG HF
  iintro ⟨HT, -, -⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  iapply H $$ HT

/-- A symbolic amount of fuel; the fuel left is given back. -/
example (n : Nat) (Φ : Val → IProp GF) :
    threadExpr i C hl(if #true then #1 else #2) ∗ thKids i G ∗
      oblFuels G ((n + 1 : Nat) : Measure) ∗
      (threadExpr i C hl(#1) -∗ thKids i G -∗ oblFuels G (n : Measure) -∗ Φ hl_val(#1))
      ⊢ lWP hl(if #true then #1 else #2) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, HG, HF, H⟩
  lwp_pures
  iapply lwp_value'
  iapply H $$ HT HG HF

/-- The later credits of a step. -/
example (Φ : Val → IProp GF) :
    threadExpr i C hl(if #true then #1 else #2) ∗ thKids i G ∗ oblFuels G 1 ∗
      (£ₒ 3 -∗ threadExpr i C hl(#1) -∗ Φ hl_val(#1))
      ⊢ lWP hl(if #true then #1 else #2) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, HG, HF, H⟩
  lwp_step with Hc : 3
  iapply lwp_value'
  iapply H $$ Hc HT

/-- `lwp_pure` finds the token. -/
example (Φ : Val → IProp GF) :
    threadExpr i C hl((if #true then #1 else #2) + #3) ∗ thKids i G ∗
      oblFuels G ((1 + 2 : Nat) : Measure) ∗
      (threadExpr i C hl(#1 + #3) -∗ thKids i G -∗ oblFuels G ((2 : Nat) : Measure) -∗
        |={E}=>m lWP hl(#1 + #3) @ s; i; E {{ Φ }})
      ⊢ lWP hl((if #true then #1 else #2) + #3) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, HG, HF, H⟩
  lwp_pure
  iexists G, 2, ∅, 0
  isplitl [HG HF]
  · iframe
    iapply witLayers_empty
  iintro HG HF - - HT
  iapply H $$ HT HG HF

/-- Errors: no fuel left; no token; no redex; a pure condition that `decide` does not prove. -/
example (Φ : Val → IProp GF) (l : Loc) (v w : Val) :
    threadExpr i C hl(if #true then #1 else #2) ∗ thKids i G ∗ oblFuels G 0 ∗
      lWP hl(if #true then #1 else #2) @ s; i; E {{ Φ }} ∗
      threadExpr i [] hl(!#l) ∗ lWP hl(!#l) @ s; i; E {{ Φ }} ∗
      threadExpr i [] hl(&v = &w) ∗ lWP hl(&v = &w) @ s; i; E {{ Φ }}
      ⊢ (lWP hl(if #true then #1 else #2) @ s; i; E {{ Φ }} ∗ lWP hl(!#l) @ s; i; E {{ Φ }}) ∗
        lWP hl(&v = &w) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, HG, HF, H, HT₁, H₁, HT₂, H₂⟩
  isplitl [HT HG HF H HT₁ H₁]
  · isplitl [HT HG HF H]
    · fail_if_success lwp_pures
      fail_if_success lwp_step
      iclear HT
      fail_if_success lwp_step
      iexact H
    · fail_if_success lwp_pures
      iexact H₁
  · fail_if_success lwp_pures
    iexact H₂

/-- error: lwp_step: the expression is a value -/
#guard_msgs in
example (Φ : Val → IProp GF) :
    threadExpr i C hl(#1) ∗ thKids i G ∗ oblFuels G 2 ⊢ lWP hl(#1) @ s; i; E {{ Φ }} := by
  iintro ⟨HT, HG, HF⟩
  lwp_step

end AutoStep

end LantanaTest.HeapLangLaws
