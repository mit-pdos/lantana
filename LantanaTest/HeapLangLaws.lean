module

public import Lantana

/-! Tests for the program logic of HeapLang (M7): the thread-expression token, the step laws
with the bookkeeping of children and witnesses, laws in an evaluation context, and contexts
determined by a step. -/

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

example (K X : Oids) (j : ThreadId) (hX : X ⊆ K) :
    thKids i K ∗ thKids j ∅ ∗ oblFuels X 1 ⊢@{IProp GF}
      |={E}=>m (thKids i (K \ X) ∗ thKids j (X ∪ ∅)) :=
  obl_move_thread_set E (.thread i) j X K ∅ hX

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

end LantanaTest.HeapLangLaws
