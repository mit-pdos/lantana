/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! # A language whose threads crash: the language, its world, its state interpretation

A worker `work n` with `n` steps of work left, a killer and a reviver, over a boolean state "the
worker is alive"; the worker is crashed while the state is `false` (`instCrash`). The closed
world `CrashGF`, the state interpretation `crashInterp` and the state fact `doneOrCrashed`.
See `docs/adequacy.md`, §7.
-/

@[expose] public noncomputable section

namespace LantanaTest.Crash

open Iris Iris.BI Iris.ProofMode Iris.Std
open Ordinals Ordinal Lantana Lantana.Model
open Iris.ProgramLogic (toVal Language PrimStep)

/-! ## The language -/

/-- The expressions: a worker with `n` steps of work left, the killer, the reviver, the value. -/
inductive Exp where
  | work (n : Nat)
  | kill
  | revive
  | ret
  deriving DecidableEq

/-- The state: the worker is alive. -/
abbrev St := Bool

/-- The steps of a thread. -/
inductive Step : Exp → St → Exp → St → Prop where
  /-- The worker works. -/
  | work (n : Nat) : Step (.work (n + 1)) true (.work n) true
  /-- The worker finishes. -/
  | finish : Step (.work 0) true .ret true
  /-- A crashed worker loops. -/
  | idle (n : Nat) : Step (.work n) false (.work n) false
  /-- The killer kills. -/
  | kill (b : St) : Step .kill b .ret false
  /-- The killer gives up. -/
  | giveUp (b : St) : Step .kill b .ret b
  /-- The reviver revives. -/
  | revive (b : St) : Step .revive b .ret true

/-- The value of an expression: `ret` is the only one. -/
def Exp.toVal : Exp → Option Unit
  | .ret => some ()
  | _ => none

instance instLanguage : Language Exp St Empty Unit where
  primStep | (e, σ), _, (e', σ', efs) => Step e σ e' σ' ∧ efs = []
  toVal := Exp.toVal
  ofVal _ := .ret
  coe_of_toVal_eq_some {e _} h := by cases e <;> first | rfl | cases h
  toVal_coe _ := rfl
  val_stuck h := by
    obtain ⟨h, -⟩ := h
    cases h <;> rfl

/-- The worker is crashed while the state is `false`. -/
instance instCrash : Crash Exp St Empty Unit where
  crashed e σ := (∃ n, e = .work n) ∧ σ = false
  crashed_not_val := by
    rintro _ _ ⟨⟨n, rfl⟩, -⟩
    rfl

/-- A step of the language. -/
theorem primStep_iff {e e' : Exp} {σ σ' : St} {obs : List Empty} {efs : List Exp} :
    PrimStep.primStep (e, σ) obs (e', σ', efs) ↔ Step e σ e' σ' ∧ efs = [] :=
  .rfl

/-! ## Evaluation contexts -/

section Context
variable (K : Exp → Exp) [Language.Context K]

theorem step_context {e e' : Exp} {σ σ' : St} (h : Step e σ e' σ') : Step (K e) σ (K e') σ' :=
  (primStep_iff.mp (Language.Context.primStep_fill (K := K) (obs := [])
    (primStep_iff.mpr ⟨h, rfl⟩))).1

theorem step_context_inv {e x : Exp} {σ σ' : St} (he : e ≠ .ret) (h : Step (K e) σ x σ') :
    ∃ e', x = K e' ∧ Step e σ e' σ' := by
  have hv : toVal e = none := by cases e <;> first | rfl | exact absurd rfl he
  obtain ⟨e', rfl, h'⟩ := Language.Context.primStep_fill_inv (K := K) (obs := []) hv
    (primStep_iff.mpr ⟨h, rfl⟩)
  exact ⟨e', rfl, (primStep_iff.mp h').1⟩

/-- The language has no evaluation context but the identity. -/
theorem context_eq_id : K = id := by
  have hkill : K .kill = .kill ∧ K .ret = .ret := by
    generalize hx : K .kill = x, hy : K .ret = y
    have h := step_context K (.kill true)
    rw [hx, hy] at h
    cases h
    exact ⟨rfl, rfl⟩
  have hwork : ∀ n, K (.work n) = .work n := by
    intro n
    induction n with
    | zero =>
      generalize hx : K (.work 0) = x
      have h := step_context K .finish
      rw [hx, hkill.2] at h
      cases h with
      | finish => rfl
      | giveUp =>
        obtain ⟨e', -, h'⟩ := step_context_inv K (e := .work 0) (x := .ret) (σ' := false)
          Exp.noConfusion (hx ▸ Step.kill true)
        cases h'
      | revive =>
        obtain ⟨e', -, h'⟩ := step_context_inv K (e := .work 0) (x := .ret) (σ' := true)
          Exp.noConfusion (hx ▸ Step.revive false)
        cases h'
    | succ n ih =>
      generalize hx : K (.work (n + 1)) = x
      have h := step_context K (.work n)
      rw [hx, ih] at h
      cases h
      rfl
  funext e
  cases e with
  | work n => exact hwork n
  | kill => exact hkill.1
  | revive =>
    generalize hx : K .revive = x
    have h := step_context K (.revive false)
    rw [hx, hkill.2] at h
    cases h
    rfl
  | ret => exact hkill.2

end Context

/-! ## The pool -/

/-- The worker (thread `0`) has finished. -/
def fin (tp : ThreadPool Exp) : Bool := decide (tp[0]? = some .ret)

/-- Only thread `0` may be a worker, and it is a worker or has finished. -/
def Shape (tp : ThreadPool Exp) : Prop :=
  (∀ j n, tp[j]? = some (.work n) → j = 0) ∧ ((∃ n, tp[0]? = some (.work n)) ∨ tp[0]? = some .ret)

/-! ## The closed world -/

/-- The functor of saved trace predicates of the language. -/
abbrev TrPredF : COFE.OFunctorPre := DiscreteFunOF fun _ : Trace (Cfg Exp St) => LaterOF IdOF

/-- The contractivity of the ghost variable's functor, as `GhostVarG` expects it. -/
abbrev ghostVarFContractive : RFunctorContractive (GhostVarF (Bool × Bool)) :=
  @instRFunctorContractiveProdOF _ _ OFunctor.constOF_RFunctorContractive
    instRFunctorContractiveAgreeRFOfOFunctorContractive

/-- The world: the temporal layer (slots 0–16) and the ghost variable of the state (17). -/
def CrashGF : BundledGFunctors.{0} := fun n =>
  match n with
  | 0 => ⟨InvMapF⟩
  | 1 => ⟨ULiftOF (constOF CoPsetDisjL)⟩
  | 2 => ⟨ULiftOF (constOF (DisjointLeibnizSet PosSet))⟩
  | 3 => ⟨ULiftOF.{4} (CreditF Ordinal.{1})⟩
  | 4 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO Bool)) OidMap))⟩
  | 5 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO OblNames)) OidMap))⟩
  | 6 => ⟨ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel)))⟩
  | 7 => ⟨ULiftOF.{4} (constOFP (Bank Fuel))⟩
  | 8 => ⟨ULiftOF (constOF (HeapView Oid (Agree (DiscreteO GName)) OidMap))⟩
  | 9 => ⟨ULiftOF.{4} (constOFP (BCred Fuel))⟩
  | 10 => ⟨ULiftOF (constOF (HeapView Parent (Agree (DiscreteO Oids)) ParentMap))⟩
  | 11 => ⟨ULiftOF (constOF (HeapView ThreadId (Agree (DiscreteO ThreadStatus)) ThreadMap))⟩
  | 12 => ⟨ULiftOF.{4} (constOFP (MonoList (DiscreteO MEvent)))⟩
  | 13 => ⟨ULiftOF (constOF (MonoList (DiscreteO (Nat × RegEntry))))⟩
  | 14 => ⟨DFracAgree.DFracAgreeRF TrPredF⟩
  | 15 => ⟨ULiftOF (constOF (MonoList (DiscreteO (HistEntry Exp St))))⟩
  | 16 => ⟨ULiftOF (constOF (HeapView ThreadId (Agree (DiscreteO Oids)) ThreadMap))⟩
  | 17 => { F := ULiftOF (GhostVarF (Bool × Bool))
            contractive := @ULiftOF.instRFunctorContractive _ ghostVarFContractive }
  | _ => ⟨constOFU Unit⟩

instance : WsatGpreS CrashGF where
  inv := ElemG.ofEq 0 (by unfold CrashGF; rfl)
  enabled := ElemG.ofEqLift 1 (by unfold CrashGF; rfl)
  disabled := ElemG.ofEqLift 2 (by unfold CrashGF; rfl)

instance : TlcGpreS CrashGF where
  elem := (ElemG.ofEq 3 (by unfold CrashGF; rfl)).ofLift

instance : InvGpreS CrashGF where
  toWsatGpreS := inferInstance
  toTlcGpreS := inferInstance

instance : OSatGpreS CrashGF where
  stateG := ⟨ElemG.ofEqLift 4 (by unfold CrashGF; rfl)⟩
  namesG := ⟨ElemG.ofEqLift 5 (by unfold CrashGF; rfl)⟩
  boundG := (ElemG.ofEq 6 (by unfold CrashGF; rfl) :
    ElemG CrashGF (ULiftOF.{4} (constOFP (Agree (DiscreteO Fuel))))).ofLift
  bankG := (ElemG.ofEq 7 (by unfold CrashGF; rfl) :
    ElemG CrashGF (ULiftOF.{4} (constOFP (Bank Fuel)))).ofLift

instance : OWitGpreS CrashGF where
  namesG := ⟨ElemG.ofEqLift 8 (by unfold CrashGF; rfl)⟩
  credG := (ElemG.ofEq 9 (by unfold CrashGF; rfl) :
    ElemG CrashGF (ULiftOF.{4} (constOFP (BCred Fuel)))).ofLift

instance : OForestGpreS CrashGF where
  kidsG := ⟨ElemG.ofEqLift 10 (by unfold CrashGF; rfl)⟩
  statusG := ⟨ElemG.ofEqLift 11 (by unfold CrashGF; rfl)⟩
  billG := ⟨ElemG.ofEqLift 16 (by unfold CrashGF; rfl)⟩

instance : MHistGpreS CrashGF where
  elem := (ElemG.ofEq 12 (by unfold CrashGF; rfl) :
    ElemG CrashGF (ULiftOF.{4} (constOFP (MonoList (DiscreteO MEvent))))).ofLift

instance : ModelGpreS CrashGF where

instance : RegGpreS Exp St CrashGF where
  listG := ⟨ElemG.ofEqLift 13 (by unfold CrashGF; rfl)⟩
  predG := { elemG := ElemG.ofEq 14 (by unfold CrashGF; rfl) }

instance : MonoListG CrashGF (HistEntry Exp St) :=
  ⟨ElemG.ofEqLift 15 (by unfold CrashGF; rfl)⟩

instance : TemporalGpreS Exp St CrashGF where

instance : GhostVarG CrashGF (Bool × Bool) where
  elemG := @ElemG.ofEqLift _ (GhostVarF (Bool × Bool)) ghostVarFContractive _ 17
    (by unfold CrashGF; rfl)

/-! ## The ghost state and the state interpretation -/

/-- The ghost state of the language: the temporal layer and the name of the ghost variable that
holds the state and whether the worker has finished. -/
class CrashGS (GF : BundledGFunctors) extends TemporalGS Exp St GF where
  [varG : GhostVarG GF (Bool × Bool)]
  /-- The name of the ghost variable. -/
  varName : GName

attribute [reducible, instance] CrashGS.varG

section
variable {GF : BundledGFunctors} [CrashGS GF]

/-- A fraction `q` of the ghost variable of the state and of "the worker has finished". -/
abbrev stVar (q : Qp) (b f : Bool) : IProp GF := CrashGS.varName GF ↪VAR{.own q} (b, f)

/-- The state interpretation: the shape of the pool and half of the ghost variable. -/
def crashInterp (σ : St) (tp : ThreadPool Exp) : IProp GF :=
  iprop(⌜Shape tp⌝ ∗ stVar (Qp.half 1) σ (fin tp))

instance instStateInterp : StateInterp Exp St GF := ⟨crashInterp⟩

/-- The program logic of the language: forked threads have the postcondition `True`. -/
instance instLantanaGS : LantanaGS Exp St Empty Unit GF where
  toTemporalGS := inferInstance
  toStateInterp := instStateInterp
  forkPost _ _ := iprop(True)

theorem stateInterp_eq (σ : St) (tp : ThreadPool Exp) :
    stateInterp (GF := GF) σ tp = iprop(⌜Shape tp⌝ ∗ stVar (Qp.half 1) σ (fin tp)) :=
  rfl

/-- The worker has finished or is crashed: a fraction of the ghost variable that says so. -/
def doneOrCrashed : IProp GF :=
  iprop(∃ (q : Qp) (b f : Bool), stVar q b f ∗ ⌜b = false ∨ f = true⌝)

/-- `doneOrCrashed` reads the state: it is `false`, or the worker has finished. -/
instance stateFact_doneOrCrashed :
    StateFact (doneOrCrashed (GF := GF)) (fun σ tp => σ = false ∨ fin tp = true) where
  state_fact σ tp := by
    rw [stateInterp_eq]
    unfold doneOrCrashed
    iintro ⟨⟨-, H₁⟩, %q, %b, %f, H₂, %h⟩
    icombine H₁ H₂ gives %⟨-, he⟩
    ipureintro
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact h

end

/-! ## Checks -/

example : TemporalGpreS Exp St CrashGF := inferInstance

example (e : Exp) (σ : St) : Crash.crashed e σ → toVal e = none :=
  Crash.crashed_not_val

/-- A crashed worker steps (to itself), so it is not stuck. -/
example (n : Nat) : PrimStep.Reducible (Exp.work n, false) :=
  ⟨[], .work n, false, [], .idle n, rfl⟩

end LantanaTest.Crash
