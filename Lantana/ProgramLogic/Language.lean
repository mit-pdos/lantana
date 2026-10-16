/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

Based on Iris-Lean's `Iris.ProgramLogic.Language`, whose header reads:
  Copyright (c) The Iris-Lean Contributors
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Fernando Leal
Modified by the Lantana-Lean Contributors; the module documentation describes the changes.
-/
module

public import Iris.ProgramLogic.Language
public import Iris.BI.WeakestPre
public import Iris.Std.Relation
public import Lantana.Init

/-! # Languages

The language interface of Lantana (Rocq `lantana/program_logic/language.v`, without the
trace part, which is `Lantana.ProgramLogic.Trace`). A step knows nothing about threads: the
thread pool is a list and a thread id is a position in it, so forked threads get fresh ids by
being appended (design decision D14), and there are no observations (D15). Hence a Lantana
language is Iris-Lean's `ToVal` plus a primitive step relation `primStep e σ e' σ' efs`.

As in Rocq (and unlike Iris-Lean), a language also carries a *type* of contexts `Ctx`, with
`ctxApply`, the identity `ctxId` and the composition `ctxComp` (design decision D31): `lWP`
quantifies over these contexts, so that a language whose contexts are syntactic (HeapLang:
lists of items, `ctxApply := fill`) can recover the context of a thread from its expression.
`Context K` says that the context `K` is an evaluation context (Rocq `LanguageCtx`).
-/

@[expose] public section

namespace Lantana

open Iris.ProgramLogic (ToVal toVal)
open Iris.ProgramLogic.Language (Atomicity)


/-- A language: expressions `Expr`, states `State`, values `Val` (with `toVal`/`ofVal`), and
the primitive step `primStep e σ e' σ' efs` of one thread, forking the threads `efs`. -/
@[lantana_alias language]
class Language (Expr : Type) (State : outParam (Type)) (Val : outParam (Type))
    extends ToVal Expr Val where
  /-- One step of the expression `e` in state `σ`: result `e'`, new state `σ'`, forked
  threads `efs` (appended to the pool). -/
  primStep : Expr → State → Expr → State → List Expr → Prop
  /-- Values do not step. -/
  val_stuck {e : Expr} {σ : State} {e' σ' efs} : primStep e σ e' σ' efs → toVal e = none
  /-- The contexts of the language: the language chooses their representation; only the
  identity and the composition are prescribed, and contexts need not be injective. -/
  Ctx : Type
  /-- Plug an expression into a context. -/
  ctxApply : Ctx → Expr → Expr
  /-- The empty context. -/
  ctxId : Ctx
  /-- `ctxComp K₁ K₂` is `K₂` plugged into `K₁` (`ctxApply_comp`). -/
  ctxComp : Ctx → Ctx → Ctx
  ctxApply_id (e : Expr) : ctxApply ctxId e = e
  ctxApply_comp (K₁ K₂ : Ctx) (e : Expr) :
    ctxApply (ctxComp K₁ K₂) e = ctxApply K₁ (ctxApply K₂ e)

export Language (primStep val_stuck ctxApply ctxId ctxComp)

attribute [lantana_alias ctx] Language.Ctx
attribute [lantana_alias ctx_apply] Language.ctxApply
attribute [lantana_alias ctx_id] Language.ctxId
attribute [lantana_alias ctx_comp] Language.ctxComp
attribute [lantana_alias ctx_id_apply, simp] Language.ctxApply_id
attribute [lantana_alias ctx_comp_apply, simp] Language.ctxApply_comp

#lantana_ignore LanguageCtxMixin "the context fields `Ctx`, …, `ctxApply_comp` of `Language`"

namespace Language

variable {Expr : Type} {State : Type} {Val : Type} [Λ : Language Expr State Val]

/-! ## Reducibility -/

@[lantana_alias reducible]
def Reducible (e : Expr) (σ : State) : Prop := ∃ e' σ' efs, primStep e σ e' σ' efs

@[lantana_alias irreducible]
def Irreducible (e : Expr) (σ : State) : Prop := ∀ e' σ' efs, ¬ primStep e σ e' σ' efs

@[lantana_alias stuck]
def Stuck (e : Expr) (σ : State) : Prop := toVal e = none ∧ Irreducible e σ

@[lantana_alias not_stuck]
def NotStuck (e : Expr) (σ : State) : Prop := (toVal e).isSome ∨ Reducible e σ

/-- Reducibility required by the stuckness `s`: `NotStuck` requires a step, `MaybeStuck`
nothing. -/
def _root_.Iris.Stuckness.maybeReducible : Iris.Stuckness → Expr → State → Prop
  | .NotStuck, e, σ => Reducible e σ
  | .MaybeStuck, _, _ => True

@[lantana_alias not_reducible]
theorem not_reducible_iff {e : Expr} {σ : State} : ¬ Reducible e σ ↔ Irreducible e σ := by
  simp [Reducible, Irreducible]

@[lantana_alias reducible_not_val]
theorem Reducible.toVal_eq_none {e : Expr} {σ : State} (h : Reducible e σ) : toVal e = none :=
  let ⟨_, _, _, h⟩ := h; val_stuck h

@[lantana_alias val_irreducible]
theorem irreducible_of_isSome {e : Expr} {σ : State} (h : (toVal e).isSome) :
    Irreducible e σ := fun _ _ _ hs => by simp [val_stuck hs] at h

@[lantana_alias not_not_stuck]
theorem not_notStuck_iff {e : Expr} {σ : State} : ¬ NotStuck e σ ↔ Stuck e σ := by
  simp only [NotStuck, Stuck, not_or, ← not_reducible_iff, Option.isSome_iff_ne_none,
    Decidable.not_not]

@[lantana_alias prim_step_not_stuck]
theorem notStuck_of_primStep {e : Expr} {σ : State} {e' σ' efs} (h : primStep e σ e' σ' efs) :
    NotStuck e σ := .inr ⟨_, _, _, h⟩

/-! ## Atomicity -/

/-- `Atomic a e`: every step of `e` ends in an irreducible (`WeaklyAtomic`) or a value
(`StronglyAtomic`) expression. `WeaklyAtomic` suffices to open invariants when the weakest
precondition ensures safety. -/
@[lantana_alias Atomic]
class Atomic (a : Atomicity) (e : Expr) : Prop where
  atomic {σ : State} {e' σ' efs} : primStep e σ e' σ' efs →
    match a with
    | .WeaklyAtomic => Irreducible e' σ'
    | .StronglyAtomic => (toVal e').isSome

@[lantana_alias stuckness_to_atomicity]
def _root_.Iris.Stuckness.toAtomicity : Iris.Stuckness → Atomicity
  | .MaybeStuck => .StronglyAtomic
  | .NotStuck => .WeaklyAtomic

@[lantana_alias strongly_atomic_atomic]
theorem Atomic.of_stronglyAtomic {e : Expr} (h : Atomic .StronglyAtomic e) (a : Atomicity) :
    Atomic a e where
  atomic hs := by
    cases a
    · exact irreducible_of_isSome (h.atomic hs)
    · exact h.atomic hs

/-! ## Evaluation contexts -/

/-- `Context K`: the context `K` is an evaluation context. -/
@[lantana_alias LanguageCtx]
class Context (K : Λ.Ctx) : Prop where
  toVal_eq_none_fill {e : Expr} : toVal e = none → toVal (ctxApply K e) = none
  primStep_fill {e : Expr} {σ : State} {e' σ' efs} :
    primStep e σ e' σ' efs → primStep (ctxApply K e) σ (ctxApply K e') σ' efs
  primStep_fill_inv {e : Expr} {σ : State} {Ke' σ' efs} :
    toVal e = none → primStep (ctxApply K e) σ Ke' σ' efs →
    ∃ e', Ke' = ctxApply K e' ∧ primStep e σ e' σ' efs

namespace Context

@[lantana_alias language_ctx_id]
instance instId : Context (ctxId : Λ.Ctx) where
  toVal_eq_none_fill h := by rwa [ctxApply_id]
  primStep_fill h := by rwa [ctxApply_id, ctxApply_id]
  primStep_fill_inv _ h := ⟨_, (ctxApply_id _).symm, by rwa [ctxApply_id] at h⟩

@[lantana_alias language_ctx_compose]
instance instComp (K₁ K₂ : Λ.Ctx) [Context K₁] [Context K₂] : Context (ctxComp K₁ K₂) where
  toVal_eq_none_fill h := by
    rw [ctxApply_comp]
    exact toVal_eq_none_fill (K := K₁) (toVal_eq_none_fill (K := K₂) h)
  primStep_fill h := by
    rw [ctxApply_comp, ctxApply_comp]
    exact primStep_fill (K := K₁) (primStep_fill (K := K₂) h)
  primStep_fill_inv hv h := by
    rw [ctxApply_comp] at h
    obtain ⟨e₁, rfl, h₁⟩ := primStep_fill_inv (K := K₁) (toVal_eq_none_fill (K := K₂) hv) h
    obtain ⟨e₂, rfl, h₂⟩ := primStep_fill_inv (K := K₂) hv h₁
    exact ⟨e₂, (ctxApply_comp ..).symm, h₂⟩

variable (K : Λ.Ctx) [Context K]

@[lantana_alias reducible_fill]
theorem reducible_fill {e : Expr} {σ : State} (h : Reducible e σ) :
    Reducible (ctxApply K e) σ :=
  let ⟨_, _, _, h⟩ := h; ⟨_, _, _, primStep_fill (K := K) h⟩

@[lantana_alias reducible_fill_inv]
theorem reducible_fill_inv {e : Expr} {σ : State} (hv : toVal e = none)
    (h : Reducible (ctxApply K e) σ) : Reducible e σ :=
  let ⟨_, _, _, h⟩ := h
  let ⟨_, _, h⟩ := primStep_fill_inv (K := K) hv h; ⟨_, _, _, h⟩

@[lantana_alias irreducible_fill]
theorem irreducible_fill {e : Expr} {σ : State} (hv : toVal e = none) (h : Irreducible e σ) :
    Irreducible (ctxApply K e) σ :=
  not_reducible_iff.mp fun hr => not_reducible_iff.mpr h (reducible_fill_inv K hv hr)

@[lantana_alias irreducible_fill_inv]
theorem irreducible_fill_inv {e : Expr} {σ : State} (h : Irreducible (ctxApply K e) σ) :
    Irreducible e σ :=
  not_reducible_iff.mp fun hr => not_reducible_iff.mpr h (reducible_fill K hr)

@[lantana_alias not_stuck_fill_inv]
theorem notStuck_fill_inv {e : Expr} {σ : State} (h : NotStuck (ctxApply K e) σ) :
    NotStuck e σ := by
  rcases h with h | h
  · by_cases hv : toVal e = none
    · simp [toVal_eq_none_fill (K := K) hv] at h
    · exact .inl (Option.isSome_iff_ne_none.mpr hv)
  · by_cases hv : toVal e = none
    · exact .inr (reducible_fill_inv K hv h)
    · exact .inl (Option.isSome_iff_ne_none.mpr hv)

@[lantana_alias stuck_fill]
theorem stuck_fill {e : Expr} {σ : State} (h : Stuck e σ) : Stuck (ctxApply K e) σ :=
  not_notStuck_iff.mp fun hn => not_notStuck_iff.mpr h (notStuck_fill_inv K hn)

end Context

/-! ## Pure steps -/

/-- A pure step: always possible, deterministic, changes neither the state nor the pool. -/
@[lantana_alias pure_step]
structure PureStep (e₁ e₂ : Expr) : Prop where
  safe (σ : State) : Reducible e₁ σ
  det {σ : State} {e₂' σ' efs} : primStep e₁ σ e₂' σ' efs → σ' = σ ∧ e₂' = e₂ ∧ efs = []

/-- `PureExec φ n e₁ e₂`: under `φ`, `e₁` reaches `e₂` in `n` pure steps. Unlike Rocq, `n > 0` is
not required; the lifting lemmas take it as a hypothesis where they need it. -/
@[lantana_alias PureExec]
class PureExec (φ : outParam Prop) (n : outParam Nat) (e₁ : Expr) (e₂ : outParam Expr) :
    Prop where
  pureExec : φ → Relation.Iterate PureStep n e₁ e₂

@[lantana_alias pure_step_ctx]
theorem PureStep.fill (K : Λ.Ctx) [Context K] {e₁ e₂ : Expr} (h : PureStep e₁ e₂) :
    PureStep (ctxApply K e₁) (ctxApply K e₂) where
  safe σ := Context.reducible_fill K (h.safe σ)
  det {σ _ _ _} hs := by
    obtain ⟨e', rfl, hs'⟩ :=
      Context.primStep_fill_inv (K := K) (h.safe σ).toVal_eq_none hs
    obtain ⟨rfl, rfl, rfl⟩ := h.det hs'
    exact ⟨rfl, rfl, rfl⟩

@[lantana_alias pure_step_nsteps_ctx]
theorem PureStep.iterate_fill (K : Λ.Ctx) [Context K] {n : Nat} {e₁ e₂ : Expr}
    (h : Relation.Iterate PureStep n e₁ e₂) :
    Relation.Iterate PureStep n (ctxApply K e₁) (ctxApply K e₂) := by
  induction h with
  | rfl => exact .rfl _
  | tail _ _ hs ih => exact .tail _ ih (hs.fill K)

/-- Not an instance: too general. -/
@[lantana_alias pure_exec_ctx]
theorem PureExec.fill (K : Λ.Ctx) [Context K] {φ n} {e₁ e₂ : Expr}
    (h : PureExec φ n e₁ e₂) : PureExec φ n (ctxApply K e₁) (ctxApply K e₂) :=
  ⟨fun hφ => PureStep.iterate_fill K (h.pureExec hφ)⟩

/-- No chain of pure steps of positive length starts from a value. -/
theorem PureStep.not_iterate_succ_val [Inhabited State] {m : Nat} {v : Val} {e : Expr}
    (h : Relation.Iterate PureStep (m + 1) (v : Expr) e) : False := by
  induction m generalizing e with
  | zero =>
    cases h with
    | tail _ h hs =>
      cases h
      obtain ⟨_, _, _, hs'⟩ := hs.safe default
      exact absurd (val_stuck hs') (by simp)
  | succ m ih =>
    cases h with
    | tail _ h _ => exact ih h

/-- Values take no pure steps. -/
@[lantana_alias rtc_pure_step_val]
theorem PureStep.iterate_val [Inhabited State] {n : Nat} {v : Val} {e : Expr}
    (h : Relation.Iterate PureStep n (v : Expr) e) : n = 0 ∧ e = v := by
  cases h with
  | rfl => exact ⟨rfl, rfl⟩
  | tail _ h hs => exact (PureStep.not_iterate_succ_val (.tail _ h hs)).elim

/-! ## Values -/

@[lantana_alias IntoVal]
class IntoVal (e : Expr) (v : Val) : Prop where
  into_val : (v : Expr) = e

@[lantana_alias AsVal]
class AsVal (e : Expr) : Prop where
  as_val : ∃ v : Val, (v : Expr) = e

@[lantana_alias as_val_is_Some]
theorem AsVal.isSome {e : Expr} [h : AsVal e] : (toVal e).isSome := by
  obtain ⟨v, rfl⟩ := h.as_val
  simp

end Language
end Lantana
