/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Prelude

/-! # Traces and trace properties

The trace part of Rocq `lantana/program_logic/language.v` and `trace/trace_prop.v`, over an
arbitrary type `C` of configurations. A trace is a position in an infinite sequence of
configurations (no coinduction, D18); a trace property (`TrProp C`, Rocq `trProp`) is a predicate
on traces, read at the current position: the external reading of temporal properties, where LTL
is reasoned about classically.

The connectives carry a subscript `ₜ` (`∧ₜ`, `□ₜ`, `◇ₜ`, `○ₜ`, `Uₜ`, `¬ₜ`, …) so that they never
clash with the `iProp` connectives (D28); the notations are scoped in `Lantana.TrProp`. Entailment
`R ⊆ S` is validity of `R →ₜ S`. Besides LTL, three atoms: a predicate on the current
configuration (`TrProp.now`), a relation between the current configuration and the next one
(`TrProp.step`), and a fact about the current position (`TrProp.atPos`); a trace property read
along the run of a trace is a predicate on positions (`TrProp.along`). Rules are in
`Lantana.Temporal.TracePropRules`, thread systems and their behaviors in
`Lantana.Temporal.ThreadSystem`. This layer is independent of the language and of Iris: Lantana's
language is an instance (`Lantana.ProgramLogic.Configuration`), whose traces are
`Trace (Cfg Expr State)`.
-/

@[expose] public section

namespace Lantana

#lantana_ignore trace_state
  "no thread label on traces: the schedule is the adequacy proof's instrument (lane fairness-sched, 2026-11-08)"

/-- A trace: a position in an infinite sequence of configurations. -/
@[lantana_alias trace]
structure Trace (C : Type) where
  pos : Nat
  seq : Nat → C

namespace Trace

variable {C : Type}

/-- The trace one position later. -/
@[lantana_alias trace_next]
def next (τ : Trace C) : Trace C := { τ with pos := τ.pos + 1 }

/-- The current configuration. -/
@[lantana_alias trace_now]
def now (τ : Trace C) : C := τ.seq τ.pos

#lantana_ignore trace_thread
  "no thread label on traces: the schedule is the adequacy proof's instrument (lane fairness-sched, 2026-11-08)"

/-- The current configuration (`Trace.now`). -/
def cfg (τ : Trace C) : C := τ.now

@[simp] theorem next_pos (τ : Trace C) : τ.next.pos = τ.pos + 1 := rfl
@[simp] theorem next_seq (τ : Trace C) : τ.next.seq = τ.seq := rfl
@[simp] theorem now_next (τ : Trace C) : τ.next.now = τ.seq (τ.pos + 1) := rfl

end Trace

/-- A predicate on configurations. -/
@[lantana_alias tsProp]
abbrev TsProp (C : Type) := C → Prop

/-- A predicate on traces: the external reading of a temporal property. -/
@[lantana_alias trProp]
abbrev TrProp (C : Type) := Trace C → Prop

namespace TrProp

variable {C : Type}

/-- A predicate on the current configuration. -/
@[lantana_alias ts_emb]
def now (P : TsProp C) : TrProp C := fun τ => P τ.now

@[lantana_alias tr_pure]
def pure (p : Prop) : TrProp C := fun _ => p

@[lantana_alias tr_and]
def and (P Q : TrProp C) : TrProp C := fun τ => P τ ∧ Q τ

@[lantana_alias tr_or]
def or (P Q : TrProp C) : TrProp C := fun τ => P τ ∨ Q τ

@[lantana_alias tr_impl]
def imp (P Q : TrProp C) : TrProp C := fun τ => P τ → Q τ

@[lantana_alias tr_forall]
def all {A : Sort _} (P : A → TrProp C) : TrProp C := fun τ => ∀ a, P a τ

@[lantana_alias tr_exist]
def ex {A : Sort _} (P : A → TrProp C) : TrProp C := fun τ => ∃ a, P a τ

/-- `□ₜ P`: `P` holds at every position from the current one on. -/
@[lantana_alias tr_always]
def always (P : TrProp C) : TrProp C :=
  fun τ => ∀ m, τ.pos ≤ m → P { τ with pos := m }

/-- `P Uₜ Q` (strong until): `Q` holds at some later position, and `P` at every position
before it. -/
@[lantana_alias tr_until]
def strongUntil (P Q : TrProp C) : TrProp C :=
  fun τ => ∃ m, τ.pos ≤ m ∧ Q { τ with pos := m } ∧ ∀ l, τ.pos ≤ l → l < m → P { τ with pos := l }

/-- `◇ₜ Q`: `Q` holds at some position from the current one on. -/
@[lantana_alias tr_eventually]
def eventually (Q : TrProp C) : TrProp C := strongUntil (pure True) Q

/-- `○ₜ P`: `P` holds at the next position. -/
@[lantana_alias tr_next]
def next (P : TrProp C) : TrProp C := fun τ => P τ.next

/-- A relation between the current configuration and the next one: the two-position atom. -/
def step (R : C → C → Prop) : TrProp C := fun τ => R τ.now τ.next.now

/-- A fact about the current position. -/
def atPos (f : Nat → Prop) : TrProp C := fun τ => f τ.pos

/-- The trace property `P` read along the run of `τ`, as a predicate on positions. -/
def along (P : TrProp C) (τ : Trace C) (n : Nat) : Prop := P { τ with pos := n }

/-! ## Notations -/

scoped notation:max "⌜" p "⌝ₜ" => TrProp.pure p
scoped infixr:35 " ∧ₜ " => TrProp.and
scoped infixr:30 " ∨ₜ " => TrProp.or
scoped infixr:25 " →ₜ " => TrProp.imp
scoped notation:max "□ₜ " P:40 => TrProp.always P
scoped notation:max "◇ₜ " P:40 => TrProp.eventually P
scoped notation:max "○ₜ " P:40 => TrProp.next P
scoped infixr:40 " Uₜ " => TrProp.strongUntil

open Lean in
/-- `∀ₜ x y, P`: the trace-level universal quantifier. -/
scoped syntax "∀ₜ " explicitBinders ", " term : term
open Lean in
/-- `∃ₜ x y, P`: the trace-level existential quantifier. -/
scoped syntax "∃ₜ " explicitBinders ", " term : term

open Lean in
scoped macro_rules
  | `(∀ₜ $xs, $b) => Lean.expandExplicitBinders ``TrProp.all xs b
  | `(∃ₜ $xs, $b) => Lean.expandExplicitBinders ``TrProp.ex xs b

/-- Negation. -/
def not (P : TrProp C) : TrProp C := P →ₜ ⌜False⌝ₜ

scoped notation:max "¬ₜ " P:40 => TrProp.not P

/-- Trace entailment `R ⊆ S`: the validity of `R →ₜ S`. -/
@[lantana_alias tr_le]
def le (R S : TrProp C) : Prop := ∀ τ, R τ → S τ

instance : HasSubset (TrProp C) := ⟨le⟩

@[lantana_alias tr_le_impl]
theorem le_iff_imp (R S : TrProp C) : R ⊆ S ↔ ∀ τ, (R →ₜ S) τ := Iff.rfl

/-! ## Fixpoints (Knaster–Tarski at `Prop`) -/

/-- A monotone trace functor. -/
@[lantana_alias tr_mono]
def Mono (Φ : TrProp C → TrProp C) : Prop :=
  ∀ R R', (∀ τ, R τ → R' τ) → ∀ τ, Φ R τ → Φ R' τ

/-- The greatest fixpoint: the union of the post-fixpoints. -/
@[lantana_alias tr_gfp]
def gfp (Φ : TrProp C → TrProp C) : TrProp C :=
  fun τ => ∃ R, (∀ τ', R τ' → Φ R τ') ∧ R τ

/-- The least fixpoint: the intersection of the pre-fixpoints. -/
@[lantana_alias tr_lfp]
def lfp (Φ : TrProp C → TrProp C) : TrProp C :=
  fun τ => ∀ R, (∀ τ', Φ R τ' → R τ') → R τ

end TrProp
end Lantana
