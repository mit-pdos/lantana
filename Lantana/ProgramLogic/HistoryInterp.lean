/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.Instances.IProp
public import Iris.BI
public import Lantana.ProgramLogic.Trace

/-! # The history of configurations and the state interpretation

Rocq `lantana/program_logic/history_interp.v`: the history of configurations as ghost state
(an append-only list with persistent snapshots `histEvent n st`), the state interpretation of
a language, and the history interpretation that the program logic threads between steps.

**Skeleton (M1):** the ghost-state class and the two history predicates are placeholders
(`opaque`); M5 defines them over Iris-Lean's `MonoList`.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI

universe u v w

/-- A history entry: a state and a thread pool (observations are dropped, D15). -/
abbrev HistEntry (Expr : Type u) (State : Type v) := State × ThreadPool Expr

/-- The ghost state of the history. (Placeholder for a `MonoListG` of `HistEntry`.) -/
@[lantana_alias histGS.histGS]
class HistGS (Expr : Type u) (State : Type v) (GF : BundledGFunctors.{w}) : Type where

/-- The state interpretation of a language: a predicate on the state and the thread pool
held between steps. Facts about the state that assertions determine through it are the
atoms of trace properties (`StateFact`). (Rocq `state_interp_class`, without
`state_interp_aux`, which is `True` in HeapLang — D17.) -/
@[lantana_alias state_interp_class]
class StateInterp (Expr : Type u) (State : Type v) (GF : BundledGFunctors.{w}) where
  /-- The interpretation of the state `σ` with thread pool `tp`. -/
  stateInterp : State → ThreadPool Expr → IProp GF

export StateInterp (stateInterp)

section
variable {Expr : Type u} {State : Type v} {GF : BundledGFunctors.{w}} [HistGS Expr State GF]

/-- The authoritative history. -/
@[lantana_alias hG_history_auth]
opaque histAuth (h : List (HistEntry Expr State)) : IProp GF

/-- A persistent snapshot: the history has entry `st` at position `n`. -/
@[lantana_alias hist_event]
opaque histEvent (n : Nat) (st : HistEntry Expr State) : IProp GF

instance histAuth_timeless (h : List (HistEntry Expr State)) :
    Timeless (histAuth (GF := GF) h) := sorry
instance histEvent_persistent (n : Nat) (st : HistEntry Expr State) :
    Persistent (histEvent (GF := GF) n st) := sorry
instance histEvent_timeless (n : Nat) (st : HistEntry Expr State) :
    Timeless (histEvent (GF := GF) n st) := sorry

section BUpd
variable [BIUpdate (IProp GF)]

@[lantana_alias hG_history_auth_app]
theorem histAuth_append (h₁ h₂ : List (HistEntry Expr State)) :
    histAuth (GF := GF) h₁ ⊢ |==> histAuth (h₁ ++ h₂) := sorry

end BUpd

@[lantana_alias hG_history_event]
theorem histAuth_event {h : List (HistEntry Expr State)} {n : Nat} {st : HistEntry Expr State}
    (hn : h[n]? = some st) : histAuth (GF := GF) h ⊢ histEvent n st := sorry

@[lantana_alias hist_event_history_lookup]
theorem histEvent_lookup (h : List (HistEntry Expr State)) (n : Nat) (st : HistEntry Expr State) :
    histAuth (GF := GF) h ∗ histEvent n st ⊢ ⌜h[n]? = some st⌝ := sorry

variable [StateInterp Expr State GF]

/-- The history interpretation: the history `h` has `n + 1` entries ending with the current
configuration, with the authoritative history and the state interpretation. -/
@[lantana_alias history_interp]
def historyInterp (h : List (HistEntry Expr State)) (n : Nat) (σ : State) (tp : ThreadPool Expr) :
    IProp GF :=
  iprop(⌜h.length = n + 1 ∧ h.getLast? = some (σ, tp)⌝ ∗ histAuth h ∗ stateInterp σ tp)

@[lantana_alias history_interp_lookup]
theorem historyInterp_lookup (h : List (HistEntry Expr State)) (n : Nat) (σ : State)
    (tp : ThreadPool Expr) : historyInterp (GF := GF) h n σ tp ⊢ ⌜h[n]? = some (σ, tp)⌝ := sorry

@[lantana_alias history_interp_step]
theorem historyInterp_step [BIUpdate (IProp GF)] (h : List (HistEntry Expr State)) (n : Nat)
    (σ₁ σ₂ : State) (tp₁ tp₂ : ThreadPool Expr) :
    historyInterp (GF := GF) h n σ₁ tp₁ ⊢ stateInterp σ₁ tp₁ ∗
      (stateInterp σ₂ tp₂ ==∗ historyInterp (h ++ [(σ₂, tp₂)]) (n + 1) σ₂ tp₂) := sorry

@[lantana_alias history_interp_hist_event_now]
theorem historyInterp_histEvent_now (h : List (HistEntry Expr State)) (n : Nat) (σ : State)
    (tp : ThreadPool Expr) : historyInterp (GF := GF) h n σ tp ⊢ histEvent n (σ, tp) := sorry

@[lantana_alias history_interp_hist_event_lookup]
theorem historyInterp_histEvent_lookup (h : List (HistEntry Expr State)) (n : Nat) (σ : State)
    (tp : ThreadPool Expr) (m : Nat) (st : HistEntry Expr State) :
    historyInterp (GF := GF) h n σ tp ∗ histEvent m st ⊢ ⌜h[m]? = some st⌝ := sorry

end

end Lantana
