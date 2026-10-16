/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.Instances.IProp
public import Iris.BI
public import Iris.BI.Lib.MonoList
public import Iris.ProofMode
public import Lantana.ProgramLogic.Trace

/-! # The history of configurations and the state interpretation

Rocq `lantana/program_logic/history_interp.v`: the history of configurations as ghost state
(an append-only list, Iris-Lean's `MonoList`, with persistent snapshots `histEvent n st`), the
state interpretation of a language, and the history interpretation that the program logic
threads between steps.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode


/-- A history entry: a state and a thread pool (observations are dropped, D15). -/
abbrev HistEntry (Expr : Type) (State : Type) := State × ThreadPool Expr

/-- The ghost state of the history: a monotone list of history entries. -/
@[lantana_alias histGS] -- Rocq `histGS.histGS`; the module prefix would duplicate the namespace
class HistGS (Expr : Type) (State : Type) (GF : BundledGFunctors) where
  [elemG : MonoListG GF (HistEntry Expr State)]
  /-- The ghost name of the history. -/
  name : GName

attribute [reducible, instance] HistGS.elemG

/-- The ghost name of the history, with the language and the world explicit. -/
abbrev histName (Expr : Type) (State : Type) (GF : BundledGFunctors)
    [HistGS Expr State GF] : GName :=
  HistGS.name (Expr := Expr) (State := State) (GF := GF)

/-- The state interpretation of a language: a predicate on the state and the thread pool
held between steps. Facts about the state that assertions determine through it are the
atoms of trace properties (`StateFact`). (Rocq `state_interp_class`, without
`state_interp_aux`, which is `True` in HeapLang — D17.) -/
@[lantana_alias state_interp_class]
class StateInterp (Expr : Type) (State : Type) (GF : BundledGFunctors) where
  /-- The interpretation of the state `σ` with thread pool `tp`. -/
  stateInterp : State → ThreadPool Expr → IProp GF

export StateInterp (stateInterp)

section
variable {Expr : Type} {State : Type} {GF : BundledGFunctors} [HistGS Expr State GF]

open MonoList

/-- The authoritative history. -/
@[lantana_alias hG_history_auth]
def histAuth (h : List (HistEntry Expr State)) : IProp GF :=
  histName Expr State GF ↪●ML h

/-- A persistent snapshot: the history has entry `st` at position `n`. -/
@[lantana_alias hist_event]
def histEvent (n : Nat) (st : HistEntry Expr State) : IProp GF :=
  histName Expr State GF ↪◯ML[n] st

@[lantana_alias hG_history_auth_timeless]
instance histAuth_timeless (h : List (HistEntry Expr State)) :
    Timeless (histAuth (GF := GF) h) := by
  unfold histAuth; infer_instance

@[lantana_alias hist_event_persistent]
instance histEvent_persistent (n : Nat) (st : HistEntry Expr State) :
    Persistent (histEvent (GF := GF) n st) := by
  unfold histEvent; infer_instance

@[lantana_alias hist_event_timeless]
instance histEvent_timeless (n : Nat) (st : HistEntry Expr State) :
    Timeless (histEvent (GF := GF) n st) := by
  unfold histEvent; infer_instance

@[lantana_alias hG_history_auth_app]
theorem histAuth_append (h₁ h₂ : List (HistEntry Expr State)) :
    histAuth (GF := GF) h₁ ⊢ |==> histAuth (h₁ ++ h₂) := by
  unfold histAuth
  iintro H
  imod auth_own_update_app _ h₂ $$ H with ⟨$, -⟩

@[lantana_alias hG_history_event]
theorem histAuth_event {h : List (HistEntry Expr State)} {n : Nat} {st : HistEntry Expr State}
    (hn : h[n]? = some st) : histAuth (GF := GF) h ⊢ histEvent n st := by
  unfold histAuth histEvent
  iintro H
  iapply idx_own_get _ n st hn
  iapply lb_own_get $$ H

@[lantana_alias hist_event_history_lookup]
theorem histEvent_lookup (h : List (HistEntry Expr State)) (n : Nat) (st : HistEntry Expr State) :
    histAuth (GF := GF) h ∗ histEvent n st ⊢ ⌜h[n]? = some st⌝ := by
  unfold histAuth histEvent
  iintro ⟨H, E⟩
  iapply auth_idx_lookup $$ H E

variable [StateInterp Expr State GF]

/-- The history interpretation: the history `h` has `n + 1` entries ending with the current
configuration, with the authoritative history and the state interpretation. -/
@[lantana_alias history_interp]
def historyInterp (h : List (HistEntry Expr State)) (n : Nat) (σ : State) (tp : ThreadPool Expr) :
    IProp GF :=
  iprop(⌜h.length = n + 1 ∧ h.getLast? = some (σ, tp)⌝ ∗ histAuth h ∗ stateInterp σ tp)

/-- The last entry of a history of length `n + 1` is its `n`-th. -/
theorem getLast?_eq_getElem?_of_length {α : Type _} {h : List α} {n : Nat} {a : α}
    (hlen : h.length = n + 1) (hlast : h.getLast? = some a) : h[n]? = some a := by
  rw [List.getLast?_eq_getElem?, hlen] at hlast
  simpa using hlast

@[lantana_alias history_interp_wf]
theorem historyInterp_wf (h : List (HistEntry Expr State)) (n : Nat) (σ : State)
    (tp : ThreadPool Expr) :
    historyInterp (GF := GF) h n σ tp ⊢ ⌜h.length = n + 1 ∧ h.getLast? = some (σ, tp)⌝ := by
  unfold historyInterp
  iintro ⟨%h, -, -⟩
  ipureintro
  exact h

@[lantana_alias history_interp_lookup]
theorem historyInterp_lookup (h : List (HistEntry Expr State)) (n : Nat) (σ : State)
    (tp : ThreadPool Expr) : historyInterp (GF := GF) h n σ tp ⊢ ⌜h[n]? = some (σ, tp)⌝ := by
  unfold historyInterp
  iintro ⟨%⟨hlen, hlast⟩, -, -⟩
  ipureintro
  exact getLast?_eq_getElem?_of_length hlen hlast

@[lantana_alias history_interp_step]
theorem historyInterp_step (h : List (HistEntry Expr State)) (n : Nat)
    (σ₁ σ₂ : State) (tp₁ tp₂ : ThreadPool Expr) :
    historyInterp (GF := GF) h n σ₁ tp₁ ⊢ stateInterp σ₁ tp₁ ∗
      (stateInterp σ₂ tp₂ ==∗ historyInterp (h ++ [(σ₂, tp₂)]) (n + 1) σ₂ tp₂) := by
  unfold historyInterp
  iintro ⟨%⟨hlen, -⟩, Ha, $⟩ Hs
  imod histAuth_append h [(σ₂, tp₂)] $$ Ha with Ha
  iframe Ha Hs
  ipureintro
  simp [hlen]

@[lantana_alias history_interp_hist_event_now]
theorem historyInterp_histEvent_now (h : List (HistEntry Expr State)) (n : Nat) (σ : State)
    (tp : ThreadPool Expr) : historyInterp (GF := GF) h n σ tp ⊢ histEvent n (σ, tp) := by
  unfold historyInterp
  iintro ⟨%⟨hlen, hlast⟩, Ha, -⟩
  iapply histAuth_event (getLast?_eq_getElem?_of_length hlen hlast) $$ Ha

@[lantana_alias history_interp_hist_event_lookup]
theorem historyInterp_histEvent_lookup (h : List (HistEntry Expr State)) (n : Nat) (σ : State)
    (tp : ThreadPool Expr) (m : Nat) (st : HistEntry Expr State) :
    historyInterp (GF := GF) h n σ tp ∗ histEvent m st ⊢ ⌜h[m]? = some st⌝ := by
  unfold historyInterp
  iintro ⟨⟨-, Ha, -⟩, He⟩
  iapply histEvent_lookup
  iframe

end

/-- The ghost state of the history at the name `γ`, over the world's camera (D32: the name is
small enough for the existential property of satisfiability, unlike `HistGS Expr State GF`). -/
@[reducible] def HistGS.ofName {Expr State : Type} {GF : BundledGFunctors}
    [MonoListG GF (HistEntry Expr State)] (γ : GName) : HistGS Expr State GF where
  name := γ

/-- Allocating the history with its first entry, at the name `γ` (D32), for every state
interpretation (chosen after the allocation, as in Rocq `history_interp_init`). -/
theorem historyInterp_init_names {Expr State : Type} {GF : BundledGFunctors}
    [MonoListG GF (HistEntry Expr State)] (σ : State) (tp : ThreadPool Expr) :
    ⊢@{IProp GF} |==> ∃ γ : GName,
      letI := HistGS.ofName (Expr := Expr) (State := State) (GF := GF) γ
      iprop(∀ _ : StateInterp Expr State GF,
        stateInterp σ tp ==∗ historyInterp [(σ, tp)] 0 σ tp) := by
  iintro
  imod MonoList.own_alloc [(σ, tp)] with ⟨%γ, Ha, -⟩
  imodintro
  iexists γ
  iintro %_SI Hs
  imodintro
  unfold historyInterp histAuth
  simp only [histName]
  iframe Ha Hs
  ipureintro
  simp

/-- Allocating the history with its first entry (the state interpretation is given). -/
@[lantana_alias history_interp_init]
theorem historyInterp_init {Expr State : Type} {GF : BundledGFunctors}
    [MonoListG GF (HistEntry Expr State)] [StateInterp Expr State GF] (σ : State)
    (tp : ThreadPool Expr) :
    ⊢@{IProp GF} |==> ∃ _ : HistGS Expr State GF,
      stateInterp σ tp ==∗ historyInterp [(σ, tp)] 0 σ tp := by
  imod historyInterp_init_names (GF := GF) σ tp with ⟨%γ, H⟩
  imodintro
  iexists HistGS.ofName γ
  iapply H

end Lantana
