/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.BaseLogic.MonoListP
public import Lantana.BaseLogic.Obligation

/-! # The model history

Rocq `lantana/base_logic/model_history.v`: an append-only list of events `(n, Ω)` (physical step
index, obligation map), owned authoritatively by the model interpretation, so that users can
take persistent snapshots `eventObl i e k o` ("at event `i`, obligation `k` was `o`") and compare
snapshots across time through the order `Obls.le`. Every model round appends an event
(`modelHistoryInterp_step`); the trace layer reads the snapshots.
-/

@[expose] public noncomputable section

namespace Lantana.Model

open Iris Iris.BI Iris.ProofMode Iris.Std LawfulPartialMap
open scoped Lantana.MonoListP

/-- An event of the model history: a physical step index and an obligation map. -/
abbrev MEvent := Nat × Obls

/-- Events are ordered by index and by `Obls.le` (Rocq `event_le`). -/
@[lantana_alias event_le]
def eventLe (e₁ e₂ : MEvent) : Prop := e₁.1 ≤ e₂.1 ∧ Obls.le e₁.2 e₂.2

@[lantana_alias event_le_reflexive]
theorem eventLe_refl (e : MEvent) : eventLe e e := ⟨Nat.le_refl _, Obls.le_refl _⟩

@[lantana_alias event_le_transitive]
theorem eventLe_trans {e₁ e₂ e₃ : MEvent} (h₁₂ : eventLe e₁ e₂) (h₂₃ : eventLe e₂ e₃) :
    eventLe e₁ e₃ :=
  ⟨Nat.le_trans h₁₂.1 h₂₃.1, Obls.le_trans h₁₂.2 h₂₃.2⟩

theorem lt_length_of_getElem? {α : Type _} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : i < l.length := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h
  exact hlt

/-- The last entry of a list of length `i + 1` is its `i`-th. -/
theorem getLast?_eq_getElem?_of_length {α : Type _} {l : List α} {i : Nat} {a : α}
    (hlen : l.length = i + 1) (hlast : l.getLast? = some a) : l[i]? = some a := by
  rw [List.getLast?_eq_getElem?, hlen] at hlast
  simpa using hlast

theorem getLast?_take {α : Type _} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    (l.take (i + 1)).getLast? = some a := by
  have hlt := lt_length_of_getElem? h
  rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left (by omega),
    Nat.add_sub_cancel, List.getElem?_take_of_lt (Nat.lt_succ_self i)]
  exact h

/-- A well-formed history: consecutive events are ordered (Rocq `model_history_wf`). -/
@[lantana_alias model_history_wf]
def ModelHistoryWf (h : List MEvent) : Prop :=
  ∀ i e₁ e₂, h[i]? = some e₁ → h[i + 1]? = some e₂ → eventLe e₁ e₂

namespace ModelHistoryWf

theorem lookup_add {h : List MEvent} (wf : ModelHistoryWf h) {i : Nat} {e₁ : MEvent}
    (hi : h[i]? = some e₁) : ∀ d e₂, h[i + d]? = some e₂ → eventLe e₁ e₂ := by
  intro d
  induction d with
  | zero => intro e₂ hj; rw [Nat.add_zero, hi] at hj; cases hj; exact eventLe_refl _
  | succ d ih =>
    intro e₂ hj
    have hlt : i + d < h.length := by have := lt_length_of_getElem? hj; omega
    exact eventLe_trans (ih _ (List.getElem?_eq_getElem hlt))
      (wf _ _ _ (List.getElem?_eq_getElem hlt) hj)

/-- Any two events of a well-formed history are ordered (Rocq `model_history_wf_lookup_1`). -/
@[lantana_alias model_history_wf_lookup_1]
theorem lookup {h : List MEvent} (wf : ModelHistoryWf h) {i j : Nat} {e₁ e₂ : MEvent}
    (hi : h[i]? = some e₁) (hj : h[j]? = some e₂) (hij : i ≤ j) : eventLe e₁ e₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact wf.lookup_add hi d e₂ hj

theorem nil : ModelHistoryWf [] := fun _ _ _ h => by simp at h

theorem singleton (e : MEvent) : ModelHistoryWf [e] := fun _ _ _ _ h₂ => by simp at h₂

/-- A prefix of a well-formed history is well-formed. -/
theorem isPrefix {h h' : List MEvent} (wf : ModelHistoryWf h) (hp : h' <+: h) :
    ModelHistoryWf h' := fun i e₁ e₂ h₁ h₂ =>
  wf i e₁ e₂ (MonoListP.prefix_getElem? hp h₁) (MonoListP.prefix_getElem? hp h₂)

/-- Appending an event above the last one keeps a history well-formed
(Rocq `model_history_wf_app`, the case of one event). -/
@[lantana_alias model_history_wf_app]
theorem append_one {h : List MEvent} (wf : ModelHistoryWf h) {e : MEvent}
    (hlast : ∀ e', h.getLast? = some e' → eventLe e' e) : ModelHistoryWf (h ++ [e]) := by
  intro i e₁ e₂ h₁ h₂
  have hlt₂ := lt_length_of_getElem? h₂
  rw [List.length_append, List.length_singleton] at hlt₂
  rcases Nat.lt_or_ge (i + 1) h.length with hlt | hge
  · rw [List.getElem?_append_left (by omega)] at h₁ h₂
    exact wf i e₁ e₂ h₁ h₂
  · have hi : i + 1 = h.length := by omega
    rw [List.getElem?_append_right (by omega), hi, Nat.sub_self] at h₂
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h₂
    subst h₂
    rw [List.getElem?_append_left (by omega)] at h₁
    apply hlast
    rw [List.getLast?_eq_getElem?, ← hi, Nat.add_sub_cancel]
    exact h₁

end ModelHistoryWf

/-- The ghost state of the model history: a monotone list of events. -/
@[lantana_alias mhistGS]
class MHistGS (GF : BundledGFunctors) where
  [elemG : MonoListGP GF MEvent]
  /-- The ghost name of the model history. -/
  name : GName

attribute [reducible, instance] MHistGS.elemG

/-- The pre-allocation class of the model history. -/
@[lantana_alias mhistGpreS]
abbrev MHistGpreS (GF : BundledGFunctors) := MonoListGP GF MEvent

namespace MHist

/-- The ghost name of the model history, with the world explicit. -/
abbrev name (GF : BundledGFunctors) [MHistGS GF] : GName := MHistGS.name (GF := GF)

variable {GF : BundledGFunctors} [MHistGS GF]

open MonoListP

/-- The authoritative, well-formed model history (Rocq `mhG_history_auth`). -/
@[lantana_alias mhG_history_auth]
def auth (h : List MEvent) : IProp GF := iprop(⌜ModelHistoryWf h⌝ ∗ (name GF ↪●MLP h))

/-- A persistent snapshot: event `e` is the `i`-th of the history (Rocq `mhG_event`). -/
@[lantana_alias mhG_event]
def event (i : Nat) (e : MEvent) : IProp GF :=
  iprop(∃ h : List MEvent, ⌜h.length = i + 1 ∧ h.getLast? = some e ∧ ModelHistoryWf h⌝ ∧
    (name GF ↪◯MLP h))

@[lantana_alias mhG_history_auth_timeless]
instance auth_timeless (h : List MEvent) : Timeless (auth (GF := GF) h) := by
  unfold auth; infer_instance

@[lantana_alias mhG_event_persistent]
instance event_persistent (i : Nat) (e : MEvent) : Persistent (event (GF := GF) i e) := by
  unfold event; infer_instance

@[lantana_alias mhG_event_timeless]
instance event_timeless (i : Nat) (e : MEvent) : Timeless (event (GF := GF) i e) := by
  unfold event; infer_instance

@[lantana_alias mhG_history_auth_wf]
theorem auth_wf (h : List MEvent) : auth (GF := GF) h ⊢ ⌜ModelHistoryWf h⌝ := by
  unfold auth
  iintro ⟨%wf, -⟩
  ipureintro
  exact wf

/-- Append one event above the last (Rocq `mhG_history_auth_app`). -/
@[lantana_alias mhG_history_auth_app]
theorem auth_append (h : List MEvent) (e : MEvent)
    (hlast : ∀ e', h.getLast? = some e' → eventLe e' e) :
    auth (GF := GF) h ⊢ |==> auth (h ++ [e]) := by
  unfold auth
  iintro ⟨%wf, H⟩
  imod auth_own_update_app _ [e] $$ H with ⟨$, -⟩
  ipureintro
  exact wf.append_one hlast

/-- A snapshot of any event of the history (Rocq `mhG_history_event`). -/
@[lantana_alias mhG_history_event]
theorem auth_event {h : List MEvent} {i : Nat} {e : MEvent} (hi : h[i]? = some e) :
    auth (GF := GF) h ⊢ event i e := by
  unfold auth event
  iintro ⟨%wf, H⟩
  iexists h.take (i + 1)
  isplit
  · ipureintro
    refine ⟨?_, getLast?_take hi, wf.isPrefix (List.take_prefix _ _)⟩
    have := lt_length_of_getElem? hi
    rw [List.length_take]
    omega
  · iapply lb_own_le _ _ (List.take_prefix _ _)
    iapply lb_own_get $$ H

/-- A snapshot is an entry of the history (Rocq `mhG_event_history_lookup`), from the raw
authoritative list. -/
theorem event_lookup_raw (h : List MEvent) (i : Nat) (e : MEvent) :
    (name GF ↪●MLP h) ⊢@{IProp GF} event i e -∗ ⌜h[i]? = some e⌝ := by
  unfold event
  iintro H ⟨%h', %⟨hlen, hlast, -⟩, E⟩
  icases auth_lb_own_valid _ _ h h' $$ H E with %⟨-, hp⟩
  ipureintro
  exact prefix_getElem? hp (getLast?_eq_getElem?_of_length hlen hlast)

@[lantana_alias mhG_event_history_lookup]
theorem event_lookup (h : List MEvent) (i : Nat) (e : MEvent) :
    auth (GF := GF) h ⊢ event i e -∗ ⌜h[i]? = some e⌝ := by
  unfold auth
  iintro ⟨-, H⟩
  iapply event_lookup_raw $$ H

/-- Snapshots are ordered in time (Rocq `mhG_event_compare`). -/
@[lantana_alias mhG_event_compare]
theorem event_compare {i j : Nat} (e₁ e₂ : MEvent) (hij : i ≤ j) :
    event (GF := GF) i e₁ ⊢ event j e₂ -∗ ⌜eventLe e₁ e₂⌝ := by
  unfold event
  iintro ⟨%h₁, %⟨hlen₁, hlast₁, -⟩, E₁⟩ ⟨%h₂, %⟨hlen₂, hlast₂, wf₂⟩, E₂⟩
  icases lb_own_valid _ h₁ h₂ $$ E₁ E₂ with %hp
  ipureintro
  have h₁e : h₁[i]? = some e₁ := getLast?_eq_getElem?_of_length hlen₁ hlast₁
  have h₂e : h₂[j]? = some e₂ := getLast?_eq_getElem?_of_length hlen₂ hlast₂
  have hp' : h₁ <+: h₂ := by
    rcases hp with hp | hp
    · exact hp
    · have := hp.length_le
      exact (hp.eq_of_length_le (by omega)) ▸ List.prefix_refl _
  exact wf₂.lookup (prefix_getElem? hp' h₁e) h₂e hij

end MHist

section Interp

variable {GF : BundledGFunctors} [MHistGS GF]

/-- The model history interpretation: `h` has `i + 1` events ending with `(n, Ω)`
(Rocq `model_history_interp`). -/
@[lantana_alias model_history_interp]
def modelHistoryInterp (h : List MEvent) (i n : Nat) (Ω : Obls) : IProp GF :=
  iprop(⌜h.length = i + 1 ∧ h.getLast? = some (n, Ω)⌝ ∗ MHist.auth h)

/-- At event `i` (which was `e`), obligation `k` was `o` (Rocq `event_obl`). -/
@[lantana_alias event_obl]
def eventObl (i : Nat) (e : MEvent) (k : Oid) (o : Obl) : IProp GF :=
  iprop(MHist.event i e ∗ ⌜get? e.2 k = some o⌝)

@[lantana_alias model_history_interp_timeless]
instance modelHistoryInterp_timeless (h : List MEvent) (i n : Nat) (Ω : Obls) :
    Timeless (modelHistoryInterp (GF := GF) h i n Ω) := by
  unfold modelHistoryInterp; infer_instance

@[lantana_alias event_obl_persistent]
instance eventObl_persistent (i : Nat) (e : MEvent) (k : Oid) (o : Obl) :
    Persistent (eventObl (GF := GF) i e k o) := by
  unfold eventObl; infer_instance

@[lantana_alias event_obl_timeless]
instance eventObl_timeless (i : Nat) (e : MEvent) (k : Oid) (o : Obl) :
    Timeless (eventObl (GF := GF) i e k o) := by
  unfold eventObl; infer_instance

@[lantana_alias model_history_interp_wf]
theorem modelHistoryInterp_wf (h : List MEvent) (i n : Nat) (Ω : Obls) :
    modelHistoryInterp (GF := GF) h i n Ω ⊢
      ⌜h.length = i + 1 ∧ h.getLast? = some (n, Ω) ∧ ModelHistoryWf h⌝ := by
  unfold modelHistoryInterp MHist.auth
  iintro ⟨%⟨hlen, hlast⟩, %wf, -⟩
  ipureintro
  exact ⟨hlen, hlast, wf⟩

@[lantana_alias model_history_interp_lookup]
theorem modelHistoryInterp_lookup (h : List MEvent) (i n : Nat) (Ω : Obls) :
    modelHistoryInterp (GF := GF) h i n Ω ⊢ ⌜h[i]? = some (n, Ω)⌝ := by
  unfold modelHistoryInterp
  iintro ⟨%⟨hlen, hlast⟩, -⟩
  ipureintro
  exact getLast?_eq_getElem?_of_length hlen hlast

/-- A round appends an event: the index does not decrease and the obligations grow in `Obls.le`
(Rocq `model_history_interp_step`; called by every round). -/
@[lantana_alias model_history_interp_step]
theorem modelHistoryInterp_step (h : List MEvent) (i : Nat) {n₁ n₂ : Nat} {Ω₁ Ω₂ : Obls}
    (hn : n₁ ≤ n₂) (hΩ : Obls.le Ω₁ Ω₂) :
    modelHistoryInterp (GF := GF) h i n₁ Ω₁ ⊢
      |==> modelHistoryInterp (h ++ [(n₂, Ω₂)]) (i + 1) n₂ Ω₂ := by
  unfold modelHistoryInterp
  iintro ⟨%⟨hlen, hlast⟩, Ha⟩
  have hlink : ∀ e', h.getLast? = some e' → eventLe e' (n₂, Ω₂) := by
    intro e' he'
    rw [hlast] at he'
    cases he'
    exact ⟨hn, hΩ⟩
  imod MHist.auth_append h (n₂, Ω₂) hlink $$ Ha with Ha
  iframe Ha
  ipureintro
  simp [hlen]

/-- A snapshot of the current obligation `k` (Rocq `model_history_interp_event_obl_now`). -/
@[lantana_alias model_history_interp_event_obl_now]
theorem modelHistoryInterp_eventObl_now (h : List MEvent) (i n : Nat) (Ω : Obls) {k : Oid}
    {o : Obl} (hk : get? Ω k = some o) :
    modelHistoryInterp (GF := GF) h i n Ω ⊢ eventObl i (n, Ω) k o := by
  unfold modelHistoryInterp eventObl
  iintro ⟨%⟨hlen, hlast⟩, Ha⟩
  isplitl [Ha]
  · iapply MHist.auth_event (getLast?_eq_getElem?_of_length hlen hlast) $$ Ha
  · ipureintro
    exact hk

/-- A snapshot of a past obligation (Rocq `model_history_interp_event_obl_any`). -/
@[lantana_alias model_history_interp_event_obl_any]
theorem modelHistoryInterp_eventObl_any (h : List MEvent) (i n : Nat) (Ω : Obls) {j : Nat}
    {e : MEvent} {k : Oid} {o : Obl} (hj : h[j]? = some e) (hk : get? e.2 k = some o) :
    modelHistoryInterp (GF := GF) h i n Ω ⊢ eventObl j e k o := by
  unfold modelHistoryInterp eventObl
  iintro ⟨-, Ha⟩
  isplitl [Ha]
  · iapply MHist.auth_event hj $$ Ha
  · ipureintro
    exact hk

/-- What a snapshot says about the current history
(Rocq `event_obl_model_history_interp_lookup`). -/
@[lantana_alias event_obl_model_history_interp_lookup]
theorem eventObl_modelHistoryInterp_lookup (h : List MEvent) (i n : Nat) (Ω : Obls) (j : Nat)
    (e : MEvent) (k : Oid) (o : Obl) :
    modelHistoryInterp (GF := GF) h i n Ω ∗ eventObl j e k o ⊢
      ⌜h[j]? = some e ∧ get? e.2 k = some o ∧ j ≤ i ∧ e.1 ≤ n ∧ Obls.le e.2 Ω⌝ := by
  unfold modelHistoryInterp eventObl MHist.auth
  iintro ⟨⟨%⟨hlen, hlast⟩, %wf, Ha⟩, ⟨He, %hk⟩⟩
  icases MHist.event_lookup_raw h j e $$ Ha He with %hj
  ipureintro
  have hji : j ≤ i := by have := lt_length_of_getElem? hj; omega
  have hle := wf.lookup hj (getLast?_eq_getElem?_of_length hlen hlast) hji
  exact ⟨hj, hk, hji, hle.1, hle.2⟩

/-- Snapshots of the same obligation are ordered in time (Rocq `event_obl_compare`). -/
@[lantana_alias event_obl_compare]
theorem eventObl_compare {i j : Nat} (e₁ e₂ : MEvent) (k : Oid) (o₁ o₂ : Obl) (hij : i ≤ j) :
    eventObl (GF := GF) i e₁ k o₁ ∗ eventObl j e₂ k o₂ ⊢
      ⌜e₁.1 ≤ e₂.1 ∧ Obls.le e₁.2 e₂.2 ∧ Obl.le o₁ o₂⌝ := by
  unfold eventObl
  iintro ⟨⟨E₁, %h₁⟩, ⟨E₂, %h₂⟩⟩
  icases MHist.event_compare e₁ e₂ hij $$ E₁ E₂ with %⟨hn, hΩ⟩
  ipureintro
  exact ⟨hn, hΩ, hΩ.2 k o₁ o₂ h₁ h₂⟩

end Interp

/-- The ghost state of the model history at the name `γ`, over the world's camera (D32: the
name is small enough for the existential property of satisfiability, unlike `MHistGS GF`). -/
@[reducible] def MHistGS.ofName {GF : BundledGFunctors} [MHistGpreS GF] (γ : GName) :
    MHistGS GF where
  name := γ

/-- Allocating the model history with its first event, at the name `γ` (D32). -/
theorem modelHistoryInterp_init_names {GF : BundledGFunctors} [MHistGpreS GF] (n : Nat)
    (Ω : Obls) :
    ⊢@{IProp GF} |==> ∃ γ : GName, letI := MHistGS.ofName (GF := GF) γ;
      modelHistoryInterp [(n, Ω)] 0 n Ω := by
  iintro
  imod MonoListP.own_alloc [(n, Ω)] with ⟨%γ, Ha, -⟩
  imodintro
  iexists γ
  unfold modelHistoryInterp MHist.auth
  simp only [MHist.name]
  iframe Ha
  ipureintro
  exact ⟨⟨rfl, rfl⟩, ModelHistoryWf.singleton _⟩

/-- Allocating the model history with its first event (Rocq `model_history_interp_init`). -/
@[lantana_alias model_history_interp_init]
theorem modelHistoryInterp_init {GF : BundledGFunctors} [MHistGpreS GF] (n : Nat) (Ω : Obls) :
    ⊢@{IProp GF} |==> ∃ _ : MHistGS GF, modelHistoryInterp [(n, Ω)] 0 n Ω := by
  imod modelHistoryInterp_init_names (GF := GF) n Ω with ⟨%γ, H⟩
  imodintro
  iexists MHistGS.ofName γ
  iexact H

end Lantana.Model
