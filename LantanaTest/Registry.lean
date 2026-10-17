/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana

/-! Tests for the temporal registry: a closed world `TestGF : BundledGFunctors.{0}` with the
ghost state of the registry for HeapLang (the monotone list of entries in slot 0, the saved
trace predicates in slot 1) and of the history (slot 2), the `RegGpreS` and `MonoListG`
instances, the allocation, a registration and the marker argument.

Universes: the list camera `MonoList (DiscreteO (Nat × RegEntry))` is in `Type`, so its slot is
`ULiftOF` of it (`ElemG.ofEqLift`), as for the history. The saved predicates
`DFracAgreeRF (DiscreteFunOF fun _ : Trace Exp State => LaterOF IdOF)` take their results in
the universe of `IProp TestGF` (`Type 4`) already, so the slot is the functor itself
(`ElemG.ofEq`); no annotation is needed. -/

namespace LantanaTest.Registry

open Iris Iris.BI Iris.ProofMode Lantana Lantana.HeapLang

/-- The functor of saved trace predicates of HeapLang. -/
abbrev TrPredF : COFE.OFunctorPre := DiscreteFunOF fun _ : Trace Exp State => LaterOF IdOF

noncomputable def TestGF : BundledGFunctors.{0} := fun n =>
  match n with
  | 0 => ⟨ULiftOF (constOF (MonoList (DiscreteO (Nat × RegEntry)))), by infer_instance⟩
  | 1 => ⟨DFracAgree.DFracAgreeRF TrPredF, by infer_instance⟩
  | 2 => ⟨ULiftOF (constOF (MonoList (DiscreteO (HistEntry Exp State)))), by infer_instance⟩
  | _ => ⟨constOFU Unit, by infer_instance⟩

noncomputable instance : RegGpreS Exp State TestGF where
  listG := ⟨ElemG.ofEqLift 0 (by unfold TestGF; rfl)⟩
  predG := { elemG := ElemG.ofEq 1 (by unfold TestGF; rfl) }

noncomputable instance : MonoListG TestGF (HistEntry Exp State) :=
  ⟨ElemG.ofEqLift 2 (by unfold TestGF; rfl)⟩

/-! Allocation. -/

example : ⊢@{IProp TestGF} |==> ∃ _ : RegGS Exp State TestGF, regAuth [] :=
  regGS_alloc

example (f : Trace Exp State → IProp TestGF) : ⊢@{IProp TestGF} |==> ∃ γ, savedTrI γ f :=
  savedTrI_alloc f

/-- Allocate the registry and register two entries; the second is at index `1`. -/
example : ⊢@{IProp TestGF} |==> ∃ _ : RegGS Exp State TestGF,
    regAuth [(0, .mark), (3, .always nroot 7)] ∗ regIdx 1 3 (.always nroot 7) := by
  imod regGS_alloc with ⟨%G, Ha⟩
  imod @regAuth_append _ _ _ G [] 0 .mark (by simp) $$ Ha with ⟨Ha, -⟩
  simp only [List.nil_append]
  imod @regAuth_append _ _ _ G [(0, .mark)] 3 (.always nroot 7) (by simp) $$ Ha with ⟨Ha, Hi⟩
  simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
  imodintro
  iexists G
  iframe

/-! The language of the registry is an output parameter: no annotations. -/

section
variable [RegGS Exp State TestGF]

example (l : List (Nat × RegEntry)) (j p : Nat) (e : RegEntry) :
    regAuth l ⊢@{IProp TestGF} regIdx j p e -∗ ⌜l[j]? = some (p, e)⌝ :=
  regAuth_idx_lookup l j p e

/-- Two snapshots of the same index agree. -/
example (j p p' : Nat) (e e' : RegEntry) :
    regIdx j p e ∗ regIdx j p' e' ⊢@{IProp TestGF} ⌜p = p'⌝ := by
  iintro ⟨H, H'⟩
  icases regIdx_agree j p p' e e' $$ H H' with %⟨hp, -⟩
  ipureintro
  exact hp

/-- The marker argument: an entry not in the prefix that ends with the marker of position `5`
was registered at position `5` or later. -/
example (l : List (Nat × RegEntry)) (j p : Nat) (e : RegEntry) (hj : l.length ≤ j) :
    regLb (l ++ [(5, .mark)]) ∗ regIdx j p e ⊢@{IProp TestGF} ⌜5 ≤ p⌝ := by
  iintro ⟨Hl, Hi⟩
  icases regIdx_lb_pos (l := l ++ [(5, .mark)]) (m := 5) j p e (by simp) $$ Hl Hi with %h
  ipureintro
  rcases h with h | h
  · rw [List.getElem?_append_right hj] at h
    rcases hk : j - l.length with _ | k
    · rw [hk] at h
      cases h
      exact Nat.le_refl _
    · rw [hk] at h
      cases h
  · exact h

/-- Saved trace predicates agree up to a later. -/
example (γ : GName) (f g : Trace Exp State → IProp TestGF) (τ : Trace Exp State) :
    savedTrI γ f ∗ savedTrI γ g ⊢@{IProp TestGF} ▷ (f τ ≡ g τ) := by
  iintro ⟨Hf, Hg⟩
  ihave H := savedTrI_agree_fun γ f g $$ Hf Hg
  inext
  ihave H2 := (discreteFun_equivI f g).mp $$ H
  ispecialize H2 $$ %τ
  iexact H2

end

/-! Registration in the registry state, given the history. -/

section
variable [RegGS Exp State TestGF] [HistGS Exp State TestGF] [StateInterp Exp State TestGF]

example (Hd : RegEntry → IProp TestGF) (e : RegEntry) (h : List (HistEntry Exp State)) (n : Nat)
    (σ : State) (tp : ThreadPool Exp) (He : ⊢ Hd e) :
    regStateWith Hd ∗ historyInterp h n σ tp ⊢@{IProp TestGF}
      |==> (historyInterp h n σ tp ∗ regStateWith Hd ∗ ∃ j, regIdx j n e) := by
  iintro ⟨Hs, HI⟩
  iapply regRegister Hd e h n σ tp $$ Hs [] HI
  iintro %st -
  iapply He

end

end LantanaTest.Registry
