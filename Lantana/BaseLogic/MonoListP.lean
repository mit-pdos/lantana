/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from Iris-Lean's `Iris.BI.Lib.MonoList`, whose header reads:
  Copyright (c) The Iris-Lean Contributors
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Markus de Medeiros
Modified by the Lantana-Lean Contributors; the module documentation describes the changes.
-/
module

public import Iris.Algebra.Lib.MonoList
public import Iris.BI
public import Iris.BI.Lib.Fractional
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Lantana.BaseLogic.LaterCredits

/-!
# Ghost state for append-only lists, in any universe

A copy of Iris-Lean's `Iris.BI.Lib.MonoList` whose element type `α` may live in any universe:
Iris-Lean's `MonoListG` uses `constOF : Type → OFunctorPre` and so only stores `Type 0` data,
but Lantana's model history records obligation maps, which contain ordinals (`Type 2`). The
functor is `Lantana.constOFP` (`LaterCredits.lean`), and the world needs a `ULiftOF` slot as in
`LantanaTest/Credits.lean`. Three assertions, with the notations suffixed by `P`:
- an authoritative proposition `γ ↪●MLP{dq} l` for the authoritative list `l`;
- a persistent assertion `γ ↪◯MLP l` witnessing that the authoritative list is at least `l`;
- a persistent assertion `γ ↪◯MLP[i] a` witnessing that index `i` holds `a`.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.MonoList

universe v

class MonoListPG (GF : BundledGFunctors) (α : Type v) where
  elem : ElemG GF (constOFP (MonoList (DiscreteO α)))

attribute [reducible, instance] MonoListPG.elem


namespace MonoListP

variable {GF : BundledGFunctors} {α : Type v} [MonoListPG GF α]

/-! ## Helper functions -/

theorem map_mk_inj : ∀ {l1 l2 : List α}, l1.map DiscreteO.mk = l2.map DiscreteO.mk → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [DiscreteO.eqv_inj h.1, map_mk_inj h.2]

theorem map_mk_prefix {l1 l2 : List α} (h : l1.map DiscreteO.mk <+: l2.map DiscreteO.mk) :
    l1 <+: l2 := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨a, b, rfl, ha, _⟩ := List.map_eq_append_iff.mp ht.symm
  exact ⟨b, by rw [map_mk_inj ha]⟩

theorem prefix_getElem? {l1 l2 : List α} {i : Nat} {a : α} (h : l1 <+: l2)
    (hi : l1[i]? = some a) : l2[i]? = some a := by
  obtain ⟨t, rfl⟩ := h
  grind

/-! ## Definitions -/

def authOwn (γ : GName) (dq : DFrac) (l : List α) : IProp GF :=
  iOwn (E := MonoListPG.elem) γ (auth dq (l.map DiscreteO.mk))


def lbOwn (γ : GName) (l : List α) : IProp GF :=
  iOwn (E := MonoListPG.elem) γ (lb (l.map DiscreteO.mk))


scoped notation γ " ↪●MLP{" dq "} " l => authOwn γ dq l
scoped notation γ " ↪●MLP " l => authOwn γ (DFrac.own 1) l
scoped notation γ " ↪●MLP□ " l => authOwn γ DFrac.discard l
scoped notation γ " ↪◯MLP " l => lbOwn γ l

def idxOwn (γ : GName) (i : Nat) (a : α) : IProp GF := iprop%
  ∃ l, ⌜l[i]? = some a⌝ ∗ lbOwn γ l

scoped notation γ " ↪◯MLP[" i "] " a => idxOwn γ i a

/-! ## Instances -/

instance {γ dq} {l : List α} : Timeless (PROP := IProp GF) (γ ↪●MLP{dq} l) := by
  unfold authOwn
  infer_instance

instance {γ} {l : List α} : Persistent (PROP := IProp GF) (γ ↪●MLP□ l) := by
  unfold authOwn
  infer_instance

instance {γ} {l : List α} : Timeless (PROP := IProp GF) (γ ↪◯MLP l) := by
  unfold lbOwn
  infer_instance

instance {γ} {l : List α} : Persistent (PROP := IProp GF) (γ ↪◯MLP l) := by
  unfold lbOwn
  infer_instance

instance {γ i} {a : α} : Timeless (PROP := IProp GF) (γ ↪◯MLP[i] a) := by
  unfold idxOwn
  infer_instance

instance {γ i} {a : α} : Persistent (PROP := IProp GF) (γ ↪◯MLP[i] a) := by
  unfold idxOwn
  infer_instance

instance {γ} {l : List α} :
    Fractional (PROP := IProp GF) (fun q : Qp => γ ↪●MLP{.own q} l) where
  fractional p q := by
    unfold authOwn
    rw [← iOwn_op.to_eq]
    exact (congrArg (iOwn _) (auth_dfrac_op (.own p) (.own q) _)).to_bi

instance {γ} {l : List α} {ioΦ ioq : Iris.ProofMode.InOut} q :
   AsFractional (PROP := IProp GF) (γ ↪●MLP{.own q} l) ioΦ (γ ↪●MLP{.own ·} l) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := inferInstance

/-! ## Agreement -/

theorem authOwn_agree (γ : GName) (dq1 dq2 : DFrac) (l1 l2 : List α) :
    ⊢@{IProp GF} (γ ↪●MLP{dq1} l1) -∗ (γ ↪●MLP{dq2} l2) -∗
      ⌜✓ (dq1 • dq2) ∧ l1 = l2⌝ := by
  unfold authOwn
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  obtain ⟨hdq, hl⟩ := (auth_dfrac_op_valid ..).mp Hvalid
  exact ⟨hdq, map_mk_inj hl⟩

theorem authOwn_exclusive (γ : GName) (l1 l2 : List α) :
    ⊢@{IProp GF} (γ ↪●MLP l1) -∗ (γ ↪●MLP l2) -∗ False := by
  unfold authOwn
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  exact (auth_op_valid ..).mp Hvalid

theorem authOwn_lbOwn_valid (γ : GName) (dq : DFrac) (l1 l2 : List α) :
    ⊢@{IProp GF} (γ ↪●MLP{dq} l1) -∗ (γ ↪◯MLP l2) -∗ ⌜✓ dq ∧ l2 <+: l1⌝ := by
  unfold authOwn lbOwn
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  obtain ⟨hdq, hpre⟩ := (both_dfrac_valid ..).mp Hvalid
  exact ⟨hdq, map_mk_prefix hpre⟩

theorem lbOwn_valid (γ : GName) (l1 l2 : List α) :
    ⊢@{IProp GF} (γ ↪◯MLP l1) -∗ (γ ↪◯MLP l2) -∗ ⌜l1 <+: l2 ∨ l2 <+: l1⌝ := by
  unfold lbOwn
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  exact (lb_op_valid ..).mp Hvalid |>.imp map_mk_prefix map_mk_prefix

theorem idx_agree (γ : GName) (i : Nat) (a1 a2 : α) :
    ⊢@{IProp GF} (γ ↪◯MLP[i] a1) -∗ (γ ↪◯MLP[i] a2) -∗ ⌜a1 = a2⌝ := by
  unfold idxOwn
  iintro H1 H2
  icases H1 with ⟨%l1, %Hl1, H1⟩
  icases H2 with ⟨%l2, %Hl2, H2⟩
  icases lbOwn_valid γ l1 l2 $$ H1 H2 with %Hpre
  ipureintro
  grind [prefix_getElem?]

theorem auth_idx_lookup (γ : GName) (dq : DFrac) (l : List α) (i : Nat) (a : α) :
    ⊢@{IProp GF} (γ ↪●MLP{dq} l) -∗ (γ ↪◯MLP[i] a) -∗ ⌜l[i]? = some a⌝ := by
  unfold idxOwn
  iintro H1 H2
  icases H2 with ⟨%l1, %Hl1, H2⟩
  icases authOwn_lbOwn_valid γ dq l l1 $$ H1 H2 with %Hpre
  ipureintro
  exact prefix_getElem? Hpre.2 Hl1

/-! ## Snapshots -/

theorem lbOwn_get (γ : GName) (dq : DFrac) (l : List α) :
    ⊢@{IProp GF} (γ ↪●MLP{dq} l) -∗ (γ ↪◯MLP l) := by
  unfold authOwn lbOwn
  iintro H
  iapply iOwn_mono $$ H
  exact included ..

theorem lbOwn_le (γ : GName) {l : List α} (l' : List α) (h : l' <+: l) :
    ⊢@{IProp GF} (γ ↪◯MLP l) -∗ (γ ↪◯MLP l') := by
  unfold lbOwn
  iintro H
  iapply iOwn_mono $$ H
  exact lb_mono (h.map _)

theorem lbOwn_nil (γ : GName) : ⊢@{IProp GF} |==> (γ ↪◯MLP ([] : List α)) := by
  unfold lbOwn
  rw [List.map_nil]
  iapply iOwn_unit

theorem idxOwn_get (γ : GName) {l : List α} (i : Nat) (a : α) (h : l[i]? = some a) :
    ⊢@{IProp GF} (γ ↪◯MLP l) -∗ (γ ↪◯MLP[i] a) := by
  unfold idxOwn
  iintro H
  iexists l
  iframe H %h

/-! ## Allocation and updates -/

theorem own_alloc (l : List α) :
    ⊢@{IProp GF} |==> ∃ γ, (γ ↪●MLP l) ∗ (γ ↪◯MLP l) := by
  unfold authOwn lbOwn
  imod iOwn_alloc (F := constOFP (MonoList (DiscreteO α)))
      (●ML (l.map DiscreteO.mk) • ◯ML (l.map DiscreteO.mk)) with ⟨%γ, H⟩
  · exact (both_valid ..).mpr List.prefix_rfl
  imodintro
  iexists γ
  icases iOwn_op $$ H with ⟨$, $⟩

theorem authOwn_update (γ : GName) {l : List α} (l' : List α) (h : l <+: l') :
    ⊢@{IProp GF} (γ ↪●MLP l) ==∗ (γ ↪●MLP l') ∗ (γ ↪◯MLP l') := by
  iintro H
  ihave >Hauth : |==> (γ ↪●MLP l') $$ [H]
  · unfold authOwn
    iapply iOwn_update $$ H
    exact update _ (h.map _)
  · ihave #$ := lbOwn_get $$ Hauth
    iframe

theorem authOwn_update_app (γ : GName) {l : List α} (l' : List α) :
    ⊢@{IProp GF} (γ ↪●MLP l) ==∗ (γ ↪●MLP (l ++ l')) ∗ (γ ↪◯MLP (l ++ l')) :=
  authOwn_update γ (l ++ l') (List.prefix_append ..)

theorem authOwn_persist (γ : GName) (dq : DFrac) (l : List α) :
    ⊢@{IProp GF} (γ ↪●MLP{dq} l) ==∗ (γ ↪●MLP□ l) := by
  unfold authOwn
  iintro H
  iapply iOwn_update $$ H
  exact auth_persist dq (l.map DiscreteO.mk)

theorem authOwn_unpersist (γ : GName) (l : List α) :
    ⊢@{IProp GF} (γ ↪●MLP□ l) ==∗ ∃ q, γ ↪●MLP{DFrac.own q} l := by
  unfold authOwn
  iintro H
  imod iOwn_updateP (auth_unpersist _) $$ H with ⟨%a, %⟨q, rfl⟩, H⟩
  iexists q
  iframe

end MonoListP


end Lantana
