/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from Iris-Lean's `Iris.Instances.Lib.GhostMap`, whose header reads:
  Copyright (c) The Iris-Lean Contributors
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Сухарик (@suhr)
Modified by the Lantana-Lean Contributors; the module documentation describes the changes.
-/
module

public import Iris.Instances.Lib.GhostMap
public import Lantana.BaseLogic.LaterCredits

/-! # Ghost maps with values in any universe

Iris-Lean's ghost maps (`Iris.Instances.Lib.GhostMap`) store their camera in a slot
`constOF (HeapView K (Agree (DiscreteO V)) H)`, and `constOF` takes a type in `Type`. The ticket
lock records layers and measures (`Layer × Measure : Type 1`) in a ghost map, so this file
repeats the part of Iris-Lean's library that it uses over Lantana's universe-polymorphic
constant functor `constOFP`: the authoritative map `γ ↪●PMAP{dq} m` and its elements
`γ ↪◯PMAP[k]{dq} v`, with the same proofs.

A candidate for upstreaming (with `constOFP`).
-/

@[expose] public noncomputable section

namespace Lantana.Examples

open Iris Iris.Std HeapView PartialMap Iris.Algebra ORA BI Iris.ProofMode

/-- The camera of a ghost map from `K` to `V`, in any universe. -/
class GhostMapPG (GF : BundledGFunctors) (K V : Type _) (H : outParam <| Type _ → Type _)
    [LawfulFiniteMap H K] where
  elem : ElemG GF (constOFP (HeapView K (Agree (DiscreteO V)) H))

attribute [reducible, instance] GhostMapPG.elem

section definitions

variable {GF : BundledGFunctors} {K V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H K]
variable [GhostMapPG GF K V H]

/-- The authoritative map. -/
def ghostMapP_auth (γ : GName) (dq : DFrac) (m : H V) : IProp GF :=
  iOwn (E := GhostMapPG.elem) γ (Auth dq (Std.PartialMap.map (fun x ↦ toAgree ⟨x⟩) m))

/-- The element `v` at the key `k`. -/
def ghostMapP_elem (γ : GName) (dq : DFrac) (k : K) (v : V) : IProp GF :=
  iOwn (E := GhostMapPG.elem) γ (Frag k dq (toAgree ⟨v⟩))

end definitions

@[inherit_doc ghostMapP_auth]
notation γ " ↪●PMAP{" dq "} " m => ghostMapP_auth γ dq m
@[inherit_doc ghostMapP_auth]
notation γ " ↪●PMAP " m => ghostMapP_auth γ (DFrac.own 1) m
@[inherit_doc ghostMapP_elem]
notation γ " ↪◯PMAP[" k "]{" dq "} " v => ghostMapP_elem γ dq k v
@[inherit_doc ghostMapP_elem]
notation γ " ↪◯PMAP[" k "] " v => ghostMapP_elem γ (DFrac.own 1) k v

section lemmas

variable {GF : BundledGFunctors} {K V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H K]
variable [GhostMapPG GF K V H]

open LawfulPartialMap

instance ghostMapP_elem_timeless (γ : GName) (k : K) (dq : DFrac) (v : V) :
    Timeless (PROP := IProp GF) (γ ↪◯PMAP[k]{dq} v) := by
  unfold ghostMapP_elem
  infer_instance

instance ghostMapP_elem_persistent (γ : GName) (k : K) (v : V) :
    Persistent (PROP := IProp GF) (γ ↪◯PMAP[k]{.discard} v) := by
  unfold ghostMapP_elem
  infer_instance

instance ghostMapP_auth_timeless (γ : GName) (dq : DFrac) (m : H V) :
    Timeless (PROP := IProp GF) (γ ↪●PMAP{dq} m) := by
  unfold ghostMapP_auth
  infer_instance

/-- Two fractions of an element: the sum of the fractions. -/
theorem ghostMapP_elem_op (γ : GName) (k : K) (p q : Qp) (v : V) :
    (γ ↪◯PMAP[k]{.own (p + q)} v) ⊣⊢@{IProp GF}
      (γ ↪◯PMAP[k]{.own p} v) ∗ (γ ↪◯PMAP[k]{.own q} v) := by
  unfold ghostMapP_elem
  refine .trans ?_ iOwn_op
  refine BIBase.BiEntails.of_eq ?_
  refine .trans ?_ (congrArg (iOwn γ) frag_add_op_eqv)
  refine congrArg (iOwn γ) (congrArg (Frag k (.own (p + q))) ?_)
  exact Agree.idemp.symm

theorem ghostMapP_elem_valid_2 (γ : GName) (k : K) (dq1 dq2 : DFrac) (v1 v2 : V) :
    (γ ↪◯PMAP[k]{dq1} v1) ∗ (γ ↪◯PMAP[k]{dq2} v2) ⊢@{IProp GF}
      ✓ (dq1 • dq2) ∧ ⌜v1 = v2⌝ := by
  unfold ghostMapP_elem
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %H
  obtain ⟨vdq, va⟩ := frag_op_valid_iff.mp H
  ipureintro
  exact ⟨vdq, congrArg (·.car) (toAgree_op_valid_iff_eq.mp va)⟩

theorem ghostMapP_elem_agree (γ : GName) (k : K) (dq1 dq2 : DFrac) (v1 v2 : V) :
    (γ ↪◯PMAP[k]{dq1} v1) ∗ (γ ↪◯PMAP[k]{dq2} v2) ⊢@{IProp GF} ⌜v1 = v2⌝ := by
  iintro H
  icases ghostMapP_elem_valid_2 $$ H with ⟨-, $⟩

/-- Two halves of an element make the whole; their values agree. -/
theorem ghostMapP_elem_combine_halves (γ : GName) (k : K) (v1 v2 : V) :
    (γ ↪◯PMAP[k]{.own (1 : Qp).half} v1) ∗ (γ ↪◯PMAP[k]{.own (1 : Qp).half} v2) ⊢@{IProp GF}
      (γ ↪◯PMAP[k] v1) ∗ ⌜v1 = v2⌝ := by
  iintro ⟨H1, H2⟩
  ihave %h := ghostMapP_elem_agree γ k _ _ v1 v2 $$ [H1 H2]
  · iframe
  subst h
  isplitl
  · have e := (ghostMapP_elem_op (GF := GF) γ k (1 : Qp).half (1 : Qp).half v1)
    rw [Qp.half_add_half] at e
    iapply e.2
    iframe
  · ipureintro
    rfl

/-- A whole element is two halves. -/
theorem ghostMapP_elem_halves (γ : GName) (k : K) (v : V) :
    (γ ↪◯PMAP[k] v) ⊢@{IProp GF}
      (γ ↪◯PMAP[k]{.own (1 : Qp).half} v) ∗ (γ ↪◯PMAP[k]{.own (1 : Qp).half} v) := by
  have e := (ghostMapP_elem_op (GF := GF) γ k (1 : Qp).half (1 : Qp).half v)
  rw [Qp.half_add_half] at e
  exact e.1

/-- Make an element read-only. -/
theorem ghostMapP_elem_persist (γ : GName) (k : K) (dq : DFrac) (v : V) :
    ⊢@{IProp GF} (γ ↪◯PMAP[k]{dq} v) ==∗ (γ ↪◯PMAP[k]{.discard} v) := by
  unfold ghostMapP_elem
  iintro H
  iapply iOwn_update $$ H
  exact update_frag_discard

theorem ghostMapP_alloc [DecidableEq K] (m : H V) :
    ⊢@{IProp GF} |==> ∃ γ, (γ ↪●PMAP m) ∗ [∗map] k ↦ v ∈ m, γ ↪◯PMAP[k] v := by
  unfold ghostMapP_elem ghostMapP_auth
  imod iOwn_alloc_strong (E := GhostMapPG.elem)
    (Auth (DFrac.own 1) (V := Agree (DiscreteO V)) (∅ : H _)) (fun _ => True)
    (fun N => ⟨N, Nat.le_refl N, trivial⟩) with ⟨%γ, -, G⟩
  · simpa only [auth_valid_iff] using DFrac.valid_own_one
  · iexists γ
    iapply BIUpdate.mono <| sep_mono_right <| bigOpM_iOwn_entail γ _ m
    iapply BIUpdate.mono <| iOwn_op.mp
    iapply iOwn_update $$ G
    have H := update_big_alloc _ (Std.PartialMap.map (fun x : V ↦ toAgree (DiscreteO.mk x)) m) _
        (disjoint_empty_right _) DFrac.valid_own_one
        (all_map fun _ _ => Agree.toAgree_valid)
    rw [union_empty_right, BigOpM.bigOpM_map_eq] at H
    exact H

theorem ghostMapP_lookup {γ dq} {m : H V} {k : K} {dq' v} :
    ⊢@{IProp GF} (γ ↪●PMAP{dq} m) -∗ (γ ↪◯PMAP[k]{dq'} v) -∗ ⌜get? m k = some v⌝ := by
  unfold ghostMapP_auth ghostMapP_elem
  iintro H1 H2
  icombine H1 H2 gives %G
  ipureintro
  have ⟨av', _, _, h_av', _, h⟩ := auth_op_frag_valid_total_discrete_iff G
  cases h₂ : get? m k <;> grind [LawfulPartialMap.get?_map, Agree.toAgree_included]

theorem ghostMapP_insert {γ} {m : H V} (k : K) (v : V) (Heq : get? m k = .none) :
    ⊢@{IProp GF} (γ ↪●PMAP m) ==∗ (γ ↪●PMAP insert m k v) ∗ γ ↪◯PMAP[k] v := by
  unfold ghostMapP_auth ghostMapP_elem
  iintro H
  imod iOwn_update (update_one_alloc (k := k) (v1 := toAgree ⟨v⟩)
    (by simp [LawfulPartialMap.get?_map, Heq])
    DFrac.valid_own_one
    Agree.toAgree_valid) $$ H with H
  icases H with ⟨H, $⟩
  imodintro
  iapply iOwn_ord_mono $$ H
  exact auth_ord_of_map_eq _ map_insert

theorem ghostMapP_delete {γ} {m : H V} (k : K) (v : V) :
    ⊢@{IProp GF} (γ ↪●PMAP m) -∗ (γ ↪◯PMAP[k] v) ==∗ γ ↪●PMAP delete m k := by
  unfold ghostMapP_auth ghostMapP_elem
  iintro H1 H2
  icombine H1 H2 as G
  imod iOwn_update (update_one_delete (k := k) (v1 := toAgree (⟨v⟩ : DiscreteO V))) $$ G with G
  iapply iOwn_ord_mono $$ G
  exact auth_ord_of_map_eq _ map_delete

theorem ghostMapP_update {γ} {m : H V} {k : K} {v : V} (w : V) :
    ⊢@{IProp GF} (γ ↪●PMAP m) -∗ (γ ↪◯PMAP[k] v) ==∗ (γ ↪●PMAP insert m k w) ∗ γ ↪◯PMAP[k] w := by
  iintro auth_m frag_kv
  ihave >aux := ghostMapP_delete $$ auth_m frag_kv
  ihave >⟨aux, $⟩ := ghostMapP_insert _ w (get?_delete_eq rfl) $$ aux
  imodintro
  unfold ghostMapP_auth
  iapply iOwn_ord_mono $$ aux
  exact auth_ord_of_map_eq _ (map_equiv insert_delete.symm)

end lemmas

end Lantana.Examples
