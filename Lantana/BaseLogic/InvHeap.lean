/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from Iris-Lean's `Iris.BI.Lib.InvHeap`, whose header reads:
  Copyright (c) The Iris-Lean Contributors
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Markus de Medeiros
Modified by the Lantana-Lean Contributors; the module documentation describes the changes.
-/
module

public import Lantana.BaseLogic.Invariants
public import Iris.Algebra
public import Iris.Algebra.Auth
public import Iris.Algebra.Excl
public import Iris.BI.Lib.GenHeap

/-! # Invariant locations

Heap locations whose values satisfy an invariant, over Lantana's invariants (Rocq:
`lantana/base_logic/gen_inv_heap.v`, itself Transfinite Iris's `gen_inv_heap.v` over Lantana's
`invGS`). This file is Iris-Lean's `Iris.BI.Lib.InvHeap` re-instantiated over `Lantana.InvGS` and
`Lantana.inv` (decision D8 (i)): the same declarations, names and statements, in namespace
`Lantana`. All accessors use `inv_acc_timeless` (the invariant body is timeless), so none needs
finite step indices.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.Std Std.PartialMap Std.LawfulPartialMap Iris.Algebra ORA Iris.BI Iris.ProofMode
open Agree Auth BigSepM Excl Heap

universe u

@[lantana_alias inv_heapN]
def invHeapN : Namespace := nroot.@"inv_heap"

@[lantana_alias inv_heap_mapUR]
abbrev InvHeapMapUR (V : Type _) (H : Type _ → Type _) : Type _ :=
  H (Option (Excl (DiscreteO V)) × Agree (DiscreteO (V → Prop)))

section toInvHeap

variable {L V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H L]

@[lantana_alias to_inv_heap]
def toInvHeap (h : H (V × (V → Prop))) : InvHeapMapUR V H :=
  map (fun p => (some (.excl ⟨p.1⟩), toAgree ⟨p.2⟩)) h

@[lantana_alias lookup_to_inv_heap_None]
theorem get?_toInvHeap_none {h : H (V × (V → Prop))} {l : L} (hl : get? h l = none) :
    get? (toInvHeap h) l = none := by
  rw [toInvHeap, get?_map, hl, Option.map_none]

@[lantana_alias lookup_to_inv_heap_Some]
theorem get?_heap_some_toInvHeap {h : H (V × (V → Prop))} {l : L} {v : V} {I : V → Prop}
    (hl : get? h l = some (v, I)) :
    get? (toInvHeap h) l = some (some (.excl ⟨v⟩), toAgree ⟨I⟩) := by
  rw [toInvHeap, get?_map, hl, Option.map_some]

@[lantana_alias lookup_to_inv_heap_Some_2]
theorem get?_toInvHeap_some {h : H (V × (V → Prop))} {l : L}
    {v' : Option (Excl (DiscreteO V))} {I' : Agree (DiscreteO (V → Prop))}
    (hl : get? (toInvHeap h) l = some (v', I')) :
    ∃ v I, v' = some (.excl ⟨v⟩) ∧ I' = toAgree ⟨I⟩ ∧ get? h l = some (v, I) := by
  rw [toInvHeap, get?_map] at hl
  rcases hh : get? h l with _ | ⟨v, I⟩ <;> rw [hh] at hl <;> simp_all

private theorem singleton_inc_toInvHeap {h : H (V × (V → Prop))} {l : L} {I : V → Prop}
    {mv : Option (Excl (DiscreteO V))}
    (hinc : ({[l := (mv, toAgree ⟨I⟩)]} : InvHeapMapUR V H) ≼ toInvHeap h) :
    ∃ v, get? h l = some (v, I) ∧ mv ≼ some (excl ⟨v⟩) := by
  obtain ⟨⟨_, _⟩, hy, hinc⟩ := singleton_inc_iff.mp hinc
  obtain ⟨v, I', rfl, rfl, hh⟩ := get?_toInvHeap_some hy
  obtain ⟨hv, hI⟩ := Prod.inc_def.mp (Option.some_inc_some_iff_is_total.mp hinc)
  cases DiscreteO.eqv_inj (toAgree_included.mp hI)
  exact ⟨v, hh, hv⟩

@[lantana_alias to_inv_heap_valid]
theorem toInvHeap_valid (h : H (V × (V → Prop))) : ✓ toInvHeap h := fun l => by
  rcases hh : get? h l with _ | ⟨v, I⟩
  · rw [get?_toInvHeap_none hh]; trivial
  · exact get?_heap_some_toInvHeap hh ▸ ⟨trivial, toAgree_valid⟩

@[lantana_alias to_inv_heap_singleton]
theorem toInvHeap_singleton [DecidableEq L] (l : L) (v : V) (I : V → Prop) :
    toInvHeap (H := H) {[l := (v, I)]} = {[l := (some (.excl ⟨v⟩), toAgree ⟨I⟩)]} := by
  rw [PartialMap.singleton, toInvHeap, map_insert, map_empty]; rfl

@[lantana_alias to_inv_heap_insert]
theorem toInvHeap_insert [DecidableEq L] (l : L) (v : V) (I : V → Prop) (h : H (V × (V → Prop))) :
    toInvHeap (insert h l (v, I)) = insert (toInvHeap h) l (some (.excl ⟨v⟩), toAgree ⟨I⟩) :=
  map_insert

end toInvHeap

@[lantana_alias inv_heapGpreS]
class invHeapPreS (L V : Type _) (GF : BundledGFunctors.{u}) (H : outParam <| Type _ → Type _)
    [LawfulFiniteMap H L] where
  invHeap : ElemG GF (constOF (Auth (InvHeapMapUR V H)))

attribute [reducible, instance] invHeapPreS.invHeap

@[lantana_alias inv_heapGS]
class invHeapGS (L V : outParam <| Type _) (GF : outParam <| BundledGFunctors.{u})
    (H : outParam <| Type _ → Type _) [LawfulFiniteMap H L]
    extends invHeapPreS L V GF H where
  invHeapName : GName

#lantana_ignore «inv_heapΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#lantana_ignore «subG_inv_heapGpreS» "Subsumed by BundledGFunctors typeclass synthesis"

open invHeapGS

section definitions

variable {GF : BundledGFunctors.{u}} {L V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H L]
variable [InvGS GF] [genHeapGS L V GF H] [invHeapGS L V GF H]

@[reducible, lantana_alias inv_heap_inv_P]
def invHeapInvP : IProp GF := iprop%
  ∃ h : H (V × (V → Prop)),
    iOwn (E := invHeapPreS.invHeap) invHeapName (● toInvHeap h) ∗
    [∗map] l ↦ p ∈ h, ⌜p.2 p.1⌝ ∗ l ↦ p.1

@[lantana_alias inv_heap_inv]
def invHeapInv : IProp GF := inv invHeapN invHeapInvP

@[lantana_alias inv_pointsto_own]
def invPointsToOwn (l : L) (v : V) (I : V → Prop) : IProp GF :=
  iOwn (E := invHeapPreS.invHeap (L := L)) invHeapName (◯ {[l := (some (.excl ⟨v⟩), toAgree ⟨I⟩)]})

@[lantana_alias inv_pointsto]
def invPointsTo (l : L) (I : V → Prop) : IProp GF :=
  iOwn (E := invHeapPreS.invHeap (L := L)) invHeapName (◯ {[l := (none, toAgree ⟨I⟩)]})

end definitions

/-- `l ↦_I v`: the location `l` holds `v`, and its values satisfy `I`. -/
scoped notation:50 l:50 " ↦_" I:max v:50 => invPointsToOwn l v I
/-- `l ↦_I □`: the values of the location `l` satisfy `I`. -/
scoped notation:50 l:50 " ↦_" I:max "□" => invPointsTo l I

section lemmas

variable {GF : BundledGFunctors.{u}} {L V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H L]
variable [InvGS GF] [invHeapGS L V GF H]

omit [InvGS GF] in
@[lantana_alias inv_pointsto_lookup_Some]
theorem invPointsTo_get?_some (l : L) (h : H (V × (V → Prop))) (I : V → Prop) :
    l ↦_I □ -∗ iOwn (E := invHeapPreS.invHeap) invHeapName (● toInvHeap h) -∗
      ⌜∃ v I', get? h l = some (v, I') ∧ I = I'⌝ := by
  iintro Hl Hauth
  unfold invPointsTo
  icombine Hauth Hl gives %Hvalid
  ipureintro
  obtain ⟨v, hh, -⟩ := singleton_inc_toInvHeap (auth_both_valid_discrete.mp Hvalid).1
  exact ⟨v, I, hh, rfl⟩

omit [InvGS GF] in
@[lantana_alias inv_pointsto_own_lookup_Some]
theorem invPointsToOwn_get?_some (l : L) (v : V) (h : H (V × (V → Prop))) (I : V → Prop) :
    l ↦_I v -∗ iOwn (E := invHeapPreS.invHeap) invHeapName (● toInvHeap h) -∗
      ⌜∃ I', get? h l = some (v, I') ∧ I = I'⌝ := by
  iintro Hl Hauth
  unfold invPointsToOwn
  icombine Hauth Hl gives %Hvalid
  ipureintro
  obtain ⟨v', hh, hv⟩ := singleton_inc_toInvHeap (auth_both_valid_discrete.mp Hvalid).1
  cases DiscreteO.eqv_inj (excl_included.mp hv)
  exact ⟨I, hh, rfl⟩

#lantana_ignore inv_pointsto_own_proper
  "Pointwise `Iff` on `V → Prop` is Lean equality by `funext`/`propext`; congruence is `congrArg`."
#lantana_ignore inv_pointsto_proper
  "Pointwise `Iff` on `V → Prop` is Lean equality by `funext`/`propext`; congruence is `congrArg`."

@[lantana_alias inv_pointsto_persistent]
instance instPersistentInvPointsTo (l : L) (I : V → Prop) : Persistent (l ↦_I □) := by
  haveI : CoreId (none : Option (Excl (DiscreteO V))) := unit_CoreId
  unfold invPointsTo
  infer_instance

@[lantana_alias inv_pointsto_timeless]
instance instTimelessInvPointsTo (l : L) (I : V → Prop) : Timeless (l ↦_I □) := by
  unfold invPointsTo
  infer_instance

@[lantana_alias inv_pointsto_own_timeless]
instance instTimelessInvPointsToOwn (l : L) (I : V → Prop) v : Timeless (l ↦_I v) := by
  unfold invPointsToOwn
  infer_instance

@[lantana_alias inv_heap_inv_persistent]
instance instPersistentInvHeapInv [genHeapGS L V GF H] :
    Persistent invHeapInv := by
  unfold invHeapInv
  infer_instance

omit [InvGS GF] in
@[lantana_alias inv_pointsto_own_inv]
theorem invPointsToOwn_inv (l : L) (v : V) (I : V → Prop) :
    l ↦_I v -∗ l ↦_I □ := by
  iintro Hl
  unfold invPointsToOwn invPointsTo
  iapply iOwn_mono $$ Hl
  refine (frag_inc_of_inc (singleton_inc_singleton_mono ?_))
  exact ⟨(some (.excl ⟨v⟩), toAgree ⟨I⟩), Prod.ext rfl Agree.idemp.symm⟩

variable [genHeapGS L V GF H]

local instance instTimelessInvHeapInvP : Timeless invHeapInvP :=
  @exists_timeless _ _ _ _ fun _ => inferInstance

@[lantana_alias inv_pointsto_acc]
theorem invPointsTo_acc {E : CoPset} {l : L} {I : V → Prop} (hN : ↑invHeapN ⊆ E) :
    invHeapInv -∗ l ↦_I □ ={E, E \ ↑invHeapN}=∗
    ∃ v, ⌜I v⌝ ∗ l ↦ v ∗ (l ↦ v ={E \ ↑invHeapN, E}=∗ ⌜True⌝) := by
  unfold invHeapInv
  iintro #Hinv Hl_inv
  imod inv_acc_timeless hN $$ Hinv with ⟨HP, Hclose⟩
  imodintro
  icases HP with ⟨%h, Hauth, HsepM⟩
  icases invPointsTo_get?_some l h I $$ Hl_inv Hauth with %⟨v, I', hh, rfl⟩
  icases bigSepM_lookup_acc hh $$ HsepM with ⟨⟨%hIv, Hl⟩, HsepM⟩
  iexists v
  iframe Hl %hIv
  iintro Hl
  imod Hclose $$ [Hauth HsepM Hl] with -
  · iexists h
    iframe Hauth
    iapply HsepM
    iframe Hl %hIv
  · imodintro; itrivial

variable [DecidableEq L]

@[lantana_alias make_inv_pointsto]
theorem make_invPointsTo {l : L} {v : V} {I : V → Prop} {E : CoPset} (hN : ↑invHeapN ⊆ E)
    (hI : I v) : invHeapInv -∗ l ↦ v ={E}=∗ l ↦_I v := by
  unfold invHeapInv
  iintro #Hinv Hl
  imod inv_acc_timeless hN $$ Hinv with ⟨HP, Hclose⟩
  icases HP with ⟨%h, Hauth, HsepM⟩
  rcases hlk : get? h l with _ | ⟨v', I'⟩
  · imod iOwn_update (auth_update_alloc (alloc_singleton_local_update
      (x := ((some (.excl ⟨v⟩), toAgree ⟨I⟩) :
        Option (Excl (DiscreteO V)) × Agree (DiscreteO (V → Prop))))
      (get?_toInvHeap_none hlk) ⟨trivial, toAgree_valid⟩)) $$ Hauth with ⟨Hauth, Hfrag⟩
    imod Hclose $$ [Hauth HsepM Hl] with -
    · iexists insert h l (v, I)
      rw [toInvHeap_insert]
      iframe Hauth
      iapply bigSepM_insert hlk
      iframe Hl HsepM %hI
    · imodintro
      unfold invPointsToOwn
      iexact Hfrag
  · icases bigSepM_lookup hlk $$ HsepM with ⟨-, Hl'⟩
    icases pointsTo_ne $$ Hl Hl' with %hne
    exact absurd rfl hne

@[lantana_alias inv_pointsto_own_acc_strong]
theorem invPointsToOwn_acc_strong {E : CoPset} (hN : (↑invHeapN : CoPset) ⊆ E) :
    invHeapInv ={E, E \ ↑invHeapN}=∗ ∀ (l : L) (v : V) (I : V → Prop), l ↦_I v -∗
      ⌜I v⌝ ∗ l ↦ v ∗ ∀ w, ⌜I w⌝ -∗ l ↦ w ==∗ l ↦_I w ∗ |={E \ ↑invHeapN, E}=> True := by
  unfold invHeapInv
  iintro #Hinv
  imod inv_acc_timeless hN $$ Hinv with ⟨HP, Hclose⟩
  imodintro
  iintro %l %v %I Hl_inv
  icases HP with ⟨%h, Hauth, HsepM⟩
  icases invPointsToOwn_get?_some $$ Hl_inv Hauth with %⟨I', hh, rfl⟩
  iunfold invPointsToOwn at Hl_inv
  icases bigSepM_delete hh $$ HsepM with ⟨⟨$, $⟩, HsepM⟩
  iintro %w %hIw Hl
  imod iOwn_update_op (auth_update (singleton_local_update
      (get?_heap_some_toInvHeap hh)
      (LocalUpdate.prod_1 _ _ (LocalUpdate.option (LocalUpdate.exclusive (x' := excl ⟨w⟩) trivial)))))
    $$ [$Hauth $Hl_inv] with ⟨Hauth, Hfrag⟩
  iunfold invPointsToOwn
  iframe Hfrag
  iapply Hclose $$ [Hauth HsepM Hl]
  iexists insert h l (w, I)
  rw [toInvHeap_insert]
  iframe Hauth
  iapply bigSepM_insert_delete
  iframe Hl HsepM %hIw

@[lantana_alias inv_pointsto_own_acc]
theorem invPointsToOwn_acc {E : CoPset} {l : L} {v : V} {I : V → Prop}
    (hN : (↑invHeapN : CoPset) ⊆ E) :
    invHeapInv -∗ l ↦_I v ={E, E \ ↑invHeapN}=∗
      ⌜I v⌝ ∗ l ↦ v ∗ ∀ w, ⌜I w⌝ -∗ l ↦ w ={E \ ↑invHeapN, E}=∗ l ↦_I w := by
  iintro #Hinv Hl
  imod invPointsToOwn_acc_strong hN $$ Hinv with Hacc
  icases Hacc $$ %l %v %I Hl with ⟨$, $, Hclose⟩
  iintro !> %w %hIw Hl
  imod Hclose $$ %w [//] Hl with ⟨Hfrag, >-⟩
  iexact Hfrag

end lemmas

@[lantana_alias inv_heap_init]
theorem invHeap_init (L V : Type _) {GF : BundledGFunctors.{u}} {H : Type _ → Type _}
    [LawfulFiniteMap H L] [DecidableEq L] [InvGS GF] [genHeapGS L V GF H]
    [invHeapPreS L V GF H] (E : CoPset) :
    ⊢ |==> ∃ _ : invHeapGS L V GF H, |={E}=> invHeapInv := by
  imod (iOwn_alloc (E := invHeapPreS.invHeap)
    (● toInvHeap (∅ : H (V × (V → Prop)))) (auth_valid.mpr (toInvHeap_valid ∅)))
    with ⟨%γ, Hauth⟩
  letI G : invHeapGS L V GF H := ⟨γ⟩
  imodintro
  iexists G
  unfold invHeapInv
  iapply inv_alloc invHeapN E invHeapInvP $$ [Hauth]
  inext
  iexists ∅
  iframe Hauth
  iapply bigSepM_empty; itrivial

end Lantana
