/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from Iris-Lean's `Iris.Instances.Lib.Invariants`, whose header reads:
  Copyright (c) The Iris-Lean Contributors
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Sergei Stepanenko
Modified by the Lantana-Lean Contributors; the module documentation describes the changes.
-/
module

public import Lantana.BaseLogic.FUpd
public import Iris.Std.Namespaces
public import Iris.Std.CoPset

/-! # Invariants

Invariants over Lantana's fancy update (Rocq: `lantana/base_logic/invariants.v`, itself Transfinite
Iris's `base_logic/lib/invariants.v` over Lantana's `invGS`). This file is Iris-Lean's
`Iris.Instances.Lib.Invariants` re-instantiated over `Lantana.InvGS` and `Lantana.uPred_fupd`
(decision D8 (i)): the same declarations, names and statements, in namespace `Lantana`. The proofs
differ only by the explicit `◇` of Lantana's fancy update.

The rules that take `∗` apart under `▷` (`inv_alter`, `inv_combine`, `inv_combine_dup_l`,
`inv_split_l/r`, `inv_split`) need finite step indices (`[SIdxFinite SI]`): they are kept with
that marker, as in Iris-Lean, but cannot be used in Lantana's ordinal build. Their transfinite
replacements are the `_timeless` variants.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.OFE Iris.ProofMode

universe u

section InvariantDefinition

variable {GF : BundledGFunctors.{u}} [InvGS GF]

#lantana_ignore inv_def "`inv` is defined directly without `seal`/`unseal`."
#lantana_ignore inv_aux "`inv` is defined directly without `seal`/`unseal`."
#lantana_ignore inv_unseal "`inv` is defined directly without `seal`/`unseal`."

/-- The invariant `P` in the namespace `N`. -/
@[lantana_alias inv]
def inv (N : Namespace) (P : IProp GF) : IProp GF :=
  iprop(□ ∀ E, ⌜↑N ⊆ E⌝ → |={E, E \ ↑N}=> ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True))

@[lantana_alias own_inv]
def own_inv (N : Namespace) (P : IProp GF) : IProp GF :=
  iprop(∃ i, ⌜i ∈ (↑N : CoPset)⌝ ∧ ownI i P)

end InvariantDefinition

section Instances

variable {GF : BundledGFunctors.{u}} [InvGS GF]

@[lantana_alias inv_contractive]
instance inv_contractive (N : Namespace) : Contractive (inv (GF := GF) N) where
  distLater_dist {n x y} H := by
    simp only [inv]
    refine intuitionistically_ne.ne ?_
    refine forall_ne (fun i => ?_)
    refine imp_ne.ne .rfl ?_
    refine wand_ne.ne .rfl ?_
    refine rupd_ne.ne ?_
    refine except0_ne.ne ?_
    refine sep_ne.ne .rfl ?_
    refine sep_ne.ne .rfl ?_
    refine sep_ne.ne ?_ ?_
    · exact Contractive.distLater_dist H
    · refine wand_ne.ne ?_ .rfl
      exact Contractive.distLater_dist H

@[lantana_alias inv_ne]
instance inv_ne (N : Namespace) : NonExpansive (inv (GF := GF) N) := ne_of_contractive _

#lantana_ignore inv_proper "Subsumed by the NonExpansive instance `inv_ne`."

@[lantana_alias inv_persistent]
instance inv_persistent (N : Namespace) (P : IProp GF) : Persistent (inv N P) := by
  simp only [inv]
  infer_instance

instance own_inv_persistent (N : Namespace) (P : IProp GF) : Persistent (own_inv N P) := by
  simp only [own_inv]
  infer_instance

@[lantana_alias except_0_inv]
theorem except_0_inv (N : Namespace) (P : IProp GF) : ⊢ ◇ inv N P -∗ inv N P := by
  simp only [inv]
  iintro #H
  imodintro
  iintro %E %Hsub
  imod H
  iapply H
  itrivial

@[lantana_alias is_except_0_inv]
instance is_except_0_inv (N : Namespace) (P : IProp GF) : IsExcept0 (inv N P) where
  is_except0 := by iintro H; iapply except_0_inv $$ H

@[lantana_alias into_inv_inv]
instance intoInv_inv (N : Namespace) (P : IProp GF) : IntoInv (inv N P) N := {}

set_option synthInstance.checkSynthOrder false in
@[lantana_alias into_acc_inv]
instance intoAcc_inv (N : Namespace) (P : IProp GF) E :
    IntoAcc (X := Unit) (inv N P) (↑N ⊆ E) iprop(True) (fupd E (E \ ↑N)) (fupd (E \ ↑N) E)
      (fun _ => iprop(▷ P)) (fun _ => iprop(▷ P)) (fun _ => none) where
  into_acc := by
    dsimp only [inv, accessor, Option.getD]
    iintro %x #Hinv -
    imod Hinv $$ %E [] with ⟨HP, Hclose⟩
    · itrivial
    · iexists ()
      imodintro
      isplitl [HP]
      · iassumption
      · iintro HP
        iapply (BIFUpdate.mono true_emp.mp)
        iapply Hclose $$ HP

end Instances

section BasicLemmas

open Iris.Std LawfulSet

variable {GF : BundledGFunctors.{u}} [InvGS GF]

@[lantana_alias own_inv_acc]
theorem own_inv_acc (E : CoPset) (N : Namespace) (P : IProp GF) (Hsub : ↑N ⊆ E) :
    ⊢ own_inv N P ={E, E \ ↑N}=∗ ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
  simp only [own_inv, fupd, uPred_fupd]
  iintro ⟨%i, %Hin, #Hown⟩ ⟨Hwsat, HE⟩
  have Hsub' : ({i} : CoPset) ⊆ ↑N := by
    intro x; simp only [mem_singleton]
    rintro ⟨⟩
    apply Hin
  have HEEQ : ↑N ∪ (E \ ↑N) = E := by
    rw [union_comm, ←diff_subset_decomp Hsub]
  have HNEQ : {i} ∪ (nclose N \ {i}) = ↑N := by
    rw [union_comm, ←diff_subset_decomp Hsub']
  ihave HE : ownE (↑N ∪ (E \ ↑N)) $$ [HE]
  · rw [HEEQ]; iexact HE
  icases ownE_op disjoint_diff_right $$ HE with ⟨HE1, HE2⟩
  ihave HE1 : ownE ({i} ∪ (nclose N \ {i})) $$ [HE1]
  · rw [HNEQ]; iexact HE1
  icases ownE_op disjoint_diff_right $$ HE1 with ⟨HE1, HE3⟩
  imodintro
  imodintro
  icases ownI_open $$ [$Hwsat $HE1 $Hown] with ⟨$, $, HD⟩
  iframe
  iintro HP ⟨Hwsat, HE⟩
  imodintro
  imodintro
  icases ownI_close $$ [$HP $Hwsat $HD $Hown] with ⟨$, HE1⟩
  icases ownE_op disjoint_diff_right $$ [$HE1 $HE3] with HE1
  rw [HNEQ]
  icases ownE_op disjoint_diff_right $$ [$HE1 $HE] with HE
  rw [HEEQ]
  iframe

@[lantana_alias fresh_inv_name]
theorem fresh_inv_name (E : PosSet) (N : Namespace) : ∃ i, i ∉ E ∧ i ∈ (↑N : CoPset) :=
  fresh_name E N

@[lantana_alias own_inv_alloc]
theorem own_inv_alloc (N : Namespace) (E : CoPset) (P : IProp GF) :
  ⊢ ▷ P ={E}=∗ own_inv N P := by
  simp only [own_inv, fupd, uPred_fupd]
  iintro HP ⟨Hw, HE⟩
  imod ownI_alloc (· ∈ (↑N : CoPset)) P $$ [HP Hw] with ⟨%i, %Hin, Hw, HI⟩
  · intro E; apply fresh_name
  · isplitl [Hw] <;> iassumption
  · imodintro; imodintro; iframe
    itrivial

@[lantana_alias own_inv_alloc_open]
theorem own_inv_alloc_open (N : Namespace) (E : CoPset) (P : IProp GF) (Hsub : ↑N ⊆ E) :
    ⊢ |={E, E \ ↑N}=> own_inv N P ∗ (▷P ={E \ ↑N, E}=∗ True) := by
  simp only [own_inv, fupd, uPred_fupd]
  iintro ⟨Hw, HE⟩
  imod ownI_alloc_open $$ Hw with ⟨%i, %Hin, Hcont, #HI, HD⟩
  · intro _; apply fresh_name
  have Hsub' : ({i} : CoPset) ⊆ ↑N := by
    intro x; simp only [mem_singleton]
    rintro ⟨⟩
    apply Hin
  have HEEQ : ↑N ∪ (E \ ↑N) = E := by
    rw [union_comm, ←diff_subset_decomp Hsub]
  have HNEQ : {i} ∪ (nclose N \ {i}) = ↑N := by
    rw [union_comm, ←diff_subset_decomp Hsub']
  ihave HE : ownE (↑N ∪ (E \ ↑N)) $$ [HE]
  · rw [HEEQ]; iexact HE
  icases ownE_op disjoint_diff_right $$ HE with ⟨HE1, HEN⟩
  ihave HE1 : ownE ({i} ∪ (nclose N \ {i})) $$ [HE1]
  · rw [HNEQ]; iexact HE1
  icases ownE_op disjoint_diff_right $$ HE1 with ⟨HEi, HENi⟩
  imodintro
  imodintro
  ispecialize Hcont $$ HEi
  isplitl [Hcont]; iassumption
  isplitl [HEN]; iassumption
  isplitl [HI]
  · iexists i; isplit
    · ipureintro; assumption
    · iexact HI
  iintro HP ⟨Hw, HE⟩
  icases ownI_close $$ [HP Hw HD] with ⟨Hwsat, HE1⟩
  · isplitl [Hw]; iassumption
    isplitl [HI]; iassumption
    isplitl [HP]; iassumption
    iassumption
  imodintro
  imodintro
  isplitl [Hwsat]; iassumption
  icases ownE_op disjoint_diff_right $$ [HENi HE1] with HE1
  · isplitl [HE1]; iassumption
    iassumption
  rw [HNEQ]
  icases ownE_op disjoint_diff_right $$ [HE1 HE] with HE
  · isplitl [HE1]; iassumption
    iassumption
  rw [HEEQ]
  isplitl [HE]; iassumption
  apply true_intro

@[lantana_alias own_inv_to_inv]
theorem own_inv_to_inv (M : Namespace) (P : IProp GF) :
    ⊢ own_inv M P -∗ inv M P := by
  simp only [inv]
  iintro #I
  imodintro
  iintro %E %Hsub
  iapply own_inv_acc _ _ _ Hsub $$ I

end BasicLemmas

section Allocation

variable {GF : BundledGFunctors.{u}} [InvGS GF]

@[lantana_alias inv_alloc]
theorem inv_alloc (N : Namespace) (E : CoPset) (P : IProp GF) :
    ⊢ ▷ P ={E}=∗ inv N P := by
  iintro HP
  imod own_inv_alloc N $$ HP with H
  imodintro
  iapply own_inv_to_inv $$ H

@[lantana_alias inv_alloc_open]
theorem inv_alloc_open (N : Namespace) (E : CoPset) (P : IProp GF) (Hsub : ↑N ⊆ E) :
    ⊢ |={E, E \ ↑N}=> inv N P ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
  imod own_inv_alloc_open _ _ P Hsub with ⟨Hown, Hcl⟩
  imodintro
  isplitr [Hcl]
  · iapply own_inv_to_inv $$ Hown
  · iexact Hcl

end Allocation

section Access

open Iris.Std LawfulSet

variable {GF : BundledGFunctors.{u}} [InvGS GF]

/-- Open an invariant: it gives `▷ P` and the means to close it. -/
@[lantana_alias inv_acc]
theorem inv_acc {E : CoPset} {N : Namespace} {P : IProp GF} (Hsub : ↑N ⊆ E) :
    ⊢ inv N P ={E, E \ ↑N}=∗ ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
  simp only [inv]
  iintro #HI
  iapply HI $$ %E []
  ipureintro; assumption

@[lantana_alias inv_acc_strong]
theorem inv_acc_strong {E : CoPset} {N : Namespace} {P : IProp GF} (Hsub : ↑N ⊆ E) :
    ⊢ inv N P ={E, E \ ↑N}=∗ ▷ P ∗ ∀ E', ▷ P ={E', ↑N ∪ E'}=∗ True := by
  iintro Hinv
  icases inv_acc subset_refl $$ Hinv with H
  rw [diff_all]
  icases fupd_mask_frame_right disjoint_diff_right (Ef := (E \ ↑N)) $$ H with H
  rw [union_empty_left, ←union_comm, ←diff_subset_decomp Hsub]
  imod H with ⟨HP, H⟩
  imodintro
  isplitl [HP]; iassumption
  iintro %E' HP
  ispecialize H $$ HP
  icases fupd_mask_frame_right disjoint_empty_left (Ef := E') $$ H with H
  rw [union_empty_left]
  imod H; imodintro; itrivial

@[lantana_alias inv_acc_timeless]
theorem inv_acc_timeless {E : CoPset} {N : Namespace} {P : IProp GF} [Timeless P]
    (Hsub : ↑N ⊆ E) : ⊢ inv N P ={E, E \ ↑N}=∗ P ∗ (P ={E \ ↑N, E}=∗ True) := by
  iintro HI
  imod inv_acc Hsub $$ HI with ⟨>HP, H⟩
  imodintro
  isplitl [HP]; iassumption
  iintro HP
  iapply H
  inext; iassumption

theorem inv_open_fupd {E : CoPset} {N : Namespace} {P Q R : IProp GF} (Hsub : ↑N ⊆ E) :
    ⊢ inv N P -∗ (▷ P ∗ Q ={E \ N}=∗ P ∗ R) -∗ Q ={E}=∗ R := by
  iintro #Hinv H HQ
  imod inv_acc Hsub $$ Hinv with ⟨HP, Hclose⟩
  imod H $$ [$] with ⟨HP, HR⟩; iframe
  imod Hclose $$ [$HP] with -
  itrivial

end Access

section Modification

variable {GF : BundledGFunctors.{u}} [InvGS GF]

/-- This rule takes `∗` apart under `▷`, so it needs finite step indices. For a timeless `P`,
see `inv_alter_timeless`. -/
@[lantana_alias inv_alter]
theorem inv_alter [SIdxFinite SI] (N : Namespace) (P Q : IProp GF) :
    ⊢ inv N P -∗ ▷ □ (P -∗ Q ∗ (Q -∗ P)) -∗ inv N Q := by
  simp only [inv]
  iintro #HI #HPQ
  imodintro
  iintro %E Hsub
  imod HI $$ %E Hsub with ⟨HP, H⟩
  imodintro
  icases HPQ $$ HP with ⟨HQ, HQP⟩
  isplitl [HQ]
  · iexact HQ
  · iintro HQ
    iapply H
    iapply HQP $$ HQ

@[lantana_alias inv_iff]
theorem inv_iff (N : Namespace) (P Q : IProp GF) :
    ⊢ inv N P -∗ ▷ □ (P ↔ Q) -∗ inv N Q := by
  simp only [inv]
  iintro #HI #HPQ
  imodintro
  iintro %E Hsub
  imod HI $$ %E Hsub with ⟨HP, H⟩
  imodintro
  isplitl [HP]
  · inext
    simp only [iff]
    iapply HPQ $$ HP
  · iintro HQ
    iapply H
    inext
    simp only [iff]
    iapply HPQ $$ HQ

@[lantana_alias inv_alter_timeless]
theorem inv_alter_timeless (N : Namespace) (P Q : IProp GF) [Timeless P] :
    ⊢ inv N P -∗ □ (P -∗ Q ∗ ▷ (Q -∗ P)) -∗ inv N Q := by
  simp only [inv]
  iintro #HI #HPQ
  imodintro
  iintro %E Hsub
  imod HI $$ %E Hsub with ⟨>HP, H⟩
  imodintro
  icases HPQ $$ HP with ⟨HQ, HQP⟩
  isplitl [HQ]
  · inext; iexact HQ
  · iintro HQ
    iapply H
    inext
    iapply HQP $$ HQ

end Modification

section Combination

open Iris.Std LawfulSet

variable {GF : BundledGFunctors.{u}} [InvGS GF]

@[lantana_alias inv_combine]
theorem inv_combine [SIdxFinite SI] (N1 N2 N : Namespace) (P Q : IProp GF) (Hdisj : N1 ## N2)
    (Hsub : ↑N1 ∪ ↑N2 ⊆ (↑N : CoPset)) : ⊢ inv N1 P -∗ inv N2 Q -∗ inv N iprop(P ∗ Q) := by
  simp only [inv]
  iintro #HI1 #HI2
  imodintro
  iintro %E %Hsub'
  imod HI1 $$ %E [] with ⟨HP, H1⟩
  · ipureintro
    exact subset_trans (subset_trans union_subset_left Hsub) Hsub'
  imod HI2 $$ %(E \ ↑N1) [] with ⟨HQ, H2⟩
  · ipureintro
    intro x; simp only [mem_diff]
    specialize Hsub x; simp only [mem_union] at Hsub
    specialize Hsub' x
    specialize Hdisj x
    grind
  iapply fupd_mask_intro
  · intro x; simp only [mem_diff, mem_diff]
    specialize Hsub x; simp only [mem_union] at Hsub
    specialize Hsub' x
    specialize Hdisj x
    grind
  iintro Hcl
  isplitl [HP HQ]; inext; isplitl [HP] <;> iassumption
  iintro ⟨HP, HQ⟩
  imod Hcl
  imod H2 $$ HQ with _
  imod H1 $$ HP with _
  imodintro
  iassumption

@[lantana_alias inv_combine_dup_l]
theorem inv_combine_dup_l [SIdxFinite SI] (N : Namespace) (P Q : IProp GF) :
    ⊢ □ (P -∗ (P ∗ P)) -∗ inv N P -∗ inv N Q -∗ inv N iprop(P ∗ Q) := by
  simp only [inv]
  iintro #HPP #HI1 #HI2
  imodintro; iintro %E #Hsub
  imod HI1 $$ %E Hsub with ⟨HP, HI1⟩
  ihave ⟨HP1, HP2⟩ : ▷ P ∗ ▷ P $$ [HP]
  · iapply later_sep; inext; iapply HPP $$ HP
  imod HI1 $$ HP2 with _
  imod HI2 $$ %E Hsub with ⟨HQ, HI2⟩
  imodintro
  isplitl [HP1 HQ]
  · inext; isplitl [HP1] <;> iassumption
  iintro ⟨_, HQ⟩
  imod HI2 $$ HQ with _
  imodintro; iassumption

end Combination

section Splitting

variable {GF : BundledGFunctors.{u}} [InvGS GF]

@[lantana_alias inv_split_l]
theorem inv_split_l [SIdxFinite SI] (N : Namespace) (P Q : IProp GF) :
    ⊢ inv N iprop(P ∗ Q) -∗ inv N P := by
  iintro H
  iapply inv_alter $$ H
  inext; imodintro
  iintro ⟨HP, HQ⟩
  isplitl [HP]; iassumption
  iintro HP
  isplitl [HP] <;> iassumption

@[lantana_alias inv_split_r]
theorem inv_split_r [SIdxFinite SI] (N : Namespace) (P Q : IProp GF) :
    ⊢ inv N iprop(P ∗ Q) -∗ inv N Q := by
  iintro H
  iapply inv_alter $$ H
  inext; imodintro
  iintro ⟨HP, HQ⟩
  isplitl [HQ]; iassumption
  iintro HQ
  isplitl [HP] <;> iassumption

@[lantana_alias inv_split]
theorem inv_split [SIdxFinite SI] (N : Namespace) (P Q : IProp GF) :
    ⊢ inv N iprop(P ∗ Q) -∗ inv N P ∗ inv N Q := by
  iintro #H
  ihave H1 := inv_split_l $$ H
  ihave H2 := inv_split_r $$ H
  isplit <;> iassumption

@[lantana_alias inv_split_l_timeless]
theorem inv_split_l_timeless (N : Namespace) (P Q : IProp GF) [Timeless P] [Timeless Q] :
    ⊢ inv N iprop(P ∗ Q) -∗ inv N P := by
  iintro #H
  iapply inv_alter_timeless N iprop(P ∗ Q) P $$ H
  imodintro
  iintro ⟨HP, HQ⟩
  isplitl [HP]; iassumption
  inext
  iintro HP
  isplitl [HP] <;> iassumption

@[lantana_alias inv_split_r_timeless]
theorem inv_split_r_timeless (N : Namespace) (P Q : IProp GF) [Timeless P] [Timeless Q] :
    ⊢ inv N iprop(P ∗ Q) -∗ inv N Q := by
  iintro #H
  iapply inv_alter_timeless N iprop(P ∗ Q) Q $$ H
  imodintro
  iintro ⟨HP, HQ⟩
  isplitl [HQ]; iassumption
  inext
  iintro HQ
  isplitl [HP] <;> iassumption

@[lantana_alias inv_split_timeless]
theorem inv_split_timeless (N : Namespace) (P Q : IProp GF) [Timeless P] [Timeless Q] :
    ⊢ inv N iprop(P ∗ Q) -∗ inv N P ∗ inv N Q := by
  iintro #H
  ihave H1 := inv_split_l_timeless N P Q $$ H
  ihave H2 := inv_split_r_timeless N P Q $$ H
  isplit <;> iassumption

end Splitting

end Lantana
