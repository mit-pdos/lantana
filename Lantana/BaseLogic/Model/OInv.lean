/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.BaseLogic.Invariants
public import Lantana.BaseLogic.Model.OSat

/-! # Invariants over the state of an obligation

Rocq `lantana/base_logic/oinv.v`: an Iris invariant whose content depends on the state of an
obligation `k`: `P` while `k` is assigned, `R` once it is discharged. The invariant holds a
fraction `q` of the assignment, so that opening it with any other fraction pins the assigned
state, and opening it with `OSat.discharged k` pins the discharged one. (Rocq's boolean flag
and its third branch `Q` are dropped, D10: `opreds.v` instantiates `Q := False`.)
-/

@[expose] public noncomputable section

namespace Lantana.Model

open Iris Iris.BI Iris.ProofMode

variable {GF : BundledGFunctors} [OSatGS GF] [InvGS GF]

namespace OSat

/-- The content of an obligation invariant (Rocq `oblG_variant`). -/
@[lantana_alias oblG_variant]
def variant (k : Oid) (q : Qp) (P R : IProp GF) : IProp GF :=
  iprop((assigned k q ∗ P) ∨ (discharged k ∗ R))

/-- The invariant over the state of obligation `k` (Rocq `oblG_inv`). -/
@[lantana_alias oblG_inv]
def oinv (N : Namespace) (k : Oid) (q : Qp) (P R : IProp GF) : IProp GF :=
  Lantana.inv N (variant k q P R)

omit [InvGS GF] in
theorem variant_unfold (k : Oid) (q : Qp) (P R : IProp GF) :
    variant k q P R ⊣⊢ (assigned k q ∗ P) ∨ (discharged k ∗ R) := .rfl

omit [InvGS GF] in
instance variant_timeless (k : Oid) (q : Qp) (P R : IProp GF) [Timeless P] [Timeless R] :
    Timeless (variant (GF := GF) k q P R) := by
  unfold variant; infer_instance

@[lantana_alias oblG_inv_persistent]
instance oinv_persistent (N : Namespace) (k : Oid) (q : Qp) (P R : IProp GF) :
    Persistent (oinv (GF := GF) N k q P R) := by
  unfold oinv; infer_instance

@[lantana_alias oblG_inv_contractive_1]
instance oinv_contractive_left (N : Namespace) (k : Oid) (q : Qp) (R : IProp GF) :
    OFE.Contractive (fun P => oinv (GF := GF) N k q P R) where
  distLater_dist h :=
    OFE.Contractive.distLater_dist (f := Lantana.inv N) fun m hm =>
      or_ne.ne (sep_ne.ne .rfl (h m hm)) .rfl

@[lantana_alias oblG_inv_contractive_3]
instance oinv_contractive_right (N : Namespace) (k : Oid) (q : Qp) (P : IProp GF) :
    OFE.Contractive (fun R => oinv (GF := GF) N k q P R) where
  distLater_dist h :=
    OFE.Contractive.distLater_dist (f := Lantana.inv N) fun m hm =>
      or_ne.ne .rfl (sep_ne.ne .rfl (h m hm))

#lantana_ignore oblG_inv_contractive_2 "no boolean flag: the branch `Q` is dropped (D10)"

section Rules

variable (E : CoPset) (N : Namespace) (k : Oid) (q : Qp) (P R : IProp GF)

@[lantana_alias oblG_inv_acc]
theorem oinv_acc (hN : ↑N ⊆ E) :
    oinv N k q P R ⊢@{IProp GF}
      |={E, E \ ↑N}=> ▷ variant k q P R ∗ (▷ variant k q P R ={E \ ↑N, E}=∗ True) := by
  unfold oinv
  iintro #I
  iapply inv_acc hN $$ I

/-- Opening with any fraction of the assignment pins the assigned branch. -/
@[lantana_alias oblG_inv_acc_assigned]
theorem oinv_acc_assigned (hN : ↑N ⊆ E) :
    oinv N k q P R ⊢@{IProp GF} |={E, E \ ↑N}=> ∀ q', assigned k q' -∗
      ▷ (assigned k q' ∗ assigned k q ∗ P) ∗ (▷ variant k q P R ={E \ ↑N, E}=∗ True) := by
  iintro I
  imod oinv_acc E N k q P R hN $$ I with ⟨V, Hclose⟩
  imodintro
  iintro %q' A
  iframe Hclose
  inext
  icases (variant_unfold k q P R).1 $$ V with (⟨A', HP⟩ | ⟨D, -⟩)
  · iframe
  · iexfalso
    iapply assigned_discharged_false k q' $$ [$A $D]

/-- Opening with the discharge pins the discharged branch. -/
@[lantana_alias oblG_inv_acc_discharged]
theorem oinv_acc_discharged (hN : ↑N ⊆ E) :
    oinv N k q P R ⊢@{IProp GF} |={E, E \ ↑N}=> discharged k -∗
      ▷ R ∗ (▷ variant k q P R ={E \ ↑N, E}=∗ True) := by
  iintro I
  imod oinv_acc E N k q P R hN $$ I with ⟨V, Hclose⟩
  imodintro
  iintro #D
  iframe Hclose
  inext
  icases (variant_unfold k q P R).1 $$ V with (⟨A, -⟩ | ⟨-, HR⟩)
  · iexfalso
    iapply assigned_discharged_false k q $$ [$A $D]
  · iexact HR

/-- A persistent `R` can be read out of a discharged invariant across a step. -/
@[lantana_alias oblG_inv_acc_discharged_persistent]
theorem oinv_acc_discharged_persistent [Persistent R] (hN : ↑N ⊆ E) :
    oinv N k q P R ⊢@{IProp GF} discharged k ={E}[E \ ↑N]▷=∗ R := by
  iintro #I #D
  imod oinv_acc_discharged E N k q P R hN $$ I with H
  icases H $$ D with ⟨HR, Hclose⟩
  imodintro
  inext
  icases HR with #HR
  imod Hclose $$ [] with -
  · inext
    iapply (variant_unfold k q P R).2
    iright
    isplitl []
    · iexact D
    · iexact HR
  · imodintro
    iexact HR

@[lantana_alias oblG_inv_alloc_assigned_false]
theorem oinv_alloc_assigned :
    ▷ (assigned k q ∗ P) ⊢@{IProp GF} |={E}=> oinv N k q P R := by
  unfold oinv
  iintro H
  iapply inv_alloc N E
  inext
  iapply (variant_unfold k q P R).2
  ileft
  iexact H

@[lantana_alias oblG_inv_alloc_discharged]
theorem oinv_alloc_discharged :
    ▷ (discharged k ∗ R) ⊢@{IProp GF} |={E}=> oinv N k q P R := by
  unfold oinv
  iintro H
  iapply inv_alloc N E
  inext
  iapply (variant_unfold k q P R).2
  iright
  iexact H

#lantana_ignore oblG_inv_alloc_assigned_true "no boolean flag: the branch `Q` is dropped (D10)"

end Rules

end OSat

end Lantana.Model
