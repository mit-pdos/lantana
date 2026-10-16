/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.ProgramLogic.OblForest

/-! # Derived rules of the obligation-forest interface

Rocq `lantana/program_logic/obl_forest_rules.v`: the usual rules of the model update
`|={E₁,E₂}=>m P` and its proof-mode instances, derived from the three core rules of the
interface (`mupd_ne`, `fupd_mupd`, `mupd_bind`); the rules of obligation invariants, witness
induction, parents, fuel and credits; the model updates and the physical steps in their usual
shapes. Everything here is derived from the statements of `Lantana.ProgramLogic.OblForest`.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode Iris.Std
open scoped Lantana.Measure Ordinals.Ordinal

/-! ## The model update -/

section Modality

variable {Expr : Type} {State : Type} {GF : BundledGFunctors} [ModelGS GF]
  [TemporalGS Expr State GF] [StateInterp Expr State GF] [TemporalInterp Expr State GF]
variable {E E₁ E₂ E₃ E₄ : CoPset} {P Q R : IProp GF}

/-- `mupd_bind` with the wand applied. -/
theorem mupd_bind' : (P -∗ |={E₂,E₃}=>m Q) ∗ (|={E₁,E₂}=>m P) ⊢ |={E₁,E₃}=>m Q :=
  (sep_mono_left (mupd_bind E₁ E₂ E₃ P Q)).trans wand_elim_left

@[lantana_alias sfmupd_intro]
theorem mupd_intro : P ⊢ |={E}=>m P :=
  fupd_intro.trans (fupd_mupd E E P)

@[lantana_alias sfmupd_mono]
theorem mupd_mono (h : P ⊢ Q) : (|={E₁,E₂}=>m P) ⊢ |={E₁,E₂}=>m Q :=
  emp_sep.2.trans <| (sep_mono_left (wand_intro (emp_sep.1.trans (h.trans mupd_intro)))).trans
    mupd_bind'

@[lantana_alias sfmupd_trans]
theorem mupd_trans : (|={E₁,E₃}=>m |={E₃,E₂}=>m P) ⊢ |={E₁,E₂}=>m P :=
  emp_sep.2.trans <| (sep_mono_left (wand_intro emp_sep.1)).trans mupd_bind'

@[lantana_alias sfmupd_frame_r]
theorem mupd_frame_r : (|={E₁,E₂}=>m P) ∗ R ⊢ |={E₁,E₂}=>m (P ∗ R) :=
  sep_comm.1.trans <| (sep_mono_left (wand_intro (sep_comm.1.trans mupd_intro))).trans mupd_bind'

@[lantana_alias sfmupd_frame_l]
theorem mupd_frame_l : R ∗ (|={E₁,E₂}=>m Q) ⊢ |={E₁,E₂}=>m (R ∗ Q) :=
  sep_comm.1.trans <| mupd_frame_r.trans (mupd_mono sep_comm.1)

@[lantana_alias fupd_sfmupd_elim]
theorem fupd_mupd_elim : (|={E₁}=> |={E₁,E₂}=>m P) ⊢ |={E₁,E₂}=>m P :=
  (fupd_mupd E₁ E₁ _).trans mupd_trans

@[lantana_alias fupd_sfmupd_elim_2]
theorem fupd_mupd_elim_2 : (|={E₁,E₂}=>m |={E₂}=> P) ⊢ |={E₁,E₂}=>m P :=
  emp_sep.2.trans <| (sep_mono_left (wand_intro (emp_sep.1.trans (fupd_mupd E₂ E₂ P)))).trans
    mupd_bind'

@[lantana_alias sfmupd_fupd_l]
theorem mupd_fupd_l : (|={E₁,E₂}=> |={E₂}=>m P) ⊢ |={E₁,E₂}=>m P :=
  (fupd_mupd E₁ E₂ _).trans mupd_trans

@[lantana_alias sfmupd_fupd_r]
theorem mupd_fupd_r : (|={E₁}=>m |={E₁,E₂}=> P) ⊢ |={E₁,E₂}=>m P :=
  (mupd_mono (fupd_mupd E₁ E₂ P)).trans mupd_trans

@[lantana_alias sfmupd_mask_mono]
theorem mupd_mask_mono (h : E₁ ⊆ E₂) : (|={E₁}=>m P) ⊢ |={E₂}=>m P := by
  refine (sep_emp.2.trans (sep_mono_right ((fupd_mask_subseteq (PROP := IProp GF) h).trans
    (fupd_mupd E₂ E₁ _)))).trans ?_
  refine (sep_mono_left (wand_intro ?_)).trans mupd_bind'
  refine (sep_comm.1.trans (sep_mono_left (wand_intro ?_))).trans mupd_bind'
  exact fupd_frame_right.trans <| (fupd_mono emp_sep.1).trans (fupd_mupd E₁ E₂ P)

@[lantana_alias sfmupd_wand_l]
theorem mupd_wand_l : (P -∗ Q) ∗ (|={E₁,E₂}=>m P) ⊢ |={E₁,E₂}=>m Q :=
  mupd_frame_l.trans (mupd_mono wand_elim_left)

@[lantana_alias sfmupd_wand_r]
theorem mupd_wand_r : (|={E₁,E₂}=>m P) ∗ (P -∗ Q) ⊢ |={E₁,E₂}=>m Q :=
  mupd_frame_r.trans (mupd_mono wand_elim_right)

@[lantana_alias sfmupd_sep]
theorem mupd_sep : (|={E}=>m P) ∗ (|={E}=>m Q) ⊢ |={E}=>m (P ∗ Q) :=
  mupd_frame_r.trans <| (mupd_mono mupd_frame_l).trans mupd_trans

@[lantana_alias sfmupd_idemp]
theorem mupd_idemp : (|={E}=>m |={E}=>m P) ⊣⊢ |={E}=>m P :=
  ⟨mupd_trans, mupd_intro⟩

#lantana_ignore sfmupd_ent_proper "Use `mupd_mono`."
#lantana_ignore sfmupd_flip_ent_proper "Use `mupd_mono`."
#lantana_ignore sfmupd_proper "`⊣⊢` is equality: use `mupd_ne` or rewriting."

@[lantana_alias sfmupd_homomorphism]
instance mupd_sep_homomorphism (E : CoPset) :
    Algebra.MonoidHomomorphism (M₁ := IProp GF) BIBase.sep BIBase.sep BIBase.emp BIBase.emp
      (flip Entails) (mupd (Expr := Expr) (State := State) E E) where
  rel_refl := .rfl
  rel_trans := flip .trans
  op_proper := sep_mono
  map_ne := mupd_ne E E
  map_op := mupd_sep
  map_unit := mupd_intro

/-! ### Big separating conjunctions -/

@[lantana_alias big_sepL_sfmupd]
theorem bigSepL_mupd {A : Type _} (Φ : Nat → A → IProp GF) (E : CoPset) (l : List A) :
    ([∗list] k ↦ x ∈ l, |={E}=>m Φ k x) ⊢ |={E}=>m ([∗list] k ↦ x ∈ l, Φ k x) :=
  Algebra.BigOpL.bigOpL_hom (R := flip Entails)
    (H := mupd_sep_homomorphism (Expr := Expr) (State := State) E) Φ l

@[lantana_alias big_sepM_sfmupd]
theorem bigSepM_mupd {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K]
    (Φ : K → V → IProp GF) (E : CoPset) (m : M V) :
    ([∗map] k ↦ x ∈ m, |={E}=>m Φ k x) ⊢ |={E}=>m ([∗map] k ↦ x ∈ m, Φ k x) :=
  Algebra.BigOpM.bigOpM_hom (R := flip Entails)
    (ι := mupd_sep_homomorphism (Expr := Expr) (State := State) E) Φ m

@[lantana_alias big_sepS_sfmupd]
theorem bigSepS_mupd {A S : Type _} [LawfulFiniteSet S A] (Φ : A → IProp GF) (E : CoPset)
    (X : S) :
    ([∗set] x ∈ X, |={E}=>m Φ x) ⊢ |={E}=>m ([∗set] x ∈ X, Φ x) :=
  Algebra.BigOpS.hom (R := flip Entails)
    (mupd_sep_homomorphism (Expr := Expr) (State := State) E) Φ X

@[lantana_alias big_sepMS_sfmupd]
theorem bigSepMS_mupd {A MS : Type _} [LawfulFiniteMultiSet MS A] (Φ : A → IProp GF)
    (E : CoPset) (X : MS) :
    ([∗mset] x ∈ X, |={E}=>m Φ x) ⊢ |={E}=>m ([∗mset] x ∈ X, Φ x) :=
  Algebra.BigOpMS.hom (R := flip Entails)
    (mupd_sep_homomorphism (Expr := Expr) (State := State) E) Φ X

/-! ### Except-0 and fancy updates around the model update -/

@[lantana_alias except_0_sfmupd]
theorem except0_mupd : ◇ (|={E₁,E₂}=>m P) ⊢ |={E₁,E₂}=>m ◇ P :=
  or_elim ((or_intro_l (Q := iprop(|={E₁,E₂}=> ◇ P))).trans
      (BIFUpdate.except0.trans (fupd_mupd E₁ E₂ _)))
    (mupd_mono except0_intro)

@[lantana_alias sfmupd_fupd_acc_gen]
theorem mupd_fupd_acc_gen : (|={E₁,E₂}=> |={E₂,E₃}=>m |={E₃,E₄}=> P) ⊢ |={E₁,E₄}=>m P :=
  (fupd_mono ((mupd_mono (fupd_mupd E₃ E₄ P)).trans mupd_trans)).trans <|
    (fupd_mupd E₁ E₂ _).trans mupd_trans

@[lantana_alias sfmupd_fupd_acc]
theorem mupd_fupd_acc : (|={E₁,E₂}=> |={E₂}=>m |={E₂,E₁}=> P) ⊢ |={E₁}=>m P :=
  mupd_fupd_acc_gen

/-! ### Proof-mode instances -/

@[lantana_alias elim_bupd_sfmupd]
instance elimModal_bupd_mupd (p : Bool) {io} (E₁ E₂ : CoPset) (P Q : IProp GF) :
    ElimModal True p io false iprop(|==> P) P (|={E₁,E₂}=>m Q) (|={E₁,E₂}=>m Q) where
  elim_modal _ := (sep_mono_left (intuitionisticallyIf_elim.trans
    (BIUpdateFUpdate.fupd_of_bupd (E := E₁)))).trans <| fupd_wand_right.trans fupd_mupd_elim

@[lantana_alias elim_fupd_sfmupd]
instance elimModal_fupd_mupd (p : Bool) {io} (E₁ E₂ E₃ : CoPset) (P Q : IProp GF) :
    ElimModal True p io false iprop(|={E₁,E₂}=> P) P (|={E₁,E₃}=>m Q) (|={E₂,E₃}=>m Q) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    fupd_wand_right.trans <| (fupd_mupd E₁ E₂ _).trans mupd_trans

@[lantana_alias elim_modal_sfmupd]
instance elimModal_mupd (p : Bool) {io} (E₁ E₂ E₃ : CoPset) (P Q : IProp GF) :
    ElimModal True p io false (|={E₁,E₂}=>m P) P (|={E₁,E₃}=>m Q) (|={E₂,E₃}=>m Q) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <| mupd_wand_r.trans mupd_trans

@[lantana_alias add_modal_fupd_sfmupd]
instance addModal_fupd_mupd (E₁ E₂ : CoPset) (P Q : IProp GF) :
    AddModal iprop(|={E₁}=> P) P (|={E₁,E₂}=>m Q) where
  add_modal := (sep_mono_left (fupd_mupd E₁ E₁ P)).trans (sep_comm.1.trans mupd_bind')

@[lantana_alias add_modal_sfmupd]
instance addModal_mupd (E₁ E₂ : CoPset) (P Q : IProp GF) :
    AddModal (|={E₁}=>m P) P (|={E₁,E₂}=>m Q) where
  add_modal := sep_comm.1.trans mupd_bind'

@[lantana_alias from_assumption_sfmupd]
instance fromAssumption_mupd (E : CoPset) (p : Bool) {ioP} (P Q : IProp GF)
    [h : FromAssumption p ioP P iprop(|={E}=> Q)] : FromAssumption p ioP P (|={E}=>m Q) where
  from_assumption := h.from_assumption.trans (fupd_mupd E E Q)

@[lantana_alias from_pure_sfmupd]
instance fromPure_mupd (E : CoPset) (a : Bool) {io} (P : IProp GF) (φ : Prop)
    [h : FromPure a P io φ] : FromPure a (|={E}=>m P) io φ where
  from_pure := h.from_pure.trans mupd_intro

@[lantana_alias into_wand_sfmupd]
instance intoWand_mupd (E : CoPset) (p q : Bool) {m} (R P Q : IProp GF)
    [h : IntoWand false false R m P Q] :
    IntoWand p q (|={E}=>m R) m (|={E}=>m P) (|={E}=>m Q) where
  into_wand := intuitionisticallyIf_elim.trans <| wand_intro <|
    (sep_mono (mupd_mono h.into_wand) intuitionisticallyIf_elim).trans <|
      mupd_sep.trans (mupd_mono wand_elim_left)

@[lantana_alias into_wand_sfmupd_persistent]
instance intoWand_mupd_persistent (E₁ E₂ : CoPset) (p q : Bool) {m} (R P Q : IProp GF)
    [h : IntoWand false q R m P Q] :
    IntoWand p q (|={E₁,E₂}=>m R) m P (|={E₁,E₂}=>m Q) where
  into_wand := intuitionisticallyIf_elim.trans <| wand_intro <|
    (sep_mono_left (mupd_mono h.into_wand)).trans <| mupd_frame_r.trans (mupd_mono wand_elim_left)

-- The masks are not determined by the argument and result slots (as for `intoWand_fupd_args`).
set_option synthInstance.checkSynthOrder false in
@[lantana_alias into_wand_sfmupd_args]
instance (priority := low) intoWand_mupd_args (E₁ E₂ : CoPset) (p q : Bool) (s : WandMode.Side)
    (R P Q : IProp GF) [h : IntoWand p false R (.matching s) P Q] :
    IntoWand p q R (.matching s) (|={E₁,E₂}=>m P) (|={E₁,E₂}=>m Q) where
  into_wand := wand_intro_left <|
    (sep_mono intuitionisticallyIf_elim h.into_wand).trans mupd_wand_r

@[lantana_alias from_sep_sfmupd]
instance fromSep_mupd (E : CoPset) (P Q₁ Q₂ : IProp GF) [h : FromSep P Q₁ Q₂] :
    FromSep (|={E}=>m P) (|={E}=>m Q₁) (|={E}=>m Q₂) where
  from_sep := mupd_sep.trans (mupd_mono h.from_sep)

@[lantana_alias from_or_sfmupd]
instance fromOr_mupd (E₁ E₂ : CoPset) (P Q₁ Q₂ : IProp GF) [h : FromOr P Q₁ Q₂] :
    FromOr (|={E₁,E₂}=>m P) (|={E₁,E₂}=>m Q₁) (|={E₁,E₂}=>m Q₂) where
  from_or := or_elim (mupd_mono (or_intro_l.trans h.from_or))
    (mupd_mono (or_intro_r.trans h.from_or))

@[lantana_alias from_exist_sfmupd]
instance fromExists_mupd (E₁ E₂ : CoPset) {α : Sort _} (P : IProp GF) (Φ : α → IProp GF)
    [h : FromExists P Φ] : FromExists (|={E₁,E₂}=>m P) (fun a => |={E₁,E₂}=>m Φ a) where
  from_exists := exists_elim fun a => mupd_mono ((exists_intro a).trans h.from_exists)

@[lantana_alias is_except_0_sfmupd]
instance isExcept0_mupd (E₁ E₂ : CoPset) (P : IProp GF) [h : IsExcept0 P] :
    IsExcept0 (|={E₁,E₂}=>m P) where
  is_except0 := except0_mupd.trans (mupd_mono h.is_except0)

@[lantana_alias from_modal_sfmupd]
instance fromModal_mupd (E : CoPset) {io} (P : IProp GF) :
    FromModal io modality_id True (|={E}=>m P) (|={E}=>m P) P where
  from_modal _ := mupd_intro

instance (priority := low) fromModal_mupd_wrongMask (E₁ E₂ : CoPset) {io} (P : IProp GF) :
    FromModal io modality_id
      (PMError "Only non-mask-changing model updates can be introduced directly.
        Use `mupd_mask_mono` or a mask-changing fancy update to change the mask.")
      (|={E₁,E₂}=>m P) (|={E₁,E₂}=>m P) P where
  from_modal h := by cases h

@[ipm_backtrack, lantana_alias frame_sfmupd]
instance frame_mupd (p : Bool) (E₁ E₂ : CoPset) (R P Q : IProp GF) [h : Frame p R P Q] :
    Frame p R (|={E₁,E₂}=>m P) (|={E₁,E₂}=>m Q) where
  frame := mupd_frame_l.trans (mupd_mono h.frame)

/-! ### Later credits -/

@[lantana_alias lc_sfmupd_add_later]
theorem lc_mupd_add_later : ⊢ £ₙ 1 -∗ ▷ (|={E₁,E₂}=>m P) -∗ |={E₁,E₂}=>m P :=
  wand_intro <| wand_intro <| (sep_mono_left (emp_sep.1.trans (wand_entails lc_fupd_elim_later))).trans
    (wand_elim_left.trans fupd_mupd_elim)

/-- `lc_mupd_add_later` with a transfinite credit. -/
theorem lc_mupd_add_later_ord :
    ⊢ £ₒ (1 : Ordinals.Ordinal.{1}) -∗ ▷ (|={E₁,E₂}=>m P) -∗ |={E₁,E₂}=>m P :=
  lc_mupd_add_later

@[lantana_alias lc_sfmupd_add_laterN]
theorem lc_mupd_add_laterN (n : Nat) : ⊢ £ₙ n -∗ ▷^[n] (|={E₁,E₂}=>m P) -∗ |={E₁,E₂}=>m P := by
  iintro Hc HP
  iapply fupd_mupd_elim
  iapply lc_fupd_add_laterN (E₁ := E₁) (E₂ := E₁) n $$ Hc
  iapply laterN_mono n fupd_intro $$ HP

end Modality

/-! ## Obligation predicates and invariants -/

section Preds

variable {GF : BundledGFunctors} [ModelGS GF]

@[lantana_alias oblP_assigned_as_fractional]
instance Obl.assigned_asFractional (k : Oid) (q : Qp) {ioΦ ioq} :
    AsFractional (Obl.assigned (GF := GF) k q) ioΦ (Obl.assigned k) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := Obl.assigned_fractional k

omit [ModelGS GF] in
/-- The assignment of `k` splits in two halves. -/
theorem Obl.assigned_halves (k : Oid) :
    Obl.assigned (GF := GF) k 1 ⊣⊢ Obl.assigned k (Qp.half 1) ∗ Obl.assigned k (Qp.half 1) := by
  have h := (Obl.assigned_fractional (GF := GF) k).fractional (Qp.half 1) (Qp.half 1)
  rwa [Qp.half_add_half] at h

#lantana_ignore oblP_inv_ne_1 "Derived from `Obl.inv_contractive_left` (`OFE.ne_of_contractive`)."
#lantana_ignore oblP_inv_ne_2 "Derived from `Obl.inv_contractive_right` (`OFE.ne_of_contractive`)."
#lantana_ignore oblP_inv_proper_1 "`⊣⊢` is equality: rewrite."
#lantana_ignore oblP_inv_proper_2 "`⊣⊢` is equality: rewrite."

@[lantana_alias oblP_variant_timeless]
instance Obl.variant_timeless (k : Oid) (P R : IProp GF) [Timeless P] [Timeless R] :
    Timeless (Obl.variant k P R) := by
  unfold Obl.variant; infer_instance

omit [ModelGS GF] in
@[lantana_alias oblP_variant_unfold]
theorem Obl.variant_unfold (k : Oid) (P R : IProp GF) :
    Obl.variant k P R ⊣⊢ (Obl.assigned k (Qp.half 1) ∗ P) ∨ (Obl.discharged k ∗ R) :=
  .rfl

variable (E : CoPset) (N : Namespace) (k : Oid) (P R : IProp GF)

@[lantana_alias oblP_inv_acc_cases]
theorem Obl.inv_acc_cases (hN : ↑N ⊆ E) :
    Obl.inv N k P R ⊢ |={E, E \ ↑N}=> ▷ Obl.variant k P R ∗
      (▷ Obl.variant k P R ={E \ ↑N, E}=∗ True) :=
  Obl.inv_acc E N k P R hN

@[lantana_alias oblP_inv_acc_assigned]
theorem Obl.inv_acc_assigned (hN : ↑N ⊆ E) :
    Obl.inv N k P R ⊢ |={E, E \ ↑N}=> ∀ q, Obl.assigned k q -∗
      ▷ (Obl.assigned k q ∗ Obl.assigned k (Qp.half 1) ∗ P) ∗
      (▷ Obl.variant k P R ={E \ ↑N, E}=∗ True) := by
  iintro I
  imod Obl.inv_acc E N k P R hN $$ I with ⟨V, Hclose⟩
  imodintro
  iintro %q A
  iframe Hclose
  inext
  icases (Obl.variant_unfold k P R).1 $$ V with (⟨A', HP⟩ | ⟨D, -⟩)
  · iframe
  · iexfalso
    iapply Obl.assigned_discharged_false k q $$ A D

@[lantana_alias oblP_inv_acc_discharged]
theorem Obl.inv_acc_discharged (hN : ↑N ⊆ E) :
    Obl.inv N k P R ⊢ |={E, E \ ↑N}=> Obl.discharged k -∗
      ▷ R ∗ (▷ Obl.variant k P R ={E \ ↑N, E}=∗ True) := by
  iintro I
  imod Obl.inv_acc E N k P R hN $$ I with ⟨V, Hclose⟩
  imodintro
  iintro #D
  iframe Hclose
  inext
  icases (Obl.variant_unfold k P R).1 $$ V with (⟨A, -⟩ | ⟨-, HR⟩)
  · iexfalso
    iapply Obl.assigned_discharged_false k _ $$ A D
  · iexact HR

@[lantana_alias oblP_inv_acc_discharged_persistent]
theorem Obl.inv_acc_discharged_persistent [Persistent R] (hN : ↑N ⊆ E) :
    Obl.inv N k P R ⊢ Obl.discharged k ={E}[E \ ↑N]▷=∗ R := by
  iintro #I #D
  imod Obl.inv_acc_discharged E N k P R hN $$ I with H
  icases H $$ D with ⟨HR, Hclose⟩
  imodintro
  inext
  icases HR with #HR
  imod Hclose $$ [] with -
  · inext
    iapply (Obl.variant_unfold k P R).2
    iright
    iframe D HR
  imodintro
  iexact HR

end Preds

/-! ## Parents -/

section Parents

variable {GF : BundledGFunctors}

@[lantana_alias parent_below_persistent]
instance parBelow_persistent (p : Parent) (ℓ : Layer) : Persistent (parBelow (GF := GF) p ℓ) := by
  cases p <;> unfold parBelow <;> infer_instance

@[lantana_alias parent_le_persistent]
instance parLe_persistent (p : Parent) (ℓ : Layer) : Persistent (parLe (GF := GF) p ℓ) := by
  cases p <;> unfold parLe <;> infer_instance

@[lantana_alias parP_below_thread]
theorem parBelow_thread (i : ThreadId) (ℓ : Layer) : ⊢ parBelow (GF := GF) (.thread i) ℓ :=
  true_intro

@[lantana_alias parP_below_obl]
theorem parBelow_obl (q : Oid) {ℓq ℓ : Layer} (h : ℓq < ℓ) :
    Wit.layer (GF := GF) q ℓq ⊢ parBelow (.obl q) ℓ := by
  simp only [parBelow]
  iintro W
  iexists ℓq
  iframe W
  ipureintro
  exact h

@[lantana_alias parP_le_thread]
theorem parLe_thread (i : ThreadId) (ℓ : Layer) : ⊢ parLe (GF := GF) (.thread i) ℓ :=
  true_intro

@[lantana_alias parP_le_obl]
theorem parLe_obl (q : Oid) {ℓq ℓ : Layer} (h : ℓq ≤ ℓ) :
    Wit.layer (GF := GF) q ℓq ⊢ parLe (.obl q) ℓ := by
  simp only [parLe]
  iintro W
  iexists ℓq
  iframe W
  ipureintro
  exact h

@[lantana_alias parP_below_le]
theorem parBelow_le (p : Parent) (ℓ : Layer) : parBelow (GF := GF) p ℓ ⊢ parLe p ℓ := by
  cases p with
  | thread i => exact .rfl
  | obl q =>
    simp only [parBelow, parLe]
    iintro ⟨%ℓq, %h, W⟩
    iexists ℓq
    iframe W
    ipureintro
    exact Ordinals.Ordinal.le_of_lt h

end Parents

end Lantana
