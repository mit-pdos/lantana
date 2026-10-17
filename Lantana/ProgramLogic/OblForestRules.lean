/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.ProgramLogic.OblForest

/-! # Derived rules of the obligation-forest interface

Rocq `lantana/program_logic/obl_forest_rules.v`: the usual rules of the model update
`|={E₁,E₂}=>m P` and its proof-mode instances, derived from the three core rules of the
interface (`mupd_ne`, `fupd_mupd`, `mupd_bind`); the rules of obligation invariants, witness
induction, parents, fuel and credits; the model updates and the physical steps in their usual
shapes. Everything here is derived from the statements of `Lantana.ProgramLogic.OblForest`.
This file also holds the rules of the base model update `|=[n,tc]=>m P` that the program logic
uses (Rocq `base_logic/mupd.v`).

Porting notes:
* The union of `OidMap = Std.ExtTreeMap` takes the values of its *right* argument, so Rocq's
  `G ∪ F` (left-biased `gmap` union) is `F ∪ G` here (`Wit.fuels_add_map_gen`,
  `embedFuels_add_map`).
* Rocq's `{[k]} ∪ K` and `K ∖ {[k]}` are `K.insert k` and `K.erase k` (as in the interface);
  sets of children moved at once use `∪` and `\`.
* The model update absorbs `◇` unconditionally (`isExcept0_mupd`), as the fancy update does.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode Iris.Std
open scoped Lantana.Measure Ordinals.Ordinal

/-! ## Sets of obligations -/

/-- `Std.ExtTreeSet.erase` as a set difference. -/
theorem Oids.erase_eq_diff (K : Oids) (k : Oid) : K.erase k = K \ {k} :=
  LawfulSet.ext fun x => by
    rw [Std.ExtTreeSet.mem_erase, mem_diff, mem_singleton, Ne,
      Std.LawfulEqCmp.compare_eq_iff_eq]
    grind

/-! ## The base model update

The rules of `|=[n,tc]=>m P` (Rocq `base_logic/mupd.v`) used by the program logic, derived from
the structural rules of the interface. -/

section Base

variable {GF : BundledGFunctors} [ModelGS GF] {n tc : Nat} {P Q R : IProp GF}

@[lantana_alias mupd_wand_l]
theorem mupdBase_wand : (P -∗ Q) ⊢ (|=[n,tc]=>m P) -∗ |=[n,tc]=>m Q :=
  (wand_mono_right (mupdBase_intro n tc Q)).trans (mupdBase_bind n tc P Q)

@[lantana_alias mupd_mono]
theorem mupdBase_mono (h : P ⊢ Q) : (|=[n,tc]=>m P) ⊢ |=[n,tc]=>m Q :=
  wand_entails ((entails_wand h).trans mupdBase_wand)

@[lantana_alias mupd_trans]
theorem mupdBase_trans : (|=[n,tc]=>m |=[n,tc]=>m P) ⊢ |=[n,tc]=>m P :=
  wand_entails (wand_rfl.trans (mupdBase_bind n tc _ P))

@[lantana_alias mupd_frame_r]
theorem mupdBase_frame_right : (|=[n,tc]=>m P) ∗ R ⊢ |=[n,tc]=>m (P ∗ R) := by
  iintro ⟨HP, HR⟩
  iapply mupdBase_wand $$ [HR] HP
  iintro HP
  isplitl [HP]
  · iexact HP
  · iexact HR

@[lantana_alias fupd_mupd]
theorem fupd_mupdBase : (|={∅}=> P) ⊢ |=[n,tc]=>m P :=
  (fupd_mono (mupdBase_intro n tc P)).trans (fupd_mupdBase_elim n tc P)

instance fromModal_mupdBase {io} : FromModal io modality_id True (|=[n,tc]=>m P)
    (|=[n,tc]=>m P) P where
  from_modal _ := mupdBase_intro n tc P

instance elimModal_mupdBase {p io} :
    ElimModal True p io false (|=[n,tc]=>m P) P (|=[n,tc]=>m Q) (|=[n,tc]=>m Q) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    sep_comm.mp.trans <| wand_elim_left_trans (mupdBase_bind n tc P Q)

instance elimModal_fupd_mupdBase {p io} :
    ElimModal True p io false iprop(|={∅}=> P) P (|=[n,tc]=>m Q) (|=[n,tc]=>m Q) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    fupd_frame_right.trans <| (fupd_mono wand_elim_right).trans (fupd_mupdBase_elim n tc Q)

end Base

/-! ## The model update -/

section Modality

variable {Expr : Type} {State : Type} {GF : BundledGFunctors} [ModelGS GF]
  [TemporalGS Expr State GF] [StateInterp Expr State GF] [TemporalInterp Expr State GF]
variable {E E₁ E₂ E₃ E₄ : CoPset} {P Q R : IProp GF}

/-- `mupd_bind` with the wand applied. -/
theorem mupd_bind' : (P -∗ |={E₂,E₃}=>m Q) ∗ (|={E₁,E₂}=>m P) ⊢ |={E₁,E₃}=>m Q :=
  (sep_mono_left (mupd_bind E₁ E₂ E₃ P Q)).trans wand_elim_left

@[lantana_alias sfmupd_wand_l]
theorem mupd_wand : (P -∗ Q) ⊢ (|={E₁,E₂}=>m P) -∗ |={E₁,E₂}=>m Q :=
  (wand_mono_right (fupd_intro.trans (fupd_mupd E₂ E₂ Q))).trans (mupd_bind E₁ E₂ E₂ P Q)

@[lantana_alias sfmupd_intro]
theorem mupd_intro : P ⊢ |={E}=>m P :=
  fupd_intro.trans (fupd_mupd E E P)

@[lantana_alias sfmupd_mono]
theorem mupd_mono (h : P ⊢ Q) : (|={E₁,E₂}=>m P) ⊢ |={E₁,E₂}=>m Q :=
  wand_entails ((entails_wand h).trans mupd_wand)

@[lantana_alias sfmupd_trans]
theorem mupd_trans : (|={E₁,E₂}=>m |={E₂,E₃}=>m P) ⊢ |={E₁,E₃}=>m P :=
  wand_entails (wand_rfl.trans (mupd_bind E₁ E₂ E₃ _ P))

@[lantana_alias sfmupd_frame_r]
theorem mupd_frame_right : (|={E₁,E₂}=>m P) ∗ R ⊢ |={E₁,E₂}=>m (P ∗ R) :=
  sep_comm.1.trans <| (sep_mono_left (wand_intro (sep_comm.1.trans mupd_intro))).trans mupd_bind'

@[lantana_alias sfmupd_frame_l]
theorem mupd_frame_left : R ∗ (|={E₁,E₂}=>m Q) ⊢ |={E₁,E₂}=>m (R ∗ Q) :=
  sep_comm.1.trans <| mupd_frame_right.trans (mupd_mono sep_comm.1)

@[lantana_alias fupd_sfmupd_elim]
theorem fupd_mupd_elim : (|={E₁}=> |={E₁,E₂}=>m P) ⊢ |={E₁,E₂}=>m P :=
  (fupd_mupd E₁ E₁ _).trans mupd_trans

@[lantana_alias fupd_sfmupd_elim_2]
theorem fupd_mupd_elim_2 : (|={E₁,E₂}=>m |={E₂}=> P) ⊢ |={E₁,E₂}=>m P :=
  (mupd_mono (fupd_mupd E₂ E₂ P)).trans mupd_trans

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

/-- `mupd_wand` with the wand applied (Rocq `sfmupd_wand_l`). -/
theorem mupd_wand_left : (P -∗ Q) ∗ (|={E₁,E₂}=>m P) ⊢ |={E₁,E₂}=>m Q :=
  mupd_frame_left.trans (mupd_mono wand_elim_left)

@[lantana_alias sfmupd_wand_r]
theorem mupd_wand_right : (|={E₁,E₂}=>m P) ∗ (P -∗ Q) ⊢ |={E₁,E₂}=>m Q :=
  mupd_frame_right.trans (mupd_mono wand_elim_right)

@[lantana_alias sfmupd_sep]
theorem mupd_sep : (|={E}=>m P) ∗ (|={E}=>m Q) ⊢ |={E}=>m (P ∗ Q) :=
  mupd_frame_right.trans <| (mupd_mono mupd_frame_left).trans mupd_trans

@[lantana_alias sfmupd_idemp]
theorem mupd_idemp : (|={E}=>m |={E}=>m P) ⊣⊢ |={E}=>m P :=
  ⟨mupd_trans, mupd_intro⟩

/-- The model update `|={E₁,E₂}=>m P` applied to the history interpretation. -/
theorem mupd_elim {h : List (HistEntry Expr State)} {n : Nat} {σ : State} {tp : ThreadPool Expr}
    (L : Nat) (hL : tp.length = L) :
    (|={E₁,E₂}=>m P) ⊢ historyTInterp h n σ tp -∗
      |={E₁,∅}=> |=[n, L]=>m |={∅,E₂}=> (historyTInterp h n σ tp ∗ P) := by
  subst hL
  unfold mupd mupdFancy
  iintro H Hσ
  iapply H $$ %h %n %σ %tp Hσ

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
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    mupd_wand_right.trans mupd_trans

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
    (sep_mono_left (mupd_mono h.into_wand)).trans <|
      mupd_frame_right.trans (mupd_mono wand_elim_left)

-- The masks are not determined by the argument and result slots (as for `intoWand_fupd_args`).
set_option synthInstance.checkSynthOrder false in
@[lantana_alias into_wand_sfmupd_args]
instance (priority := low) intoWand_mupd_args (E₁ E₂ : CoPset) (p q : Bool) (s : WandMode.Side)
    (R P Q : IProp GF) [h : IntoWand p false R (.matching s) P Q] :
    IntoWand p q R (.matching s) (|={E₁,E₂}=>m P) (|={E₁,E₂}=>m Q) where
  into_wand := wand_intro_left <|
    (sep_mono intuitionisticallyIf_elim h.into_wand).trans mupd_wand_right

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

/-- The model update absorbs `◇` (as the fancy update does; Rocq requires `IsExcept0 P`). -/
@[lantana_alias is_except_0_sfmupd]
instance isExcept0_mupd (E₁ E₂ : CoPset) (P : IProp GF) : IsExcept0 (|={E₁,E₂}=>m P) where
  is_except0 := or_elim ((or_intro_l (Q := iprop(|={E₁,E₂}=> P))).trans
    (BIFUpdate.except0.trans (fupd_mupd E₁ E₂ P))) .rfl

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
  frame := mupd_frame_left.trans (mupd_mono h.frame)

/-! ### Later credits -/

@[lantana_alias lc_sfmupd_add_later]
theorem lc_mupd_add_later : ⊢ £ₙ 1 -∗ ▷ (|={E₁,E₂}=>m P) -∗ |={E₁,E₂}=>m P :=
  wand_intro <| wand_intro <|
    (sep_mono_left (emp_sep.1.trans (wand_entails lc_fupd_elim_later))).trans
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

variable {GF : BundledGFunctors} [ModelGS GF]

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

/-! ## Fuel and credit algebra -/

section Fuel

variable {GF : BundledGFunctors}

open BigSepL BigSepS Ordinals Ordinal LawfulSet

private theorem bigSepL_bupd_of {A : Type _} {Φ Ψ : A → IProp GF} {l : List A}
    (h : ∀ x, Φ x ⊢ |==> Ψ x) : ([∗list] x ∈ l, Φ x) ⊢ |==> [∗list] x ∈ l, Ψ x :=
  (bigSepL_mono_of_forall fun {_ x} => h x).trans (bigSepL_bupd _ _)

private theorem bigSepS_bupd_of {Φ Ψ : Oid → IProp GF} {K : Oids}
    (h : ∀ x, Φ x ⊢ |==> Ψ x) : ([∗set] x ∈ K, Φ x) ⊢ |==> [∗set] x ∈ K, Ψ x :=
  (bigSepS_mono_of_forall h).trans (bigSepS_bupd _ _)

private theorem bigSepL_bupd_sep_of {A : Type _} {Φ Ψ₁ Ψ₂ : A → IProp GF} {l : List A}
    (h : ∀ x, Φ x ⊢ |==> (Ψ₁ x ∗ Ψ₂ x)) :
    ([∗list] x ∈ l, Φ x) ⊢ |==> (([∗list] x ∈ l, Ψ₁ x) ∗ [∗list] x ∈ l, Ψ₂ x) :=
  (bigSepL_bupd_of h).trans (BIUpdate.mono bigSepL_sep_eqv.1)

private theorem bigSepS_bupd_sep_of {Φ Ψ₁ Ψ₂ : Oid → IProp GF} {K : Oids}
    (h : ∀ x, Φ x ⊢ |==> (Ψ₁ x ∗ Ψ₂ x)) :
    ([∗set] x ∈ K, Φ x) ⊢ |==> (([∗set] x ∈ K, Ψ₁ x) ∗ [∗set] x ∈ K, Ψ₂ x) :=
  (bigSepS_bupd_of h).trans (BIUpdate.mono bigSepS_sep.1)

private theorem bigSepL_eqv_of {A : Type _} {Φ Ψ : A → IProp GF} {l : List A}
    (h : ∀ x, Φ x ⊣⊢ Ψ x) : ([∗list] x ∈ l, Φ x) ⊣⊢ [∗list] x ∈ l, Ψ x :=
  ⟨bigSepL_mono_of_forall fun {_ x} => (h x).1, bigSepL_mono_of_forall fun {_ x} => (h x).2⟩

/-- Two big separating conjunctions of affine propositions over sets combine into one over the
union (Rocq `big_sepS_union_2`). -/
private theorem bigSepS_union_2 {Φ : Oid → IProp GF} {X Y : Oids} :
    ([∗set] x ∈ X, Φ x) ∗ ([∗set] x ∈ Y, Φ x) ⊢ [∗set] x ∈ X ∪ Y, Φ x := by
  have hXY : X ∪ Y = X ∪ (Y \ X) := LawfulSet.ext fun x => by
    simp only [mem_union, mem_diff]; grind
  rw [hXY]
  exact (sep_mono_right (bigSepS_subseteq diff_subset_left)).trans
    (bigSepS_union disjoint_diff_right).2

/-! ### Fuel -/

variable [ModelGS GF]

@[lantana_alias oblP_fuel_layer_eq]
theorem Obl.fuel_layer_eq (k : Oid) {ℓ₁ ℓ₂ : Layer} (μ : Measure) (h : ℓ₁ = ℓ₂) :
    Obl.fuel (GF := GF) k ℓ₁ μ ⊣⊢ Obl.fuel k ℓ₂ μ :=
  h ▸ .rfl

#lantana_ignore oblP_fuel_layer_eq_list "Layer equality is Leibniz: rewrite."
#lantana_ignore oblP_fuel_layer_eq_set "Layer equality is Leibniz: rewrite."

/-- Fuels at one layer with equal interpretations are equal (Rocq `oblP_fuel_eq`; the same as
`Obl.fuel_eq`, with the layer explicit). -/
@[lantana_alias oblP_fuel_eq]
theorem Obl.fuel_eq_of_rep (k : Oid) (ℓ : Layer) {μ₁ μ₂ : Measure}
    (h : Measure.rep ℓ μ₁ = Measure.rep ℓ μ₂) : Obl.fuel (GF := GF) k ℓ μ₁ ⊣⊢ Obl.fuel k ℓ μ₂ :=
  Obl.fuel_eq k h

@[lantana_alias oblP_fuel_eq_list]
theorem Obl.fuel_eq_of_rep_list (K : List Oid) (ℓ : Layer) {μ₁ μ₂ : Measure}
    (h : Measure.rep ℓ μ₁ = Measure.rep ℓ μ₂) :
    ([∗list] k ∈ K, Obl.fuel (GF := GF) k ℓ μ₁) ⊣⊢ [∗list] k ∈ K, Obl.fuel k ℓ μ₂ :=
  bigSepL_eqv_of fun k => Obl.fuel_eq_of_rep k ℓ h

@[lantana_alias oblP_fuel_eq_set]
theorem Obl.fuel_eq_of_rep_set (K : Oids) (ℓ : Layer) {μ₁ μ₂ : Measure}
    (h : Measure.rep ℓ μ₁ = Measure.rep ℓ μ₂) :
    ([∗set] k ∈ K, Obl.fuel (GF := GF) k ℓ μ₁) ⊣⊢ [∗set] k ∈ K, Obl.fuel k ℓ μ₂ :=
  bigSepS_eqv fun _ => Obl.fuel_eq_of_rep _ ℓ h

@[lantana_alias oblP_fuel_mon_gen_list]
theorem Obl.fuel_mono_gen_list (K : List Oid) {ℓ₁ ℓ₂ : Layer} {μ₁ μ₂ : Measure} (hℓ : ℓ₁ ≤ ℓ₂)
    (h : Measure.rep ℓ₁ μ₁ ≤ Measure.rep ℓ₂ μ₂) :
    ([∗list] k ∈ K, Obl.fuel (GF := GF) k ℓ₂ μ₂) ⊢ |==> [∗list] k ∈ K, Obl.fuel k ℓ₁ μ₁ :=
  bigSepL_bupd_of fun k => Obl.fuel_mono_gen k hℓ h

@[lantana_alias oblP_fuel_mon_gen_set]
theorem Obl.fuel_mono_gen_set (K : Oids) {ℓ₁ ℓ₂ : Layer} {μ₁ μ₂ : Measure} (hℓ : ℓ₁ ≤ ℓ₂)
    (h : Measure.rep ℓ₁ μ₁ ≤ Measure.rep ℓ₂ μ₂) :
    ([∗set] k ∈ K, Obl.fuel (GF := GF) k ℓ₂ μ₂) ⊢ |==> [∗set] k ∈ K, Obl.fuel k ℓ₁ μ₁ :=
  bigSepS_bupd_of fun k => Obl.fuel_mono_gen k hℓ h

@[lantana_alias oblP_fuel_mon]
theorem Obl.fuel_mono (k : Oid) (ℓ : Layer) {μ₁ μ₂ : Measure}
    (h : Measure.rep ℓ μ₁ ≤ Measure.rep ℓ μ₂) :
    Obl.fuel (GF := GF) k ℓ μ₂ ⊢ |==> Obl.fuel k ℓ μ₁ :=
  Obl.fuel_mono_gen k Ordinal.le_rfl h

@[lantana_alias oblP_fuel_mon_list]
theorem Obl.fuel_mono_list (K : List Oid) (ℓ : Layer) {μ₁ μ₂ : Measure}
    (h : Measure.rep ℓ μ₁ ≤ Measure.rep ℓ μ₂) :
    ([∗list] k ∈ K, Obl.fuel (GF := GF) k ℓ μ₂) ⊢ |==> [∗list] k ∈ K, Obl.fuel k ℓ μ₁ :=
  bigSepL_bupd_of fun k => Obl.fuel_mono k ℓ h

@[lantana_alias oblP_fuel_mon_set]
theorem Obl.fuel_mono_set (K : Oids) (ℓ : Layer) {μ₁ μ₂ : Measure}
    (h : Measure.rep ℓ μ₁ ≤ Measure.rep ℓ μ₂) :
    ([∗set] k ∈ K, Obl.fuel (GF := GF) k ℓ μ₂) ⊢ |==> [∗set] k ∈ K, Obl.fuel k ℓ μ₁ :=
  bigSepS_bupd_of fun k => Obl.fuel_mono k ℓ h

@[lantana_alias oblP_fuel_layer_mon]
theorem Obl.fuel_layer_mono (k : Oid) {ℓ₁ ℓ₂ : Layer} (μ : Measure) (h : ℓ₁ ≤ ℓ₂) :
    Obl.fuel (GF := GF) k ℓ₂ μ ⊢ |==> Obl.fuel k ℓ₁ μ :=
  Obl.fuel_mono_gen k h (Measure.rep_layer_le h μ)

@[lantana_alias oblP_fuel_layer_mon_list]
theorem Obl.fuel_layer_mono_list (K : List Oid) {ℓ₁ ℓ₂ : Layer} (μ : Measure) (h : ℓ₁ ≤ ℓ₂) :
    ([∗list] k ∈ K, Obl.fuel (GF := GF) k ℓ₂ μ) ⊢ |==> [∗list] k ∈ K, Obl.fuel k ℓ₁ μ :=
  bigSepL_bupd_of fun k => Obl.fuel_layer_mono k μ h

@[lantana_alias oblP_fuel_layer_mon_set]
theorem Obl.fuel_layer_mono_set (K : Oids) {ℓ₁ ℓ₂ : Layer} (μ : Measure) (h : ℓ₁ ≤ ℓ₂) :
    ([∗set] k ∈ K, Obl.fuel (GF := GF) k ℓ₂ μ) ⊢ |==> [∗set] k ∈ K, Obl.fuel k ℓ₁ μ :=
  bigSepS_bupd_of fun k => Obl.fuel_layer_mono k μ h

@[lantana_alias oblP_fuel_mon_split]
theorem Obl.fuel_mono_split (k : Oid) (ℓ : Layer) {μ₁ μ₂ μ₃ : Measure}
    (h : Measure.rep ℓ μ₁ +ₕ Measure.rep ℓ μ₂ ≤ Measure.rep ℓ μ₃) :
    Obl.fuel (GF := GF) k ℓ μ₃ ⊢ |==> (Obl.fuel k ℓ μ₁ ∗ Obl.fuel k ℓ μ₂) :=
  (Obl.fuel_mono k ℓ (μ₁ := μ₁ + μ₂) (by rw [Measure.rep_add]; exact h)).trans
    (BIUpdate.mono (Obl.fuel_add k ℓ μ₁ μ₂).1)

@[lantana_alias oblP_fuel_mon_split_list]
theorem Obl.fuel_mono_split_list (K : List Oid) (ℓ : Layer) {μ₁ μ₂ μ₃ : Measure}
    (h : Measure.rep ℓ μ₁ +ₕ Measure.rep ℓ μ₂ ≤ Measure.rep ℓ μ₃) :
    ([∗list] k ∈ K, Obl.fuel (GF := GF) k ℓ μ₃) ⊢
      |==> (([∗list] k ∈ K, Obl.fuel k ℓ μ₁) ∗ [∗list] k ∈ K, Obl.fuel k ℓ μ₂) :=
  bigSepL_bupd_sep_of fun k => Obl.fuel_mono_split k ℓ h

@[lantana_alias oblP_fuel_mon_split_set]
theorem Obl.fuel_mono_split_set (K : Oids) (ℓ : Layer) {μ₁ μ₂ μ₃ : Measure}
    (h : Measure.rep ℓ μ₁ +ₕ Measure.rep ℓ μ₂ ≤ Measure.rep ℓ μ₃) :
    ([∗set] k ∈ K, Obl.fuel (GF := GF) k ℓ μ₃) ⊢
      |==> (([∗set] k ∈ K, Obl.fuel k ℓ μ₁) ∗ [∗set] k ∈ K, Obl.fuel k ℓ μ₂) :=
  bigSepS_bupd_sep_of fun k => Obl.fuel_mono_split k ℓ h

@[lantana_alias oblP_fuel_lt]
theorem Obl.fuel_lt (k : Oid) (ℓ : Layer) {μ₁ μ₂ : Measure}
    (h : Measure.rep ℓ μ₁ < Measure.rep ℓ μ₂) :
    Obl.fuel (GF := GF) k ℓ μ₂ ⊢ |==> (Obl.fuel k ℓ μ₁ ∗ Obl.fuel k ℓ 1) :=
  Obl.fuel_mono_split k ℓ (by rw [Measure.rep_ofNat]; exact nadd_one_le_of_lt h)

@[lantana_alias oblP_fuel_lt_list]
theorem Obl.fuel_lt_list (K : List Oid) (ℓ : Layer) {μ₁ μ₂ : Measure}
    (h : Measure.rep ℓ μ₁ < Measure.rep ℓ μ₂) :
    ([∗list] k ∈ K, Obl.fuel (GF := GF) k ℓ μ₂) ⊢
      |==> (([∗list] k ∈ K, Obl.fuel k ℓ μ₁) ∗ [∗list] k ∈ K, Obl.fuel k ℓ 1) :=
  bigSepL_bupd_sep_of fun k => Obl.fuel_lt k ℓ h

@[lantana_alias oblP_fuel_lt_set]
theorem Obl.fuel_lt_set (K : Oids) (ℓ : Layer) {μ₁ μ₂ : Measure}
    (h : Measure.rep ℓ μ₁ < Measure.rep ℓ μ₂) :
    ([∗set] k ∈ K, Obl.fuel (GF := GF) k ℓ μ₂) ⊢
      |==> (([∗set] k ∈ K, Obl.fuel k ℓ μ₁) ∗ [∗set] k ∈ K, Obl.fuel k ℓ 1) :=
  bigSepS_bupd_sep_of fun k => Obl.fuel_lt k ℓ h

@[lantana_alias oblP_fuel_embed]
theorem Obl.fuel_embed (k : Oid) (ℓ : Layer) {A : Type} {r : A → A → Prop} (hwf : WellFounded r)
    {a₁ a₂ : A} (h : r a₁ a₂) :
    Obl.fuel (GF := GF) k ℓ ⟪hwf, a₂⟫ ⊢ |==> (Obl.fuel k ℓ ⟪hwf, a₁⟫ ∗ Obl.fuel k ℓ 1) :=
  Obl.fuel_lt k ℓ (Measure.rep_embed_lt ℓ hwf h)

@[lantana_alias oblP_fuel_embed_list]
theorem Obl.fuel_embed_list (K : List Oid) (ℓ : Layer) {A : Type} {r : A → A → Prop}
    (hwf : WellFounded r) {a₁ a₂ : A} (h : r a₁ a₂) :
    ([∗list] k ∈ K, Obl.fuel (GF := GF) k ℓ ⟪hwf, a₂⟫) ⊢
      |==> (([∗list] k ∈ K, Obl.fuel k ℓ ⟪hwf, a₁⟫) ∗ [∗list] k ∈ K, Obl.fuel k ℓ 1) :=
  bigSepL_bupd_sep_of fun k => Obl.fuel_embed k ℓ hwf h

@[lantana_alias oblP_fuel_embed_set]
theorem Obl.fuel_embed_set (K : Oids) (ℓ : Layer) {A : Type} {r : A → A → Prop}
    (hwf : WellFounded r) {a₁ a₂ : A} (h : r a₁ a₂) :
    ([∗set] k ∈ K, Obl.fuel (GF := GF) k ℓ ⟪hwf, a₂⟫) ⊢
      |==> (([∗set] k ∈ K, Obl.fuel k ℓ ⟪hwf, a₁⟫) ∗ [∗set] k ∈ K, Obl.fuel k ℓ 1) :=
  bigSepS_bupd_sep_of fun k => Obl.fuel_embed k ℓ hwf h

@[lantana_alias oblP_fuel_large]
theorem Obl.fuel_large (k : Oid) (ℓ : Layer) {A : Type} {r : A → A → Prop} (hwf : WellFounded r)
    (a : A) : Obl.fuel (GF := GF) k ℓ ℵ ⊢ |==> (Obl.fuel k ℓ ⟪hwf, a⟫ ∗ Obl.fuel k ℓ 1) :=
  Obl.fuel_lt k ℓ (Measure.rep_large_lt ℓ hwf a)

@[lantana_alias oblP_fuel_large_list]
theorem Obl.fuel_large_list (K : List Oid) (ℓ : Layer) {A : Type} {r : A → A → Prop}
    (hwf : WellFounded r) (a : A) :
    ([∗list] k ∈ K, Obl.fuel (GF := GF) k ℓ ℵ) ⊢
      |==> (([∗list] k ∈ K, Obl.fuel k ℓ ⟪hwf, a⟫) ∗ [∗list] k ∈ K, Obl.fuel k ℓ 1) :=
  bigSepL_bupd_sep_of fun k => Obl.fuel_large k ℓ hwf a

@[lantana_alias oblP_fuel_large_set]
theorem Obl.fuel_large_set (K : Oids) (ℓ : Layer) {A : Type} {r : A → A → Prop}
    (hwf : WellFounded r) (a : A) :
    ([∗set] k ∈ K, Obl.fuel (GF := GF) k ℓ ℵ) ⊢
      |==> (([∗set] k ∈ K, Obl.fuel k ℓ ⟪hwf, a⟫) ∗ [∗set] k ∈ K, Obl.fuel k ℓ 1) :=
  bigSepS_bupd_sep_of fun k => Obl.fuel_large k ℓ hwf a

@[lantana_alias oblP_fuel_add_list]
theorem Obl.fuel_add_list (K : List Oid) (ℓ : Layer) (μ₁ μ₂ : Measure) :
    ([∗list] k ∈ K, Obl.fuel (GF := GF) k ℓ (μ₁ + μ₂)) ⊣⊢
      ([∗list] k ∈ K, Obl.fuel k ℓ μ₁) ∗ [∗list] k ∈ K, Obl.fuel k ℓ μ₂ :=
  (bigSepL_eqv_of fun k => Obl.fuel_add k ℓ μ₁ μ₂).trans bigSepL_sep_eqv

@[lantana_alias oblP_fuel_add_set]
theorem Obl.fuel_add_set (K : Oids) (ℓ : Layer) (μ₁ μ₂ : Measure) :
    ([∗set] k ∈ K, Obl.fuel (GF := GF) k ℓ (μ₁ + μ₂)) ⊣⊢
      ([∗set] k ∈ K, Obl.fuel k ℓ μ₁) ∗ [∗set] k ∈ K, Obl.fuel k ℓ μ₂ :=
  (bigSepS_eqv fun _ => Obl.fuel_add _ ℓ μ₁ μ₂).trans bigSepS_sep

@[lantana_alias oblP_fuel_mult]
theorem Obl.fuel_mult (k : Oid) (ℓ : Layer) {μ₁ μ₂ : Measure} (s : Measure)
    (h : Measure.rep ℓ μ₁ < Measure.rep ℓ μ₂) :
    Obl.fuel (GF := GF) k ℓ (s * μ₂) ⊢ |==> (Obl.fuel k ℓ (s * μ₁) ∗ Obl.fuel k ℓ s) :=
  Obl.fuel_mono_split k ℓ (by
    rw [Measure.rep_mul, Measure.rep_mul, nadd_comm, ← jmul_succ]
    exact jmul_le_jmul Ordinal.le_rfl (succ_le_of_lt h))

@[lantana_alias oblP_fuel_mult_list]
theorem Obl.fuel_mult_list (K : List Oid) (ℓ : Layer) {μ₁ μ₂ : Measure} (s : Measure)
    (h : Measure.rep ℓ μ₁ < Measure.rep ℓ μ₂) :
    ([∗list] k ∈ K, Obl.fuel (GF := GF) k ℓ (s * μ₂)) ⊢
      |==> (([∗list] k ∈ K, Obl.fuel k ℓ (s * μ₁)) ∗ [∗list] k ∈ K, Obl.fuel k ℓ s) :=
  bigSepL_bupd_sep_of fun k => Obl.fuel_mult k ℓ s h

@[lantana_alias oblP_fuel_mult_set]
theorem Obl.fuel_mult_set (K : Oids) (ℓ : Layer) {μ₁ μ₂ : Measure} (s : Measure)
    (h : Measure.rep ℓ μ₁ < Measure.rep ℓ μ₂) :
    ([∗set] k ∈ K, Obl.fuel (GF := GF) k ℓ (s * μ₂)) ⊢
      |==> (([∗set] k ∈ K, Obl.fuel k ℓ (s * μ₁)) ∗ [∗set] k ∈ K, Obl.fuel k ℓ s) :=
  bigSepS_bupd_sep_of fun k => Obl.fuel_mult k ℓ s h

@[lantana_alias oblP_fuel_expn]
theorem Obl.fuel_expn (k : Oid) (ℓ : Layer) {μ₁ μ₂ : Measure} (s : Measure)
    (h : Measure.rep ℓ μ₁ < Measure.rep ℓ μ₂) (hs : 0 < Measure.rep ℓ s) :
    Obl.fuel (GF := GF) k ℓ (s ^ μ₂) ⊢ |==> Obl.fuel k ℓ (s ^ μ₁ * s) :=
  Obl.fuel_mono k ℓ (by
    rw [Measure.rep_mul, Measure.rep_pow, Measure.rep_pow, ← jpow_succ hs]
    exact jpow_le_jpow Ordinal.le_rfl (succ_le_of_lt h))

@[lantana_alias oblP_fuel_expn_list]
theorem Obl.fuel_expn_list (K : List Oid) (ℓ : Layer) {μ₁ μ₂ : Measure} (s : Measure)
    (h : Measure.rep ℓ μ₁ < Measure.rep ℓ μ₂) (hs : 0 < Measure.rep ℓ s) :
    ([∗list] k ∈ K, Obl.fuel (GF := GF) k ℓ (s ^ μ₂)) ⊢
      |==> [∗list] k ∈ K, Obl.fuel k ℓ (s ^ μ₁ * s) :=
  bigSepL_bupd_of fun k => Obl.fuel_expn k ℓ s h hs

@[lantana_alias oblP_fuel_expn_set]
theorem Obl.fuel_expn_set (K : Oids) (ℓ : Layer) {μ₁ μ₂ : Measure} (s : Measure)
    (h : Measure.rep ℓ μ₁ < Measure.rep ℓ μ₂) (hs : 0 < Measure.rep ℓ s) :
    ([∗set] k ∈ K, Obl.fuel (GF := GF) k ℓ (s ^ μ₂)) ⊢
      |==> [∗set] k ∈ K, Obl.fuel k ℓ (s ^ μ₁ * s) :=
  bigSepS_bupd_of fun k => Obl.fuel_expn k ℓ s h hs

@[lantana_alias oblP_fuel_extend_list]
theorem Obl.fuel_extend_list (K : List Oid) {ℓ₁ ℓ₂ : Layer} (h : ℓ₁ < ℓ₂) (μ : Measure) :
    ([∗list] k ∈ K, Obl.fuel (GF := GF) k ℓ₂ 1) ⊢ |==> [∗list] k ∈ K, Obl.fuel k ℓ₁ μ :=
  bigSepL_bupd_of fun k => Obl.fuel_extend k h μ

@[lantana_alias oblP_fuel_extend_set]
theorem Obl.fuel_extend_set (K : Oids) {ℓ₁ ℓ₂ : Layer} (h : ℓ₁ < ℓ₂) (μ : Measure) :
    ([∗set] k ∈ K, Obl.fuel (GF := GF) k ℓ₂ 1) ⊢ |==> [∗set] k ∈ K, Obl.fuel k ℓ₁ μ :=
  bigSepS_bupd_of fun k => Obl.fuel_extend k h μ

@[lantana_alias oblP_fuel_add_nat]
theorem Obl.fuel_add_nat (k : Oid) (ℓ : Layer) {m₁ m₂ n : Nat} (h : n = m₁ + m₂) :
    Obl.fuel (GF := GF) k ℓ (n : Measure) ⊣⊢
      Obl.fuel k ℓ (m₁ : Measure) ∗ Obl.fuel k ℓ (m₂ : Measure) := by
  subst h
  refine (Obl.fuel_eq_of_rep k ℓ ?_).trans (Obl.fuel_add k ℓ _ _)
  rw [Measure.rep_add]
  exact Measure.rep_nat_add ℓ m₁ m₂

/-! ### Witness credits -/

#lantana_ignore witP_cred_eq "Ordinal equality is Leibniz: rewrite."

@[lantana_alias witP_cred_mon_split]
theorem Wit.cred_mono_split (k : Oid) {a₀ a₁ a₂ : Fuel} (h : a₀ +ₕ a₁ ≤ a₂) :
    Wit.cred (GF := GF) k a₂ ⊢ |==> (Wit.cred k a₀ ∗ Wit.cred k a₁) :=
  (Wit.cred_mono k h).trans (BIUpdate.mono (Wit.cred_split k a₀ a₁).1)

@[lantana_alias witP_cred_lt]
theorem Wit.cred_lt (k : Oid) {a₀ a₁ : Fuel} (h : a₀ < a₁) :
    Wit.cred (GF := GF) k a₁ ⊢ |==> (Wit.cred k a₀ ∗ Wit.cred k 1) :=
  Wit.cred_mono_split k (nadd_one_le_of_lt h)

/-! ### Fuels of sets of obligations -/

@[lantana_alias oblP_fuels_add_gen]
theorem oblFuels_add_gen (K : Oids) (m₁ m₂ : Measure) :
    oblFuels (GF := GF) K (m₁ + m₂) ⊢ oblFuels K m₁ ∗ oblFuels K m₂ :=
  (bigSepS_mono_of_forall fun k => exists_elim fun ℓ =>
    (Obl.fuel_add k ℓ m₁ m₂).1.trans (sep_mono (exists_intro (Ψ := fun ℓ => Obl.fuel k ℓ _) ℓ)
      (exists_intro (Ψ := fun ℓ => Obl.fuel k ℓ _) ℓ))).trans
    bigSepS_sep.1

@[lantana_alias oblP_fuels_add]
theorem oblFuels_add (n m : Nat) (K : Oids) :
    oblFuels (GF := GF) K ((n + m : Nat) : Measure) ⊢
      oblFuels K (n : Measure) ∗ oblFuels K (m : Measure) :=
  (bigSepS_mono_of_forall fun k => exists_elim fun ℓ =>
    (Obl.fuel_add_nat k ℓ rfl).1.trans (sep_mono (exists_intro (Ψ := fun ℓ => Obl.fuel k ℓ _) ℓ)
      (exists_intro (Ψ := fun ℓ => Obl.fuel k ℓ _) ℓ))).trans
    bigSepS_sep.1

@[lantana_alias oblP_fuels_add_nat]
theorem oblFuels_add_nat (m₁ m₂ n : Nat) (K : Oids) (h : n = m₁ + m₂) :
    oblFuels (GF := GF) K (n : Measure) ⊢ oblFuels K (m₁ : Measure) ∗ oblFuels K (m₂ : Measure) :=
  h ▸ oblFuels_add m₁ m₂ K

@[lantana_alias oblP_fuels_init]
theorem oblFuels_init (K : Oids) (m : Measure) (ℓ : Layer) :
    ([∗set] k ∈ K, Obl.fuel (GF := GF) k ℓ m) ⊢ oblFuels K m :=
  bigSepS_mono_of_forall fun k => exists_intro (Ψ := fun ℓ => Obl.fuel k ℓ m) ℓ

@[lantana_alias oblP_fuels_add_obl]
theorem oblFuels_add_obl (K : Oids) (k : Oid) (ℓ : Layer) (n : Measure) :
    Obl.fuel (GF := GF) k ℓ n ⊢ oblFuels K n -∗ oblFuels (K.insert k) n := by
  unfold oblFuels
  refine wand_intro ?_
  rw [insert_eq_singleton_union_extTreeSet]
  refine (sep_mono_left ?_).trans bigSepS_union_2
  exact (exists_intro (Ψ := fun ℓ => Obl.fuel k ℓ n) ℓ).trans
    (bigSepS_singleton (Φ := fun k => iprop(∃ ℓ, Obl.fuel k ℓ n))).2

@[lantana_alias oblP_fuels_add_obls]
theorem oblFuels_add_obls (K₁ K₂ : Oids) (n : Measure) :
    oblFuels (GF := GF) K₁ n ⊢ oblFuels K₂ n -∗ oblFuels (K₁ ∪ K₂) n :=
  wand_intro bigSepS_union_2

@[lantana_alias oblP_fuels_remove_obl]
theorem oblFuels_remove_obl (k : Oid) (K : Oids) (n : Measure) :
    oblFuels (GF := GF) K n ⊢ oblFuels (K.erase k) n :=
  bigSepS_subseteq fun _ hx => (Std.ExtTreeSet.mem_erase.mp hx).2

@[lantana_alias oblP_fuels_remove_obls]
theorem oblFuels_remove_obls (K₂ K₁ : Oids) (n : Measure) :
    oblFuels (GF := GF) K₁ n ⊢ oblFuels (K₁ \ K₂) n :=
  bigSepS_subseteq diff_subset_left

end Fuel

/-! ## Witness induction -/

section Witness

variable {GF : BundledGFunctors} [ModelGS GF]

open BigSepM BigSepS LawfulPartialMap LawfulFiniteMap

omit [ModelGS GF] in
/-- `Std.ExtTreeMap.insert` is the partial-map insertion of Iris-Lean. -/
theorem OidMap.insert_eq {V : Type _} (F : OidMap V) (k : Oid) (v : V) :
    F.insert k v = PartialMap.insert F k v := by
  refine Std.ExtTreeMap.ext_getElem? fun k' => ?_
  change (F.insert k v)[k']? = (F.alter k fun _ => some v)[k']?
  rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_alter]

omit [ModelGS GF] in
/-- The union of `Std.ExtTreeMap` is right-biased: `F ∪ G` takes the values of `G`. -/
theorem OidMap.union_insert {V : Type _} (F G : OidMap V) (k : Oid) (v : V) :
    F ∪ G.insert k v = (F ∪ G).insert k v :=
  Std.ExtTreeMap.union_insert_right_eq_insert_union (p := ⟨k, v⟩)

omit [ModelGS GF] in
theorem OidMap.union_empty {V : Type _} (F : OidMap V) : F ∪ ∅ = F :=
  Std.ExtTreeMap.ext_getElem? fun k => by
    rw [Std.ExtTreeMap.getElem?_union, Std.ExtTreeMap.getElem?_empty]; rfl

omit [ModelGS GF] in
theorem OidMap.empty_union {V : Type _} (F : OidMap V) : ∅ ∪ F = F :=
  Std.ExtTreeMap.ext_getElem? fun k => by
    rw [Std.ExtTreeMap.getElem?_union, Std.ExtTreeMap.getElem?_empty, Option.or_none]

/-- Adding the fuels `G` (each `(l, m)` of `G` with `ℓ < l`, given as fuel `m * ▽` at `l`) to the
witness induction (Rocq `wit_fuels_add_map_gen`; Rocq's `G ∪ F` is `F ∪ G` here, as the union of
`Std.ExtTreeMap` takes the values of its right argument). -/
@[lantana_alias wit_fuels_add_map_gen]
theorem Wit.fuels_add_map_gen (k : Oid) (ℓ : Layer) (α : Fuel) (F G : OidMap (Layer × Measure)) :
    Wit.fuels (GF := GF) k ℓ α F ⊢
      ([∗map] g ↦ lm ∈ G, ⌜ℓ < lm.1⌝ ∗ Obl.fuel g lm.1 (lm.2 * ▽)) ==∗
        Wit.fuels k ℓ α (F ∪ G) := by
  induction G using LawfulFiniteMap.induction_on with
  | hemp =>
    rw [OidMap.union_empty]
    iintro W -
    imodintro
    iexact W
  | hins f x G hf ih =>
    rw [show F ∪ PartialMap.insert G f x = (F ∪ G).insert f x by
      rw [← OidMap.insert_eq, OidMap.union_insert]]
    iintro W Fs
    icases (bigSepM_insert hf).1 $$ Fs with ⟨⟨%hl, Ff⟩, Fs⟩
    imod ih $$ W Fs with W
    iapply Wit.fuels_add k α (F ∪ G) f x.2 hl $$ W Ff

@[lantana_alias wit_fuels_add_map]
theorem Wit.fuels_add_map (k : Oid) (ℓ : Layer) (α : Fuel) (F : OidMap (Layer × Measure))
    (G : Oids) (l : Layer) (m : Measure) (hl : ℓ < l) :
    Wit.fuels (GF := GF) k ℓ α F ⊢ ([∗set] g ∈ G, Obl.fuel g l (m * ▽)) ==∗
      Wit.fuels k ℓ α (F ∪ (FiniteMap.ofSet (l, m) G : OidMap (Layer × Measure))) := by
  iintro W Fs
  iapply Wit.fuels_add_map_gen k ℓ α F _ $$ W
  iapply (bigSepM_ofSet _ G (l, m)).2
  iapply bigSepS_impl $$ Fs
  imodintro
  iintro %g %_ F
  isplitr
  · ipureintro
    exact hl
  · iexact F

@[lantana_alias wit_fuels_ind]
theorem Wit.fuels_ind (k : Oid) (ℓ : Layer) (α : Fuel) (F : OidMap (Layer × Measure))
    (P : IProp GF) :
    □ ((Wit.cred k 1 ==∗ ([∗map] f ↦ lm ∈ F, Obl.fuel f lm.1 lm.2) ∗ P) ==∗ P) ∗
      Wit.fuels k ℓ α F ⊢ |==> P := by
  induction α using WellFounded.induction Ordinals.Ordinal.lt_wf with
  | h α IH =>
    iintro ⟨#H, WF⟩
    iapply H
    iintro Wc
    imod Wit.fuels_decr k ℓ α F $$ WF Wc with ⟨%α₀, %hlt, WF, Fs⟩
    imod IH α₀ hlt $$ [WF] with HP
    · isplitl []
      · iexact H
      · iexact WF
    imodintro
    isplitl [Fs]
    · iexact Fs
    · iexact HP

/-- Witness-layer induction (WIT-IND): with a witness of `k` at layer `ℓ` and fuel `m * ▽` at
a layer `l` above `ℓ` for each `g ∈ G`, every credit of `k` can be exchanged for fuel `m` of
each `g ∈ G` until `P` holds. -/
@[lantana_alias wit_layer_ind]
theorem Wit.layer_ind (k : Oid) (ℓ : Layer) (G : Oids) (l : Layer) (m : Measure) (P : IProp GF)
    (hl : ℓ < l) :
    □ ((Wit.cred k 1 ==∗ ([∗set] g ∈ G, Obl.fuel g l m) ∗ P) ==∗ P) ∗ Wit.layer k ℓ ∗
      ([∗set] g ∈ G, Obl.fuel g l (m * ▽)) ⊢ |==> P := by
  have hmap : ([∗map] f ↦ lm ∈ (∅ ∪ (FiniteMap.ofSet (l, m) G : OidMap (Layer × Measure))),
      Obl.fuel (GF := GF) f lm.1 lm.2) ⊣⊢ [∗set] g ∈ G, Obl.fuel g l m := by
    rw [OidMap.empty_union]
    exact bigSepM_ofSet _ G (l, m)
  iintro ⟨#IND, #Wl, FG⟩
  icases Wit.fuels_init k ℓ $$ Wl with ⟨%α, Wf0⟩
  imod Wit.fuels_add_map k ℓ α ∅ G l m hl $$ Wf0 FG with WF
  iapply Wit.fuels_ind k ℓ α _ P
  isplitl []
  · imodintro
    iintro H
    iapply IND
    iintro Wc
    imod H $$ Wc with ⟨Fs, HP⟩
    imodintro
    isplitl [Fs]
    · iapply hmap.1 $$ Fs
    · iexact HP
  · iexact WF

/-! ### Fuels for an induction on an embedded well-founded order -/

/-- Each fuel `(l, m)` of `F`, times the rank of `a` (Rocq `embed_fuels`). -/
@[lantana_alias embed_fuels]
def embedFuels {A : Type} {r : A → A → Prop} (hwf : WellFounded r) (a : A)
    (F : OidMap (Layer × Measure)) : IProp GF :=
  iprop([∗map] f ↦ lm ∈ F, Obl.fuel f lm.1 (lm.2 * ⟪hwf, a⟫))

@[lantana_alias embed_fuels_init]
theorem embedFuels_init {A : Type} {r : A → A → Prop} (hwf : WellFounded r) (a : A) :
    ⊢ embedFuels (GF := GF) hwf a ∅ := by
  unfold embedFuels
  exact bigSepM_empty.2

/-- Adding fuel `m * ℵ` at `l` for each `g ∈ G` (Rocq `embed_fuels_add_map`, with the union
flipped as in `Wit.fuels_add_map_gen`). -/
@[lantana_alias embed_fuels_add_map]
theorem embedFuels_add_map {A : Type} {r : A → A → Prop} (hwf : WellFounded r) (a : A)
    (F : OidMap (Layer × Measure)) (G : Oids) (l : Layer) (m : Measure) :
    embedFuels (GF := GF) hwf a F ⊢ ([∗set] g ∈ G, Obl.fuel g l (m * ℵ)) ==∗
      embedFuels hwf a (F ∪ (FiniteMap.ofSet (l, m) G : OidMap (Layer × Measure))) := by
  unfold embedFuels
  induction G using FiniteSet.set_ind with
  | hemp =>
    rw [ofSet_empty, OidMap.union_empty]
    iintro E -
    imodintro
    iexact E
  | hadd g G hg ih =>
    rw [ofSet_insert, ← OidMap.insert_eq, OidMap.union_insert, OidMap.insert_eq]
    iintro E Fs
    icases (bigSepS_insert hg).1 $$ Fs with ⟨Fg, Fs⟩
    imod ih $$ E Fs with E
    imod Obl.fuel_mono g l (μ₁ := m * ⟪hwf, a⟫) (by
      rw [Measure.rep_mul, Measure.rep_mul]
      exact Ordinals.Ordinal.jmul_le_jmul Ordinals.Ordinal.le_rfl
        (Ordinals.Ordinal.le_of_lt (Measure.rep_large_lt l hwf a))) $$ Fg with Fg
    imodintro
    iapply bigSepM_insert_delete.2
    isplitl [Fg]
    · iexact Fg
    · iapply bigSepM_subseteq delete_subset_self $$ E

@[lantana_alias embed_fuels_decr]
theorem embedFuels_decr {A : Type} {r : A → A → Prop} (hwf : WellFounded r) {a a' : A}
    (F : OidMap (Layer × Measure)) (h : r a' a) :
    embedFuels (GF := GF) hwf a F ⊢
      |==> (embedFuels hwf a' F ∗ [∗map] f ↦ lm ∈ F, Obl.fuel f lm.1 lm.2) := by
  unfold embedFuels
  exact (bigSepM_mono_of_forall fun {f} {lm : Layer × Measure} => Obl.fuel_mult f lm.1 lm.2
    (Measure.rep_embed_lt lm.1 hwf h)).trans <|
    (bigSepM_bupd _).trans (BIUpdate.mono (BiEntails.of_eq bigSepM_sep_eq).1)

end Witness

/-! ## Model updates in their usual shapes -/

section ModelUpdates

variable {Expr : Type} {State : Type} {GF : BundledGFunctors} [ModelGS GF]
  [TemporalGS Expr State GF] [StateInterp Expr State GF] [TemporalInterp Expr State GF]

open BigSepS LawfulSet

/-! ### Allocation and moves -/

@[lantana_alias obl_alloc_assigned]
theorem obl_alloc_assigned (E : CoPset) (p : Parent) (K : Oids) (ℓ : Layer) (μ : Measure) :
    parLe (GF := GF) p ℓ ⊢ Par.kids p K -∗
      |={E}=>m ∃ k : Oid, ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ oblKids k ∅ ∗
        Obl.assigned k (Qp.half 1) ∗ Obl.fuel k ℓ μ ∗ Wit.layer k ℓ ∗
        (∀ (E : CoPset) (N : Namespace) (P R : IProp GF), ▷ P ={E}=∗ Obl.inv N k P R) := by
  iintro B C
  imod Obl.new E p K ℓ μ $$ B C with ⟨%k, %hk, C, Ck, A, F, W⟩
  icases (Obl.assigned_halves k).1 $$ A with ⟨A1, A2⟩
  imodintro
  iexists k
  iframe C Ck A1 F W
  isplitr
  · ipureintro
    exact hk
  iintro %E' %N %P %R HP
  iapply Obl.inv_alloc_assigned E' N k P R $$ A2 HP

/-- Moving a set `X` of children of `p₁` below `p₂`: one unit of fuel each, each at its own
layer. -/
@[lantana_alias obl_move_set_gen]
theorem obl_move_set_gen (E : CoPset) (p₁ p₂ : Parent) (K₁ K₂ X : Oids) (hX : X ⊆ K₁) :
    Par.kids (GF := GF) p₁ K₁ ⊢ Par.kids p₂ K₂ -∗
      ([∗set] k ∈ X, ∃ ℓ : Layer, parBelow p₂ ℓ ∗ Obl.fuel k ℓ 1) -∗
      |={E}=>m ⌜X ## K₂⌝ ∗ Par.kids p₁ (K₁ \ X) ∗ Par.kids p₂ (X ∪ K₂) := by
  induction X using FiniteSet.set_ind with
  | hemp =>
    rw [diff_empty, union_empty_left]
    iintro P1 P2 -
    imodintro
    iframe P1 P2
    ipureintro
    exact disjoint_empty_left
  | hadd x X hx ih =>
    have hbig := bigSepS_insert (Φ := fun k => iprop(∃ ℓ : Layer, parBelow (GF := GF) p₂ ℓ ∗
      Obl.fuel k ℓ 1)) hx
    rw [LawfulSet.insert_union] at hX hbig ⊢
    have hxK : x ∈ K₁ \ X :=
      mem_diff.mpr ⟨hX x (mem_union.mpr (.inl (mem_singleton.mpr rfl))), hx⟩
    have e₁ : K₁ \ ({x} ∪ X) = (K₁ \ X).erase x := by
      rw [Oids.erase_eq_diff]
      exact LawfulSet.ext fun y => by simp only [mem_diff, mem_union, mem_singleton]; grind
    have e₂ : {x} ∪ X ∪ K₂ = (X ∪ K₂).insert x := by
      rw [insert_eq_singleton_union_extTreeSet]
      exact LawfulSet.ext fun y => by simp only [mem_union, mem_singleton]; grind
    rw [e₁, e₂]
    iintro P1 P2 Fs
    icases hbig.1 $$ Fs with ⟨⟨%ℓ, B, Fx⟩, Fs⟩
    imod ih (fun y hy => hX y (mem_union.mpr (.inr hy))) $$ P1 P2 Fs with ⟨%hdis, P1, P2⟩
    imod Obl.move E p₁ p₂ (K₁ \ X) (X ∪ K₂) x ℓ hxK $$ B P1 P2 Fx with ⟨%hx₂, P1, P2⟩
    imodintro
    iframe P1 P2
    ipureintro
    intro y ⟨hy, hy₂⟩
    rcases mem_union.mp hy with hy | hy
    · exact hx₂ (mem_singleton.mp hy ▸ mem_union.mpr (.inr hy₂))
    · exact hdis y ⟨hy, hy₂⟩

/-- Moving a set `X` of children of `p₁` below the thread `j`: one unit of fuel each, at any
layer. -/
@[lantana_alias obl_move_thread_set]
theorem obl_move_thread_set (E : CoPset) (p₁ : Parent) (j : ThreadId) (K₁ K₂ X : Oids)
    (hX : X ⊆ K₁) :
    Par.kids (GF := GF) p₁ K₁ ⊢ thKids j K₂ -∗ ([∗set] k ∈ X, ∃ ℓ : Layer, Obl.fuel k ℓ 1) -∗
      |={E}=>m ⌜X ## K₂⌝ ∗ Par.kids p₁ (K₁ \ X) ∗ thKids j (X ∪ K₂) := by
  iintro P1 P2 Fs
  iapply obl_move_set_gen E p₁ (.thread j) K₁ K₂ X hX $$ P1 P2
  iapply bigSepS_impl $$ Fs
  imodintro
  iintro %k %_ ⟨%ℓ, F⟩
  iexists ℓ
  iframe F
  iapply parBelow_thread j ℓ

/-- Moving a set `X` of children of `p₁` below the obligation `q`: one unit of fuel each, each at
a layer above the witness layer `ℓq` of `q`. -/
@[lantana_alias obl_move_obl_set]
theorem obl_move_obl_set (E : CoPset) (p₁ : Parent) (q : Oid) (K₁ K₂ X : Oids) (ℓq : Layer)
    (hX : X ⊆ K₁) :
    Wit.layer (GF := GF) q ℓq ⊢ Par.kids p₁ K₁ -∗ oblKids q K₂ -∗
      ([∗set] k ∈ X, ∃ ℓ : Layer, ⌜ℓq < ℓ⌝ ∗ Obl.fuel k ℓ 1) -∗
      |={E}=>m ⌜X ## K₂⌝ ∗ Par.kids p₁ (K₁ \ X) ∗ oblKids q (X ∪ K₂) := by
  iintro #W P1 P2 Fs
  iapply obl_move_set_gen E p₁ (.obl q) K₁ K₂ X hX $$ P1 P2
  iapply bigSepS_impl $$ Fs
  imodintro
  iintro %k %_ ⟨%ℓ, %hl, F⟩
  iexists ℓ
  iframe F
  iapply parBelow_obl q hl $$ W

/-- Moving a set `X` of children of `k` up to the parent `p` of `k`, for free. -/
@[lantana_alias obl_move_up_set]
theorem obl_move_up_set (E : CoPset) (p : Parent) (K : Oids) (k : Oid) (Kk X : Oids)
    (hk : k ∈ K) (hX : X ⊆ Kk) :
    Par.kids (GF := GF) p K ⊢ oblKids k Kk -∗
      |={E}=>m ⌜X ## K⌝ ∗ Par.kids p (X ∪ K) ∗ oblKids k (Kk \ X) := by
  induction X using FiniteSet.set_ind with
  | hemp =>
    rw [diff_empty, union_empty_left]
    iintro P Ck
    imodintro
    iframe P Ck
    ipureintro
    exact disjoint_empty_left
  | hadd x X hx ih =>
    rw [LawfulSet.insert_union] at hX ⊢
    have hxK : x ∈ Kk \ X :=
      mem_diff.mpr ⟨hX x (mem_union.mpr (.inl (mem_singleton.mpr rfl))), hx⟩
    have e₁ : Kk \ ({x} ∪ X) = (Kk \ X).erase x := by
      rw [Oids.erase_eq_diff]
      exact LawfulSet.ext fun y => by simp only [mem_diff, mem_union, mem_singleton]; grind
    have e₂ : {x} ∪ X ∪ K = (X ∪ K).insert x := by
      rw [insert_eq_singleton_union_extTreeSet]
      exact LawfulSet.ext fun y => by simp only [mem_union, mem_singleton]; grind
    rw [e₁, e₂]
    iintro P Ck
    imod ih (fun y hy => hX y (mem_union.mpr (.inr hy))) $$ P Ck with ⟨%hdis, P, Ck⟩
    imod Obl.move_up E p (X ∪ K) k (Kk \ X) x (mem_union.mpr (.inr hk)) hxK $$ P Ck
      with ⟨%hx₂, P, Ck⟩
    imodintro
    iframe P Ck
    ipureintro
    intro y ⟨hy, hy₂⟩
    rcases mem_union.mp hy with hy | hy
    · exact hx₂ (mem_singleton.mp hy ▸ mem_union.mpr (.inr hy₂))
    · exact hdis y ⟨hy, hy₂⟩

@[lantana_alias obl_alloc_discharged]
theorem obl_alloc_discharged (E : CoPset) (ℓ : Layer) :
    ⊢ |={E}=>m ∃ k : Oid, Obl.discharged (GF := GF) k ∗ Wit.layer k ℓ ∗
      (∀ (E : CoPset) (N : Namespace) (P R : IProp GF), ▷ R ={E}=∗ Obl.inv N k P R) := by
  imod Obl.new_discharged E ℓ with ⟨%k, #D, W⟩
  imodintro
  iexists k
  iframe D W
  iintro %E' %N %P %R HR
  iapply Obl.inv_alloc_discharged E' N k P R $$ D HR

@[lantana_alias obl_check_witnesses]
theorem obl_check_witnesses (E : CoPset) (R : Oids) :
    ([∗set] r ∈ R, ∃ ℓ : Layer, Wit.layer (GF := GF) r ℓ) ⊢
      |={E}=>m [∗set] r ∈ R, (Wit.cred r 0 ∨ Obl.discharged r) :=
  (bigSepS_mono_of_forall fun r => exists_elim fun ℓ => Obl.check_witness E r ℓ).trans
    (bigSepS_mupd _ E R)

/-! ### Discharge -/

/-- Discharging `k` after moving its children up to its parent `p` (for free). -/
@[lantana_alias obl_discharge_lift_kids]
theorem obl_discharge_lift_kids (E : CoPset) (p : Parent) (K : Oids) (k : Oid) (Kk : Oids)
    (hk : k ∈ K) :
    Par.kids (GF := GF) p K ⊢ oblKids k Kk -∗ Obl.assigned k 1 -∗
      |={E}=>m Par.kids p (Kk ∪ K.erase k) ∗ Obl.discharged k := by
  iintro P Ck A
  imod obl_move_up_set E p K k Kk Kk hk subset_refl $$ P Ck with ⟨%hdis, P, Ck⟩
  rw [diff_all]
  imod Obl.discharge_leaf E p (Kk ∪ K) k (mem_union.mpr (.inr hk)) $$ P Ck A with ⟨P, D⟩
  have e : (Kk ∪ K).erase k = Kk ∪ K.erase k := by
    rw [Oids.erase_eq_diff, Oids.erase_eq_diff]
    exact LawfulSet.ext fun y => by
      simp only [mem_diff, mem_union, mem_singleton]
      have := hdis y
      grind
  imodintro
  iframe D
  iapply (show Par.kids (GF := GF) p ((Kk ∪ K).erase k) ⊢ Par.kids p (Kk ∪ K.erase k) by
    rw [e]) $$ P

/-- Discharging `k` with the invariant `Obl.inv N k P R`: `P` is taken out, and once `R` is
established, `k` (a childless child of `p`) is discharged. -/
@[lantana_alias obl_discharge_inv]
theorem obl_discharge_inv (E : CoPset) (N : Namespace) (k : Oid) (P R : IProp GF)
    (hN : ↑N ⊆ E) :
    Obl.inv N k P R ⊢ |={E, E \ ↑N}=> ∀ q, Obl.assigned k q -∗
      ▷ (Obl.assigned k q ∗ Obl.assigned k (Qp.half 1) ∗ P) ∗
      (∀ (p : Parent) (K : Oids), ⌜k ∈ K⌝ → Par.kids p K -∗ oblKids k ∅ -∗
        Obl.assigned k 1 -∗ ▷ R -∗
        ∀ E' : CoPset, |={E'}=>m |={E \ ↑N, E}=> Par.kids p (K.erase k) ∗ Obl.discharged k) := by
  iintro #I
  imod Obl.inv_acc_assigned E N k P R hN $$ I with H
  imodintro
  iintro %q A
  icases H $$ %q A with ⟨HP, Hclose⟩
  iframe HP
  iintro %p %K %hk Kp Kk A HR %E'
  imod Obl.discharge_leaf E' p K k hk $$ Kp Kk A with ⟨Kp, #D⟩
  imodintro
  imod Hclose $$ [HR] with -
  · inext
    iapply (Obl.variant_unfold k P R).2
    iright
    iframe D HR
  imodintro
  iframe Kp D

end ModelUpdates

/-! ## Physical steps in their usual shapes -/

section Steps

variable {GF : BundledGFunctors} [ModelGS GF]

@[lantana_alias mprog_step]
theorem mprog_step (n tc : Nat) (i : ThreadId) (P : IProp GF) :
    (|={∅}=> ∃ K : Oids, thKids i K ∗ oblFuels K 1 ∗
        ∃ R : Oids, ([∗set] r ∈ R, ∃ ℓ : Layer, Wit.layer r ℓ) ∗
          (thKids i K ∗ ([∗set] r ∈ R, Wit.cred r 1 ∨ Obl.discharged r) ={∅}=∗ P)) ⊢
      mprog n tc i P := by
  iintro H
  iapply fupd_mprog
  imod H with ⟨%K, T, F, %R, W, H⟩
  imodintro
  have hstep := step_progress (GF := GF) n tc i K R P
  simp only [witLayers, witCreds] at hstep
  iapply hstep $$ T F W
  iintro T C
  iapply H
  isplitl [T]
  · iexact T
  · iexact C

@[lantana_alias mphys_step]
theorem mphys_step (n₁ n₂ tc₁ tc₂ : Nat) (P : IProp GF) (hn : n₁ ≤ n₂) (htc : tc₁ ≤ tc₂) :
    (|={∅}=> ([∗list] j ∈ List.range' tc₁ (tc₂ - tc₁), thKids j ∅) ={∅}=∗ P) ⊢
      mphys n₁ n₂ tc₁ tc₂ P :=
  (fupd_mono (step_fork n₁ n₂ tc₁ tc₂ P hn htc)).trans (fupd_mphys n₁ n₂ tc₁ tc₂ P)

end Steps

end Lantana
