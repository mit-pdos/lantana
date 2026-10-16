/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.BaseLogic.LaterCredits
public import Iris.Instances.Lib.WSat
public import Iris.BI.Updates
public import Iris.Std.CoPset

/-! # Fancy updates on the relational update

Lantana's fancy update `|={E₁,E₂}=> P` (Rocq: `lantana/base_logic/fancy_updates.v`), built on the
relational update of transfinite later credits instead of the basic update:
`uPred_fupd E₁ E₂ P := wsat ∗ ownE E₁ -∗ |==>r ◇ (wsat ∗ ownE E₂ ∗ P)`.

Iris-Lean's `Iris.Instances.Lib.FUpd` (template of this file) builds the fancy update on its `Nat`
later-credit update `|==£>`, whose `▷^[n] False` escape disjunct hides the `◇`; Lantana's `|==>r`
has no escape disjunct, so the `◇` is explicit (decision D8 (i)). World satisfaction (`wsat`,
`ownE`, `ownI`, `wsat_alloc`) is Iris-Lean's `Iris.Instances.Lib.WSat`, unchanged.

Lantana never provides an instance of Iris-Lean's `InvGS_gen` (and this file does not import
`Iris.Instances.Lib.FUpd`): two `BIFUpdate (IProp GF)` instances would compete.

The `BIFUpdate` instance brings Iris-Lean's derived fancy-update laws (`Iris.BI.Updates`) and its
proof-mode instances (`Iris.ProofMode.InstancesUpdates`). The credits are Lantana's `£ₒ α`, not
Iris-Lean's `£ n`, so there is no `BIFUpdLaterCredits` instance; `lc_fupd_elim_later` and its
variants are lemmas here.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.OFE Iris.ProofMode Iris.Std Ordinals

universe u

/-! ## The ghost state of invariants and credits -/

section InvG

/-- `GF` contains the ghost state of world satisfaction and of transfinite later credits. -/
@[lantana_alias invGpreS]
class InvGpreS (GF : BundledGFunctors.{u}) where
  toWsatGpreS : WsatGpreS GF
  toTlcGpreS : TlcGpreS GF

attribute [reducible, instance] InvGpreS.toWsatGpreS
attribute [reducible, instance] InvGpreS.toTlcGpreS

attribute [lantana_alias invGpreS_wsat] InvGpreS.toWsatGpreS
attribute [lantana_alias invGpreS_lc] InvGpreS.toTlcGpreS

/-- The ghost state of world satisfaction and of transfinite later credits is allocated
(Rocq: `invGS`). -/
@[lantana_alias invGS]
class InvGS (GF : BundledGFunctors.{u}) extends WsatGS GF, TlcGS GF

attribute [lantana_alias invGS_wsat] InvGS.toWsatGS
attribute [lantana_alias invGS_lc] InvGS.toCreditGS

#lantana_ignore «invΣ» "Superseded by the `InvGpreS` typeclass on `BundledGFunctors`."
#lantana_ignore «subG_invΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis."

/-- Allocate world satisfaction and an empty credit supply. -/
@[lantana_alias invGS_alloc]
theorem invGS_alloc {GF : BundledGFunctors.{u}} [InvGpreS GF] :
    ⊢@{IProp GF} |==> ∃ _ : InvGS GF, (∃ x : Ordinal.{1}, ●£ₒ x) ∗ wsat ∗ ownE ⊤ := by
  imod wsat_alloc with ⟨%W, Hw, HE⟩
  imod credit_alloc (A := Ordinal.{1}) 0 with ⟨%C, Hs, -⟩
  imodintro
  iexists { toWsatGS := W, toCreditGS := C }
  isplitl [Hs]
  · iexists 0
    iexact Hs
  isplitl [Hw]
  · iexact Hw
  · iexact HE

end InvG

/-! ## The fancy update -/

section FUpd

variable {GF : BundledGFunctors.{u}} [InvGS GF]

#lantana_ignore uPred_fupd_def "`uPred_fupd` is defined directly without `seal`/`unseal`."
#lantana_ignore uPred_fupd_aux "`uPred_fupd` is defined directly without `seal`/`unseal`."
#lantana_ignore uPred_fupd_unseal "`uPred_fupd` is defined directly without `seal`/`unseal`."

/-- The fancy update: given world satisfaction and the mask `E₁`, update the ghost state with the
relational update, and give back world satisfaction, the mask `E₂` and `P`, under `◇`. -/
@[lantana_alias uPred_fupd]
def uPred_fupd (E₁ E₂ : CoPset) (P : IProp GF) : IProp GF :=
  iprop(wsat ∗ ownE E₁ -∗ |==>r ◇ (wsat ∗ ownE E₂ ∗ P))

instance uPred_fupd_ne {E₁ E₂ : CoPset} : NonExpansive (uPred_fupd (GF := GF) E₁ E₂) where
  ne {_ _ _} h := by
    simp only [uPred_fupd]
    exact wand_ne.ne .rfl <| rupd_ne.ne <| except0_ne.ne <| sep_ne.ne .rfl <| sep_ne.ne .rfl h

instance uPred_fupd_instance : FUpd (IProp GF) where
  fupd := uPred_fupd

end FUpd

section Instances

open Std.LawfulSet

#lantana_ignore uPred_fupd_mixin "The `BiFUpdMixin` laws are supplied directly in `uPred_bi_fupd`."

variable {GF : BundledGFunctors.{u}} [InvGS GF]

@[lantana_alias uPred_bi_fupd]
instance uPred_bi_fupd : BIFUpdate (IProp GF) where
  fupd := uPred_fupd
  ne := uPred_fupd_ne
  subset {E1 E2} Hsub := by
    simp only [uPred_fupd]
    iintro ⟨Hw, HE⟩
    rw [diff_subset_decomp Hsub]
    icases (ownE_op (disjoint_symm disjoint_diff_right)).mp $$ HE with ⟨HE1, HE2⟩
    imodintro
    imodintro
    iframe Hw HE2
    iintro ⟨Hw, HE2⟩
    imodintro
    imodintro
    iframe Hw
    isplitl
    · iapply (ownE_op (disjoint_symm disjoint_diff_right)).mpr
      iframe
    · iempintro
  except0 {E1 E2 P} := by
    simp only [uPred_fupd]
    iintro H Hwe
    imod H
    iapply H $$ Hwe
  mono H := by
    simp only [uPred_fupd]
    iintro Hupd HwE
    iapply rupd_mono (except0_mono (sep_mono_right (sep_mono_right H)))
    iapply Hupd $$ HwE
  trans {_ _ _ _} := by
    simp only [uPred_fupd]
    iintro Hupd HwE
    imod Hupd $$ HwE with >⟨Hw, HE, Hupd⟩
    iapply Hupd
    iframe
  mask_frame_right_strong {E1 E2 Ef P} Hdisj := by
    simp only [uPred_fupd]
    iintro Hupd ⟨Hwsat, HE⟩
    icases (ownE_op Hdisj).mp $$ HE with ⟨HE1, HEf⟩
    imod Hupd $$ [Hwsat HE1] with >⟨Hw, HE2, HP⟩
    · iframe
    icases (ownE_op_iff (E1 := E2) (E2 := Ef)).mpr $$ [HE2 HEf] with ⟨%Hdisj', HE⟩
    · iframe
    imodintro
    imodintro
    iframe Hw HE
    iapply HP
    ipureintro
    exact Hdisj'
  frame_right {_ _ _ _} := by
    simp only [uPred_fupd]
    iintro ⟨Hupd, HR⟩ HwE
    imod Hupd $$ HwE with >⟨Hw, HE, HP⟩
    imodintro
    imodintro
    iframe

@[lantana_alias uPred_bi_bupd_fupd]
instance uPred_bi_bupd_fupd : BIUpdateFUpdate (IProp GF) where
  fupd_of_bupd {_ _} := by
    iintro H
    simp only [fupd, uPred_fupd]
    iintro ⟨Hw, HE⟩
    imod H
    imodintro
    imodintro
    iframe

theorem fupd_eq {E₁ E₂ : CoPset} {P : IProp GF} :
    iprop(|={E₁,E₂}=> P) = uPred_fupd E₁ E₂ P := rfl

/-- Unfold the fancy update. -/
theorem fupd_unfold {E₁ E₂ : CoPset} {P : IProp GF} :
    (|={E₁,E₂}=> P) ⊣⊢ (wsat ∗ ownE E₁ -∗ |==>r ◇ (wsat ∗ ownE E₂ ∗ P)) := .rfl

end Instances

/-! ## Relational updates and later credits at fancy updates -/

section LaterCredits

variable {GF : BundledGFunctors.{u}} [InvGS GF]

open Ordinals Ordinal

@[lantana_alias rupd_fupd]
theorem rupd_fupd {E : CoPset} {P : IProp GF} : (|==>r P) ⊢ |={E}=> P := by
  iintro Hupd
  simp only [fupd, uPred_fupd]
  iintro ⟨Hw, HE⟩
  imod Hupd
  imodintro
  imodintro
  iframe

/-- Typical use: `imod lc_fupd_elim_later_ord $$ Hcredit HP with HP`. -/
@[lantana_alias lc_fupd_elim_later_ord]
theorem lc_fupd_elim_later_ord {E : CoPset} {P : IProp GF} :
    ⊢ £ₒ (1 : Ordinal.{1}) -∗ ▷ P -∗ |={E}=> P := by
  iintro Hf HP
  simp only [fupd, uPred_fupd]
  iintro ⟨Hw, HE⟩
  iapply tlc_later
  isplitl [Hf]
  · iexact Hf
  inext
  imodintro
  imodintro
  iframe

@[lantana_alias lc_fupd_elim_later]
theorem lc_fupd_elim_later {E : CoPset} {P : IProp GF} : ⊢ £ₙ 1 -∗ ▷ P -∗ |={E}=> P :=
  lc_fupd_elim_later_ord

/-- Typical use on a fancy-update goal: `iapply lc_fupd_add_later_ord $$ Hcredit`. -/
@[lantana_alias lc_fupd_add_later_ord]
theorem lc_fupd_add_later_ord {E₁ E₂ : CoPset} {P : IProp GF} :
    ⊢ £ₒ (1 : Ordinal.{1}) -∗ (▷ |={E₁,E₂}=> P) -∗ |={E₁,E₂}=> P := by
  iintro Hf HP
  iapply fupd_trans (E2 := E₁)
  iapply lc_fupd_elim_later_ord $$ Hf HP

@[lantana_alias lc_fupd_add_later]
theorem lc_fupd_add_later {E₁ E₂ : CoPset} {P : IProp GF} :
    ⊢ £ₙ 1 -∗ (▷ |={E₁,E₂}=> P) -∗ |={E₁,E₂}=> P :=
  lc_fupd_add_later_ord

@[lantana_alias lc_fupd_add_laterN]
theorem lc_fupd_add_laterN {E₁ E₂ : CoPset} {P : IProp GF} (n : Nat) :
    ⊢ £ₙ n -∗ ▷^[n] (|={E₁,E₂}=> P) -∗ |={E₁,E₂}=> P := by
  induction n with
  | zero =>
    iintro _ HP
    simp only [BIBase.laterN, Nat.repeat]
    iexact HP
  | succ n ih =>
    iintro Hf HP
    icases (tlc_succ_nat n).mp $$ Hf with ⟨H1, Hf⟩
    iapply lc_fupd_add_later $$ H1
    inext
    iapply ih $$ Hf HP

end LaterCredits

/-! ## Optional allocation `ALC? p P` -/

section ALCb

variable {GF : BundledGFunctors.{u}} {A : Type _} [UCMRA A] [CreditGS GF A] [CreditCamera A]

/-- `ALC? p P` is `ALC P` if `p`, and `P` otherwise (Rocq: `ALC? p P := Nat.iter (b2n p) ALC P`). -/
def ALCb (p : Bool) (P : IProp GF) : IProp GF :=
  match p with
  | true => ALC P
  | false => P

/-- `ALC? p P`. -/
scoped syntax:max "ALC? " term:max ppSpace term:max : term

macro_rules
  | `(iprop(ALC?%$tk $p $P)) => ``($(wrapIprop tk ``ALCb) $p iprop($P))
  | `(ALC? $p $P) => ``(ALCb $p $P)

@[simp] theorem ALCb_true {P : IProp GF} : ALCb true P = ALC P := rfl
@[simp] theorem ALCb_false {P : IProp GF} : ALCb false P = P := rfl

@[lantana_alias from_modal_ALCb]
instance fromModal_ALCb {io} {b : Bool} {P : IProp GF} :
    FromModal io modality_id True (ALCb b P) (ALCb b P) P where
  from_modal _ := by cases b <;> simp only [ALCb] <;> first | exact ALC_intro | exact .rfl

@[lantana_alias from_pure_ALCb]
instance fromPure_ALCb {a io φ} {b : Bool} {P : IProp GF} [h : FromPure a P io φ] :
    FromPure a (ALCb b P) io φ where
  from_pure := by cases b <;> simp only [ALCb] <;> first | exact h.1.trans ALC_intro | exact h.1

@[lantana_alias elim_rupd_ALCb]
instance elimModal_ALCb {p io} {b : Bool} {P Q : IProp GF} :
    ElimModal True p io false (ALCb b P) P (ALCb b Q) Q where
  elim_modal h := by
    cases b
    · exact (sep_mono_left intuitionisticallyIf_elim).trans wand_elim_right
    · exact (elimModal_ALC (p := p) (io := io)).elim_modal h

end ALCb

end Lantana
