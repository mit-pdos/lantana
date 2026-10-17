/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.BaseLogic.FUpd
public import Iris.Instances.UPred.Transfinite
public import Iris.Algebra.StepIndexChoice
public import Iris.Std.FromMathlib

/-! # Satisfiability

Satisfiability predicates on `IProp GF`, used to eliminate updates in the adequacy proofs
(Rocq: `lantana/base_logic/satisfiable.v`, `relational_updates.v:306-384`, and `sat_ALC` of
`later_credits.v:275-289`; on top of Transfinite Iris's `bi/satisfiable.v` and
`base_logic/lib/satisfiable.v`).

Iris-Lean's `Satisfiable PROP` (`Iris.BI.Transfinite`) is one canonical predicate per `PROP`,
whereas adequacy needs a family of predicates with the same laws: the model's satisfiability
framed with a credit supply, with world satisfaction and an enabled mask, and with a user frame.
Following Rocq (decision D9), a satisfiability predicate is a structure `SatPred GF` (monotone,
and sound for pure propositions), with one mixin class per law (`SatLater`, `SatBUpd`,
`SatExists`, `SatRUpd`, `SatRUpdUpdate`, and `SatFUpd` for mask-indexed families `SatAt GF`).
The base predicate `iPropSat` is Iris-Lean's `UPred.satisfiable`.

The predicate adequacy uses is `iPropSatLcAtFrame F E`:
`(iPropSatLcAtFrame F E).sat P ↔ iPropSat.sat ((∃ x, ●£ₒ x) ∗ ((wsat ∗ ownE E) ∗ (F ∗ P)))`.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.OFE Iris.ProofMode Ordinals
open Relation (TransGen)
open FromMathlib.Relation (ReflTransGen)

universe u v

/-! ## Satisfiability predicates and their laws -/

/-- A satisfiability predicate: monotone, and sound for pure propositions (Transfinite Iris:
`Satisfiable sat`). -/
structure SatPred (GF : BundledGFunctors.{u}) where
  sat : IProp GF → Prop
  mono {P Q : IProp GF} : (P ⊢ Q) → sat P → sat Q
  elim {φ : Prop} : sat iprop(⌜φ⌝) → φ

section Classes

variable {GF : BundledGFunctors.{u}}

/-- Satisfiability commutes with `▷` (Transfinite Iris: `SatisfiableLater`). -/
class SatLater (S : SatPred GF) : Prop where
  later {P : IProp GF} : S.sat iprop(▷ P) → S.sat P

/-- Satisfiability eliminates basic updates (Transfinite Iris: `SatisfiableBUpd`). -/
class SatBUpd (S : SatPred GF) : Prop where
  bupd {P : IProp GF} : S.sat iprop(|==> P) → S.sat P

/-- The existential property over `X` (Transfinite Iris: `SatisfiableExists X`). -/
class SatExists (S : SatPred GF) (X : Type v) : Prop where
  exists_ {Φ : X → IProp GF} : S.sat iprop(∃ x, Φ x) → ∃ x, S.sat (Φ x)

/-- Satisfiability eliminates relational updates. -/
@[lantana_alias SatisfiableRUpd]
class SatRUpd {X : Type v} [RUpdG GF X] (S : SatPred GF) : Prop where
  rupd {P : IProp GF} : S.sat iprop(|==>r P) → S.sat P

attribute [lantana_alias sat_rupd] SatRUpd.rupd

/-- Satisfiability allows updating the (framed) relational-update supply. -/
@[lantana_alias SatisfiableRUpdUpdate]
class SatRUpdUpdate {X : Type v} [RUpdG GF X] (S : SatPred GF) : Prop where
  pred_upd {P Q : IProp GF} : (∀ x : X, RUpdG.pred x ⊢ |==> ∃ y : X, RUpdG.pred y ∗ Q) →
    S.sat P → S.sat iprop(P ∗ Q)

attribute [lantana_alias sat_pred_upd] SatRUpdUpdate.pred_upd

/-- A mask-indexed family of satisfiability predicates (Rocq: `sat_at : coPset → iProp Σ → Prop`). -/
abbrev SatAt (GF : BundledGFunctors.{u}) := CoPset → SatPred GF

/-- Satisfiability eliminates fancy updates, changing the mask. -/
@[lantana_alias SatisfiableAtFupd]
class SatFUpd [InvGS GF] (S : SatAt GF) : Prop where
  fupd {E₁ E₂ : CoPset} {P : IProp GF} : (S E₁).sat iprop(|={E₁,E₂}=> P) → (S E₂).sat P

attribute [lantana_alias sat_fupd] SatFUpd.fupd

/-- The laws of a mask-indexed satisfiability predicate. -/
@[lantana_alias SatisfiableAt]
class SatAtLaws [InvGS GF] (S : SatAt GF) : Prop where
  bupd (E : CoPset) : SatBUpd (S E)
  later (E : CoPset) : SatLater (S E)
  fupd : SatFUpd S

attribute [instance] SatAtLaws.bupd SatAtLaws.later SatAtLaws.fupd

attribute [lantana_alias sat_at_bupd] SatAtLaws.bupd
attribute [lantana_alias sat_at_later] SatAtLaws.later
#lantana_ignore sat_at_satisfiable "Every `SatPred` is satisfiable: the laws are its fields."

end Classes

/-! ## Derived laws -/

namespace SatPred

variable {GF : BundledGFunctors.{u}} (S : SatPred GF)

theorem sat_later [SatLater S] {P : IProp GF} : S.sat iprop(▷ P) → S.sat P := SatLater.later

theorem sat_laterN [SatLater S] {P : IProp GF} (n : Nat) : S.sat iprop(▷^[n] P) → S.sat P := by
  induction n with
  | zero => exact id
  | succ n ih => exact fun h => ih (S.sat_later h)

theorem sat_bupd [SatBUpd S] {P : IProp GF} : S.sat iprop(|==> P) → S.sat P := SatBUpd.bupd

theorem sat_exists {X : Type v} [SatExists S X] {Φ : X → IProp GF} :
    S.sat iprop(∃ x, Φ x) → ∃ x, S.sat (Φ x) := SatExists.exists_

theorem sat_or [SatExists S Bool] {P Q : IProp GF} : S.sat iprop(P ∨ Q) → S.sat P ∨ S.sat Q := by
  intro h
  have h' : S.sat iprop(∃ b : Bool, if b then P else Q) :=
    S.mono (or_elim (exists_intro_trans true .rfl) (exists_intro_trans false .rfl)) h
  obtain ⟨b, hb⟩ := S.sat_exists h'
  cases b
  · exact .inr hb
  · exact .inl hb

theorem sat_sep {P Q : IProp GF} : S.sat iprop(P ∗ Q) → S.sat P ∧ S.sat Q :=
  fun h => ⟨S.mono sep_elim_left h, S.mono sep_elim_right h⟩

theorem sat_and {P Q : IProp GF} : S.sat iprop(P ∧ Q) → S.sat P ∧ S.sat Q :=
  fun h => ⟨S.mono and_elim_l h, S.mono and_elim_r h⟩

theorem sat_pure_sep {φ : Prop} {P : IProp GF} : S.sat iprop(⌜φ⌝ ∗ P) → φ ∧ S.sat P :=
  fun h => ⟨S.elim (S.sat_sep h).1, (S.sat_sep h).2⟩

theorem sat_forall {X : Sort _} (x : X) {Φ : X → IProp GF} : S.sat iprop(∀ x, Φ x) → S.sat (Φ x) :=
  S.mono (forall_elim x)

theorem sat_impl {P Q : IProp GF} (h : S.sat iprop(P → Q)) (hP : True ⊢ P) : S.sat Q :=
  S.mono ((and_intro (true_intro.trans hP) .rfl).trans imp_elim_right) h

theorem sat_wand {P Q : IProp GF} (h : S.sat iprop(P -∗ Q)) (hP : True ⊢ P) : S.sat Q :=
  S.mono (true_sep_mpr.trans ((sep_mono_left hP).trans wand_elim_right)) h

theorem sat_pers {P : IProp GF} : S.sat iprop(<pers> P) → S.sat P :=
  S.mono persistently_elim

theorem sat_intuitionistically {P : IProp GF} : S.sat iprop(□ P) → S.sat P :=
  S.mono intuitionistically_elim

theorem sat_false : ¬S.sat iprop(False) :=
  fun h => S.elim (S.mono (false_elim (P := iprop(⌜False⌝))) h)

end SatPred

/-! ## The satisfiability of the model -/

section IPropSat

variable {GF : BundledGFunctors.{u}}

/-- The satisfiability of the model: at every step index, `P` holds for some valid resource
(Transfinite Iris: `iProp_sat`). -/
def iPropSat : SatPred GF where
  sat := UPred.satisfiable
  mono h hs := UPred.satisfiable_mono hs h
  elim h := UPred.pure_soundness (UPred.satisfiable_elim h)

theorem iPropSat_intro : (iPropSat (GF := GF)).sat iprop(True) :=
  UPred.satisfiable_intro .rfl

instance iPropSat_later : SatLater (iPropSat (GF := GF)) where
  later := UPred.satisfiable_later

instance iPropSat_bupd : SatBUpd (iPropSat (GF := GF)) where
  bupd := UPred.satisfiable_bupd

/-- The existential property of the model, for types small enough for the step index. -/
instance iPropSat_exists {X : Type v} [SIdxLarge SI X] : SatExists (iPropSat (GF := GF)) X where
  exists_ h := UPred.satisfiable_exists h

/-- Finite existentials hold for every type of step indices. -/
instance (priority := high) iPropSat_exists_bool : SatExists (iPropSat (GF := GF)) Bool where
  exists_ h := UPred.satisfiable_finite_exists (Q := fun _ => True) [true, false]
    (fun b _ => by cases b <;> simp) (fun _ => pure_intro trivial) h

end IPropSat

/-! ## Framing -/

section Frame

variable {GF : BundledGFunctors.{u}}

/-- Satisfiability framed with `F` (Transfinite Iris: `sat_frame`). -/
def satFrame (S : SatPred GF) (F : IProp GF) : SatPred GF where
  sat P := S.sat iprop(F ∗ P)
  mono h := S.mono (sep_mono_right h)
  elim h := S.elim (S.mono sep_elim_right h)

variable {S : SatPred GF} {F : IProp GF}

theorem satFrame_sat {P : IProp GF} : (satFrame S F).sat P ↔ S.sat iprop(F ∗ P) := .rfl

instance satFrame_later [SatLater S] : SatLater (satFrame S F) where
  later h := S.sat_later (S.mono ((sep_mono_left later_intro).trans later_sep_2) h)

instance satFrame_bupd [SatBUpd S] : SatBUpd (satFrame S F) where
  bupd h := S.sat_bupd (S.mono bupd_frame_left h)

instance satFrame_exists {X : Type v} [SatExists S X] : SatExists (satFrame S F) X where
  exists_ h := S.sat_exists (S.mono sep_exists_left.mp h)

@[lantana_alias sat_frame_rupd]
instance satFrame_rupd {X : Type v} [RUpdG GF X] [SatRUpd S] : SatRUpd (satFrame S F) where
  rupd h := SatRUpd.rupd (S := S) (S.mono rupd_frame_l h)

@[lantana_alias sat_frame_rupd_update]
instance satFrame_rupdUpdate {X : Type v} [RUpdG GF X] [SatRUpdUpdate S] :
    SatRUpdUpdate (satFrame S F) where
  pred_upd hup h := S.mono sep_assoc.mp (SatRUpdUpdate.pred_upd hup h)

theorem sat_frame_move {P : IProp GF} : (satFrame S F).sat P ↔ (satFrame S iprop(emp)).sat iprop(F ∗ P) :=
  ⟨S.mono emp_sep.mpr, S.mono emp_sep.mp⟩

theorem sat_sat_frame {P : IProp GF} : (satFrame S iprop(emp)).sat P ↔ S.sat P :=
  ⟨S.mono emp_sep.mp, S.mono emp_sep.mpr⟩

end Frame

/-! ## Eliminating relational updates -/

section RUpd

variable {GF : BundledGFunctors.{u}} {X : Type v} [RUpdG GF X]

/-- If `|==>r P` is satisfiable with the supply `x`, then `P` is satisfiable with a smaller
supply. This lifts the existential quantifier over the supply out of the logic, by the
existential property of the model. -/
@[lantana_alias rupd_satisfiable]
theorem rupd_satisfiable (S : SatPred GF) [SatLater S] [SatBUpd S] [SatExists S X]
    [SatExists S Bool] {P : IProp GF} (x : X) :
    S.sat iprop(RUpdG.pred x ∗ |==>r P) →
      ∃ x', ReflTransGen (RUpdG.rel GF) x' x ∧ S.sat iprop(RUpdG.pred x' ∗ P) := by
  induction (WellFounded.transGen (RUpdG.rel_wf (GF := GF))).apply x with
  | intro x _ ih =>
  intro hsat
  have hsat' := S.mono (Q := iprop(|==> ∃ x' : X,
      (⌜ReflTransGen (RUpdG.rel GF) x' x⌝ ∗ RUpdG.pred x' ∗ P) ∨
      ▷ (⌜TransGen (RUpdG.rel GF) x' x⌝ ∗ RUpdG.pred x' ∗ |==>r P))) ?_ hsat
  · obtain ⟨x', hx'⟩ := S.sat_exists (S.sat_bupd hsat')
    rcases S.sat_or hx' with h | h
    · obtain ⟨hrtc, h⟩ := S.sat_pure_sep h
      exact ⟨x', hrtc, h⟩
    · obtain ⟨htc, h⟩ := S.sat_pure_sep (S.sat_later h)
      obtain ⟨x'', hrtc, h⟩ := ih x' htc h
      exact ⟨x'', hrtc.trans (FromMathlib.Relation.TransGen.to_reflTransGen htc), h⟩
  · iintro ⟨Hpr, Hupd⟩
    imod rupd_unfold.mp $$ Hupd %x Hpr with (⟨Hpr, HP⟩ | ⟨%x', %hx', Hpr, HP⟩)
    · imodintro
      iexists x
      ileft
      isplitr
      · ipureintro; exact .refl
      iframe
    · imodintro
      iexists x'
      iright
      inext
      isplitr
      · ipureintro; exact hx'
      iframe

/-- Satisfiability framed with some supply (Rocq: `sat_lc`). -/
@[lantana_alias sat_lc]
abbrev satLc (S : SatPred GF) : SatPred GF := satFrame S iprop(∃ x : X, RUpdG.pred x)

variable {S : SatPred GF}

@[lantana_alias sat_lc_satisfiable_rupd]
instance satLc_rupd [SatLater S] [SatBUpd S] [SatExists S X] [SatExists S Bool] :
    SatRUpd (satLc (X := X) S) where
  rupd {P} h := by
    have h := S.mono (Q := iprop(∃ x : X, RUpdG.pred x ∗ |==>r P)) sep_exists_right.mp h
    obtain ⟨x, h⟩ := S.sat_exists h
    obtain ⟨x', _, h⟩ := rupd_satisfiable S x h
    exact S.mono (sep_mono_left (exists_intro x')) h

@[lantana_alias sat_lc_satisfiable_rupd_update]
instance satLc_rupdUpdate [SatBUpd S] : SatRUpdUpdate (satLc (X := X) S) where
  pred_upd {P Q} hup h := by
    refine S.sat_bupd (S.mono ?_ h)
    iintro ⟨⟨%x, Hpr⟩, HP⟩
    imod hup x $$ Hpr with ⟨%y, Hpr, HQ⟩
    imodintro
    isplitl [Hpr]
    · iexists y
      iexact Hpr
    iframe

end RUpd

section Tlc

variable {GF : BundledGFunctors.{u}} [TlcGS GF]

/-- `rupd_satisfiable` for transfinite later credits. -/
theorem rupd_satisfiable_tlc (S : SatPred GF) [SatLater S] [SatBUpd S]
    [SatExists S Ordinal.{1}] [SatExists S Bool] {P : IProp GF} (x : Ordinal.{1}) :
    S.sat iprop(●£ₒ x ∗ |==>r P) → ∃ x', ReflTransGen (· < ·) x' x ∧ S.sat iprop(●£ₒ x' ∗ P) :=
  rupd_satisfiable S x

end Tlc

/-! ## Eliminating the allocation modality -/

section ALC

variable {GF : BundledGFunctors.{u}} {A : Type v} [UCMRA A] [CreditGS GF A] [CreditCamera A]


theorem supply_alloc_unit (x : A) {z : A} :
    ●£ₒ z ⊢@{IProp GF} |==> (●£ₒ (x • z) ∗ £ₒ (x • UORA.unit)) := by
  unfold supply credit
  iintro H
  imod iOwn_update (Auth.auth_update_alloc (LocalUpdate.op_discrete z UORA.unit x
    fun _ => CreditCamera.valid_trivial _)) $$ H with H
  icases iOwn_op $$ H with ⟨Hs, Hc⟩
  imodintro
  iframe

/-- Allocate new credits `x`, increasing the supply. -/
theorem supply_alloc (x : A) {z : A} : ●£ₒ z ⊢@{IProp GF} |==> (●£ₒ (x • z) ∗ £ₒ x) := by
  iintro H
  imod supply_alloc_unit x $$ H with ⟨Hs, Hc⟩
  icases credit_split.mp $$ Hc with ⟨Hc, -⟩
  imodintro
  iframe

/-- Satisfiability eliminates `ALC`: the credits it asks for are added to the supply. -/
@[lantana_alias sat_ALC]
theorem sat_ALC {S : SatPred GF} [SatRUpd S] [SatRUpdUpdate S] [SatExists S A] {P : IProp GF} :
    S.sat (ALC P) → S.sat P := by
  intro h
  obtain ⟨x, h⟩ := S.sat_exists h
  have h := SatRUpdUpdate.pred_upd (X := A) (S := S) (Q := £ₒ x) (fun z => ?_) h
  · exact SatRUpd.rupd (X := A) (S := S) (S.mono wand_elim_left h)
  · iintro Hz
    imod supply_alloc x $$ Hz with ⟨Hs, Hc⟩
    imodintro
    iexists x • z
    iframe

theorem sat_ALCb {S : SatPred GF} [SatRUpd S] [SatRUpdUpdate S] [SatExists S A] {b : Bool}
    {P : IProp GF} : S.sat (ALCb b P) → S.sat P := by
  cases b
  · exact id
  · exact sat_ALC

end ALC

/-! ## Satisfiability with masks -/

section SatAt

variable {GF : BundledGFunctors.{u}} [InvGS GF]

/-- Satisfiability framed with world satisfaction and the mask `E` (Rocq: `sat_at`). -/
@[lantana_alias sat_at]
abbrev satAt (S : SatPred GF) : SatAt GF := fun E => satFrame S iprop(wsat ∗ ownE E)

variable {S : SatPred GF}

@[lantana_alias sat_at_satisfiable_at_fupd]
instance satAt_fupd [SatRUpd S] [SatLater S] : SatFUpd (satAt S) where
  fupd {E₁ E₂ P} h := by
    refine S.sat_later (SatRUpd.rupd (X := Ordinal.{1}) (S := S) (S.mono ?_ h))
    iintro ⟨⟨Hw, HE⟩, HP⟩
    ihave HP := fupd_unfold.mp $$ HP
    imod HP $$ [Hw HE] with HP
    · iframe
    imodintro
    iapply except0_into_later
    imod HP with ⟨Hw, HE, HP⟩
    imodintro
    iframe

@[lantana_alias sat_at_satisfiable_at_bupd]
instance satAt_bupd [SatRUpd S] (E : CoPset) : SatBUpd (satAt S E) where
  bupd h := SatRUpd.rupd (X := Ordinal.{1}) (S := S) (S.mono (bupd_frame_left.trans bupd_rupd) h)

@[lantana_alias sat_at_satisfiable_at]
instance satAt_laws [SatRUpd S] [SatLater S] : SatAtLaws (satAt S) where
  bupd _ := inferInstance
  later _ := inferInstance
  fupd := inferInstance

/-- A mask-indexed satisfiability predicate framed with `F` (Rocq: `sat_at_frame`). -/
@[lantana_alias sat_at_frame]
abbrev satAtFrame (S : SatAt GF) (F : IProp GF) : SatAt GF := fun E => satFrame (S E) F

@[lantana_alias sat_at_frame_satisfiable_at_fupd]
instance satAtFrame_fupd {S : SatAt GF} [SatFUpd S] {F : IProp GF} : SatFUpd (satAtFrame S F) where
  fupd h := SatFUpd.fupd (S := S) ((S _).mono fupd_frame_left h)

@[lantana_alias sat_at_frame_satisfiable_at]
instance satAtFrame_laws {S : SatAt GF} [SatAtLaws S] {F : IProp GF} :
    SatAtLaws (satAtFrame S F) where
  bupd _ := inferInstance
  later _ := inferInstance
  fupd := inferInstance

end SatAt

/-! ## The satisfiability used by adequacy -/

section IPropSatLc

variable {GF : BundledGFunctors.{u}}

/-- The model's satisfiability framed with some credit supply (Rocq: `iProp_sat_lc`). -/
abbrev iPropSatLc {X : Type v} [RUpdG GF X] : SatPred GF := satLc (X := X) iPropSat

variable [InvGS GF]

/-- ... and with world satisfaction and an enabled mask (Rocq: `iProp_sat_lc_at`). -/
abbrev iPropSatLcAt : SatAt GF := satAt iPropSatLc

/-- ... and with a frame `F` (Rocq: `iProp_sat_lc_at_frame`). -/
abbrev iPropSatLcAtFrame (F : IProp GF) : SatAt GF := satAtFrame iPropSatLcAt F

theorem iPropSatLcAtFrame_sat {F : IProp GF} {E : CoPset} {P : IProp GF} :
    (iPropSatLcAtFrame F E).sat P ↔
      iPropSat.sat iprop((∃ x : Ordinal.{1}, ●£ₒ x) ∗ ((wsat ∗ ownE E) ∗ (F ∗ P))) := .rfl

@[lantana_alias iProp_sat_lc_and]
theorem iProp_sat_lc_and {P Q : IProp GF} :
    (iPropSatLc (X := Ordinal.{1})).sat iprop(P ∧ Q) →
      (iPropSatLc (X := Ordinal.{1})).sat P ∧ (iPropSatLc (X := Ordinal.{1})).sat Q :=
  SatPred.sat_and _

@[lantana_alias iProp_sat_lc_at_and]
theorem iProp_sat_lc_at_and {E : CoPset} {P Q : IProp GF} :
    (iPropSatLcAt E).sat iprop(P ∧ Q) → (iPropSatLcAt E).sat P ∧ (iPropSatLcAt E).sat Q :=
  SatPred.sat_and _

@[lantana_alias iProp_sat_lc_at_frame_and]
theorem iProp_sat_lc_at_frame_and {E : CoPset} {F P Q : IProp GF} :
    (iPropSatLcAtFrame F E).sat iprop(P ∧ Q) →
      (iPropSatLcAtFrame F E).sat P ∧ (iPropSatLcAtFrame F E).sat Q :=
  SatPred.sat_and _

end IPropSatLc

end Lantana
