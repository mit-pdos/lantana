/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

The section `ConstOF` is adapted from the `constOF` instances of Iris-Lean's `Iris.Algebra.OFE`
and `Iris.Algebra.CMRA`, whose headers read:
  Copyright (c) The Iris-Lean Contributors
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Mario Carneiro, Sebastian Graf, Sergei Stepanenko, Markus de Medeiros (`OFE`);
  Mario Carneiro, Сухарик (@suhr), Markus de Medeiros, Puming Liu (`CMRA`)
Modified by the Lantana-Lean Contributors (universe-polymorphic `constOFP`).
-/
module

public import Lantana.BaseLogic.RUpd
public import Iris.Algebra.Auth
public import Iris.Algebra.OrdinalCamera

/-! # Transfinite later credits `£ₒ α`

A generic theory of credits for relational updates (Rocq: `lantana/base_logic/later_credits.v`,
after the artifact of "Later Credits", Spies et al. 2022), the allocation modality `ALC`, and the
instance with ordinals (camera operation the natural sum `+ₕ`).

The credits of a discrete camera `A` with a well-founded relation `rel` (`CreditCamera A`) live
in an authoritative camera `Auth A` in a ghost slot (`CreditGpreS`, `CreditGS`): `●£ₒ a` is the
total supply and `£ₒ a` are credits. Spending credits along `rel` eliminates a later in front of a
relational update (`auth_rupd_step`).

The notations are `£ₒ α` and `£ₙ n` (decision D29): Iris-Lean's global `£ n` is reserved for its
`Nat` credits. The credit type is an `outParam` of `CreditGS`, so that `ALC P` finds it from the
ghost state in scope; `credit`, `supply` and `ALC` take their camera instance as an implicit
argument (`{_ : UCMRA A}`), determined by the `CreditGS` instance.

Transfinite later credits (`TlcGS`) are over `Ordinal.{1}` itself, with the camera of
`NatOrdinal` (operation `+ₕ`) as a scoped instance, as Iris-Lean's `Credit` camera on `Nat` is
scoped. With the type synonym `NatOrdinal.{1}` as the credit type, `£ₒ α` for `α : Ordinal.{1}`
elaborates to `credit (A := Ordinal) α` (the types are defeq) while lemma instances give
`credit (A := NatOrdinal) α`, and the proof mode does not identify the two.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.OFE Iris.COFE Iris.ProofMode Auth
open Relation (TransGen)

universe u v

/-! ## A universe-polymorphic constant functor -/

section ConstOF

variable {B : Type v}

/-- The constant functor on `B`, for `B` in any universe. Iris-Lean's `constOF` takes `B : Type`;
the ordinal credits live in `Type 2`. A candidate for upstreaming. -/
abbrev constOFP (B : Type v) : OFunctorPre := fun _ _ _ _ => B

instance constOFP_oFunctor [COFE B] : OFunctor (constOFP B) where
  ofe := _
  map _ _ := ⟨id, OFE.id_ne⟩
  map_ne := by intros; constructor; simp
  map_id := by simp
  map_comp := by simp

instance constOFP_oFunctorContractive [COFE B] : OFunctorContractive (constOFP B) where
  map_contractive.1 := by simp [OFunctor.map]

instance constOFP_rFunctor [ORA B] : RFunctor (constOFP B) where
  cmra := inferInstance
  map _ _ := (ORA.Hom.id : B -C> B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

instance constOFP_rFunctorAffine [ORA B] [IncOrd B] : RFunctorAffine (constOFP B) where
  affine := inferInstance

instance constOFP_rFunctorContractive [ORA B] : RFunctorContractive (constOFP B) where
  map_contractive.1 := fun _ => .rfl

instance constOFP_uRFunctor [UORA B] : URFunctor (constOFP B) where
  cmra := inferInstance
  map _ _ := (ORA.Hom.id : B -C> B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

instance constOFP_uRFunctorContractive [UORA B] : URFunctorContractive (constOFP B) where
  map_contractive.1 _ := .rfl

end ConstOF

/-! ## Credit cameras and their ghost state -/

/-- A camera of credits: discrete, cancellative, all elements valid, with a well-founded
relation `rel` (spending credits decreases the supply along it) that is compatible with framing,
and a successor `next`. -/
@[lantana_alias auth_rupd]
class CreditCamera (A : Type v) [UCMRA A] extends toCMRADiscrete : ORA.Discrete A where
  rel : A → A → Prop
  next : A → A
  rel_wf : WellFounded rel
  rel_frame {a a' : A} (f : A) : rel a' a → rel (a' • f) (a • f)
  op_cancel {a f f' : A} : a • f = a • f' → f = f'
  next_step (x : A) : rel x (next x)
  valid_trivial (x : A) : ✓ x

attribute [lantana_alias auth_rupd_rel] CreditCamera.rel
attribute [lantana_alias auth_rupd_next] CreditCamera.next
attribute [lantana_alias auth_rupd_rel_wf] CreditCamera.rel_wf
attribute [lantana_alias auth_rupd_rel_frame] CreditCamera.rel_frame
attribute [lantana_alias auth_rupd_op_cancel] CreditCamera.op_cancel
attribute [lantana_alias auth_rupd_next_step] CreditCamera.next_step
attribute [lantana_alias auth_valid_trivial] CreditCamera.valid_trivial

#lantana_ignore auth_rupd_discrete "The parent structure `ORA.Discrete` of `CreditCamera`."
#lantana_ignore auth_rupd_rel_proper "The OFE of a discrete camera is Leibniz."

@[lantana_alias auth_rupd_rel_irrefl]
theorem CreditCamera.rel_irrefl {A : Type v} [UCMRA A] [CreditCamera A] (x : A) :
    ¬CreditCamera.rel x x := by
  induction (CreditCamera.rel_wf (A := A)).apply x with
  | intro x _ ih => exact fun h => ih x h h

#lantana_ignore type_inj_existential "`SIdxLarge SI X` is an instance for every `X : Type ≤ 3`."
#lantana_ignore rupd_type_exists_finite "Finite existentials are theorems of Iris-Lean (`SIdx`)."

/-- The functor of the credit ghost state. -/
abbrev CreditF (A : Type v) [UCMRA A] : OFunctorPre := AuthURF (constOFP A)

/-- `GF` contains the credit ghost state over `A`. For `A` outside `Type`, the slot is
`ULiftOF.{w} (CreditF A)` and the instance `(ElemG.ofEq τ h).ofLift` (see `LantanaTest.Credits`). -/
@[lantana_alias auth_rupd_GpreS]
class CreditGpreS (GF : BundledGFunctors.{u}) (A : Type v) [UCMRA A] where
  elem : ElemG GF (CreditF A)

attribute [reducible, instance] CreditGpreS.elem

/-- The credit ghost state over `A` is allocated at the name `name`. The credit type is an
`outParam`: a world has one credit type. -/
@[lantana_alias auth_rupdGS]
class CreditGS (GF : BundledGFunctors.{u}) (A : outParam (Type v)) [UCMRA A]
    extends CreditGpreS GF A where
  name : GName

attribute [lantana_alias auth_rupd_name] CreditGS.name

#lantana_ignore «auth_rupdΣ» "Superseded by `CreditGpreS` on a closed `BundledGFunctors`."
#lantana_ignore «subG_auth_rupdΣ» "Superseded by `ElemG` synthesis."

section Defs

/-- The total supply of credits is `a` (Rocq: `rupdA`). -/
@[lantana_alias rupdA]
def supply {GF : BundledGFunctors.{u}} {A : Type v} {_ : UCMRA A} [G : CreditGS GF A] (a : A) :
    IProp GF :=
  iOwn (E := G.elem) G.name (● a)

/-- The credits `a` (Rocq: `rupdF`). -/
@[lantana_alias rupdF]
def credit {GF : BundledGFunctors.{u}} {A : Type v} {_ : UCMRA A} [G : CreditGS GF A] (a : A) :
    IProp GF :=
  iOwn (E := G.elem) G.name (◯ a)

/-- Credits (Rocq: `£ a`). -/
scoped notation:max "£ₒ " a:40 => credit a
/-- The total supply of credits (Rocq: `●£ a`). -/
scoped notation:max "●£ₒ " a:40 => supply a

/-- The relational update of the credits: the predicate is the supply. -/
@[lantana_alias auth_rupdGS_instance]
instance CreditGS.rupdG {GF : BundledGFunctors.{u}} {A : Type v} {_ : UCMRA A} [CreditGS GF A]
    [CreditCamera A] : RUpdG GF A where
  pred := supply
  rel := CreditCamera.rel
  rel_wf := CreditCamera.rel_wf

end Defs

section Credits

variable {GF : BundledGFunctors.{u}} {A : Type v} [UCMRA A] [CreditGS GF A] [CreditCamera A]

omit [CreditCamera A] in
instance credit_timeless {a : A} : Timeless (£ₒ a : IProp GF) := by
  unfold credit; exact iOwn_timeless

theorem rupdG_pred_eq (x : A) : RUpdG.pred x = (●£ₒ x : IProp GF) := rfl

theorem rupdG_rel_eq : RUpdG.rel GF = CreditCamera.rel (A := A) := rfl

omit [CreditGS GF A] in
/-- Decreasing the credits `b` to `b'` also decreases the total supply `a`. -/
@[lantana_alias auth_rupd_rel_update]
theorem auth_rupd_rel_update {a b b' : A} (hb : b ≼ a) (h : CreditCamera.rel b' b) :
    ∃ a', (a, b) ~l~> (a', b') ∧ CreditCamera.rel a' a := by
  obtain ⟨f, rfl⟩ := hb
  refine ⟨b' • f, discrete_unital_triv_local_update CreditCamera.valid_trivial fun hz => ?_,
    CreditCamera.rel_frame f h⟩
  rw [CreditCamera.op_cancel hz]

/-- Spending the credits `a` down to `a'` decreases the supply along `rel`. -/
theorem supply_credit_step {x a a' : A} (h : CreditCamera.rel a' a) :
    ●£ₒ x ∗ £ₒ a ⊢@{IProp GF} |==> ∃ x', ⌜CreditCamera.rel x' x⌝ ∗ ●£ₒ x' ∗ £ₒ a' := by
  unfold supply credit
  refine iOwn_op.mpr.trans <| iOwn_valid_r.trans <|
    (sep_mono_right (UPred.discrete_valid _).mp).trans ?_
  iintro ⟨H, %hv⟩
  obtain ⟨x', hl, hx⟩ := auth_rupd_rel_update (auth_both_valid_discrete.mp hv).1 h
  imod iOwn_update (auth_update hl) $$ H with H
  icases iOwn_op $$ H with ⟨Hs, Hc⟩
  imodintro
  iexists x'
  isplitr
  · ipureintro; exact hx
  isplitl [Hs]
  · iexact Hs
  · iexact Hc

/-- Spending the credits `a` down to `a'` eliminates a later in front of the goal. -/
@[lantana_alias auth_rupd_step]
theorem auth_rupd_step {a a' : A} {P : IProp GF} (h : CreditCamera.rel a' a) :
    £ₒ a ∗ (£ₒ a' -∗ ▷ |==>r P) ⊢ |==>r P := by
  refine .trans ?_ rupd_step
  iintro ⟨Hf, H⟩ %x Hx
  imod supply_credit_step h $$ [Hx Hf] with ⟨%x', %hx, Hx, Hf⟩
  · isplitl [Hx]
    · iexact Hx
    · iexact Hf
  imodintro
  iexists x'
  isplitr
  · ipureintro; exact .single hx
  isplitl [Hx]
  · iexact Hx
  · iapply H $$ Hf

@[lantana_alias auth_rupd_weaken]
theorem auth_rupd_weaken {a a' : A} (h : a' = a ∨ CreditCamera.rel a' a) :
    £ₒ a ⊢ (|==>r £ₒ a' : IProp GF) := by
  rcases h with rfl | h
  · exact rupd_intro
  · iintro Hf
    iapply auth_rupd_step h
    isplitl [Hf]
    · iexact Hf
    iintro Hf
    inext
    iapply rupd_intro $$ Hf

omit [CreditCamera A] in
@[lantana_alias rupdF_split]
theorem credit_split {x y : A} : £ₒ (x • y) ⊣⊢ (£ₒ x ∗ £ₒ y : IProp GF) := by
  unfold credit
  rw [frag_op]
  exact iOwn_op

#lantana_ignore rupdF_equiv "The OFE of a discrete camera is Leibniz; use equality."

omit [CreditCamera A] in
theorem credit_unit : ⊢@{IProp GF} |==> £ₒ (UORA.unit : A) := by
  unfold credit
  exact iOwn_unit (F := CreditF A) (ε := (UORA.unit : Auth A))

end Credits

/-! ## The allocation modality -/

section Allocation

/-- `ALC P` allocates any number of new credits for the proof of `P` (used in the weakest
precondition). -/
@[lantana_alias ALC]
def ALC {GF : BundledGFunctors.{u}} {A : Type v} {_ : UCMRA A} [CreditGS GF A] [CreditCamera A]
    (P : IProp GF) : IProp GF :=
  iprop(∃ x : A, £ₒ x -∗ |==>r P)

variable {GF : BundledGFunctors.{u}} {A : Type v} [UCMRA A] [CreditGS GF A] [CreditCamera A]

@[lantana_alias ALC_later]
theorem ALC_later {P : IProp GF} : ALC P ⊣⊢ ALC iprop(▷ P) := by
  unfold ALC
  constructor
  · iintro ⟨%x, H⟩
    iexists x
    iintro Hx
    iapply rupd_mono later_intro $$ (H $$ Hx)
  · iintro ⟨%x, H⟩
    iexists x • CreditCamera.next (UORA.unit : A)
    iintro Hx
    icases credit_split.mp $$ Hx with ⟨Hx, Hn⟩
    imod H $$ Hx with HP
    iapply auth_rupd_step (CreditCamera.next_step _)
    isplitl [Hn]
    · iexact Hn
    iintro _
    inext
    iapply rupd_intro $$ HP

@[lantana_alias ALC_rupd]
theorem ALC_rupd {P : IProp GF} : ALC P ⊣⊢ ALC iprop(|==>r P) := by
  unfold ALC
  constructor
  · iintro ⟨%x, H⟩
    iexists x
    iintro Hx
    iapply rupd_intro $$ (H $$ Hx)
  · iintro ⟨%x, H⟩
    iexists x
    iintro Hx
    iapply rupd_trans $$ (H $$ Hx)

@[lantana_alias ALC_bupd]
theorem ALC_bupd {P : IProp GF} : ALC P ⊣⊢ ALC iprop(|==> P) := by
  unfold ALC
  constructor
  · iintro ⟨%x, H⟩
    iexists x
    iintro Hx
    imod H $$ Hx with HP
    imodintro
    imodintro
    iexact HP
  · iintro ⟨%x, H⟩
    iexists x
    iintro Hx
    iapply rupd_bupd_r $$ (H $$ Hx)

@[lantana_alias ALC_credits]
theorem ALC_credits (x : A) {P : IProp GF} : ALC P ⊣⊢ ALC iprop(£ₒ x -∗ P) := by
  unfold ALC
  constructor
  · iintro ⟨%y, H⟩
    iexists y
    iintro Hy
    imod H $$ Hy with HP
    imodintro
    iintro _
    iexact HP
  · iintro ⟨%y, H⟩
    iexists x • y
    iintro Hxy
    icases credit_split.mp $$ Hxy with ⟨Hx, Hy⟩
    imod H $$ Hy with HP
    imodintro
    iapply HP $$ Hx

@[lantana_alias ALC_fmap]
theorem ALC_fmap {P Q : IProp GF} : ALC iprop(P -∗ Q) ⊢ ALC P -∗ ALC Q := by
  unfold ALC
  iintro ⟨%x1, HPQ⟩ ⟨%x2, HP⟩
  iexists x1 • x2
  iintro Hx
  icases credit_split.mp $$ Hx with ⟨Hx1, Hx2⟩
  imod HP $$ Hx2 with HP
  imod HPQ $$ Hx1 with HPQ
  imodintro
  iapply HPQ $$ HP

@[lantana_alias ALC_intro]
theorem ALC_intro {P : IProp GF} : P ⊢ ALC P := by
  unfold ALC
  iintro HP
  iexists UORA.unit
  iintro _
  imodintro
  iexact HP

@[lantana_alias ALC_alloc]
theorem ALC_alloc (x : A) {P : IProp GF} : (£ₒ x -∗ |==>r P) ⊢ ALC P :=
  ALC_intro.trans <| ALC_credits x |>.mpr.trans ALC_rupd.mpr

@[lantana_alias ALC_wand]
theorem ALC_wand {P Q : IProp GF} : (P -∗ Q) ⊢ ALC P -∗ ALC Q :=
  ALC_intro.trans ALC_fmap

@[lantana_alias ALC_mono]
theorem ALC_mono {P Q : IProp GF} (h : P ⊢ Q) : ALC P ⊢ ALC Q :=
  wand_entails <| (entails_wand h).trans ALC_wand

#lantana_ignore ALC_ent_proper "Subsumed by `ALC_mono`."
#lantana_ignore ALC_flip_ent_proper "Subsumed by `ALC_mono`."
#lantana_ignore ALC_equiv_proper "Subsumed by the `NonExpansive` instance `ALC_ne`."

@[lantana_alias ALC_ne]
instance ALC_ne : NonExpansive (ALC (GF := GF) (A := A)) where
  ne {_ _ _} H := exists_ne fun _ => wand_ne.ne .rfl (rupd_ne.ne H)

@[lantana_alias ALC_contractive]
instance ALC_contractive : Contractive (ALC (GF := GF) (A := A)) where
  distLater_dist {_ _ _} H :=
    (equiv_iff.mpr ALC_later).dist.trans <| .trans (ALC_ne.ne (Contractive.distLater_dist H))
      (equiv_iff.mpr ALC_later).dist.symm

@[lantana_alias from_modal_ALC]
instance fromModal_ALC {io} {P : IProp GF} : FromModal io modality_id True (ALC P) (ALC P) P where
  from_modal _ := ALC_intro

@[lantana_alias from_pure_ALC]
instance fromPure_ALC {a io φ} {P : IProp GF} [h : FromPure a P io φ] :
    FromPure a (ALC P) io φ where
  from_pure := h.1.trans ALC_intro

@[lantana_alias elim_rupd_ALC]
instance elimModal_ALC {p io} {P Q : IProp GF} :
    ElimModal True p io false (ALC P) P (ALC Q) Q where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    sep_comm.mp.trans <| (sep_mono_left ALC_wand).trans wand_elim_left

@[lantana_alias frame_ALC]
instance frame_ALC {p} {R P Q : IProp GF} [h : Frame p R P Q] : Frame p R (ALC P) (ALC Q) where
  frame := (sep_mono_left ((wand_intro h.frame).trans ALC_wand)).trans wand_elim_left

@[lantana_alias into_wand_ALC]
instance intoWand_ALC {m} {R P Q : IProp GF} [h : IntoWand false false R m P Q] :
    IntoWand false false (ALC R) m (ALC P) (ALC Q) where
  into_wand := (ALC_mono h.into_wand).trans ALC_fmap

end Allocation

/-- Allocate the credit ghost state with `k` credits. -/
@[lantana_alias auth_rupd_alloc]
theorem credit_alloc {GF : BundledGFunctors.{u}} {A : Type v} [UCMRA A] [CreditCamera A]
    [G : CreditGpreS GF A] (k : A) :
    ⊢@{IProp GF} |==> ∃ _ : CreditGS GF A, ●£ₒ k ∗ £ₒ k := by
  imod iOwn_alloc (E := G.elem) ((● k) • (◯ k))
    (auth_both_valid_discrete.mpr ⟨ORA.inc_refl k, CreditCamera.valid_trivial k⟩)
    with ⟨%γ, H⟩
  icases iOwn_op $$ H with ⟨Hs, Hc⟩
  iexists { elem := G.elem, name := γ }
  imodintro
  unfold supply credit
  iframe

/-! ## Transfinite later credits -/

section Ordinal

open Ordinals Ordinal

/-- Ordinals with the natural sum are a credit camera. -/
instance instCreditCameraNatOrdinal : CreditCamera NatOrdinal.{u} where
  rel := (· < ·)
  next := succ
  rel_wf := Ordinal.lt_wf
  rel_frame f h := nadd_lt_nadd_right h f
  op_cancel h := NatOrdinal.add_left_cancel _ h
  next_step := lt_succ
  valid_trivial := NatOrdinal.valid

/-! The credit camera on `Ordinal` itself is the camera of `NatOrdinal`: its operation is the
natural sum `+ₕ`, not `+`. Scoped, as Iris-Lean's `Credit` camera on `Nat` is. -/

scoped instance instCOFEOrdinal : COFE Ordinal.{u} := inferInstanceAs (COFE NatOrdinal.{u})
scoped instance instOFEDiscreteOrdinal : OFE.Discrete Ordinal.{u} :=
  inferInstanceAs (OFE.Discrete NatOrdinal.{u})
scoped instance instUCMRAOrdinal : UCMRA Ordinal.{u} := inferInstanceAs (UCMRA NatOrdinal.{u})
scoped instance instCMRADiscreteOrdinal : ORA.Discrete Ordinal.{u} :=
  inferInstanceAs (ORA.Discrete NatOrdinal.{u})
scoped instance instCreditCameraOrdinal : CreditCamera Ordinal.{u} :=
  inferInstanceAs (CreditCamera NatOrdinal.{u})

theorem ordinal_op_eq (a b : Ordinal.{u}) : Op.op a b = a +ₕ b := rfl

theorem ordinal_unit_eq : (UORA.unit : Ordinal.{u}) = 0 := rfl

/-- Transfinite later credits: the credit ghost state over `Ordinal.{1}` (Rocq: `tlcGS`). -/
abbrev TlcGS (GF : BundledGFunctors.{u}) := CreditGS GF Ordinal.{1}
/-- Rocq: `tlcGpreS`. -/
abbrev TlcGpreS (GF : BundledGFunctors.{u}) := CreditGpreS GF Ordinal.{1}

/-- `n` credits, for a natural number `n` (Rocq: `£n n`). -/
scoped notation:max "£ₙ " n:40 => £ₒ (Ordinals.Ordinal.ofNat n)

variable {GF : BundledGFunctors.{u}} [TlcGS GF]

#lantana_ignore tlc_equiv "The ordinals are a quotient with Leibniz equality; use equality."

@[lantana_alias tlc_split]
theorem tlc_split {α β : Ordinal.{1}} : £ₒ (α +ₕ β) ⊣⊢@{IProp GF} £ₒ α ∗ £ₒ β :=
  credit_split

@[lantana_alias tlc_succ]
theorem tlc_succ {α : Ordinal.{1}} : £ₒ (succ α) ⊣⊢@{IProp GF} £ₙ 1 ∗ £ₒ α := by
  rw [show succ α = ofNat 1 +ₕ α by rw [ofNat_succ, ofNat_zero, succ_nadd, zero_nadd]]
  exact tlc_split

@[lantana_alias tlc_later_strong]
theorem tlc_later_strong {α β : Ordinal.{1}} {P : IProp GF} (h : β < α) :
    £ₒ α ∗ (£ₒ β -∗ ▷ |==>r P) ⊢@{IProp GF} |==>r P :=
  auth_rupd_step h

@[lantana_alias tlc_later]
theorem tlc_later {P : IProp GF} : £ₙ 1 ∗ ▷ (|==>r P) ⊢@{IProp GF} |==>r P := by
  iintro ⟨H1, HP⟩
  iapply tlc_later_strong (α := ofNat 1) (lt_succ 0)
  isplitl [H1]
  · iexact H1
  iintro _
  iexact HP

@[lantana_alias tlc_succ_nat]
theorem tlc_succ_nat (n : Nat) : £ₙ (n + 1) ⊣⊢@{IProp GF} £ₙ 1 ∗ £ₙ n := by
  rw [ofNat_succ]
  exact tlc_succ

@[lantana_alias tlc_laterN]
theorem tlc_laterN {P : IProp GF} (n : Nat) : £ₙ n ∗ ▷^[n] (|==>r P) ⊢@{IProp GF} |==>r P := by
  induction n with
  | zero => exact sep_elim_right
  | succ n ih =>
    iintro ⟨Hn, HP⟩
    icases (tlc_succ_nat n).mp $$ Hn with ⟨H1, Hn⟩
    iapply tlc_later
    isplitl [H1]
    · iexact H1
    inext
    iapply ih
    isplitl [Hn]
    · iexact Hn
    iexact HP

@[lantana_alias tlc_weaken]
theorem tlc_weaken {α β : Ordinal.{1}} (h : β ≤ α) : £ₒ α ⊢@{IProp GF} |==>r £ₒ β :=
  auth_rupd_weaken (Ordinal.lt_or_eq_of_le h).symm

@[lantana_alias tlc_zero]
theorem tlc_zero : ⊢@{IProp GF} |==> £ₒ (0 : Ordinal.{1}) :=
  credit_unit

#lantana_ignore tlc_loeb "`CreditExchange`/`credit_ind` are not ported yet."

@[lantana_alias tlc_omega]
theorem tlc_omega (n : Nat) : £ₒ ω ⊢@{IProp GF} |==>r £ₙ n :=
  tlc_weaken (Ordinal.le_of_lt (ofNat_lt_omega n))

@[lantana_alias tlc_split_nat]
theorem tlc_split_nat (n m : Nat) : £ₙ (n + m) ⊣⊢@{IProp GF} £ₙ n ∗ £ₙ m := by
  rw [← nadd_ofNat]
  exact tlc_split

@[lantana_alias tlc_split_one]
theorem tlc_split_one {n m : Nat} (h : n = 1 + m) : £ₙ n ⊢@{IProp GF} £ₙ m ∗ £ₙ 1 := by
  subst h
  rw [Nat.add_comm]
  exact (tlc_split_nat m 1).mp

@[lantana_alias tlc_one_nat]
theorem tlc_one_nat : £ₙ 1 ⊣⊢@{IProp GF} £ₒ (1 : Ordinal.{1}) :=
  .rfl

/-! Proof-mode instances for splitting and combining credits. -/

instance intoSep_tlc_nadd {α β : Ordinal.{1}} : IntoSep (£ₒ (α +ₕ β) : IProp GF) (£ₒ α) (£ₒ β) where
  into_sep := tlc_split.mp

instance fromSep_tlc_nadd {α β : Ordinal.{1}} : FromSep (£ₒ (α +ₕ β) : IProp GF) (£ₒ α) (£ₒ β) where
  from_sep := tlc_split.mpr

instance combineSepAs_tlc_nadd {α β : Ordinal.{1}} :
    CombineSepAs (£ₒ α : IProp GF) (£ₒ β) (£ₒ (α +ₕ β)) where
  combine_sep_as := tlc_split.mpr

instance intoSep_tlc_succ {α : Ordinal.{1}} : IntoSep (£ₒ (succ α) : IProp GF) (£ₙ 1) (£ₒ α) where
  into_sep := tlc_succ.mp

instance fromSep_tlc_succ {α : Ordinal.{1}} : FromSep (£ₒ (succ α) : IProp GF) (£ₙ 1) (£ₒ α) where
  from_sep := tlc_succ.mpr

instance (priority := high) intoSep_tlc_nat_add {n m : Nat} :
    IntoSep (£ₙ (n + m) : IProp GF) (£ₙ n) (£ₙ m) where
  into_sep := (tlc_split_nat n m).mp

instance (priority := high) fromSep_tlc_nat_add {n m : Nat} :
    FromSep (£ₙ (n + m) : IProp GF) (£ₙ n) (£ₙ m) where
  from_sep := (tlc_split_nat n m).mpr

instance (priority := high) combineSepAs_tlc_nat_add {n m : Nat} :
    CombineSepAs (£ₙ n : IProp GF) (£ₙ m) (£ₙ (n + m)) where
  combine_sep_as := (tlc_split_nat n m).mpr

end Ordinal

end Lantana
