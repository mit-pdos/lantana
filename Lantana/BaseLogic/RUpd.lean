/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Init
public import Iris.ProofMode
public import Iris.Instances.IProp

/-! # Relational updates `|==>r P`

The later-elimination update of "Later Credits" (Spies et al., ICFP 2022), generalised from
natural numbers to any type `X` of credit supplies with a well-founded relation (Rocq:
`lantana/base_logic/relational_updates.v`). Iris-Lean's `le_upd` (`|==£>`,
`Iris.Instances.Lib.LaterCredits`) is the template; unlike it, `rupdPre` has no `▷^[n] False`
escape disjunct: Lantana eliminates relational updates through satisfiability, and the fancy
update makes `◇` explicit instead.

`|==>r P` is a Banach fixpoint per `P`, as `le_upd` is. The credit type is an `outParam` of
`RUpdG`, so that `|==>r P` finds it from the ghost state in scope, as Rocq's type class search
does.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.OFE Iris.ProofMode

universe u v

/-- A relational update structure on `IProp GF`: `pred x` says "the total credit supply is
`x`", and the supply decreases along the well-founded relation `rel`. -/
@[lantana_alias rupdG]
class RUpdG (GF : BundledGFunctors.{u}) (X : outParam (Type v)) where
  /-- The total credit supply is `x` (Rocq: `rupd_pred`). -/
  pred : X → IProp GF
  /-- The supply decreases along `rel` (Rocq: `rupd_rel`). -/
  rel : X → X → Prop
  rel_wf : WellFounded rel

attribute [lantana_alias rupd_pred] RUpdG.pred
attribute [lantana_alias rupd_rel] RUpdG.rel
attribute [lantana_alias rupd_rel_wf] RUpdG.rel_wf

#lantana_ignore rtc_acc "`WellFounded.transGen` in Lean core."
#lantana_ignore tc_inv_rtc "`WellFounded.transGen` in Lean core."
#lantana_ignore rtc_embed_tc "`WellFounded.transGen` in Lean core."
#lantana_ignore tc_wf "`WellFounded.transGen` in Lean core."

section RUpd

variable {GF : BundledGFunctors.{u}} {X : Type v} [RUpdG GF X]

open Relation (TransGen)

/-- Given the supply `x`, update the ghost state, then either finish with the same supply, or
decrease the supply and continue under a later. -/
@[lantana_alias rupd_pre]
def rupdPre (P R : IProp GF) : IProp GF :=
  iprop(∀ x : X, RUpdG.pred x -∗ |==>
    ((RUpdG.pred x ∗ P) ∨ ∃ x' : X, ⌜TransGen (RUpdG.rel GF) x' x⌝ ∗ RUpdG.pred x' ∗ ▷ R))

@[lantana_alias rupd_pre_contractive]
instance rupdPre_contractive {P : IProp GF} : Contractive (rupdPre (X := X) P) where
  distLater_dist {_ _ _} H := by
    simp only [rupdPre]
    refine forall_ne fun _ => wand_ne.ne .rfl <| UPred.bupd_ne.ne <| or_ne.ne .rfl ?_
    refine exists_ne fun _ => sep_ne.ne .rfl <| sep_ne.ne .rfl ?_
    exact Contractive.distLater_dist H

#lantana_ignore rupd_def "`rupd` is defined directly without `seal`/`unseal`."
#lantana_ignore rupd_aux "`rupd` is defined directly without `seal`/`unseal`."
#lantana_ignore rupd_eq "`rupd` is defined directly without `seal`/`unseal`."

/-- The relational update `|==>r P`. -/
@[lantana_alias rupd]
def rupd (P : IProp GF) : IProp GF := fixpoint (rupdPre (X := X) P)

/-- The relational update. -/
scoped syntax:max "|==>r " term:40 : term

macro_rules
  | `(iprop(|==>r%$tk $P)) => ``($(wrapIprop tk ``rupd) iprop($P))

delab_rule rupd
  | `($_ $P) => do ``(iprop(|==>r $(← unpackIprop P)))

@[lantana_alias rupd_unfold]
theorem rupd_unfold {P : IProp GF} :
    (|==>r P) ⊣⊢ ∀ x : X, RUpdG.pred x -∗ |==>
      ((RUpdG.pred x ∗ P) ∨ ∃ x' : X, ⌜TransGen (RUpdG.rel GF) x' x⌝ ∗ RUpdG.pred x' ∗ ▷ |==>r P) :=
  (fixpoint_unfold ⟨rupdPre (X := X) P, inferInstance⟩).to_bi.trans .rfl

@[lantana_alias rupd_ne]
instance rupd_ne : NonExpansive (rupd (GF := GF) (X := X)) where
  ne {n} := by
    apply SIdx.lt_wf.induction n
    intro _ IH P Q H
    refine (equiv_iff.mpr rupd_unfold).dist.trans <| .trans ?_ (equiv_iff.mpr rupd_unfold).dist.symm
    refine forall_ne fun _ => wand_ne.ne .rfl <| UPred.bupd_ne.ne <| or_ne.ne (sep_ne.ne .rfl H) ?_
    refine exists_ne fun _ => sep_ne.ne .rfl <| sep_ne.ne .rfl ?_
    exact Contractive.distLater_dist fun k hk => IH k hk (H.lt hk)

#lantana_ignore rupd_ent_proper "Subsumed by `rupd_mono`."
#lantana_ignore rupd_flip_ent_proper "Subsumed by `rupd_mono`."
#lantana_ignore rupd_equiv_proper "Subsumed by the `NonExpansive` instance `rupd_ne`."

@[lantana_alias bupd_rupd]
theorem bupd_rupd {P : IProp GF} : (|==> P) ⊢ |==>r P := by
  iintro H
  iapply rupd_unfold
  iintro %x Hx
  imod H; imodintro
  ileft
  iframe

@[lantana_alias rupd_intro]
theorem rupd_intro {P : IProp GF} : P ⊢ |==>r P := by
  iintro H
  iapply bupd_rupd
  imodintro
  iexact H

/-- The bind rule, by Löb induction. -/
@[lantana_alias rupd_bind]
theorem rupd_bind {P Q : IProp GF} : (P -∗ |==>r Q) ⊢ (|==>r P) -∗ |==>r Q := by
  refine wand_entails (loeb_weak ?_)
  iintro IH H G
  iapply rupd_unfold
  iintro %x Hx
  imod rupd_unfold $$ G Hx with (⟨Hx, G⟩ | ⟨%x', %hx', Hx, G⟩)
  · imod rupd_unfold $$ (H $$ G) Hx with (⟨Hx, G⟩ | ⟨%x'', %hx'', Hx, G⟩)
    · imodintro; ileft; iframe
    · imodintro; iright; iexists x''; iframe; itrivial
  · imodintro; iright; iexists x'; iframe
    isplit
    · itrivial
    inext
    iapply IH $$ H G

/-- The general form of spending credits to eliminate a later. -/
@[lantana_alias rupd_step]
theorem rupd_step {P : IProp GF} :
    (∀ x : X, RUpdG.pred x -∗ |==> ∃ y : X, ⌜TransGen (RUpdG.rel GF) y x⌝ ∗ RUpdG.pred y ∗ ▷ |==>r P)
      ⊢ |==>r P := by
  iintro H
  iapply rupd_unfold
  iintro %x Hx
  imod H $$ %x Hx with H
  imodintro
  iright
  iexact H

@[lantana_alias rupd_mono]
theorem rupd_mono {P Q : IProp GF} (h : P ⊢ Q) : (|==>r P) ⊢ |==>r Q :=
  wand_entails <| (entails_wand (h.trans rupd_intro)).trans rupd_bind

@[lantana_alias rupd_trans]
theorem rupd_trans {P : IProp GF} : (|==>r |==>r P) ⊢ |==>r P :=
  wand_entails <| (entails_wand .rfl).trans rupd_bind

@[lantana_alias rupd_frame_r]
theorem rupd_frame_r {P R : IProp GF} : (|==>r P) ∗ R ⊢ |==>r (P ∗ R) := by
  iintro ⟨H, HR⟩
  iapply rupd_bind $$ [HR] H
  iintro HP
  iapply rupd_intro
  iframe

@[lantana_alias rupd_frame_l]
theorem rupd_frame_l {P R : IProp GF} : R ∗ (|==>r P) ⊢ |==>r (R ∗ P) :=
  sep_comm.mp.trans <| rupd_frame_r.trans <| rupd_mono sep_comm.mp

@[lantana_alias rupd_bupd_l]
theorem rupd_bupd_l {P : IProp GF} : (|==> |==>r P) ⊢ |==>r P :=
  bupd_rupd.trans rupd_trans

@[lantana_alias rupd_bupd_r]
theorem rupd_bupd_r {P : IProp GF} : (|==>r |==> P) ⊢ |==>r P :=
  (rupd_mono bupd_rupd).trans rupd_trans

@[lantana_alias rupd_wand_l]
theorem rupd_wand_l {P Q : IProp GF} : (P -∗ Q) ∗ (|==>r P) ⊢ |==>r Q :=
  rupd_frame_l.trans <| rupd_mono wand_elim_left

@[lantana_alias rupd_wand_r]
theorem rupd_wand_r {P Q : IProp GF} : (|==>r P) ∗ (P -∗ Q) ⊢ |==>r Q :=
  rupd_frame_r.trans <| rupd_mono wand_elim_right

@[lantana_alias rupd_sep]
theorem rupd_sep {P Q : IProp GF} : (|==>r P) ∗ (|==>r Q) ⊢ |==>r (P ∗ Q) :=
  rupd_frame_r.trans <| (rupd_mono rupd_frame_l).trans rupd_trans

@[lantana_alias rupd_idemp]
theorem rupd_idemp {P : IProp GF} : (|==>r |==>r P) ⊣⊢ |==>r P :=
  ⟨rupd_trans, rupd_intro⟩

#lantana_ignore rupd_homomorphism "Not needed: Lantana states big-op rules directly."
#lantana_ignore big_sepL_rupd "Not ported yet: no client in the base logic."
#lantana_ignore big_sepM_rupd "Not ported yet: no client in the base logic."
#lantana_ignore big_sepS_rupd "Not ported yet: no client in the base logic."
#lantana_ignore big_sepMS_rupd "Not ported yet: no client in the base logic."

@[lantana_alias except_0_rupd]
theorem except_0_rupd {P : IProp GF} : ◇ (|==>r P) ⊢ |==>r ◇ P := by
  simp only [BIBase.except0]
  iintro (HF | H)
  · iapply rupd_intro
    ileft
    iexact HF
  · iapply rupd_mono or_intro_r $$ H

#lantana_ignore bi_bupd_mixin_rupd "Only a safety check; the laws are the lemmas above."

end RUpd

/-! ## Proof-mode instances -/

section ProofMode

variable {GF : BundledGFunctors.{u}} {X : Type v} [RUpdG GF X]

@[lantana_alias elim_bupd_rupd]
instance elimModal_bupd_rupd {p io} {P Q : IProp GF} :
    ElimModal True p io false iprop(|==> P) P iprop(|==>r Q) iprop(|==>r Q) where
  elim_modal _ :=
    (sep_mono_left (intuitionisticallyIf_elim.trans bupd_rupd)).trans <| rupd_wand_r.trans rupd_trans

@[lantana_alias add_modal_bupd]
instance addModal_bupd_rupd {P Q : IProp GF} : AddModal iprop(|==> P) P iprop(|==>r Q) where
  add_modal := (sep_mono_left bupd_rupd).trans <| rupd_wand_r.trans rupd_trans

@[lantana_alias from_assumption_rupd]
instance fromAssumption_rupd {p ioP} {P Q : IProp GF} [h : FromAssumption p ioP P Q] :
    FromAssumption p ioP P iprop(|==>r Q) where
  from_assumption := h.1.trans rupd_intro

@[lantana_alias from_pure_rupd]
instance fromPure_rupd {a io φ} {P : IProp GF} [h : FromPure a P io φ] :
    FromPure a iprop(|==>r P) io φ where
  from_pure := h.1.trans rupd_intro

@[lantana_alias into_wand_rupd]
instance intoWand_rupd {p q m} {R P Q : IProp GF} [h : IntoWand false false R m P Q] :
    IntoWand p q iprop(|==>r R) m iprop(|==>r P) iprop(|==>r Q) where
  into_wand := intuitionisticallyIf_elim.trans <| wand_intro <|
    (sep_mono (rupd_mono h.into_wand) intuitionisticallyIf_elim).trans <|
      rupd_sep.trans (rupd_mono wand_elim_left)

@[lantana_alias into_wand_rupd_persistent]
instance intoWand_rupd_persistent {p q m} {R P Q : IProp GF} [h : IntoWand false q R m P Q] :
    IntoWand p q iprop(|==>r R) m P iprop(|==>r Q) where
  into_wand := intuitionisticallyIf_elim.trans <| wand_intro <|
    (sep_mono_left (rupd_mono h.into_wand)).trans <| rupd_frame_r.trans (rupd_mono wand_elim_left)

@[lantana_alias into_wand_rupd_args]
instance (priority := low) intoWand_rupd_args {p q} {s : WandMode.Side} {R P Q : IProp GF}
    [h : IntoWand p false R (.matching s) P Q] :
    IntoWand p q R (.matching s) iprop(|==>r P) iprop(|==>r Q) where
  into_wand := wand_intro_left <| (sep_mono intuitionisticallyIf_elim h.into_wand).trans rupd_wand_r

@[lantana_alias from_sep_rupd]
instance fromSep_rupd {P Q1 Q2 : IProp GF} [h : FromSep P Q1 Q2] :
    FromSep iprop(|==>r P) iprop(|==>r Q1) iprop(|==>r Q2) where
  from_sep := rupd_sep.trans (rupd_mono h.1)

@[lantana_alias from_or_rupd]
instance fromOr_rupd {P Q1 Q2 : IProp GF} [h : FromOr P Q1 Q2] :
    FromOr iprop(|==>r P) iprop(|==>r Q1) iprop(|==>r Q2) where
  from_or := or_elim (rupd_mono (or_intro_l.trans h.1)) (rupd_mono (or_intro_r.trans h.1))

@[lantana_alias from_exist_rupd]
instance fromExists_rupd {α : Sort _} {P : IProp GF} {Φ : α → IProp GF} [h : FromExists P Φ] :
    FromExists iprop(|==>r P) (fun a => iprop(|==>r Φ a)) where
  from_exists := exists_elim fun a => rupd_mono ((exists_intro a).trans h.1)

@[lantana_alias is_except_0_rupd]
instance isExcept0_rupd {P : IProp GF} [h : IsExcept0 P] : IsExcept0 iprop(|==>r P) where
  is_except0 := except_0_rupd.trans (rupd_mono h.1)

@[lantana_alias from_modal_rupd]
instance fromModal_rupd {io} {P : IProp GF} :
    FromModal io modality_id True iprop(|==>r P) iprop(|==>r P) P where
  from_modal _ := rupd_intro

@[lantana_alias elim_modal_rupd]
instance elimModal_rupd {p io} {P Q : IProp GF} :
    ElimModal True p io false iprop(|==>r P) P iprop(|==>r Q) iprop(|==>r Q) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <| rupd_wand_r.trans rupd_trans

@[lantana_alias add_modal_rupd]
instance addModal_rupd {P Q : IProp GF} : AddModal iprop(|==>r P) P iprop(|==>r Q) where
  add_modal := rupd_wand_r.trans rupd_trans

@[lantana_alias frame_rupd]
instance frame_rupd {p} {R P Q : IProp GF} [h : Frame p R P Q] :
    Frame p R iprop(|==>r P) iprop(|==>r Q) where
  frame := rupd_frame_l.trans (rupd_mono h.frame)

end ProofMode

end Lantana
