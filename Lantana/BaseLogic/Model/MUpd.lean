/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI.Lib.Fixpoint
public import Lantana.BaseLogic.FUpd
public import Lantana.BaseLogic.Model.ModelHistory
public import Lantana.BaseLogic.Model.OSat
public import Lantana.BaseLogic.Model.OWit
public import Lantana.BaseLogic.Model.OForest

/-! # The model interpretation and the model update

Rocq `lantana/base_logic/mupd.v` and `model_physical_updates.v`: the ghost state of the whole
model (`ModelGS`), its interpretation `modelInterp h i Ω W n tc` (history, obligations, forest,
witnesses, and the witness invariant), and the model update `mupd n tc P` as the *least fixpoint*
of rounds (D11): the prover changes the obligations by `Obls.lef`, the environment picks any
admissible witnesses, and the update continues. `modelInterp_mupd_steps` is adequacy's
elimination: the rounds compose into `Obls.le` and witnesses keeping a lower bound exist
(`owitInv_exists_witnesses`). The two single rounds of a physical step, `mprog` (progress of the
scheduled thread) and `mphys` (change of the step index and thread count), close the file. The
fancy version `|={E₁,E₂}=>m` and the derived rules are in `Lantana.ProgramLogic.OblForest` and
`OblForestRules`; the Rocq aliases of `mupd`, `mprog`, `mphys` and their core rules sit on the
interface's declarations, which are these definitions once the interface is sealed.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode Iris.Std LawfulPartialMap
open Lantana.Model

/-- The ghost state of the model that a world provides (Rocq `mupdGpreS`). -/
@[lantana_alias mupdGpreS]
class ModelGpreS (GF : BundledGFunctors) where
  [invG : InvGpreS GF]
  [osatG : OSatGpreS GF]
  [owitG : OWitGpreS GF]
  [oforestG : OForestGpreS GF]
  [mhistG : MHistGpreS GF]

attribute [reducible, instance] ModelGpreS.invG ModelGpreS.osatG ModelGpreS.owitG
  ModelGpreS.oforestG ModelGpreS.mhistG

/-- The ghost state of the model (Rocq `mupdGS`): invariants and credits, obligations,
witnesses, the forest with the thread statuses, and the model history. -/
@[lantana_alias mupdGS]
class ModelGS (GF : BundledGFunctors) where
  [toInvGS : InvGS GF]
  [toOSatGS : OSatGS GF]
  [toOWitGS : OWitGS GF]
  [toOForestGS : OForestGS GF]
  [toMHistGS : MHistGS GF]

attribute [reducible, instance] ModelGS.toInvGS ModelGS.toOSatGS ModelGS.toOWitGS
  ModelGS.toOForestGS ModelGS.toMHistGS

namespace Model

open Iris Iris.BI Iris.ProofMode Iris.Std LawfulPartialMap

section ModelInterp

variable {GF : BundledGFunctors} [ModelGS GF]

/-- The model interpretation (Rocq `model_interp`): the history of `i + 1` events ending at
`(n, Ω)`, the ghost state of the obligations `Ω`, the forest over the `tc` threads, the
witnesses `W` with the witness invariant. -/
@[lantana_alias model_interp]
def modelInterp (h : List MEvent) (i : Nat) (Ω : Obls) (W : Witnesses) (n tc : Nat) :
    IProp GF :=
  iprop(modelHistoryInterp h i n Ω ∗ osat Ω ∗ oforest Ω tc ∗ owit W ∗
    ⌜owitInvFair Ω W⌝)

instance modelInterp_timeless (h : List MEvent) (i : Nat) (Ω : Obls) (W : Witnesses)
    (n tc : Nat) : Timeless (modelInterp (GF := GF) h i Ω W n tc) := by
  unfold modelInterp; infer_instance

@[lantana_alias model_interp_owit_inv]
theorem modelInterp_owitInv (h : List MEvent) (i : Nat) (Ω : Obls) (W : Witnesses)
    (n tc : Nat) : modelInterp (GF := GF) h i Ω W n tc ⊢ ⌜owitInvFair Ω W⌝ := by
  unfold modelInterp
  iintro ⟨-, -, -, -, %h⟩
  ipureintro
  exact h

theorem modelInterp_owitInv' (h : List MEvent) (i : Nat) (Ω : Obls) (W : Witnesses)
    (n tc : Nat) :
    modelInterp (GF := GF) h i Ω W n tc ⊢
      modelInterp h i Ω W n tc ∗ ⌜owitInvFair Ω W⌝ := by
  unfold modelInterp
  iintro ⟨HH, Hs, Hf, Hw, %hI⟩
  iframe HH Hs Hf Hw
  ipureintro
  exact ⟨hI, hI⟩

/-- A trivial round: the obligations do not change, the environment may lower the witnesses
(Rocq, inside `fupd_mupd_elim`). -/
theorem modelInterp_trivial_round (h : List MEvent) (i : Nat) (Ω : Obls) (W₁ W₂ : Witnesses)
    (n tc : Nat) (hW : W₁.lef W₂) (hI₂ : owitInvFair Ω W₂) :
    modelInterp (GF := GF) h i Ω W₁ n tc ⊢
      |==> modelInterp (h ++ [(n, Ω)]) (i + 1) Ω W₂ n tc := by
  unfold modelInterp
  iintro ⟨HH, Hs, Hf, Hw, %hI₁⟩
  imod modelHistoryInterp_step h i (Nat.le_refl n) (Obls.le_refl Ω) $$ HH with HH
  imodintro
  iframe HH Hs Hf
  isplitl [Hw]
  · iapply owit_mon (wits_lef_same_mono hI₁ hW hI₂) $$ Hw
  · ipureintro
    exact hI₂

/-! ### The model update as a least fixpoint -/

/-- One round of the model update (Rocq `mupd_pre`): either `P` holds now (under a fancy update
at the empty mask), or, given the model, the prover changes the obligations by `Obls.lef` and,
for every admissible choice of witnesses by the environment, returns the new model and
continues. -/
@[lantana_alias mupd_pre]
def mupdPre (n tc : Nat) (mupd : IProp GF → IProp GF) (P : IProp GF) : IProp GF :=
  iprop((|={∅}=> P) ∨
    ∀ (h : List MEvent) (i : Nat) (Ω₁ : Obls) (W₁ : Witnesses),
      modelInterp h i Ω₁ W₁ n tc ={∅}=∗ ∃ Ω₂, ⌜Obls.lef Ω₁ Ω₂⌝ ∗
        ∀ W₂, ⌜W₁.lef W₂ ∧ owitInvFair Ω₂ W₂⌝ ={∅}=∗
          modelInterp (h ++ [(n, Ω₂)]) (i + 1) Ω₂ W₂ n tc ∗ mupd P)

@[lantana_alias mupd_pre_mono]
theorem mupdPre_mono (n tc : Nat) {Φ Ψ : IProp GF → IProp GF} :
    □ (∀ P, Φ P -∗ Ψ P) ⊢ ∀ P, mupdPre n tc Φ P -∗ mupdPre n tc Ψ P := by
  iintro #H %P Hpre
  unfold mupdPre
  icases Hpre with (HP | Hround)
  · ileft
    iexact HP
  · iright
    iintro %h %i %Ω₁ %W₁ HM
    imod Hround $$ HM with ⟨%Ω₂, %hΩ, Hk⟩
    imodintro
    iexists Ω₂
    isplitr
    · ipureintro
      exact hΩ
    iintro %W₂ %hW
    imod Hk $$ %W₂ %hW with ⟨HM, HΦ⟩
    imodintro
    iframe HM
    iapply H $$ HΦ

@[lantana_alias mupd_pre_mono']
instance mupdPre_monoPred (n tc : Nat) : BIMonoPred (mupdPre (GF := GF) n tc) where
  mono_pred := by
    intro Φ Ψ _ _
    iintro #H %P Hpre
    iapply mupdPre_mono n tc $$ [] Hpre
    iexact H
  mono_pred_ne {Φ} _ := ⟨fun {m} P Q hPQ => by
    unfold mupdPre
    refine or_ne.ne (OFE.NonExpansive.ne hPQ) ?_
    refine forall_ne fun h => forall_ne fun i => forall_ne fun Ω₁ => forall_ne fun W₁ => ?_
    refine wand_ne.ne .rfl (OFE.NonExpansive.ne ?_)
    refine exists_ne fun Ω₂ => sep_ne.ne .rfl (forall_ne fun W₂ => ?_)
    refine wand_ne.ne .rfl (OFE.NonExpansive.ne ?_)
    exact sep_ne.ne .rfl (OFE.NonExpansive.ne hPQ)⟩

/-- The base model update `|=[n,tc]=>m P` (Rocq `mupd`). -/
def mupd (n tc : Nat) (P : IProp GF) : IProp GF := bi_least_fixpoint (mupdPre n tc) P

@[lantana_alias mupd_unfold]
theorem mupd_unfold (n tc : Nat) (P : IProp GF) :
    mupd n tc P ⊣⊢ mupdPre n tc (mupd n tc) P :=
  (least_fixpoint_unfold ..).to_bi

instance mupd_ne (n tc : Nat) : OFE.NonExpansive (mupd (GF := GF) n tc) :=
  inferInstanceAs (OFE.NonExpansive (bi_least_fixpoint (mupdPre n tc)))

/-- Strong induction (Rocq `mupd_ind_strong`). -/
@[lantana_alias mupd_ind_strong]
theorem mupd_ind_strong (n tc : Nat) (Ψ : IProp GF → IProp GF) [OFE.NonExpansive Ψ] :
    □ (∀ P, mupdPre n tc (fun P => iprop(Ψ P ∧ mupd n tc P)) P -∗ Ψ P) ⊢
      ∀ P, mupd n tc P -∗ Ψ P :=
  wand_entails (least_fixpoint_ind (mupdPre n tc) Ψ)

/-- Induction (Rocq `mupd_ind`). -/
@[lantana_alias mupd_ind]
theorem mupd_ind (n tc : Nat) (Ψ : IProp GF → IProp GF) [OFE.NonExpansive Ψ] :
    □ (∀ P, mupdPre n tc Ψ P -∗ Ψ P) ⊢ ∀ P, mupd n tc P -∗ Ψ P :=
  wand_entails (least_fixpoint_iter (mupdPre n tc) (Φ := Ψ))

theorem fupd_mupd (n tc : Nat) (P : IProp GF) : (|={∅}=> P) ⊢ mupd n tc P := by
  iintro H
  iapply (mupd_unfold n tc P).2
  unfold mupdPre
  ileft
  iexact H

theorem mupd_intro (n tc : Nat) (P : IProp GF) : P ⊢ mupd n tc P :=
  fupd_intro.trans (fupd_mupd n tc P)

/-- A fancy update at the empty mask before the model update is absorbed by a trivial round
(Rocq `fupd_mupd_elim`). -/
theorem fupd_mupd_elim (n tc : Nat) (P : IProp GF) :
    (|={∅}=> mupd n tc P) ⊢ mupd n tc P := by
  iintro H
  iapply (mupd_unfold n tc P).2
  unfold mupdPre
  iright
  iintro %h %i %Ω₁ %W₁ HM
  imod H with H
  imodintro
  iexists Ω₁
  isplitr
  · ipureintro
    exact Obls.lef_refl Ω₁
  iintro %W₂ %⟨hW, hI₂⟩
  imod modelInterp_trivial_round h i Ω₁ W₁ W₂ n tc hW hI₂ $$ HM with HM
  imodintro
  iframe

/-- A model update that only reads the model, which it returns unchanged (a trivial round;
Rocq `mupd_read` in `temporal_formula.v`). -/
theorem mupd_read (n tc : Nat) (P : IProp GF) :
    (∀ (h : List MEvent) (i : Nat) (Ω : Obls) (W : Witnesses),
      modelInterp h i Ω W n tc -∗ modelInterp h i Ω W n tc ∗ P) ⊢ mupd n tc P := by
  iintro H
  iapply (mupd_unfold n tc P).2
  unfold mupdPre
  iright
  iintro %h %i %Ω₁ %W₁ HM
  icases H $$ %h %i %Ω₁ %W₁ HM with ⟨HM, HP⟩
  imodintro
  iexists Ω₁
  isplitr
  · ipureintro
    exact Obls.lef_refl Ω₁
  iintro %W₂ %⟨hW, hI₂⟩
  imod modelInterp_trivial_round h i Ω₁ W₁ W₂ n tc hW hI₂ $$ HM with HM
  imodintro
  iframe HM
  iapply mupd_intro n tc P $$ HP

/-- A snapshot of the current obligation `k` (Rocq `model_interp_event_obl`). -/
@[lantana_alias model_interp_event_obl]
theorem modelInterp_eventObl {h : List MEvent} {i : Nat} {Ω : Obls} {W : Witnesses}
    {n tc : Nat} {k : Oid} {o : Obl} (hk : get? Ω k = some o) :
    modelInterp h i Ω W n tc ⊢ eventObl (GF := GF) i (n, Ω) k o := by
  unfold modelInterp
  iintro ⟨HH, -, -, -, -⟩
  iapply modelHistoryInterp_eventObl_now h i n Ω hk $$ HH

/-- What a snapshot says about the current model (`eventObl_modelHistoryInterp_lookup`). -/
theorem modelInterp_eventObl_lookup (h : List MEvent) (i : Nat) (Ω : Obls) (W : Witnesses)
    (n tc j : Nat) (e : MEvent) (k : Oid) (o : Obl) :
    modelInterp h i Ω W n tc ∗ eventObl (GF := GF) j e k o ⊢
      ⌜h[j]? = some e ∧ get? e.2 k = some o ∧ j ≤ i ∧ e.1 ≤ n ∧ Obls.le e.2 Ω⌝ := by
  unfold modelInterp
  iintro ⟨⟨HH, -, -, -, -⟩, He⟩
  iapply eventObl_modelHistoryInterp_lookup h i n Ω j e k o
  iframe HH He

/-- Sequencing (Rocq `mupd_bind`). -/
theorem mupd_bind (n tc : Nat) (P Q : IProp GF) :
    (P -∗ mupd n tc Q) ⊢ mupd n tc P -∗ mupd n tc Q := by
  letI Ψ : IProp GF → IProp GF := fun P => iprop((P -∗ mupd n tc Q) -∗ mupd n tc Q)
  letI : OFE.NonExpansive Ψ := ⟨fun _ _ _ h => wand_ne.ne (wand_ne.ne h .rfl) .rfl⟩
  iintro HPQ HP
  iapply mupd_ind_strong n tc Ψ $$ [] HP HPQ
  iintro !> %P' Hpre HPQ'
  unfold mupdPre
  icases Hpre with (HP' | Hround)
  · iapply fupd_mupd_elim
    imod HP' with HP'
    imodintro
    iapply HPQ' $$ HP'
  · iapply (mupd_unfold n tc Q).2
    unfold mupdPre
    iright
    iintro %h %i %Ω₁ %W₁ HM
    imod Hround $$ HM with ⟨%Ω₂, %hΩ, Hk⟩
    imodintro
    iexists Ω₂
    isplitr
    · ipureintro
      exact hΩ
    iintro %W₂ %hW
    imod Hk $$ %W₂ %hW with ⟨HM, ⟨HΨ, -⟩⟩
    imodintro
    iframe HM
    iapply HΨ $$ HPQ'


/-- A non-discharging round (Rocq `mupd_nd_step`): the environment's witnesses then satisfy
`Witnesses.ndf`. -/
@[lantana_alias mupd_nd_step]
theorem mupd_nd_step (n tc : Nat) (P : IProp GF) :
    (∀ (h : List MEvent) (i : Nat) (Ω₁ : Obls) (W₁ : Witnesses),
      modelInterp h i Ω₁ W₁ n tc ={∅}=∗ ∃ Ω₂, ⌜Obls.ndf Ω₁ Ω₂⌝ ∗
        ∀ W₂, ⌜W₁.ndf W₂ ∧ owitInvFair Ω₂ W₂⌝ ={∅}=∗
          modelInterp (h ++ [(n, Ω₂)]) (i + 1) Ω₂ W₂ n tc ∗ mupd n tc P)
      ⊢@{IProp GF} mupd n tc P := by
  iintro H
  iapply (mupd_unfold n tc P).2
  unfold mupdPre
  iright
  iintro %h %i %Ω₁ %W₁ HM
  icases modelInterp_owitInv' h i Ω₁ W₁ n tc $$ HM with ⟨HM, %hI₁⟩
  imod H $$ HM with ⟨%Ω₂, %hΩ, Hk⟩
  imodintro
  iexists Ω₂
  isplitr
  · ipureintro
    exact hΩ.lef
  iintro %W₂ %⟨hW, hI₂⟩
  iapply Hk $$ %W₂ %(⟨wits_lef_wits_ndf hI₁ hΩ hW hI₂, hI₂⟩)

/-- Running a model update against the model (Rocq `model_interp_mupd_steps`, the elimination
used by adequacy): the rounds compose into `Obls.le`, and the environment can always choose
witnesses keeping a lower bound `γ` that is strictly monotone and below `fairMeasureUb`. -/
@[lantana_alias model_interp_mupd_steps]
theorem modelInterp_mupd_steps (n tc : Nat) (γ : ThreadId → Fuel → Fuel)
    (hγ : owitInvLbMonoFair γ) (P : IProp GF) :
    mupd n tc P ⊢@{IProp GF} ∀ (h : List MEvent) (i : Nat) (Ω : Obls) (W : Witnesses),
      ⌜owitInvLb γ Ω W⌝ → modelInterp h i Ω W n tc ={∅}=∗
        P ∗ ∃ h' i' Ω' W', ⌜Obls.le Ω Ω' ∧ owitInvLb γ Ω' W'⌝ ∗
          modelInterp (h ++ h') (i + i') Ω' W' n tc := by
  letI Ψ : IProp GF → IProp GF := fun P => iprop(∀ (h : List MEvent) (i : Nat) (Ω : Obls)
    (W : Witnesses), ⌜owitInvLb γ Ω W⌝ → modelInterp h i Ω W n tc ={∅}=∗
      P ∗ ∃ h' i' Ω' W', ⌜Obls.le Ω Ω' ∧ owitInvLb γ Ω' W'⌝ ∗
        modelInterp (h ++ h') (i + i') Ω' W' n tc)
  letI : OFE.NonExpansive Ψ := ⟨fun _ _ _ h => forall_ne fun _ => forall_ne fun _ =>
    forall_ne fun _ => forall_ne fun _ =>
      imp_ne.ne .rfl (wand_ne.ne .rfl (OFE.NonExpansive.ne (sep_ne.ne h .rfl)))⟩
  iintro HM
  iapply mupd_ind n tc Ψ $$ [] HM
  iintro !> %P' Hpre %h %i %Ω %W %hLb HM
  unfold mupdPre
  icases Hpre with (HP | Hround)
  · imod HP with HP
    imodintro
    iframe HP
    iexists [], 0, Ω, W
    isplitr
    · ipureintro
      exact ⟨Obls.le_refl Ω, hLb⟩
    · rw [List.append_nil, Nat.add_zero]
      iexact HM
  · icases modelInterp_owitInv' h i Ω W n tc $$ HM with ⟨HM, %hI⟩
    imod Hround $$ HM with ⟨%Ω₂, %hΩ, Hk⟩
    obtain ⟨W₂, hW, hI₂, hLb₂⟩ := owitInv_exists_witnesses hγ hΩ hI hLb
    imod Hk $$ %W₂ %(⟨hW, hI₂⟩) with ⟨HM, HΨ⟩
    imod HΨ $$ %(h ++ [(n, Ω₂)]) %(i + 1) %Ω₂ %W₂ %hLb₂ HM
      with ⟨HP, %h', %i', %Ω', %W', %⟨hle, hLb'⟩, HM⟩
    imodintro
    iframe HP
    iexists [(n, Ω₂)] ++ h', 1 + i', Ω', W'
    isplitr
    · ipureintro
      exact ⟨Obls.le_trans hΩ.le hle, hLb'⟩
    · rw [← List.append_assoc, ← Nat.add_assoc]
      iexact HM

end ModelInterp

/-- The ghost names of the model: of world satisfaction and the credits, of the obligations, of
the witnesses, of the forest and of the model history (D32: small enough for the existential
property of satisfiability, unlike `ModelGS GF`). -/
structure _root_.Lantana.ModelNames where
  /-- World satisfaction and the credits. -/
  inv : InvNames
  /-- The obligations. -/
  osat : OSatNames
  /-- The name map of the witnesses. -/
  owit : GName
  /-- The forest. -/
  oforest : OForestNames
  /-- The model history. -/
  mhist : GName

/-- The ghost state of the model at the names `γ`, over the world's cameras. -/
@[reducible] def _root_.Lantana.ModelGS.ofNames {GF : BundledGFunctors} [ModelGpreS GF]
    (γ : ModelNames) : ModelGS GF where
  toInvGS := InvGS.ofNames γ.inv
  toOSatGS := OSatGS.ofNames γ.osat
  toOWitGS := OWitGS.ofName γ.owit
  toOForestGS := OForestGS.ofNames γ.oforest
  toMHistGS := MHistGS.ofName γ.mhist

/-- Allocation of the model at names `γ` (D32), with the credit supply, world satisfaction and
the full mask of the invariants. -/
theorem modelInterp_alloc_names {GF : BundledGFunctors} [ModelGpreS GF] (n : Nat) :
    ⊢@{IProp GF} |==> ∃ γ : ModelNames, letI := ModelGS.ofNames (GF := GF) γ
      iprop((∃ x : Ordinals.Ordinal.{1}, ●£ₒ x) ∗ wsat ∗ ownE ⊤ ∗
        modelInterp [(n, ∅)] 0 ∅ ∅ n 0) := by
  imod invGS_alloc_names (GF := GF) with ⟨%γi, ⟨%x, Hc⟩, Hw, HE⟩
  imod modelHistoryInterp_init_names (GF := GF) n ∅ with ⟨%γh, HH⟩
  imod osat_alloc_names (GF := GF) with ⟨%γs, Hs⟩
  imod @owit_alloc_names GF (OSatGS.ofNames γs) _ with ⟨%γw, Hwit⟩
  imod @oforest_alloc_names GF (OSatGS.ofNames γs) _ with ⟨%γf, Hf⟩
  imodintro
  iexists ⟨γi, γs, γw, γf, γh⟩
  isplitl [Hc]
  · iexists x
    iexact Hc
  iframe Hw HE
  unfold modelInterp
  iframe HH Hs Hf Hwit
  ipureintro
  exact owitInv_empty

/-- Allocation of the model (Rocq `model_interp_alloc`), with the credit supply, world
satisfaction and the full mask of the invariants. -/
@[lantana_alias model_interp_alloc]
theorem modelInterp_alloc {GF : BundledGFunctors} [ModelGpreS GF] (n : Nat) :
    ⊢@{IProp GF} |==> ∃ _ : ModelGS GF,
      (∃ x : Ordinals.Ordinal.{1}, ●£ₒ x) ∗ wsat ∗ ownE ⊤ ∗
      modelInterp [(n, ∅)] 0 ∅ ∅ n 0 := by
  imod modelInterp_alloc_names (GF := GF) n with ⟨%γ, H⟩
  imodintro
  iexists ModelGS.ofNames γ
  iexact H

/-! ### The rounds of a physical step (Rocq `model_physical_updates.v`) -/

section Physical

variable {GF : BundledGFunctors} [ModelGS GF]

/-- The progress round of the scheduled thread `i` (Rocq `mprog`): every obligation of `i`
strictly progresses, every assigned witness strictly progresses, the environment chooses the
witnesses. -/
def mprog (n tc : Nat) (i : ThreadId) (P : IProp GF) : IProp GF :=
  iprop(∀ (h : List MEvent) (a : Nat) (Ω₁ : Obls) (W₁ : Witnesses),
    modelInterp h a Ω₁ W₁ n tc ={∅}=∗
      ∃ Ω₂, ⌜Obls.condProgress (Obl.condOwner i) Ω₁ Ω₂⌝ ∗
      ∀ W₂, ⌜Witnesses.condProgress Witness.condAssigned W₁ W₂ ∧
        owitInvFair Ω₂ W₂⌝ ={∅}=∗
        modelInterp (h ++ [(n, Ω₂)]) (a + 1) Ω₂ W₂ n tc ∗ P)

/-- The physical round (Rocq `mphys`): the step index and the thread count change, the model
does not. -/
def mphys (n₁ n₂ tc₁ tc₂ : Nat) (P : IProp GF) : IProp GF :=
  iprop(∀ (h : List MEvent) (a : Nat) (Ω : Obls) (W : Witnesses),
    modelInterp h a Ω W n₁ tc₁ ={∅}=∗
      modelInterp (h ++ [(n₂, Ω)]) (a + 1) Ω W n₂ tc₂ ∗ P)

instance mprog_ne (n tc : Nat) (i : ThreadId) : OFE.NonExpansive (mprog (GF := GF) n tc i) :=
  ⟨fun _ _ _ h => by
    unfold mprog
    refine forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => ?_
    refine wand_ne.ne .rfl (OFE.NonExpansive.ne ?_)
    refine exists_ne fun _ => sep_ne.ne .rfl (forall_ne fun _ => ?_)
    exact wand_ne.ne .rfl (OFE.NonExpansive.ne (sep_ne.ne .rfl h))⟩

instance mphys_ne (n₁ n₂ tc₁ tc₂ : Nat) :
    OFE.NonExpansive (mphys (GF := GF) n₁ n₂ tc₁ tc₂) :=
  ⟨fun _ _ _ h => by
    unfold mphys
    refine forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => ?_
    exact wand_ne.ne .rfl (OFE.NonExpansive.ne (sep_ne.ne .rfl h))⟩

theorem mprog_wand (n tc : Nat) (i : ThreadId) (P Q : IProp GF) :
    (P -∗ Q) ⊢ mprog n tc i P -∗ mprog n tc i Q := by
  unfold mprog
  iintro HPQ H %h %a %Ω₁ %W₁ HM
  imod H $$ HM with ⟨%Ω₂, %hΩ, Hk⟩
  imodintro
  iexists Ω₂
  isplitr
  · ipureintro
    exact hΩ
  iintro %W₂ %hW
  imod Hk $$ %W₂ %hW with ⟨HM, HP⟩
  imodintro
  iframe HM
  iapply HPQ $$ HP

@[lantana_alias mprog_mono]
theorem mprog_mono (n tc : Nat) (i : ThreadId) {P Q : IProp GF} (h : P ⊢ Q) :
    mprog n tc i P ⊢ mprog n tc i Q := by
  iintro H
  iapply mprog_wand n tc i P Q $$ [] H
  iintro HP
  iapply h $$ HP

@[lantana_alias fupd_mprog]
theorem fupd_mprog (n tc : Nat) (i : ThreadId) (P : IProp GF) :
    (|={∅}=> mprog n tc i P) ⊢ mprog n tc i P := by
  unfold mprog
  iintro H %h %a %Ω₁ %W₁ HM
  imod H with H
  iapply H $$ HM

theorem mphys_wand (n₁ n₂ tc₁ tc₂ : Nat) (P Q : IProp GF) :
    (P -∗ Q) ⊢ mphys n₁ n₂ tc₁ tc₂ P -∗ mphys n₁ n₂ tc₁ tc₂ Q := by
  unfold mphys
  iintro HPQ H %h %a %Ω %W HM
  imod H $$ HM with ⟨HM, HP⟩
  imodintro
  iframe HM
  iapply HPQ $$ HP

@[lantana_alias mphys_mono]
theorem mphys_mono (n₁ n₂ tc₁ tc₂ : Nat) {P Q : IProp GF} (h : P ⊢ Q) :
    mphys n₁ n₂ tc₁ tc₂ P ⊢ mphys n₁ n₂ tc₁ tc₂ Q := by
  iintro H
  iapply mphys_wand n₁ n₂ tc₁ tc₂ P Q $$ [] H
  iintro HP
  iapply h $$ HP

@[lantana_alias fupd_mphys]
theorem fupd_mphys (n₁ n₂ tc₁ tc₂ : Nat) (P : IProp GF) :
    (|={∅}=> mphys n₁ n₂ tc₁ tc₂ P) ⊢ mphys n₁ n₂ tc₁ tc₂ P := by
  unfold mphys
  iintro H %h %a %Ω %W HM
  imod H with H
  iapply H $$ HM

end Physical

end Model

end Lantana
