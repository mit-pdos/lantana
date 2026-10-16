/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Algebra.Measure
public import Lantana.BaseLogic.Model.OSat
public import Lantana.BaseLogic.Model.OWit
public import Lantana.BaseLogic.Model.OInv
public import Lantana.BaseLogic.Model.MapBigOp

/-! # The user-facing predicates on obligations and witnesses

Rocq `lantana/base_logic/opreds.v` §14.1–14.2, the part that does not involve the forest: the
fuel encoding (`modelFuel ℓ μ := Measure.rep ℓ ((1 + ▽) * μ)`, D10 item 6), the predicates
`oblAssigned` (half of the ghost fraction; the other quarters are the children shares
`oblShare`), `oblDischarged`, `oblFuel`, `oblInv` (an `OSat.oinv` at a quarter), `witCred`,
`witLayer`, and the witness-induction package `witFuels` with `collectFuels`, with their pure
and ghost rules (fuel arithmetic, invariant allocation and access, `witFuels_add/decr`). The
forest-dependent predicates (`parKids`, `thDone`) and the model-update rules are in `OPreds`.
These are the implementations behind the sealed interface `Lantana.ProgramLogic.OblForest`.
-/

@[expose] public noncomputable section

namespace Lantana.Model

open Iris Iris.BI Iris.ProofMode Iris.Std LawfulPartialMap
open Ordinals Ordinal
open scoped Lantana.Measure

/-! ## The fuel encoding -/

/-- The model fuel of a user fuel `μ` at layer `ℓ`: each unit carries an extra `▽` (D10 item 6,
Rocq `measure_rep ℓ ((1 ⊕ ▽) × μ)`). -/
def modelFuel (ℓ : Layer) (μ : Measure) : Fuel := Measure.rep ℓ ((1 + ▽) * μ)

theorem modelFuel_add (ℓ : Layer) (μ₁ μ₂ : Measure) :
    modelFuel ℓ (μ₁ + μ₂) = modelFuel ℓ μ₁ +ₕ modelFuel ℓ μ₂ := by
  unfold modelFuel
  rw [Measure.rep_mul, Measure.rep_mul, Measure.rep_mul, Measure.rep_add ℓ μ₁ μ₂, jmul_nadd]

theorem modelFuel_mono {ℓ₁ ℓ₂ : Layer} {μ₁ μ₂ : Measure} (hℓ : ℓ₁ ≤ ℓ₂)
    (h : Measure.rep ℓ₁ μ₁ ≤ Measure.rep ℓ₂ μ₂) :
    modelFuel ℓ₁ μ₁ ≤ modelFuel ℓ₂ μ₂ := by
  unfold modelFuel
  rw [Measure.rep_mul, Measure.rep_mul]
  exact jmul_le_jmul (Measure.rep_layer_le hℓ _) h

theorem modelFuel_one (ℓ : Layer) : modelFuel ℓ 1 = 1 +ₕ Measure.rep ℓ ▽ := by
  unfold modelFuel
  rw [Measure.rep_mul, Measure.rep_ofNat, jmul_one, Measure.rep_add, Measure.rep_ofNat]

/-- One unit at a higher layer dominates any fuel at a lower layer. -/
theorem modelFuel_le_extend {ℓ₁ ℓ₂ : Layer} (h : ℓ₁ < ℓ₂) (μ : Measure) :
    modelFuel ℓ₁ μ ≤ modelFuel ℓ₂ 1 := by
  rw [modelFuel_one]
  refine Ordinal.le_trans (le_fairMeasureUb _) (Ordinal.le_trans (Measure.rep_extend h _) ?_)
  exact le_nadd_self _ _

theorem modelFuel_mul_extend (ℓ : Layer) (μ : Measure) :
    modelFuel ℓ (μ * ▽) = modelFuel ℓ μ ×ⱼ Measure.rep ℓ ▽ := by
  unfold modelFuel
  rw [Measure.rep_mul, Measure.rep_mul, Measure.rep_mul, jmul_assoc]

/-- Scaling a fuel by `α` with `α₀ < α` leaves a copy of the fuel. -/
theorem jmul_succ_le {c α₀ α : Fuel} (h : α₀ < α) :
    c +ₕ c ×ⱼ α₀ ≤ c ×ⱼ α := by
  rw [← jmul_succ]
  exact jmul_le_jmul Ordinal.le_rfl (succ_le_of_lt h)

theorem Qp.half_add (p q : Qp) : (p + q).half = p.half + q.half :=
  Subtype.ext (by grind)

namespace OPreds

variable {GF : BundledGFunctors} [OSatGS GF]

/-! ## Definitions (Rocq `opreds.v` §14.1) -/

/-- A fraction `q` of the assignment of `k`, as the user sees it: half of the ghost fraction
(the two other quarters are the shares of the children predicates). -/
@[lantana_alias omodel.oblP_assigned]
def oblAssigned (k : Oid) (q : Qp) : IProp GF :=
  iprop(OSat.elem k ∗ OSat.assigned k q.half)

@[lantana_alias omodel.oblP_discharged]
def oblDischarged (k : Oid) : IProp GF :=
  iprop(OSat.elem k ∗ OSat.discharged k)

/-- Fuel of `k` as a model fuel. -/
@[lantana_alias omodel.oblP_fuel_val]
def oblFuelVal (k : Oid) (α : Fuel) : IProp GF :=
  iprop(OSat.elem k ∗ OSat.fuel k α)

@[lantana_alias omodel.oblP_fuel]
def oblFuel (k : Oid) (ℓ : Layer) (μ : Measure) : IProp GF :=
  oblFuelVal k (modelFuel ℓ μ)

/-- The children-share of the assignment of `k` (a quarter). -/
@[lantana_alias omodel.oblP_share]
def oblShare (k : Oid) : IProp GF :=
  iprop(OSat.elem k ∗ OSat.assigned k (Qp.half (Qp.half 1)))

@[lantana_alias omodel.oblP_inv]
def oblInv [InvGS GF] (N : Namespace) (k : Oid) (P R : IProp GF) : IProp GF :=
  iprop(OSat.elem k ∗ OSat.oinv N k (Qp.half (Qp.half 1)) P R)

@[lantana_alias omodel.witP_bound_val]
def witBoundVal [OWitGS GF] (k : Oid) (α : Fuel) : IProp GF :=
  iprop(OSat.elem k ∗ OWit.bound k α)

@[lantana_alias omodel.witP_cred]
def witCred [OWitGS GF] (k : Oid) (a : Fuel) : IProp GF :=
  iprop(OSat.elem k ∗ OWit.cred k a)

/-- The witness of `k` is at layer `ℓ`: its bound and its fuel bound are measures at `ℓ`. -/
@[lantana_alias omodel.witP_layer]
def witLayer [OWitGS GF] (k : Oid) (ℓ : Layer) : IProp GF :=
  iprop((∃ μ : Measure, witBoundVal k (fairMeasureUb (Measure.rep ℓ μ))) ∗
    ∃ μ : Measure, OSat.bound k (Measure.rep ℓ μ))

/-- Fuels of other obligations scaled by `α` (Rocq `collect_fuels`). -/
@[lantana_alias omodel.collect_fuels]
def collectFuels (α : Fuel) (F : OidMap (Layer × Measure)) : IProp GF :=
  iprop([∗map] s ↦ lm ∈ F, oblFuelVal s (modelFuel lm.1 lm.2 ×ⱼ α))

/-- The witness-induction package (Rocq `wit_fuels`). -/
@[lantana_alias omodel.wit_fuels]
def witFuels [OWitGS GF] (k : Oid) (ℓ : Layer) (α : Fuel) (F : OidMap (Layer × Measure)) :
    IProp GF :=
  iprop(∃ μ : Measure, ⌜α ≤ fairMeasureUb (Measure.rep ℓ μ)⌝ ∗ witBoundVal k α ∗
    collectFuels α F ∗ ∃ μ : Measure, OSat.bound k (Measure.rep ℓ μ))

/-- The content of a user obligation invariant (Rocq `oblP_variant`). -/
@[lantana_alias omodel.oblP_variant]
def oblVariant (k : Oid) (P R : IProp GF) : IProp GF :=
  iprop((oblAssigned k (Qp.half 1) ∗ P) ∨ (oblDischarged k ∗ R))

/-! ## Instances -/

instance oblAssigned_timeless (k : Oid) (q : Qp) : Timeless (oblAssigned (GF := GF) k q) := by
  unfold oblAssigned; infer_instance

instance oblDischarged_persistent (k : Oid) : Persistent (oblDischarged (GF := GF) k) := by
  unfold oblDischarged; infer_instance

instance oblDischarged_timeless (k : Oid) : Timeless (oblDischarged (GF := GF) k) := by
  unfold oblDischarged; infer_instance

instance oblFuelVal_timeless (k : Oid) (α : Fuel) : Timeless (oblFuelVal (GF := GF) k α) := by
  unfold oblFuelVal; infer_instance

instance oblFuel_timeless (k : Oid) (ℓ : Layer) (μ : Measure) :
    Timeless (oblFuel (GF := GF) k ℓ μ) := by
  unfold oblFuel; infer_instance

instance oblShare_timeless (k : Oid) : Timeless (oblShare (GF := GF) k) := by
  unfold oblShare; infer_instance

instance oblInv_persistent [InvGS GF] (N : Namespace) (k : Oid) (P R : IProp GF) :
    Persistent (oblInv N k P R) := by
  unfold oblInv; infer_instance

instance oblInv_contractive_left [InvGS GF] (N : Namespace) (k : Oid) (R : IProp GF) :
    OFE.Contractive (fun P => oblInv (GF := GF) N k P R) where
  distLater_dist h := sep_ne.ne .rfl (OFE.Contractive.distLater_dist
    (f := fun P => OSat.oinv N k (Qp.half (Qp.half 1)) P R) h)

instance oblInv_contractive_right [InvGS GF] (N : Namespace) (k : Oid) (P : IProp GF) :
    OFE.Contractive (fun R => oblInv (GF := GF) N k P R) where
  distLater_dist h := sep_ne.ne .rfl (OFE.Contractive.distLater_dist
    (f := fun R => OSat.oinv N k (Qp.half (Qp.half 1)) P R) h)

instance witBoundVal_persistent [OWitGS GF] (k : Oid) (α : Fuel) :
    Persistent (witBoundVal (GF := GF) k α) := by
  unfold witBoundVal; infer_instance

instance witBoundVal_timeless [OWitGS GF] (k : Oid) (α : Fuel) :
    Timeless (witBoundVal (GF := GF) k α) := by
  unfold witBoundVal; infer_instance

instance witCred_timeless [OWitGS GF] (k : Oid) (a : Fuel) : Timeless (witCred (GF := GF) k a) := by
  unfold witCred; infer_instance

instance witLayer_persistent [OWitGS GF] (k : Oid) (ℓ : Layer) :
    Persistent (witLayer (GF := GF) k ℓ) := by
  unfold witLayer; infer_instance

instance witLayer_timeless [OWitGS GF] (k : Oid) (ℓ : Layer) :
    Timeless (witLayer (GF := GF) k ℓ) := by
  unfold witLayer; infer_instance

instance collectFuels_timeless (α : Fuel) (F : OidMap (Layer × Measure)) :
    Timeless (collectFuels (GF := GF) α F) := by
  unfold collectFuels; infer_instance

instance witFuels_timeless [OWitGS GF] (k : Oid) (ℓ : Layer) (α : Fuel)
    (F : OidMap (Layer × Measure)) :
    Timeless (witFuels (GF := GF) k ℓ α F) := by
  unfold witFuels; infer_instance

instance collectFuels_empty_persistent (α : Fuel) :
    Persistent (collectFuels (GF := GF) α ∅) := by
  unfold collectFuels
  rw [BigSepM.bigSepM_empty.to_eq]
  infer_instance

instance witFuels_empty_persistent [OWitGS GF] (k : Oid) (ℓ : Layer) (α : Fuel) :
    Persistent (witFuels (GF := GF) k ℓ α ∅) := by
  unfold witFuels; infer_instance

/-- `oblAssigned k` is fractional (Rocq `oblP_assigned_fractional`). -/
instance oblAssigned_fractional (k : Oid) : Fractional (oblAssigned (GF := GF) k) where
  fractional p q := by
    unfold oblAssigned
    rw [Qp.half_add, ((OSat.assigned_fractional k).fractional p.half q.half).to_eq]
    constructor
    · iintro ⟨#He, Hp, Hq⟩
      isplitl [Hp]
      · iframe Hp
        iexact He
      · iframe Hq
        iexact He
    · iintro ⟨⟨#He, Hp⟩, ⟨-, Hq⟩⟩
      iframe Hp Hq
      iexact He

instance oblAssigned_asFractional (k : Oid) (q : Qp) {ioΦ ioq : InOut} :
    AsFractional (oblAssigned (GF := GF) k q) ioΦ (oblAssigned k) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := oblAssigned_fractional k

/-! ## Pure and ghost rules (Rocq `opreds.v` §14.2) -/

@[lantana_alias omodel.oblP_assigned_discharged_false]
theorem oblAssigned_discharged_false (k : Oid) (q : Qp) :
    oblAssigned (GF := GF) k q ⊢ oblDischarged k -∗ False := by
  unfold oblAssigned oblDischarged
  iintro ⟨-, Ha⟩ ⟨-, Hd⟩
  iapply OSat.assigned_discharged_false k q.half $$ [$Ha $Hd]

@[lantana_alias omodel.oblP_fuel_mon_gen]
theorem oblFuel_mono_gen (k : Oid) {ℓ₁ ℓ₂ : Layer} {μ₁ μ₂ : Measure}
    (hℓ : ℓ₁ ≤ ℓ₂)
    (h : Measure.rep ℓ₁ μ₁ ≤ Measure.rep ℓ₂ μ₂) :
    oblFuel (GF := GF) k ℓ₂ μ₂ ⊢ |==> oblFuel k ℓ₁ μ₁ := by
  unfold oblFuel oblFuelVal
  iintro ⟨#He, Hf⟩
  imod OSat.fuel_mon (modelFuel_mono hℓ h) $$ Hf with Hf
  imodintro
  iframe Hf
  iexact He

@[lantana_alias omodel.oblP_fuel_add]
theorem oblFuel_add (k : Oid) (ℓ : Layer) (μ₁ μ₂ : Measure) :
    oblFuel (GF := GF) k ℓ (μ₁ + μ₂) ⊣⊢
      oblFuel k ℓ μ₁ ∗ oblFuel k ℓ μ₂ := by
  unfold oblFuel oblFuelVal
  rw [modelFuel_add, (OSat.fuel_split k _ _).to_eq]
  constructor
  · iintro ⟨#He, H₁, H₂⟩
    isplitl [H₁]
    · iframe H₁
      iexact He
    · iframe H₂
      iexact He
  · iintro ⟨⟨#He, H₁⟩, ⟨-, H₂⟩⟩
    iframe H₁ H₂
    iexact He

@[lantana_alias omodel.oblP_fuel_extend]
theorem oblFuel_extend (k : Oid) {ℓ₁ ℓ₂ : Layer} (h : ℓ₁ < ℓ₂) (μ : Measure) :
    oblFuel (GF := GF) k ℓ₂ 1 ⊢ |==> oblFuel k ℓ₁ μ := by
  unfold oblFuel oblFuelVal
  iintro ⟨#He, Hf⟩
  imod OSat.fuel_mon (modelFuel_le_extend h μ) $$ Hf with Hf
  imodintro
  iframe Hf
  iexact He

@[lantana_alias omodel.witP_cred_mon]
theorem witCred_mono [OWitGS GF] (k : Oid) {a₀ a₁ : Fuel} (h : a₀ ≤ a₁) :
    witCred (GF := GF) k a₁ ⊢ |==> witCred k a₀ := by
  unfold witCred
  iintro ⟨#He, Hc⟩
  imod OWit.cred_mon h $$ Hc with Hc
  imodintro
  iframe Hc
  iexact He

@[lantana_alias omodel.witP_cred_split]
theorem witCred_split [OWitGS GF] (k : Oid) (a₀ a₁ : Fuel) :
    witCred (GF := GF) k (a₀ +ₕ a₁) ⊣⊢ witCred k a₀ ∗ witCred k a₁ := by
  unfold witCred
  rw [(OWit.cred_split k a₀ a₁).to_eq]
  constructor
  · iintro ⟨#He, H₁, H₂⟩
    isplitl [H₁]
    · iframe H₁
      iexact He
    · iframe H₂
      iexact He
  · iintro ⟨⟨#He, H₁⟩, ⟨-, H₂⟩⟩
    iframe H₁ H₂
    iexact He

@[lantana_alias omodel.witP_layer_oblG_bound]
theorem witLayer_bound [OWitGS GF] (k : Oid) (ℓ : Layer) :
    witLayer (GF := GF) k ℓ ⊢ ∃ μ : Measure, OSat.bound k (Measure.rep ℓ μ) := by
  unfold witLayer
  iintro ⟨-, H⟩
  iexact H

/-! ### Witness induction -/

@[lantana_alias omodel.wit_fuels_init]
theorem witFuels_init [OWitGS GF] (k : Oid) (ℓ : Layer) :
    witLayer (GF := GF) k ℓ ⊢ ∃ α : Fuel, witFuels k ℓ α ∅ := by
  unfold witLayer witFuels collectFuels
  iintro ⟨⟨%μ, #Hb⟩, ⟨%μ', #Hβ⟩⟩
  iexists fairMeasureUb (Measure.rep ℓ μ)
  iexists μ
  isplitr
  · ipureintro
    exact Ordinal.le_rfl
  isplitl []
  · iexact Hb
  isplitl []
  · iapply BigSepM.bigSepM_empty.mpr
    iempintro
  · iexists μ'
    iexact Hβ

@[lantana_alias omodel.wit_fuels_witP_layer]
theorem witFuels_layer [OWitGS GF] (k : Oid) (ℓ : Layer) (α : Fuel)
    (F : OidMap (Layer × Measure)) :
    witFuels (GF := GF) k ℓ α F ⊢ witLayer k ℓ := by
  unfold witFuels witLayer witBoundVal
  iintro ⟨%μ, %hα, ⟨#He, #Hb⟩, -, ⟨%μ', #Hβ⟩⟩
  isplitl []
  · iexists μ
    isplitl []
    · iexact He
    · iapply OWit.bound_mon hα $$ Hb
  · iexists μ'
    iexact Hβ

/-- Add the fuel of an obligation at a higher layer to the package (Rocq `wit_fuels_add`); an
earlier entry for `f` is dropped. -/
@[lantana_alias omodel.wit_fuels_add]
theorem witFuels_add [OWitGS GF] (k : Oid) {ℓ₁ ℓ₂ : Layer} (α : Fuel)
    (F : OidMap (Layer × Measure))
    (f : Oid) (μ : Measure) (h : ℓ₁ < ℓ₂) :
    witFuels (GF := GF) k ℓ₁ α F ⊢
      oblFuel f ℓ₂ (μ * ▽) ==∗ witFuels k ℓ₁ α (insert F f (ℓ₂, μ)) := by
  unfold witFuels collectFuels oblFuel oblFuelVal
  iintro ⟨%μ', %hα, Hb, HF, Hβ⟩ ⟨#He, Hf⟩
  have hle : modelFuel ℓ₂ μ ×ⱼ α ≤ modelFuel ℓ₂ (μ * ▽) := by
    rw [modelFuel_mul_extend]
    refine jmul_le_jmul Ordinal.le_rfl (Ordinal.le_trans hα (Measure.rep_extend h _))
  imod OSat.fuel_mon hle $$ Hf with Hf
  imodintro
  iexists μ'
  isplitr
  · ipureintro
    exact hα
  iframe Hb Hβ
  iapply BigSepM.bigSepM_insert_delete.2
  isplitl [Hf]
  · iframe Hf
    iexact He
  · iapply BigSepM.bigSepM_subseteq delete_subset_self $$ HF

/-- Spending one credit strictly lowers the bound and releases one copy of every collected
fuel (Rocq `wit_fuels_decr`). -/
@[lantana_alias omodel.wit_fuels_decr]
theorem witFuels_decr [OWitGS GF] (k : Oid) (ℓ : Layer) (α : Fuel)
    (F : OidMap (Layer × Measure)) :
    witFuels (GF := GF) k ℓ α F ⊢ witCred k 1 ==∗
      ∃ α₀ : Fuel, ⌜α₀ < α⌝ ∗ witFuels k ℓ α₀ F ∗
        [∗map] f ↦ lm ∈ F, oblFuel f lm.1 lm.2 := by
  unfold witFuels collectFuels witBoundVal witCred oblFuel
  iintro ⟨%μ, %hα, ⟨#He, #Hb⟩, HF, ⟨%μ', #Hβ⟩⟩ ⟨-, Hc⟩
  imod OWit.cred_spend zero_lt_one $$ [$Hb $Hc] with ⟨%α₀, %hα₀, #Hb₀⟩
  have hpt : ∀ (s : Oid) (lm lm' : Layer × Measure), lm = lm' →
      oblFuelVal (GF := GF) s (modelFuel lm.1 lm.2 ×ⱼ α) ⊢
        |==> (oblFuelVal s (modelFuel lm'.1 lm'.2 ×ⱼ α₀) ∗
          oblFuelVal s (modelFuel lm.1 lm.2)) := by
    intro s lm lm' hlm
    subst hlm
    unfold oblFuelVal
    iintro ⟨#He', Hf⟩
    imod OSat.fuel_mon_split (jmul_succ_le hα₀) $$ Hf with ⟨Hf₀, Hf⟩
    imodintro
    isplitl [Hf]
    · iframe Hf
      iexact He'
    · iframe Hf₀
      iexact He'
  imod bigSepM_mapForall2_bupd (mapForall2_refl (fun _ _ => rfl) F) hpt $$ HF with ⟨HF, HC⟩
  imodintro
  iexists α₀
  isplitr
  · ipureintro
    exact hα₀
  iframe HC
  iexists μ
  isplitr
  · ipureintro
    exact Ordinal.le_of_lt (Ordinal.lt_of_lt_of_le hα₀ hα)
  isplitl []
  · isplitl []
    · iexact He
    · iexact Hb₀
  iframe HF
  iexists μ'
  iexact Hβ

/-! ### Invariants over obligations -/

@[lantana_alias omodel.oblP_inv_alloc_assigned]
theorem oblInv_alloc_assigned [InvGS GF] (E : CoPset) (N : Namespace) (k : Oid)
    (P R : IProp GF) :
    ⊢@{IProp GF} oblAssigned k (Qp.half 1) -∗ ▷ P ={E}=∗ oblInv N k P R := by
  unfold oblAssigned oblInv
  iintro ⟨#He, Ha⟩ HP
  imod OSat.oinv_alloc_assigned E N k (Qp.half (Qp.half 1)) P R $$ [$Ha $HP] with H
  imodintro
  iframe H
  iexact He

@[lantana_alias omodel.oblP_inv_alloc_discharged]
theorem oblInv_alloc_discharged [InvGS GF] (E : CoPset) (N : Namespace) (k : Oid)
    (P R : IProp GF) :
    ⊢@{IProp GF} oblDischarged k -∗ ▷ R ={E}=∗ oblInv N k P R := by
  unfold oblDischarged oblInv
  iintro ⟨#He, #Hd⟩ HR
  imod OSat.oinv_alloc_discharged E N k (Qp.half (Qp.half 1)) P R $$ [$Hd $HR] with H
  imodintro
  iframe H
  iexact He

/-- The user variant and the ghost variant agree given that `k` exists. -/
theorem oblVariant_eq (k : Oid) (P R : IProp GF) :
    OSat.elem k ∗ OSat.variant k (Qp.half (Qp.half 1)) P R ⊢@{IProp GF} oblVariant k P R := by
  unfold oblVariant oblAssigned oblDischarged
  iintro ⟨#He, H⟩
  icases (OSat.variant_unfold k _ P R).1 $$ H with (⟨Ha, HP⟩ | ⟨Hd, HR⟩)
  · ileft
    iframe Ha HP
    iexact He
  · iright
    iframe Hd HR
    iexact He

theorem oblVariant_eq' (k : Oid) (P R : IProp GF) :
    oblVariant k P R ⊢@{IProp GF} OSat.variant k (Qp.half (Qp.half 1)) P R := by
  unfold oblVariant oblAssigned oblDischarged
  iintro (⟨⟨-, Ha⟩, HP⟩ | ⟨⟨-, Hd⟩, HR⟩)
  · iapply (OSat.variant_unfold k _ P R).2
    ileft
    iframe
  · iapply (OSat.variant_unfold k _ P R).2
    iright
    iframe

@[lantana_alias omodel.oblP_inv_acc]
theorem oblInv_acc [InvGS GF] (E : CoPset) (N : Namespace) (k : Oid) (P R : IProp GF)
    (hN : ↑N ⊆ E) :
    oblInv N k P R ⊢@{IProp GF} |={E, E \ ↑N}=> ▷ oblVariant k P R ∗
      (▷ oblVariant k P R ={E \ ↑N, E}=∗ True) := by
  unfold oblInv
  iintro ⟨#He, #I⟩
  imod OSat.oinv_acc E N k _ P R hN $$ I with ⟨HV, Hclose⟩
  imodintro
  isplitl [HV]
  · inext
    iapply oblVariant_eq k P R
    iframe HV
    iexact He
  · iintro HV
    iapply Hclose
    inext
    iapply oblVariant_eq' k P R $$ HV

end OPreds

end Lantana.Model
