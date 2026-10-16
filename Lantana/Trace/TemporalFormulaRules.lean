/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TemporalFormulaRun

/-! # Rules for the temporal formulas `alwaysI`, `untilI`, `finallyI`, `untilIDone`

Rocq `lantana/trace/temporal_formula_rules.v`: access, allocation (registration), discharge
and fractions, with the proof-mode instances for `iinv`, and the guarantees: a registered
invariant guarantees an always (`guar_alwaysI`), a registered obligation invariant an until
(`guar_untilI`), a done until an until with any left reading (`guar_untilIDone`). Each rule is
stated for the readings `G` (`_guar`/`_as` forms) and for the canonical readings. The
guarantees inferred from the shape of a formula (`GuarOf`) close the file.

The guarantee of an until has the rank `succ (succ (fairMeasureUb fu))` for the fuel `fu` of
its obligation where the guarantee is used: after the step the obligation, read with a credit
allocated by the step (`ALC_credits`), has a fuel `fu' ≤ fu`, whose measure is below
`fairMeasureUb fu`, and `untilRun` continues from there.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode
open Lantana.Model
open Iris.Std LawfulPartialMap
open scoped Lantana.TrSpec Lantana.TrProp

variable {Expr State Val : Type} {GF : BundledGFunctors} [Language Expr State Val]
-- Named, to be passed explicitly to `TrSpec.canon_le` (see "Always" below).
variable [instM : ModelGS GF] [instT : TemporalGS Expr State GF] [StateInterp Expr State GF]

section Rules
variable {E : CoPset} {N : Namespace} {k : Oid} {q : Qp} {P Q : IProp GF}

/-! ## Always

A `⊑ₛ` premise is given as `@TrSpec.canon_le _ _ _ _ _ instM instT _ _ _ hG`, with the ambient
instances explicit: elaborated against the expected `⊑ₛ`, the application would get the
instances bound by `⊑ₛ` for its own instance arguments (as noted in `LantanaTest.Guarantee`;
holes do not suffice under a `⊑ₛ` rule such as `TrSpec.always_mono`). -/

@[lantana_alias alwaysI_guar_acc]
theorem alwaysIGuar_acc {G : TrSpec Expr State GF} (hN : ↑N ⊆ E) :
    alwaysIGuar N P G ⊢ |={E, E \ ↑N}=> ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True) :=
  (alwaysIGuar_inv N P G).trans (wand_entails (inv_acc hN))

@[lantana_alias alwaysI_as_acc]
theorem alwaysIAs_acc {V : IProp GF} (hN : ↑N ⊆ E) :
    alwaysIAs (Expr := Expr) (State := State) N P V ⊢
      |={E, E \ ↑N}=> ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
  rw [alwaysIAs_eq]; exact alwaysIGuar_acc hN

@[lantana_alias alwaysI_acc]
theorem alwaysI_acc (hN : ↑N ⊆ E) :
    alwaysI N P ⊢ |={E, E \ ↑N}=> ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
  rw [alwaysI_eq]; exact alwaysIGuar_acc hN

/-! ### Proof-mode integration: `iinv` opens the always formulas like invariants -/

@[lantana_alias into_inv_alwaysI_guar]
instance intoInv_alwaysIGuar (N : Namespace) (P : IProp GF) (G : TrSpec Expr State GF) :
    IntoInv (alwaysIGuar N P G) N := {}

set_option synthInstance.checkSynthOrder false in
@[lantana_alias into_acc_alwaysI_guar]
instance intoAcc_alwaysIGuar (N : Namespace) (P : IProp GF) (G : TrSpec Expr State GF) E :
    IntoAcc (X := Unit) (alwaysIGuar N P G) (↑N ⊆ E) iprop(True) (fupd E (E \ ↑N))
      (fupd (E \ ↑N) E) (fun _ => iprop(▷ P)) (fun _ => iprop(▷ P)) (fun _ => none) where
  into_acc := by
    dsimp only [accessor, Option.getD]
    iintro %hN #H -
    imod alwaysIGuar_acc hN $$ H with ⟨HP, Hclose⟩
    iexists ()
    imodintro
    isplitl [HP]
    · iexact HP
    · iintro HP
      iapply (BIFUpdate.mono true_emp.mp)
      iapply Hclose $$ HP

@[lantana_alias into_inv_alwaysI_as]
instance intoInv_alwaysIAs (N : Namespace) (P V : IProp GF) :
    IntoInv (alwaysIAs (Expr := Expr) (State := State) N P V) N := {}

set_option synthInstance.checkSynthOrder false in
@[lantana_alias into_acc_alwaysI_as]
instance intoAcc_alwaysIAs (N : Namespace) (P V : IProp GF) E :
    IntoAcc (X := Unit) (alwaysIAs (Expr := Expr) (State := State) N P V) (↑N ⊆ E) iprop(True)
      (fupd E (E \ ↑N)) (fupd (E \ ↑N) E) (fun _ => iprop(▷ P)) (fun _ => iprop(▷ P))
      (fun _ => none) where
  into_acc := by
    rw [alwaysIAs_eq]
    exact (intoAcc_alwaysIGuar N P _ E).into_acc

@[lantana_alias into_inv_alwaysI]
instance intoInv_alwaysI (N : Namespace) (P : IProp GF) :
    IntoInv (alwaysI (Expr := Expr) (State := State) N P) N := {}

set_option synthInstance.checkSynthOrder false in
@[lantana_alias into_acc_alwaysI]
instance intoAcc_alwaysI (N : Namespace) (P : IProp GF) E :
    IntoAcc (X := Unit) (alwaysI (Expr := Expr) (State := State) N P) (↑N ⊆ E) iprop(True)
      (fupd E (E \ ↑N)) (fupd (E \ ↑N) E) (fun _ => iprop(▷ P)) (fun _ => iprop(▷ P))
      (fun _ => none) where
  into_acc := by
    rw [alwaysI_eq]
    exact (intoAcc_alwaysIGuar N P _ E).into_acc

/-! ### Registration and allocation -/

/-- Registering an existing invariant, with a later-guarded guarantee of its content
(Rocq `alwaysI_register_guar`). -/
@[lantana_alias alwaysI_register_guar]
theorem alwaysIGuar_register {G : TrSpec Expr State GF} (hN : ↑N ⊆ E) :
    inv N P ⊢ ▷ (P ⊨ₜ G) -∗ |={E}=>m alwaysIGuar N P G := by
  rw [alwaysIGuar_unfold]
  iintro #Hinv #HG
  iapply mupd_read_fupd
  iintro %h %n %σ %tp HI TI
  imod inv_acc hN $$ Hinv with ⟨HP, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hcl %g %i %Ω %W MI
  ihave #C : ▷ record G n $$ [HP HI MI]
  · iapply guar_elim_later_guar P G h n σ tp g i Ω W $$ HG
    iframe HP HI MI
  ihave #HE := historyInterp_histEvent_now h n σ tp $$ HI
  iframe MI
  imod Hcl with -
  imod Hclose $$ HP with -
  imod savedTrI_alloc G.internal with ⟨%γ, #Hγ⟩
  iunfold regState at TI
  imod regRegister regEntryInterp (.always N γ) h n σ tp $$ TI [] HI with ⟨HI, TI, %j, #Hj⟩
  · iintro %st -
    simp only [regEntryInterp]
    iexists P, G
    iframe Hγ Hinv
    iexact HG
  imodintro
  iframe HI
  isplitl [TI]
  · iunfold regState
    iexact TI
  iexists j, n, γ, (σ, tp)
  iframe Hj HE Hγ Hinv HG
  iexact C

/-- Registering an existing invariant, read as a consequence `V` of its content
(Rocq `alwaysI_register`). -/
@[lantana_alias alwaysI_register]
theorem alwaysI_register {V : IProp GF} (hN : ↑N ⊆ E) :
    inv N P ⊢ □ (P -∗ V) -∗ |={E}=>m alwaysIAs (Expr := Expr) (State := State) N P V := by
  rw [alwaysIAs_eq]
  iintro #Hinv #HPV
  iapply alwaysIGuar_register hN $$ Hinv []
  inext
  iapply guar_mono $$ HPV
  iapply guar_canon

@[lantana_alias alwaysI_alloc_guar]
theorem alwaysIGuar_alloc {G : TrSpec Expr State GF} :
    ▷ (P ⊨ₜ G) ⊢ ▷ P -∗ |={E}=>m alwaysIGuar N P G := by
  rw [alwaysIGuar_unfold]
  iintro #HG HP
  iapply mupd_read
  iintro %h %n %σ %tp %g %i %Ω %W HI TI MI
  ihave #C : ▷ record G n $$ [HP HI MI]
  · iapply guar_elim_later_guar P G h n σ tp g i Ω W $$ HG
    iframe HP HI MI
  ihave #HE := historyInterp_histEvent_now h n σ tp $$ HI
  iframe MI
  imod savedTrI_alloc G.internal with ⟨%γ, #Hγ⟩
  imod inv_alloc N E P $$ HP with #Hinv
  iunfold regState at TI
  imod regRegister regEntryInterp (.always N γ) h n σ tp $$ TI [] HI with ⟨HI, TI, %j, #Hj⟩
  · iintro %st -
    simp only [regEntryInterp]
    iexists P, G
    iframe Hγ Hinv
    iexact HG
  imodintro
  iframe HI
  isplitl [TI]
  · iunfold regState
    iexact TI
  iexists j, n, γ, (σ, tp)
  iframe Hj HE Hγ Hinv HG
  iexact C

@[lantana_alias alwaysI_alloc]
theorem alwaysI_alloc : ▷ P ⊢ |={E}=>m alwaysI N P := by
  rw [alwaysI_eq]
  iintro HP
  iapply alwaysIGuar_alloc $$ [] HP
  inext
  iapply guar_canon

/-! ### Guarantees -/

/-- A registered always guarantees the always of its reading (Rocq `guar_alwaysI_guar`): the
certificate at `n` from the bundle, then the loop from `n + 1`. -/
@[lantana_alias guar_alwaysI_guar]
theorem guar_alwaysIGuar {G : TrSpec Expr State GF} :
    ⊢@{IProp GF} alwaysIGuar N P G ⊨ₜ □ₛ G := by
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, -, A⟩
  iunfold alwaysIGuar at A
  icases A with ⟨%j, %r, %γa, %st, #Hj, #HE, #Hγ, -, -, #AC⟩
  icases historyInterp_histEvent_lookup h n σ tp r st $$ [HI HE] with %hr
  · iframe HI HE
  icases historyInterp_wf h n σ tp $$ HI with %⟨hlen, -⟩
  have hrn : r ≤ n := by
    have := (List.getElem?_eq_some_iff.mp hr).1
    omega
  iapply record_intro
  imodintro
  iintro %Sys %l %h' %g %v %Ω' %W' %τf %γ %σ' %tp' #ST %⟨hbeh, hfs, hlb, hht⟩ #B HS
  ihave #C := bundleAlwaysCert l n j r N γa G hrn $$ B Hj Hγ []
  · iintro %hr'
    subst hr'
    iexact AC
  have hU : ▷ iprop(G.internal ⟨n, τf⟩ ∧ TrIProp.always G.internal ⟨n + 1, τf⟩) ⊢
      (□ₛ G).internal ⟨n, τf⟩ :=
    TrIProp.defer_intro_later.trans (TrIProp.always_unfold G.internal ⟨n, τf⟩).mpr
  iapply hU
  inext
  isplit
  · iapply record_elim G $$ C ST %⟨hbeh, hfs, hlb, hht⟩ B HS
  · iapply alwaysRun Sys N γa G j r $$ ST Hj Hγ %h' %(n + 1) %σ' %tp' %g %v %Ω' %W' %τf %γ
      %⟨by omega, hbeh.next, hfs, hlb, hht⟩ HS

@[lantana_alias guar_alwaysI_as]
theorem guar_alwaysIAs {V : IProp GF} :
    ⊢@{IProp GF} alwaysIAs (Expr := Expr) (State := State) N P V ⊨ₜ □ₛ TrSpec.canon V := by
  rw [alwaysIAs_eq]; exact guar_alwaysIGuar

@[lantana_alias guar_alwaysI]
theorem guar_alwaysI : ⊢@{IProp GF} alwaysI N P ⊨ₜ □ₛ TrSpec.canon P := by
  rw [alwaysI_eq]; exact guar_alwaysIGuar

@[lantana_alias guar_alwaysI_as_valid]
theorem guar_alwaysIAs_valid {V : IProp GF} {G : TrSpec Expr State GF} (hG : ⊢ V ⊨ₜ G) :
    ⊢@{IProp GF} alwaysIAs (Expr := Expr) (State := State) N P V ⊨ₜ □ₛ G :=
  guar_alwaysIAs.trans (guar_weaken (TrSpec.always_mono
    (@TrSpec.canon_le _ _ _ _ _ instM instT _ _ _ hG)))

@[lantana_alias guar_alwaysI_valid]
theorem guar_alwaysI_valid {G : TrSpec Expr State GF} (hG : ⊢ P ⊨ₜ G) :
    ⊢@{IProp GF} alwaysI N P ⊨ₜ □ₛ G :=
  guar_alwaysI.trans (guar_weaken (TrSpec.always_mono
    (@TrSpec.canon_le _ _ _ _ _ instM instT _ _ _ hG)))

/-! ## Until -/

/-! ### Fractions -/

@[lantana_alias untilI_guar_frac_split]
theorem untilIGuar_frac_split {G₁ G₂ : TrSpec Expr State GF} {q₁ q₂ : Qp} (h : q = q₁ + q₂) :
    untilIGuar N k q P Q G₁ G₂ ⊢ untilIGuar N k q₁ P Q G₁ G₂ ∗ untilIGuar N k q₂ P Q G₁ G₂ := by
  subst h
  exact ((untilIGuar_fractional N k P Q G₁ G₂).fractional q₁ q₂).mp

@[lantana_alias untilI_guar_frac_add]
theorem untilIGuar_frac_add {G₁ G₂ G₁' G₂' : TrSpec Expr State GF} {q₁ q₂ : Qp}
    {P' Q' : IProp GF} (h : q = q₁ + q₂) :
    untilIGuar N k q₁ P Q G₁ G₂ ⊢ untilIGuar N k q₂ P' Q' G₁' G₂' -∗
      untilIGuar N k q P Q G₁ G₂ := by
  subst h
  simp only [untilIGuar_unfold]
  rw [Model.Qp.half_add, ((Obl.assigned_fractional k).fractional q₁.half q₂.half).to_eq]
  iintro ⟨A₁, #U⟩ ⟨A₂, -⟩
  iframe A₁ A₂
  iexact U

@[lantana_alias untilI_frac_split]
theorem untilI_frac_split {q₁ q₂ : Qp} (h : q = q₁ + q₂) :
    untilI N k q P Q ⊢ untilI N k q₁ P Q ∗ untilI N k q₂ P Q := by
  simp only [untilI_eq]; exact untilIGuar_frac_split h

@[lantana_alias untilI_frac_add]
theorem untilI_frac_add {q₁ q₂ : Qp} {P' Q' : IProp GF} (h : q = q₁ + q₂) :
    untilI N k q₁ P Q ⊢ untilI N k q₂ P' Q' -∗ untilI N k q P Q := by
  simp only [untilI_eq]; exact untilIGuar_frac_add h

/-! ### Allocation -/

/-- A strong until registers, with later-guarded guarantees of its formulas, and records the
left formula at the current position (Rocq `untilI_guar_init`). -/
@[lantana_alias untilI_guar_init]
theorem untilIGuar_init {G₁ G₂ : TrSpec Expr State GF} :
    Obl.assigned k 1 ⊢ ▷ (P ⊨ₜ G₁) -∗ ▷ (Q ⊨ₜ G₂) -∗ ▷ P -∗
      |={E}=>m untilIGuar N k 1 P Q G₁ G₂ := by
  rw [untilIGuar_unfold]
  unfold untilIGuarPers
  iintro Oa #HG₁ #HG₂ HP
  icases (Obl.assigned_halves k).mp $$ Oa with ⟨Oa, Oa'⟩
  iapply mupd_read
  iintro %h %n %σ %tp %g %i %Ω %W HI TI MI
  ihave #C : ▷ record G₁ n $$ [HP HI MI]
  · iapply guar_elim_later_guar P G₁ h n σ tp g i Ω W $$ HG₁
    iframe HP HI MI
  icases Obl.assigned_modelInterp_lookup k _ g i Ω W n tp.length $$ [Oa MI] with %hk
  · iframe Oa MI
  obtain ⟨fu, o, hk⟩ := hk
  ihave #EA := modelInterp_eventObl hk $$ MI
  ihave #HE := historyInterp_histEvent_now h n σ tp $$ HI
  iframe MI
  imod Obl.inv_alloc_assigned E N k P (untilDischarged k G₂) $$ Oa' HP with #OI
  imod savedTrI_alloc G₁.internal with ⟨%γP, #HγP⟩
  imod savedTrI_alloc G₂.internal with ⟨%γQ, #HγQ⟩
  iunfold regState at TI
  imod regRegister regEntryInterp (.until N k γP γQ) h n σ tp $$ TI [] HI
    with ⟨HI, TI, %j, #Hj⟩
  · iintro %st -
    simp only [regEntryInterp]
    iexists P, G₁, G₂
    iframe HγP HγQ OI
    iexact HG₁
  imodintro
  iframe HI
  isplitl [TI]
  · iunfold regState
    iexact TI
  iframe Oa
  iexists j, n, γP, γQ, (σ, tp), i, Ω, fu, o
  iframe Hj HE HγP HγQ OI HG₁ HG₂ EA
  iexact C

@[lantana_alias untilI_init]
theorem untilI_init : Obl.assigned k 1 ⊢ ▷ P -∗ |={E}=>m untilI N k 1 P Q := by
  rw [untilI_eq]
  iintro Oa HP
  iapply untilIGuar_init $$ Oa [] [] HP
  · inext
    iapply guar_canon
  · inext
    iapply guar_canon

/-- The obligation and the strong until at once: `k` is a new child of `p`, and the formulas
are chosen once `k` is known (Rocq `untilI_guar_alloc`). -/
@[lantana_alias untilI_guar_alloc]
theorem untilIGuar_alloc (p : Parent) (K : Oids) (ℓ : Layer) (μ : Measure) :
    parLe (GF := GF) p ℓ ⊢ Par.kids p K -∗
      |={E}=>m ∃ k : Oid, ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ oblKids k ∅ ∗ Obl.fuel k ℓ μ ∗
        Wit.layer k ℓ ∗
        ∀ (E' : CoPset) (N : Namespace) (P Q : IProp GF) (G₁ G₂ : TrSpec Expr State GF),
          ▷ (P ⊨ₜ G₁) -∗ ▷ (Q ⊨ₜ G₂) -∗ ▷ P -∗ |={E'}=>m untilIGuar N k 1 P Q G₁ G₂ := by
  iintro B Kp
  imod Obl.new E p K ℓ μ $$ B Kp with ⟨%k, %hk, Kp, Kk, Oa, F, #W⟩
  imodintro
  iexists k
  isplitr
  · ipureintro
    exact hk
  iframe Kp Kk F
  isplitr
  · iexact W
  iintro %E' %N' %P' %Q' %G₁ %G₂ HG₁ HG₂ HP
  iapply untilIGuar_init $$ Oa HG₁ HG₂ HP

/-- Allocation: a new obligation below `p` with its fuel and witness, and the right to turn it
into an until with any formulas. -/
@[lantana_alias untilI_alloc]
theorem untilI_alloc (p : Parent) (K : Oids) (ℓ : Layer) (μ : Measure) :
    parLe (GF := GF) p ℓ ⊢ Par.kids p K -∗
      |={E}=>m ∃ k : Oid, ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ oblKids k ∅ ∗ Obl.fuel k ℓ μ ∗
        Wit.layer k ℓ ∗
        ∀ (E' : CoPset) (N : Namespace) (P Q : IProp GF), ▷ P -∗ |={E'}=>m untilI N k 1 P Q := by
  iintro B Kp
  imod Obl.new E p K ℓ μ $$ B Kp with ⟨%k, %hk, Kp, Kk, Oa, F, #W⟩
  imodintro
  iexists k
  isplitr
  · ipureintro
    exact hk
  iframe Kp Kk F
  isplitr
  · iexact W
  iintro %E' %N' %P' %Q' HP
  iapply untilI_init $$ Oa HP

/-! ### Done untils -/

/-- A done until from a fresh obligation: `k`, a childless child of `p`, is discharged at once
with `Q` at hand (Rocq `untilI_done_guar_init`). -/
@[lantana_alias untilI_done_guar_init]
theorem untilIDoneGuar_init {G₂ : TrSpec Expr State GF} (p : Parent) (K : Oids) (hk : k ∈ K) :
    Obl.assigned k 1 ⊢ Par.kids p K -∗ oblKids k ∅ -∗ ▷ (Q ⊨ₜ G₂) -∗ Q -∗
      |={E}=>m untilIDoneGuar k Q G₂ ∗ Par.kids p (K.erase k) := by
  rw [untilIDoneGuar_unfold]
  iintro Oa Kp Kk #HG₂ HQ
  imod Obl.discharge_leaf E p K k hk $$ Kp Kk Oa with ⟨Kp, #D⟩
  imodintro
  iframe HQ Kp
  isplitr
  · iexact D
  · iexact HG₂

@[lantana_alias untilI_done_init]
theorem untilIDone_init (p : Parent) (K : Oids) (hk : k ∈ K) :
    Obl.assigned k 1 ⊢ Par.kids p K -∗ oblKids k ∅ -∗ Q -∗
      |={E}=>m untilIDone k Q ∗ Par.kids p (K.erase k) := by
  rw [untilIDone_eq]
  iintro Oa Kp Kk HQ
  iapply untilIDoneGuar_init p K hk $$ Oa Kp Kk [] HQ
  inext
  iapply guar_canon

@[lantana_alias untilI_done_guar_elim]
theorem untilIDoneGuar_elim {G₂ : TrSpec Expr State GF} :
    untilIDoneGuar k Q G₂ ⊢ Q ∗ Obl.discharged k := by
  rw [untilIDoneGuar_unfold]
  iintro ⟨HQ, D, -⟩
  iframe HQ D

@[lantana_alias untilI_done_elim]
theorem untilIDone_elim : untilIDone k Q ⊢ Q ∗ Obl.discharged k := by
  rw [untilIDone_eq]; exact untilIDoneGuar_elim

/-- A done until guarantees the until of any left reading, from its right formula: no run is
needed (Rocq `guar_untilI_done_guar`). -/
@[lantana_alias guar_untilI_done_guar]
theorem guar_untilIDoneGuar (G₁ G₂ : TrSpec Expr State GF) :
    ⊢@{IProp GF} untilIDoneGuar k Q G₂ ⊨ₜ (G₁ 𝒰ₛ G₂) := by
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, MI, U⟩
  iunfold untilIDoneGuar at U
  icases U with ⟨HQ, -, #HG₂⟩
  iapply guar_elim Q (G₁ 𝒰ₛ G₂) h n σ tp m i Ω W $$ [] [HI MI HQ]
  · iapply guar_until_now $$ HG₂
  · iframe HI MI HQ

@[lantana_alias guar_untilI_done]
theorem guar_untilIDone (G₁ : TrSpec Expr State GF) :
    ⊢@{IProp GF} untilIDone k Q ⊨ₜ (G₁ 𝒰ₛ TrSpec.canon Q) := by
  rw [untilIDone_eq]; exact guar_untilIDoneGuar G₁ _

@[lantana_alias guar_untilI_done_finally]
theorem guar_untilIDone_finally :
    ⊢@{IProp GF} untilIDone k Q ⊨ₜ ◇ₛ (TrSpec.canon (Expr := Expr) (State := State) Q) :=
  guar_untilIDone TrSpec.true

@[lantana_alias guar_untilI_done_valid]
theorem guar_untilIDone_valid (G₁ : TrSpec Expr State GF) {G₂ : TrSpec Expr State GF}
    (hG₂ : ⊢ Q ⊨ₜ G₂) : ⊢@{IProp GF} untilIDone k Q ⊨ₜ (G₁ 𝒰ₛ G₂) :=
  (guar_untilIDone G₁).trans
    (guar_weaken (TrSpec.strongUntil_mono (TrSpec.le_refl G₁)
      (@TrSpec.canon_le _ _ _ _ _ instM instT _ _ _ hG₂)))

/-! ### Discharge -/

/-- Discharge: `P` is taken out; once `Q` holds, `k` (a childless child of `p`) is discharged,
the record of `G₂` at the discharge is left in the invariant, and the until becomes a done
until (Rocq `untilI_guar_discharge_done`). -/
@[lantana_alias untilI_guar_discharge_done]
theorem untilIGuar_discharge_done {G₁ G₂ : TrSpec Expr State GF} (hN : ↑N ⊆ E) :
    untilIGuar N k 1 P Q G₁ G₂ ⊢ |={E, E \ ↑N}=> ▷ (P ∗
      ∀ (p : Parent) (K : Oids), ⌜k ∈ K⌝ → Par.kids p K -∗ oblKids k ∅ -∗ Q -∗
        ∀ E' : CoPset, |={E'}=>m |={E \ ↑N, E}=>
          (untilIDoneGuar k Q G₂ ∗ Par.kids p (K.erase k))) := by
  rw [untilIGuar_unfold]
  iintro ⟨Oa, #U⟩
  ihave #OI := untilIGuarPers_inv N k P Q G₁ G₂ $$ U
  icases untilIGuarPers_guar N k P Q G₁ G₂ $$ U with ⟨-, #HG₂⟩
  imod Obl.inv_acc_assigned E N k P _ hN $$ OI with H
  icases H $$ %(Qp.half 1) Oa with ⟨H, ACC⟩
  imodintro
  inext
  icases H with ⟨Oa₁, Oa₂, HP⟩
  iframe HP
  iintro %p %K %hk Kp Kk HQ %E'
  ihave Oa := (Obl.assigned_halves k).mpr $$ [Oa₁ Oa₂]
  · iframe Oa₁ Oa₂
  imod Obl.discharge_leaf E' p K k hk $$ Kp Kk Oa with ⟨Kp, #D⟩
  imod mupd_read (E := E') (P := iprop(Q ∗ untilDischarged k G₂)) $$ [HQ] with ⟨HQ, #R⟩
  · iintro %h %n %σ %tp %g %i %Ω %W HI TI MI
    ihave #TQ : record G₂ n $$ [HI MI HQ]
    · iapply guar_elim Q G₂ h n σ tp g i Ω W $$ HG₂
      iframe HI MI HQ
    icases Obl.discharged_modelInterp_lookup k g i Ω W n tp.length $$ [D MI] with %hkd
    · iframe D MI
    ihave #EF := modelInterp_eventObl hkd $$ MI
    iframe MI
    imodintro
    iframe HI TI HQ
    iunfold untilDischarged
    iexists n, i, Ω
    iframe EF
    iexact TQ
  imodintro
  imod ACC $$ [] with -
  · inext
    iapply (Obl.variant_unfold k P _).2
    iright
    iframe D
    iexact R
  imodintro
  iframe Kp
  iunfold untilIDoneGuar
  iframe HQ
  isplitr
  · iexact D
  · inext
    iexact HG₂

@[lantana_alias untilI_discharge_done]
theorem untilI_discharge_done (hN : ↑N ⊆ E) :
    untilI N k 1 P Q ⊢ |={E, E \ ↑N}=> ▷ (P ∗
      ∀ (p : Parent) (K : Oids), ⌜k ∈ K⌝ → Par.kids p K -∗ oblKids k ∅ -∗ Q -∗
        ∀ E' : CoPset, |={E'}=>m |={E \ ↑N, E}=> (untilIDone k Q ∗ Par.kids p (K.erase k))) := by
  rw [untilI_eq, untilIDone_eq]; exact untilIGuar_discharge_done hN

/-- The same, with the done until taken apart (Rocq `untilI_guar_discharge`). -/
@[lantana_alias untilI_guar_discharge]
theorem untilIGuar_discharge {G₁ G₂ : TrSpec Expr State GF} (hN : ↑N ⊆ E) :
    untilIGuar N k 1 P Q G₁ G₂ ⊢ |={E, E \ ↑N}=> ▷ (P ∗
      ∀ (p : Parent) (K : Oids), ⌜k ∈ K⌝ → Par.kids p K -∗ oblKids k ∅ -∗ Q -∗
        ∀ E' : CoPset, |={E'}=>m |={E \ ↑N, E}=>
          (Q ∗ Par.kids p (K.erase k) ∗ Obl.discharged k)) := by
  iintro U
  imod untilIGuar_discharge_done hN $$ U with H
  imodintro
  inext
  icases H with ⟨HP, H⟩
  iframe HP
  iintro %p %K %hk Kp Kk HQ %E'
  imod H $$ %p %K %hk Kp Kk HQ %E' with H
  imodintro
  imod H with ⟨D, Kp⟩
  imodintro
  icases untilIDoneGuar_elim $$ D with ⟨HQ, Dk⟩
  iframe HQ Kp Dk

/-- Discharge: open the until, then discharge the leaf obligation `k` with `Q`. -/
@[lantana_alias untilI_discharge]
theorem untilI_discharge (hN : ↑N ⊆ E) :
    untilI N k 1 P Q ⊢ |={E, E \ ↑N}=> ▷ (P ∗
      ∀ (p : Parent) (K : Oids), ⌜k ∈ K⌝ → Par.kids p K -∗ oblKids k ∅ -∗ Q -∗
        ∀ E' : CoPset, |={E'}=>m |={E \ ↑N, E}=>
          (Q ∗ Par.kids p (K.erase k) ∗ Obl.discharged k)) := by
  rw [untilI_eq]; exact untilIGuar_discharge hN

/-! ### Access -/

@[lantana_alias untilI_guar_discharged_false]
theorem untilIGuar_discharged_false {G₁ G₂ : TrSpec Expr State GF} :
    untilIGuar N k q P Q G₁ G₂ ⊢ Obl.discharged k -∗ False := by
  rw [untilIGuar_unfold]
  iintro ⟨Oa, -⟩ D
  iapply Obl.assigned_discharged_false k _ $$ Oa D

@[lantana_alias untilI_discharged_false]
theorem untilI_discharged_false : untilI N k q P Q ⊢ Obl.discharged k -∗ False := by
  rw [untilI_eq]; exact untilIGuar_discharged_false

@[lantana_alias untilI_guar_acc]
theorem untilIGuar_acc {G₁ G₂ : TrSpec Expr State GF} (hN : ↑N ⊆ E) :
    untilIGuar N k q P Q G₁ G₂ ⊢
      |={E, E \ ↑N}=> ▷ (P ∗ (▷ P ={E \ ↑N, E}=∗ untilIGuar N k q P Q G₁ G₂)) := by
  rw [untilIGuar_unfold]
  iintro ⟨Oa, #U⟩
  ihave #OI := untilIGuarPers_inv N k P Q G₁ G₂ $$ U
  imod Obl.inv_acc_assigned E N k P _ hN $$ OI with H
  icases H $$ %q.half Oa with ⟨H, ACC⟩
  imodintro
  inext
  icases H with ⟨Oa, Oa₂, HP⟩
  iframe HP
  iintro HP
  imod ACC $$ [Oa₂ HP] with -
  · inext
    iapply (Obl.variant_unfold k P _).2
    ileft
    iframe Oa₂ HP
  imodintro
  iframe Oa
  iexact U

@[lantana_alias untilI_acc]
theorem untilI_acc (hN : ↑N ⊆ E) :
    untilI N k q P Q ⊢ |={E, E \ ↑N}=> ▷ (P ∗ (▷ P ={E \ ↑N, E}=∗ untilI N k q P Q)) := by
  rw [untilI_eq]; exact untilIGuar_acc hN

/-- Discharge with the right formula at hand, using a later credit
(Rocq `untilI_guar_discharge_lc`). -/
@[lantana_alias untilI_guar_discharge_lc]
theorem untilIGuar_discharge_lc {G₁ G₂ : TrSpec Expr State GF} (p : Parent) (K : Oids)
    (hN : ↑N ⊆ E) (hk : k ∈ K) :
    £ₙ 1 ⊢ Par.kids p K -∗ oblKids k ∅ -∗ untilIGuar N k 1 P Q G₁ G₂ -∗ Q -∗
      |={E}=>m Q ∗ Par.kids p (K.erase k) ∗ Obl.discharged k := by
  iintro LC Kp Kk HU HQ
  imod untilIGuar_discharge hN $$ HU with HU
  iapply lc_mupd_add_later $$ LC
  inext
  icases HU with ⟨-, HU⟩
  imod HU $$ %p %K %hk Kp Kk HQ %(E \ ↑N) with HU
  imod HU with ⟨HQ, Kp, D⟩
  imodintro
  iframe HQ Kp D

@[lantana_alias finallyI_discharge]
theorem finallyI_discharge (p : Parent) (K : Oids) (hN : ↑N ⊆ E) (hk : k ∈ K) :
    £ₙ 1 ⊢ Par.kids p K -∗ oblKids k ∅ -∗ finallyI N k 1 Q -∗ Q -∗
      |={E}=>m Q ∗ Par.kids p (K.erase k) ∗ Obl.discharged k := by
  unfold finallyI
  rw [untilI_eq]
  exact untilIGuar_discharge_lc p K hN hk

/-! ### Guarantees -/

/-- A registered until guarantees the until of its readings (Rocq `guar_untilI_guar`), with
the rank `succ (succ (fairMeasureUb fu))` for the fuel `fu` of `k` now: the certificate decides
which content holds now; if the left one, a credit of the step opens the obligation invariant
after the step, and the loop continues from the new state of `k`. -/
@[lantana_alias guar_untilI_guar]
theorem guar_untilIGuar {G₁ G₂ : TrSpec Expr State GF} :
    ⊢@{IProp GF} untilIGuar N k q P Q G₁ G₂ ⊨ₜ (G₁ 𝒰ₛ G₂) := by
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, MI, U⟩
  iunfold untilIGuar at U
  icases U with ⟨Oa, U⟩
  iunfold untilIGuarPers at U
  icases U with ⟨%j, %r, %γP, %γQ, %st, %v, %Ω₁, %fu₁, %o₁, #Hj, #HE, #HγP, #HγQ, #OI, -, -, -,
    #AC⟩
  icases Obl.assigned_modelInterp_lookup k _ m i Ω W n tp.length $$ [Oa MI] with %hk
  · iframe Oa MI
  obtain ⟨fu, o, hk⟩ := hk
  ihave #EA := modelInterp_eventObl hk $$ MI
  icases historyInterp_histEvent_lookup h n σ tp r st $$ [HI HE] with %hr
  · iframe HI HE
  icases historyInterp_wf h n σ tp $$ HI with %⟨hlen, -⟩
  have hrn : r ≤ n := by
    have := (List.getElem?_eq_some_iff.mp hr).1
    omega
  iapply record_intro
  imodintro
  iintro %Sys %l %h' %g %v' %Ω' %W' %τf %γ %σ' %tp' #ST %⟨hbeh, hfs, hlb, hht⟩ #B
    ⟨HI', MI', Sy'⟩
  icases bundleUntilCert l n j r N k γP γQ G₁ G₂ hrn $$ B Hj HγP HγQ [] with #C
  · iintro %hr'
    subst hr'
    inext
    ileft
    iexact AC
  have hex : TrIProp.strongUntil G₁.internal G₂.internal
      (Ordinals.Ordinal.succ (Ordinals.Ordinal.succ (fairMeasureUb fu))) ⟨n, τf⟩ ⊢
      (G₁ 𝒰ₛ G₂).internal ⟨n, τf⟩ :=
    exists_intro (Ψ := fun a : Fuel => TrIProp.strongUntil G₁.internal G₂.internal a ⟨n, τf⟩) _
  iapply hex
  have hU : TrIProp.defer iprop(G₂.internal ⟨n, τf⟩ ∨ (G₁.internal ⟨n, τf⟩ ∧ ∃ a' : Fuel,
      ⌜a' < Ordinals.Ordinal.succ (Ordinals.Ordinal.succ (fairMeasureUb fu))⌝ ∧
      TrIProp.strongUntil G₁.internal G₂.internal a' ⟨n + 1, τf⟩)) ⊢
      TrIProp.strongUntil G₁.internal G₂.internal
        (Ordinals.Ordinal.succ (Ordinals.Ordinal.succ (fairMeasureUb fu))) ⟨n, τf⟩ :=
    (TrIProp.until_unfold G₁.internal G₂.internal _ ⟨n, τf⟩).mpr
  iapply hU
  unfold TrIProp.defer
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hcl
  inext
  imod Hcl with -
  imodintro
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hcl
  iapply (ALC_credits (Ordinals.Ordinal.ofNat 1)).mpr
  iapply ALC_intro
  iintro LC
  imod Hcl with -
  icases C with ((#TrecP | #TrecQ) | ⟨%n', %i', %Ω'', %hn', #EF, #TQ'⟩)
  · -- `P` holds at `n`: the obligation at `n + 1` decides
    imod Obl.inv_acc ⊤ N k P _ CoPset.subseteq_top $$ OI with ⟨Var, Hclose⟩
    imod lc_fupd_elim_later $$ LC Var with Var
    icases (Obl.variant_unfold k P _).1 $$ Var with (⟨Oa', HP'⟩ | ⟨#Of, #R⟩)
    · icases Obl.assigned_modelInterp_lookup k _ g v' Ω' W' (n + 1) tp'.length $$ [Oa' MI']
        with %hk'
      · iframe Oa' MI'
      obtain ⟨fu', o', hk'⟩ := hk'
      icases modelInterp_eventObl_lookup g v' Ω' W' (n + 1) tp'.length i (n, Ω) k
        (.assigned fu o) $$ [MI' EA] with %⟨-, -, -, -, hle⟩
      · iframe MI' EA
      have hfu : fu' ≤ fu := by
        rcases hle.2 k _ _ hk hk' with ⟨h₁, -⟩ | h₁
        · exact h₁
        · exact Ordinals.Ordinal.le_of_lt h₁
      imod Hclose $$ [Oa' HP'] with -
      · inext
        iapply (Obl.variant_unfold k P _).2
        ileft
        iframe Oa' HP'
      imodintro
      iright
      isplit
      · iapply record_elim G₁ $$ TrecP ST %⟨hbeh, hfs, hlb, hht⟩ B [HI' MI' Sy']
        iframe HI' MI' Sy'
      · iexists Ordinals.Ordinal.succ (fairMeasure (γ (n + 1)) o' fu')
        isplit
        · ipureintro
          refine Ordinals.Ordinal.succ_lt_succ_iff.mpr (Ordinals.Ordinal.lt_succ_iff.mpr ?_)
          exact Ordinals.Ordinal.le_trans (fairMeasure_le_ub _ o' fu') (fairMeasureUb_le_mono hfu)
        · iapply untilRun Sys N k γP γQ j r P G₁ G₂ $$ ST Hj HγP HγQ OI %h' %(n + 1) %σ' %tp' %g
            %v' %Ω' %W' %τf %γ %fu' %o' %⟨by omega, hbeh.next, hfs, hlb, hht, hk'⟩
            [HI' MI' Sy']
          iframe HI' MI' Sy'
    · -- discharged during the step: at `n` (before the step) or at `n + 1` (after)
      iunfold untilDischarged at R
      icases R with ⟨%n', %i', %Ω'', #EF, #TQ'⟩
      icases modelInterp_eventObl_lookup g v' Ω' W' (n + 1) tp'.length i' (n', Ω'') k
        .discharged $$ [MI' EF] with %⟨-, -, -, hn₁, -⟩
      · iframe MI' EF
      icases eventObl_assigned_discharged_le $$ [EA EF] with %hn₂
      · iframe EA EF
      imod Hclose $$ [] with -
      · inext
        iapply (Obl.variant_unfold k P _).2
        iright
        iframe Of
        iunfold untilDischarged
        iexists n', i', Ω''
        iframe EF
        iexact TQ'
      imodintro
      by_cases hnn : n' = n
      · subst hnn
        ileft
        iapply record_elim G₂ $$ TQ' ST %⟨hbeh, hfs, hlb, hht⟩ B [HI' MI' Sy']
        iframe HI' MI' Sy'
      · have hn' : n' = n + 1 := by simp only at hn₁; omega
        subst hn'
        iright
        isplit
        · iapply record_elim G₁ $$ TrecP ST %⟨hbeh, hfs, hlb, hht⟩ B [HI' MI' Sy']
          iframe HI' MI' Sy'
        · iexists 0
          isplit
          · ipureintro
            exact Ordinals.Ordinal.zero_lt_succ _
          · iapply untilRunDischarged Sys G₁.internal G₂ 0 h' (n + 1) σ' tp' g v' Ω' W' τf γ
              ⟨hbeh.next, hfs, hlb, hht⟩ $$ ST TQ' [HI' MI' Sy']
            iframe HI' MI' Sy'
  · -- `Q` holds at `n`
    imodintro
    ileft
    iapply record_elim G₂ $$ TrecQ ST %⟨hbeh, hfs, hlb, hht⟩ B [HI' MI' Sy']
    iframe HI' MI' Sy'
  · -- discharged before the check: the discharge was at `n`
    icases eventObl_assigned_discharged_le $$ [EA EF] with %hn₂
    · iframe EA EF
    have hnn : n' = n := by omega
    subst hnn
    imodintro
    ileft
    iapply record_elim G₂ $$ TQ' ST %⟨hbeh, hfs, hlb, hht⟩ B [HI' MI' Sy']
    iframe HI' MI' Sy'

@[lantana_alias guar_untilI]
theorem guar_untilI : ⊢@{IProp GF} untilI N k q P Q ⊨ₜ (TrSpec.canon P 𝒰ₛ TrSpec.canon Q) := by
  rw [untilI_eq]; exact guar_untilIGuar

@[lantana_alias guar_untilI_valid]
theorem guar_untilI_valid {G₁ G₂ : TrSpec Expr State GF} (hG₁ : ⊢ P ⊨ₜ G₁) (hG₂ : ⊢ Q ⊨ₜ G₂) :
    ⊢@{IProp GF} untilI N k q P Q ⊨ₜ (G₁ 𝒰ₛ G₂) :=
  guar_untilI.trans
    (guar_weaken (TrSpec.strongUntil_mono (@TrSpec.canon_le _ _ _ _ _ instM instT _ _ _ hG₁)
      (@TrSpec.canon_le _ _ _ _ _ instM instT _ _ _ hG₂)))

/-! ## Inference -/

instance guarOf_alwaysI (G : TrSpec Expr State GF) [GuarOf P G] : GuarOf (alwaysI N P) (□ₛ G) :=
  ⟨guar_alwaysI_valid GuarOf.guar_of⟩
instance guarOf_untilI (G₁ G₂ : TrSpec Expr State GF) [GuarOf P G₁] [GuarOf Q G₂] :
    GuarOf (untilI N k q P Q) (G₁ 𝒰ₛ G₂) :=
  ⟨guar_untilI_valid GuarOf.guar_of GuarOf.guar_of⟩
instance guarOf_untilIDone (G₂ : TrSpec Expr State GF) [GuarOf Q G₂] :
    GuarOf (untilIDone k Q) (◇ₛ G₂) :=
  ⟨guar_untilIDone_valid TrSpec.true GuarOf.guar_of⟩
instance guarOf_stateFact (φ : State → ThreadPool Expr → Prop) [StateFact P φ] :
    GuarOf P (TrSpec.state φ) := ⟨guar_state_fact P φ⟩
instance guarOf_sep (G₁ G₂ : TrSpec Expr State GF) [GuarOf P G₁] [GuarOf Q G₂] :
    GuarOf iprop(P ∗ Q) (G₁ ∧ₛ G₂) := by
  have h₁ : ⊢ P ⊨ₜ G₁ := GuarOf.guar_of
  have h₂ : ⊢ Q ⊨ₜ G₂ := GuarOf.guar_of
  exact ⟨h₂.trans (wand_entails (h₁.trans guar_sep))⟩
instance guarOf_and (G₁ G₂ : TrSpec Expr State GF) [GuarOf P G₁] [GuarOf Q G₂] :
    GuarOf iprop(P ∧ Q) (G₁ ∧ₛ G₂) := by
  have h₁ : ⊢ P ⊨ₜ G₁ := GuarOf.guar_of
  have h₂ : ⊢ Q ⊨ₜ G₂ := GuarOf.guar_of
  exact ⟨h₂.trans (wand_entails (h₁.trans guar_and))⟩
instance guarOf_or (G₁ G₂ : TrSpec Expr State GF) [GuarOf P G₁] [GuarOf Q G₂] :
    GuarOf iprop(P ∨ Q) (G₁ ∨ₛ G₂) := by
  have h₁ : ⊢ P ⊨ₜ G₁ := GuarOf.guar_of
  have h₂ : ⊢ Q ⊨ₜ G₂ := GuarOf.guar_of
  exact ⟨h₂.trans (wand_entails (h₁.trans guar_or))⟩
instance guarOf_pure (φ : Prop) :
    GuarOf (iprop(⌜φ⌝) : IProp GF) (TrSpec.pure (Expr := Expr) (State := State) φ) :=
  ⟨guar_pure φ⟩

end Rules

end Lantana
