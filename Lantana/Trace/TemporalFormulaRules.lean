/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
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
open Iris.ProgramLogic (Language)
open Lantana.Model
open Iris.Std LawfulPartialMap
open scoped Lantana.TrSpec Lantana.TrProp

variable {Expr State Obs Val : Type} {GF : BundledGFunctors} [Language Expr State Obs Val]
-- Named, to be passed explicitly to `TrSpec.canon_le` (see "Always" below).
variable [Crash Expr State Obs Val] [instM : ModelGS GF] [instT : TemporalGS Expr State GF]
  [StateInterp Expr State GF]

section Rules
variable {E : CoPset} {N : Namespace} {k : Oid} {q : Qp} {P Q : IProp GF}

/-! ## Always

A `⊑ₛ` premise is given as `@TrSpec.canon_le _ _ _ _ _ _ _ instM instT _ _ _ hG`, with the ambient
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
  iintro Hcl %g %i %Ω %W %tc %X MI
  ihave #C : ▷ record G n $$ [HP HI MI]
  · iapply guar_elim_later_guar P G h n σ tp g i Ω W tc X $$ HG
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
  iintro %h %n %σ %tp %g %i %Ω %W %tc %X HI TI MI
  ihave #C : ▷ record G n $$ [HP HI MI]
  · iapply guar_elim_later_guar P G h n σ tp g i Ω W tc X $$ HG
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
  iintro %h %n %σ %tp %m %i %Ω %W %tc %X ⟨HI, -, A⟩
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
  iintro %Sys %l %h' %g %v %Ω' %W' %τf %sched %γ %σ' %tp' #ST %⟨hsch, hfs, hlb, hht⟩ #B HS
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
  · iapply record_elim G $$ C ST %⟨hsch, hfs, hlb, hht⟩ B HS
  · iapply alwaysRun Sys N γa G j r $$ ST Hj Hγ %h' %(n + 1) %σ' %tp' %g %v %Ω' %W' %τf %sched
      %γ %⟨by omega, hsch, hfs, hlb, hht⟩ HS

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
    (@TrSpec.canon_le _ _ _ _ _ _ _ instM instT _ _ _ hG)))

@[lantana_alias guar_alwaysI_valid]
theorem guar_alwaysI_valid {G : TrSpec Expr State GF} (hG : ⊢ P ⊨ₜ G) :
    ⊢@{IProp GF} alwaysI N P ⊨ₜ □ₛ G :=
  guar_alwaysI.trans (guar_weaken (TrSpec.always_mono
    (@TrSpec.canon_le _ _ _ _ _ _ _ instM instT _ _ _ hG)))

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
  iintro %h %n %σ %tp %g %i %Ω %W %tc %X HI TI MI
  ihave #C : ▷ record G₁ n $$ [HP HI MI]
  · iapply guar_elim_later_guar P G₁ h n σ tp g i Ω W tc X $$ HG₁
    iframe HP HI MI
  icases Obl.assigned_modelInterp_lookup k _ g i Ω W n tc X $$ [Oa MI] with %hk
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

/-- The obligation and the strong until at once: `k` is a new child of `p`, added to the bill
of `p`, and the formulas are chosen once `k` is known (Rocq `untilI_guar_alloc`). -/
@[lantana_alias untilI_guar_alloc]
theorem untilIGuar_alloc (p : Parent) (K B : Oids) (ℓ : Layer) (μ : Measure) :
    parLe (GF := GF) p ℓ ⊢ Par.kids p K -∗ Par.bill p B -∗
      |={E}=>m ∃ k : Oid, ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ Par.bill p (B.insert k) ∗
        oblKids k ∅ ∗ Obl.fuel k ℓ μ ∗ Wit.layer k ℓ ∗
        ∀ (E' : CoPset) (N : Namespace) (P Q : IProp GF) (G₁ G₂ : TrSpec Expr State GF),
          ▷ (P ⊨ₜ G₁) -∗ ▷ (Q ⊨ₜ G₂) -∗ ▷ P -∗ |={E'}=>m untilIGuar N k 1 P Q G₁ G₂ := by
  iintro Hl Kp HB
  imod Obl.new E p K B ℓ μ $$ Hl Kp HB with ⟨%k, %hk, Kp, HB, Kk, Oa, F, #W⟩
  imodintro
  iexists k
  isplitr
  · ipureintro
    exact hk
  iframe Kp HB Kk F
  isplitr
  · iexact W
  iintro %E' %N' %P' %Q' %G₁ %G₂ HG₁ HG₂ HP
  iapply untilIGuar_init $$ Oa HG₁ HG₂ HP

/-- Allocation: a new obligation below `p`, added to the bill of `p`, with its fuel and
witness, and the right to turn it into an until with any formulas. -/
@[lantana_alias untilI_alloc]
theorem untilI_alloc (p : Parent) (K B : Oids) (ℓ : Layer) (μ : Measure) :
    parLe (GF := GF) p ℓ ⊢ Par.kids p K -∗ Par.bill p B -∗
      |={E}=>m ∃ k : Oid, ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ Par.bill p (B.insert k) ∗
        oblKids k ∅ ∗ Obl.fuel k ℓ μ ∗ Wit.layer k ℓ ∗
        ∀ (E' : CoPset) (N : Namespace) (P Q : IProp GF), ▷ P -∗ |={E'}=>m untilI N k 1 P Q := by
  iintro Hl Kp HB
  imod Obl.new E p K B ℓ μ $$ Hl Kp HB with ⟨%k, %hk, Kp, HB, Kk, Oa, F, #W⟩
  imodintro
  iexists k
  isplitr
  · ipureintro
    exact hk
  iframe Kp HB Kk F
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
    ⊢@{IProp GF} untilIDoneGuar k Q G₂ ⊨ₜ (G₁ Uₛ G₂) := by
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W %tc %X ⟨HI, MI, U⟩
  iunfold untilIDoneGuar at U
  icases U with ⟨HQ, -, #HG₂⟩
  iapply guar_elim Q (G₁ Uₛ G₂) h n σ tp m i Ω W tc X $$ [] [HI MI HQ]
  · iapply guar_until_now $$ HG₂
  · iframe HI MI HQ

@[lantana_alias guar_untilI_done]
theorem guar_untilIDone (G₁ : TrSpec Expr State GF) :
    ⊢@{IProp GF} untilIDone k Q ⊨ₜ (G₁ Uₛ TrSpec.canon Q) := by
  rw [untilIDone_eq]; exact guar_untilIDoneGuar G₁ _

@[lantana_alias guar_untilI_done_finally]
theorem guar_untilIDone_finally :
    ⊢@{IProp GF} untilIDone k Q ⊨ₜ ◇ₛ (TrSpec.canon (Expr := Expr) (State := State) Q) :=
  guar_untilIDone TrSpec.true

@[lantana_alias guar_untilI_done_valid]
theorem guar_untilIDone_valid (G₁ : TrSpec Expr State GF) {G₂ : TrSpec Expr State GF}
    (hG₂ : ⊢ Q ⊨ₜ G₂) : ⊢@{IProp GF} untilIDone k Q ⊨ₜ (G₁ Uₛ G₂) :=
  (guar_untilIDone G₁).trans
    (guar_weaken (TrSpec.strongUntil_mono (TrSpec.le_refl G₁)
      (@TrSpec.canon_le _ _ _ _ _ _ _ instM instT _ _ _ hG₂)))

/-! ### Discharge -/

/-- Opening the obligation invariant of an until held in full: its content with the whole
assignment of `k`, and the closing that takes the content back, discharged or not, after which
the half of the assignment kept rebuilds the until. -/
theorem untilIGuar_acc_assigned {G₁ G₂ : TrSpec Expr State GF} (hN : ↑N ⊆ E) :
    untilIGuar N k 1 P Q G₁ G₂ ⊢ |={E, E \ ↑N}=> ▷ (Obl.assigned k 1 ∗ P) ∗ ▷ (Q ⊨ₜ G₂) ∗
      (▷ Obl.variant k P (untilDischarged k G₂) ={E \ ↑N, E}=∗
        Obl.assigned k (Qp.half 1) -∗ untilIGuar N k 1 P Q G₁ G₂) := by
  rw [untilIGuar_unfold]
  iintro ⟨Oa, #U⟩
  ihave #OI := untilIGuarPers_inv N k P Q G₁ G₂ $$ U
  icases untilIGuarPers_guar N k P Q G₁ G₂ $$ U with ⟨-, #HG₂⟩
  imod Obl.inv_acc_assigned E N k P _ hN $$ OI with H
  icases H $$ %(Qp.half 1) Oa with ⟨H, ACC⟩
  imodintro
  isplitl [H]
  · inext
    icases H with ⟨Oa₁, Oa₂, HP⟩
    iframe HP
    iapply (Obl.assigned_halves k).mpr
    iframe Oa₁ Oa₂
  iframe HG₂
  iintro V
  imod ACC $$ V with -
  imodintro
  iintro Oa
  iframe Oa U

/-- The record of the right formula of a discharged obligation at the current position, from a
resource `X` that implies `Q`, which is given back. -/
theorem untilIGuar_record_discharged {G₂ : TrSpec Expr State GF} (E : CoPset) {X : IProp GF}
    (hX : X ⊢ Q) : (Q ⊨ₜ G₂) ⊢ Obl.discharged k -∗ X -∗ |={E}=>m X ∗ untilDischarged k G₂ := by
  iintro #HG₂ #D HX
  iapply mupd_read
  iintro %h %n %σ %tp %g %i %Ω %W %tc %Y HI TI MI
  ihave #TQ : record G₂ n $$ [HI MI HX]
  · iapply guar_elim Q G₂ h n σ tp g i Ω W tc Y $$ HG₂
    iframe HI MI
    iapply hX $$ HX
  icases Obl.discharged_modelInterp_lookup k g i Ω W n tc Y $$ [D MI] with %hkd
  · iframe D MI
  ihave #EF := modelInterp_eventObl hkd $$ MI
  iframe MI
  imodintro
  iframe HI TI HX
  iunfold untilDischarged
  iexists n, i, Ω
  iframe EF
  iexact TQ

/-- The discharge of an until whose invariant is open, at any mask: `k`, a childless child of
`p`, is discharged with a resource `X` that implies `Q`, which is given back with the content
that closes the invariant (the record of `G₂` at the discharge). -/
theorem untilIGuar_discharge_opened {G₂ : TrSpec Expr State GF} (E : CoPset) (p : Parent)
    (K : Oids) (hk : k ∈ K) {X : IProp GF} (hX : X ⊢ Q) :
    (Q ⊨ₜ G₂) ⊢ Obl.assigned k 1 -∗ Par.kids p K -∗ oblKids k ∅ -∗ X -∗
      |={E}=>m X ∗ Par.kids p (K.erase k) ∗ Obl.discharged k ∗
        Obl.variant k P (untilDischarged k G₂) := by
  iintro #HG₂ Oa Kp Kk HX
  imod Obl.discharge_leaf E p K k hk $$ Kp Kk Oa with ⟨Kp, #D⟩
  imod untilIGuar_record_discharged E hX $$ HG₂ D HX with ⟨HX, #R⟩
  imodintro
  iframe HX Kp D
  iapply (Obl.variant_unfold k P _).2
  iright
  iframe D R

theorem untilI_acc_assigned (hN : ↑N ⊆ E) :
    untilI N k 1 P Q ⊢ |={E, E \ ↑N}=> ▷ (Obl.assigned k 1 ∗ P) ∗
      (▷ Obl.variant k P (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) Q))
        ={E \ ↑N, E}=∗ Obl.assigned k (Qp.half 1) -∗ untilI N k 1 P Q) := by
  rw [untilI_eq]
  iintro U
  imod untilIGuar_acc_assigned hN $$ U with ⟨H, -, ACC⟩
  imodintro
  iframe H ACC

theorem untilI_record_discharged (E : CoPset) {X : IProp GF} (hX : X ⊢ Q) :
    Obl.discharged k ⊢ X -∗
      |={E}=>m X ∗ untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) Q) :=
  (emp_sep.2.trans (sep_mono_left (guar_canon Q))).trans
    (wand_elim (untilIGuar_record_discharged E hX))

theorem untilI_discharge_opened (E : CoPset) (p : Parent) (K : Oids) (hk : k ∈ K)
    {X : IProp GF} (hX : X ⊢ Q) :
    Obl.assigned k 1 ⊢ Par.kids p K -∗ oblKids k ∅ -∗ X -∗
      |={E}=>m X ∗ Par.kids p (K.erase k) ∗ Obl.discharged k ∗
        Obl.variant k P (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) Q)) :=
  (emp_sep.2.trans (sep_mono_left (guar_canon Q))).trans
    (wand_elim (untilIGuar_discharge_opened E p K hk hX))

theorem finallyI_acc_assigned (hN : ↑N ⊆ E) :
    finallyI N k 1 Q ⊢ |={E, E \ ↑N}=> ▷ Obl.assigned k 1 ∗
      (▷ Obl.variant k iprop(True)
          (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) Q))
        ={E \ ↑N, E}=∗ Obl.assigned k (Qp.half 1) -∗ finallyI N k 1 Q) := by
  unfold finallyI
  iintro U
  imod untilI_acc_assigned hN $$ U with ⟨H, ACC⟩
  imodintro
  iframe ACC
  inext
  icases H with ⟨H, -⟩
  iexact H

theorem finallyI_discharge_opened (E : CoPset) (p : Parent) (K : Oids) (hk : k ∈ K)
    {X : IProp GF} (hX : X ⊢ Q) :
    Obl.assigned k 1 ⊢ Par.kids p K -∗ oblKids k ∅ -∗ X -∗
      |={E}=>m X ∗ Par.kids p (K.erase k) ∗ Obl.discharged k ∗
        Obl.variant k iprop(True)
          (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) Q)) :=
  untilI_discharge_opened E p K hk hX

/-- Discharge: `P` is taken out; once `Q` holds, `k` (a childless child of `p`) is discharged,
the record of `G₂` at the discharge is left in the invariant, and the until becomes a done
until (Rocq `untilI_guar_discharge_done`). -/
@[lantana_alias untilI_guar_discharge_done]
theorem untilIGuar_discharge_done {G₁ G₂ : TrSpec Expr State GF} (hN : ↑N ⊆ E) :
    untilIGuar N k 1 P Q G₁ G₂ ⊢ |={E, E \ ↑N}=> ▷ (P ∗
      ∀ (p : Parent) (K : Oids), ⌜k ∈ K⌝ → Par.kids p K -∗ oblKids k ∅ -∗ Q -∗
        ∀ E' : CoPset, |={E'}=>m |={E \ ↑N, E}=>
          (untilIDoneGuar k Q G₂ ∗ Par.kids p (K.erase k))) := by
  iintro U
  imod untilIGuar_acc_assigned hN $$ U with ⟨H, #HG₂, ACC⟩
  imodintro
  inext
  icases H with ⟨Oa, HP⟩
  iframe HP
  iintro %p %K %hk Kp Kk HQ %E'
  imod untilIGuar_discharge_opened (P := P) E' p K hk .rfl $$ HG₂ Oa Kp Kk HQ
    with ⟨HQ, Kp, #D, V⟩
  imodintro
  imod ACC $$ [V] with -
  · inext
    iexact V
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

/-! ### Sets of untils

A finite set `S` of untils held in full opens at once, to a mask `E'` that their pairwise
disjoint namespaces avoid; the records of a set of discharged obligations come from one
resource that implies all their right formulas; and a forest of opened untils is discharged in one
model update, with those records. -/

section Sets
open BigSepS LawfulSet
variable {S : Oids} {E' : CoPset} {N : Oid → Namespace} {P Q : Oid → IProp GF}

/-- Opening the obligation invariants of a finite set of untils held in full, whose namespaces
are pairwise disjoint and outside `E'`: each content with the whole assignment under one later,
and the closing that takes the contents back and rebuilds each until from the half kept. -/
theorem untilIGuar_acc_assigned_set {G₁ G₂ : Oid → TrSpec Expr State GF} (hE' : E' ⊆ E)
    (hN : ∀ k, k ∈ S → ↑(N k) ⊆ E \ E')
    (hdisj : ∀ k k', k ∈ S → k' ∈ S → k ≠ k' → (↑(N k) : CoPset) ## ↑(N k')) :
    ([∗set] k ∈ S, untilIGuar (N k) k 1 (P k) (Q k) (G₁ k) (G₂ k)) ⊢ |={E, E'}=>
      ([∗set] k ∈ S, ▷ (Obl.assigned k 1 ∗ P k) ∗ ▷ (Q k ⊨ₜ G₂ k)) ∗
      (([∗set] k ∈ S, ▷ Obl.variant k (P k) (untilDischarged k (G₂ k))) ={E', E}=∗
        [∗set] k ∈ S, (Obl.assigned k (Qp.half 1) -∗
          untilIGuar (N k) k 1 (P k) (Q k) (G₁ k) (G₂ k))) := by
  induction S using FiniteSet.set_ind generalizing E with
  | hemp =>
    iintro -
    iapply fupd_mask_intro hE'
    iintro Hclose
    isplitr
    · iapply bigSepS_empty.2
      iempintro
    · iintro -
      imod Hclose with -
      imodintro
      iapply bigSepS_empty.2
      iempintro
  | hadd x T hx ih =>
    have hNx' := hN x (mem_insert.2 (.inl rfl))
    have hNx : ↑(N x) ⊆ E := fun p hp => (mem_diff.1 (hNx' p hp)).1
    have hE'x : E' ⊆ E \ ↑(N x) := fun p hp =>
      mem_diff.2 ⟨hE' p hp, fun hpN => (mem_diff.1 (hNx' p hpN)).2 hp⟩
    have hNT : ∀ k, k ∈ T → ↑(N k) ⊆ (E \ ↑(N x)) \ E' := fun k hk p hp => by
      have hkx : k ≠ x := fun h => hx (h ▸ hk)
      have hp' := mem_diff.1 (hN k (mem_insert_of_mem hk) p hp)
      exact mem_diff.2 ⟨mem_diff.2 ⟨hp'.1, fun hpN =>
        hdisj k x (mem_insert_of_mem hk) (mem_insert.2 (.inl rfl)) hkx p ⟨hp, hpN⟩⟩, hp'.2⟩
    have hdisjT : ∀ k k', k ∈ T → k' ∈ T → k ≠ k' → (↑(N k) : CoPset) ## ↑(N k') :=
      fun k k' hk hk' => hdisj k k' (mem_insert_of_mem hk) (mem_insert_of_mem hk')
    iintro Us
    icases (bigSepS_insert hx).1 $$ Us with ⟨U, Us⟩
    imod untilIGuar_acc_assigned hNx $$ U with ⟨H₁, #HG₂, ACC⟩
    imod ih hE'x hNT hdisjT $$ Us with ⟨H, ACCs⟩
    imodintro
    isplitl [H₁ H]
    · iapply (bigSepS_insert hx).2
      iframe H₁ H
      iexact HG₂
    · iintro Vs
      icases (bigSepS_insert hx).1 $$ Vs with ⟨V, Vs⟩
      imod ACCs $$ Vs with Ws
      imod ACC $$ V with W
      imodintro
      iapply (bigSepS_insert hx).2
      iframe W Ws

/-- The masks of the namespaces `N₀.@k` below `N₀`, opened from `E` to `E \ ↑N₀`. -/
private theorem ndot_masks {N₀ : Namespace} (hN : ↑N₀ ⊆ E) :
    E \ ↑N₀ ⊆ E ∧ (∀ k : Oid, ↑(N₀.@k) ⊆ E \ (E \ ↑N₀)) ∧
      ∀ k k' : Oid, k ≠ k' → (↑(N₀.@k) : CoPset) ## ↑(N₀.@k') :=
  ⟨diff_subset_left, fun k p hp => mem_diff.2 ⟨hN p (nclose_subseteq N₀ k p hp),
    fun h => (mem_diff.1 h).2 (nclose_subseteq N₀ k p hp)⟩,
    fun _ _ hkk' => ndot_ne_disjoint N₀ hkk'⟩

/-- The opening of a set of untils whose namespaces `N₀.@k` lie below `N₀`. -/
theorem untilIGuar_acc_assigned_set_ndot {G₁ G₂ : Oid → TrSpec Expr State GF} {N₀ : Namespace}
    (hN : ↑N₀ ⊆ E) :
    ([∗set] k ∈ S, untilIGuar (N₀.@k) k 1 (P k) (Q k) (G₁ k) (G₂ k)) ⊢ |={E, E \ ↑N₀}=>
      ([∗set] k ∈ S, ▷ (Obl.assigned k 1 ∗ P k) ∗ ▷ (Q k ⊨ₜ G₂ k)) ∗
      (([∗set] k ∈ S, ▷ Obl.variant k (P k) (untilDischarged k (G₂ k))) ={E \ ↑N₀, E}=∗
        [∗set] k ∈ S, (Obl.assigned k (Qp.half 1) -∗
          untilIGuar (N₀.@k) k 1 (P k) (Q k) (G₁ k) (G₂ k))) :=
  have ⟨hE', hNk, hdisj⟩ := ndot_masks hN
  untilIGuar_acc_assigned_set hE' (fun k _ => hNk k) fun k k' _ _ => hdisj k k'

/-- The records of the right formulas of a set of discharged obligations, from one resource `X`
that implies all of them, which is given back: the contents that close their invariants. -/
theorem untilIGuar_record_discharged_set {G₂ : Oid → TrSpec Expr State GF} (E : CoPset)
    {X : IProp GF} (hX : ∀ k, k ∈ S → X ⊢ Q k) :
    ([∗set] k ∈ S, (Q k ⊨ₜ G₂ k) ∗ Obl.discharged k) ⊢ X -∗
      |={E}=>m X ∗ [∗set] k ∈ S, Obl.variant k (P k) (untilDischarged k (G₂ k)) := by
  induction S using FiniteSet.set_ind with
  | hemp =>
    iintro - HX
    imodintro
    iframe HX
    iapply bigSepS_empty.2
    iempintro
  | hadd x T hx ih =>
    iintro Hs HX
    icases (bigSepS_insert hx).1 $$ Hs with ⟨⟨#HG₂, #D⟩, Hs⟩
    imod untilIGuar_record_discharged E (hX x (mem_insert.2 (.inl rfl))) $$ HG₂ D HX
      with ⟨HX, #R⟩
    imod ih (fun k hk => hX k (mem_insert_of_mem hk)) $$ Hs HX with ⟨HX, Vs⟩
    imodintro
    iframe HX
    iapply (bigSepS_insert hx).2
    iframe Vs
    iapply (Obl.variant_unfold x (P x) _).2
    iright
    iframe D R

theorem untilI_acc_assigned_set (hE' : E' ⊆ E) (hN : ∀ k, k ∈ S → ↑(N k) ⊆ E \ E')
    (hdisj : ∀ k k', k ∈ S → k' ∈ S → k ≠ k' → (↑(N k) : CoPset) ## ↑(N k')) :
    ([∗set] k ∈ S, untilI (N k) k 1 (P k) (Q k)) ⊢ |={E, E'}=>
      ([∗set] k ∈ S, ▷ (Obl.assigned k 1 ∗ P k)) ∗
      (([∗set] k ∈ S, ▷ Obl.variant k (P k)
          (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) (Q k)))) ={E', E}=∗
        [∗set] k ∈ S, (Obl.assigned k (Qp.half 1) -∗ untilI (N k) k 1 (P k) (Q k))) := by
  simp only [untilI_eq]
  iintro Us
  imod untilIGuar_acc_assigned_set hE' hN hdisj $$ Us with ⟨H, ACC⟩
  imodintro
  iframe ACC
  iapply bigSepS_mono_of_forall (fun _ => sep_elim_left) $$ H

theorem untilI_acc_assigned_set_ndot {N₀ : Namespace} (hN : ↑N₀ ⊆ E) :
    ([∗set] k ∈ S, untilI (N₀.@k) k 1 (P k) (Q k)) ⊢ |={E, E \ ↑N₀}=>
      ([∗set] k ∈ S, ▷ (Obl.assigned k 1 ∗ P k)) ∗
      (([∗set] k ∈ S, ▷ Obl.variant k (P k)
          (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) (Q k))))
        ={E \ ↑N₀, E}=∗
        [∗set] k ∈ S, (Obl.assigned k (Qp.half 1) -∗ untilI (N₀.@k) k 1 (P k) (Q k))) :=
  have ⟨hE', hNk, hdisj⟩ := ndot_masks hN
  untilI_acc_assigned_set hE' (fun k _ => hNk k) fun k k' _ _ => hdisj k k'

theorem untilI_record_discharged_set (E : CoPset) {X : IProp GF} (hX : ∀ k, k ∈ S → X ⊢ Q k) :
    ([∗set] k ∈ S, Obl.discharged k) ⊢ X -∗ |={E}=>m X ∗ [∗set] k ∈ S,
      Obl.variant k (P k)
        (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) (Q k))) :=
  (bigSepS_mono_of_forall fun k => emp_sep.2.trans (sep_mono_left (guar_canon (Q k)))).trans
    (untilIGuar_record_discharged_set E hX)

theorem finallyI_acc_assigned_set (hE' : E' ⊆ E) (hN : ∀ k, k ∈ S → ↑(N k) ⊆ E \ E')
    (hdisj : ∀ k k', k ∈ S → k' ∈ S → k ≠ k' → (↑(N k) : CoPset) ## ↑(N k')) :
    ([∗set] k ∈ S, finallyI (N k) k 1 (Q k)) ⊢ |={E, E'}=> ([∗set] k ∈ S, Obl.assigned k 1) ∗
      (([∗set] k ∈ S, ▷ Obl.variant k iprop(True)
          (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) (Q k)))) ={E', E}=∗
        [∗set] k ∈ S, (Obl.assigned k (Qp.half 1) -∗ finallyI (N k) k 1 (Q k))) := by
  unfold finallyI
  iintro Us
  imod untilI_acc_assigned_set hE' hN hdisj $$ Us with ⟨H, ACC⟩
  icases (bigSepS_mono_of_forall fun _ => later_mono sep_elim_left).trans bigSepS_later_2 $$ H
    with >H
  imodintro
  iframe ACC H

theorem finallyI_acc_assigned_set_ndot {N₀ : Namespace} (hN : ↑N₀ ⊆ E) :
    ([∗set] k ∈ S, finallyI (N₀.@k) k 1 (Q k)) ⊢ |={E, E \ ↑N₀}=>
      ([∗set] k ∈ S, Obl.assigned k 1) ∗
      (([∗set] k ∈ S, ▷ Obl.variant k iprop(True)
          (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) (Q k))))
        ={E \ ↑N₀, E}=∗
        [∗set] k ∈ S, (Obl.assigned k (Qp.half 1) -∗ finallyI (N₀.@k) k 1 (Q k))) :=
  have ⟨hE', hNk, hdisj⟩ := ndot_masks hN
  finallyI_acc_assigned_set hE' (fun k _ => hNk k) fun k k' _ _ => hdisj k k'

theorem finallyI_record_discharged_set (E : CoPset) {X : IProp GF}
    (hX : ∀ k, k ∈ S → X ⊢ Q k) :
    ([∗set] k ∈ S, Obl.discharged k) ⊢ X -∗ |={E}=>m X ∗ [∗set] k ∈ S,
      Obl.variant k iprop(True)
        (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) (Q k))) :=
  untilI_record_discharged_set E hX

/-- The discharge of a forest of untils whose invariants are open, in one model update at any
mask: every obligation of `S`, closed under children and hanging below the roots `ps`, is
discharged with a resource `X` that implies all their right formulas, which is given back with
the contents that close their invariants. -/
theorem untilIGuar_discharge_opened_forest {G₂ : Oid → TrSpec Expr State GF} (E : CoPset)
    (ps : List Parent) (K : Parent → Oids) (kids : Oid → Oids)
    (hclosed : ∀ k, k ∈ S → kids k ⊆ S)
    (hcovered : ∀ x, x ∈ S → (∃ p, p ∈ ps ∧ x ∈ K p) ∨ ∃ k, k ∈ S ∧ x ∈ kids k)
    {X : IProp GF} (hX : ∀ k, k ∈ S → X ⊢ Q k) :
    ([∗list] p ∈ ps, Par.kids p (K p)) ⊢
      ([∗set] k ∈ S, (Q k ⊨ₜ G₂ k) ∗ Obl.assigned k 1 ∗ oblKids k (kids k)) -∗ X -∗
        |={E}=>m X ∗ ([∗list] p ∈ ps, Par.kids p (K p \ S)) ∗
          [∗set] k ∈ S, Obl.discharged k ∗ Obl.variant k (P k) (untilDischarged k (G₂ k)) := by
  iintro Hps HS HX
  icases bigSepS_sep.1 $$ HS with ⟨#HG, HS⟩
  imod obl_discharge_forest E ps K S kids hclosed hcovered $$ Hps [HS] with ⟨Hps, #HD⟩
  · iapply bigSepS_mono_of_forall (fun _ => sep_comm.1) $$ HS
  imod untilIGuar_record_discharged_set (P := P) E hX $$ [] HX with ⟨HX, HV⟩
  · iapply bigSepS_sep.2
    iframe HG HD
  imodintro
  iframe HX Hps
  iapply bigSepS_sep.2
  iframe HD HV

/-- The same, where the roots end without children. -/
theorem untilIGuar_discharge_opened_forest_all {G₂ : Oid → TrSpec Expr State GF} (E : CoPset)
    (ps : List Parent) (K : Parent → Oids) (kids : Oid → Oids) (hK : ∀ p, p ∈ ps → K p ⊆ S)
    (hclosed : ∀ k, k ∈ S → kids k ⊆ S)
    (hcovered : ∀ x, x ∈ S → (∃ p, p ∈ ps ∧ x ∈ K p) ∨ ∃ k, k ∈ S ∧ x ∈ kids k)
    {X : IProp GF} (hX : ∀ k, k ∈ S → X ⊢ Q k) :
    ([∗list] p ∈ ps, Par.kids p (K p)) ⊢
      ([∗set] k ∈ S, (Q k ⊨ₜ G₂ k) ∗ Obl.assigned k 1 ∗ oblKids k (kids k)) -∗ X -∗
        |={E}=>m X ∗ ([∗list] p ∈ ps, Par.kids p ∅) ∗
          [∗set] k ∈ S, Obl.discharged k ∗ Obl.variant k (P k) (untilDischarged k (G₂ k)) := by
  iintro Hps HS HX
  imod untilIGuar_discharge_opened_forest (P := P) E ps K kids hclosed hcovered hX $$ Hps HS HX
    with ⟨HX, Hps, HV⟩
  imodintro
  iframe HX HV
  iapply BigSepL.bigSepL_mono ?_ $$ Hps
  intro _ p hp
  have hp' := hK p (List.mem_of_getElem? hp)
  rw [eq_empty_iff.2 fun y hy => (mem_diff.1 hy).2 (hp' y (mem_diff.1 hy).1)]

/-- The same below the threads `js`, which end without children. -/
theorem untilIGuar_discharge_opened_forest_threads {G₂ : Oid → TrSpec Expr State GF}
    (E : CoPset) (js : List ThreadId) (K : ThreadId → Oids) (kids : Oid → Oids)
    (hK : ∀ j, j ∈ js → K j ⊆ S) (hclosed : ∀ k, k ∈ S → kids k ⊆ S)
    (hcovered : ∀ x, x ∈ S → (∃ j, j ∈ js ∧ x ∈ K j) ∨ ∃ k, k ∈ S ∧ x ∈ kids k)
    {X : IProp GF} (hX : ∀ k, k ∈ S → X ⊢ Q k) :
    ([∗list] j ∈ js, thKids j (K j)) ⊢
      ([∗set] k ∈ S, (Q k ⊨ₜ G₂ k) ∗ Obl.assigned k 1 ∗ oblKids k (kids k)) -∗ X -∗
        |={E}=>m X ∗ ([∗list] j ∈ js, thKids j ∅) ∗
          [∗set] k ∈ S, Obl.discharged k ∗ Obl.variant k (P k) (untilDischarged k (G₂ k)) := by
  let K' : Parent → Oids := fun p => match p with
    | .thread j => K j
    | .obl _ => ∅
  have h := untilIGuar_discharge_opened_forest_all (P := P) (G₂ := G₂) E (js.map .thread) K'
    kids
    (fun p hp => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
      exact hK j hj)
    hclosed
    (fun x hx => (hcovered x hx).imp_left fun ⟨j, hj, hxj⟩ =>
      ⟨.thread j, List.mem_map_of_mem hj, hxj⟩)
    hX
  rw [BigSepL.bigSepL_map, BigSepL.bigSepL_map] at h
  exact h

/-- The guarantees of the canonical readings, for the set `S`. -/
private theorem bigSepS_guar_canon (kids : Oid → Oids) :
    ([∗set] k ∈ S, Obl.assigned k 1 ∗ oblKids k (kids k)) ⊢@{IProp GF}
      [∗set] k ∈ S, (Q k ⊨ₜ TrSpec.canon (Expr := Expr) (State := State) (Q k)) ∗
        Obl.assigned k 1 ∗ oblKids k (kids k) :=
  bigSepS_mono_of_forall fun k => emp_sep.2.trans (sep_mono_left (guar_canon (Q k)))

theorem untilI_discharge_opened_forest (E : CoPset) (ps : List Parent) (K : Parent → Oids)
    (kids : Oid → Oids) (hclosed : ∀ k, k ∈ S → kids k ⊆ S)
    (hcovered : ∀ x, x ∈ S → (∃ p, p ∈ ps ∧ x ∈ K p) ∨ ∃ k, k ∈ S ∧ x ∈ kids k)
    {X : IProp GF} (hX : ∀ k, k ∈ S → X ⊢ Q k) :
    ([∗list] p ∈ ps, Par.kids p (K p)) ⊢
      ([∗set] k ∈ S, Obl.assigned k 1 ∗ oblKids k (kids k)) -∗ X -∗
        |={E}=>m X ∗ ([∗list] p ∈ ps, Par.kids p (K p \ S)) ∗
          [∗set] k ∈ S, Obl.discharged k ∗ Obl.variant k (P k)
            (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) (Q k))) := by
  iintro Hps HS
  iapply untilIGuar_discharge_opened_forest (P := P) E ps K kids hclosed hcovered hX $$ Hps
  iapply bigSepS_guar_canon kids $$ HS

theorem untilI_discharge_opened_forest_all (E : CoPset) (ps : List Parent) (K : Parent → Oids)
    (kids : Oid → Oids) (hK : ∀ p, p ∈ ps → K p ⊆ S) (hclosed : ∀ k, k ∈ S → kids k ⊆ S)
    (hcovered : ∀ x, x ∈ S → (∃ p, p ∈ ps ∧ x ∈ K p) ∨ ∃ k, k ∈ S ∧ x ∈ kids k)
    {X : IProp GF} (hX : ∀ k, k ∈ S → X ⊢ Q k) :
    ([∗list] p ∈ ps, Par.kids p (K p)) ⊢
      ([∗set] k ∈ S, Obl.assigned k 1 ∗ oblKids k (kids k)) -∗ X -∗
        |={E}=>m X ∗ ([∗list] p ∈ ps, Par.kids p ∅) ∗
          [∗set] k ∈ S, Obl.discharged k ∗ Obl.variant k (P k)
            (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) (Q k))) := by
  iintro Hps HS
  iapply untilIGuar_discharge_opened_forest_all (P := P) E ps K kids hK hclosed hcovered hX
    $$ Hps
  iapply bigSepS_guar_canon kids $$ HS

theorem untilI_discharge_opened_forest_threads (E : CoPset) (js : List ThreadId)
    (K : ThreadId → Oids) (kids : Oid → Oids) (hK : ∀ j, j ∈ js → K j ⊆ S)
    (hclosed : ∀ k, k ∈ S → kids k ⊆ S)
    (hcovered : ∀ x, x ∈ S → (∃ j, j ∈ js ∧ x ∈ K j) ∨ ∃ k, k ∈ S ∧ x ∈ kids k)
    {X : IProp GF} (hX : ∀ k, k ∈ S → X ⊢ Q k) :
    ([∗list] j ∈ js, thKids j (K j)) ⊢
      ([∗set] k ∈ S, Obl.assigned k 1 ∗ oblKids k (kids k)) -∗ X -∗
        |={E}=>m X ∗ ([∗list] j ∈ js, thKids j ∅) ∗
          [∗set] k ∈ S, Obl.discharged k ∗ Obl.variant k (P k)
            (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) (Q k))) := by
  iintro Hjs HS
  iapply untilIGuar_discharge_opened_forest_threads (P := P) E js K kids hK hclosed hcovered hX
    $$ Hjs
  iapply bigSepS_guar_canon kids $$ HS

theorem finallyI_discharge_opened_forest (E : CoPset) (ps : List Parent) (K : Parent → Oids)
    (kids : Oid → Oids) (hclosed : ∀ k, k ∈ S → kids k ⊆ S)
    (hcovered : ∀ x, x ∈ S → (∃ p, p ∈ ps ∧ x ∈ K p) ∨ ∃ k, k ∈ S ∧ x ∈ kids k)
    {X : IProp GF} (hX : ∀ k, k ∈ S → X ⊢ Q k) :
    ([∗list] p ∈ ps, Par.kids p (K p)) ⊢
      ([∗set] k ∈ S, Obl.assigned k 1 ∗ oblKids k (kids k)) -∗ X -∗
        |={E}=>m X ∗ ([∗list] p ∈ ps, Par.kids p (K p \ S)) ∗
          [∗set] k ∈ S, Obl.discharged k ∗ Obl.variant k iprop(True)
            (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) (Q k))) :=
  untilI_discharge_opened_forest E ps K kids hclosed hcovered hX

theorem finallyI_discharge_opened_forest_all (E : CoPset) (ps : List Parent) (K : Parent → Oids)
    (kids : Oid → Oids) (hK : ∀ p, p ∈ ps → K p ⊆ S) (hclosed : ∀ k, k ∈ S → kids k ⊆ S)
    (hcovered : ∀ x, x ∈ S → (∃ p, p ∈ ps ∧ x ∈ K p) ∨ ∃ k, k ∈ S ∧ x ∈ kids k)
    {X : IProp GF} (hX : ∀ k, k ∈ S → X ⊢ Q k) :
    ([∗list] p ∈ ps, Par.kids p (K p)) ⊢
      ([∗set] k ∈ S, Obl.assigned k 1 ∗ oblKids k (kids k)) -∗ X -∗
        |={E}=>m X ∗ ([∗list] p ∈ ps, Par.kids p ∅) ∗
          [∗set] k ∈ S, Obl.discharged k ∗ Obl.variant k iprop(True)
            (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) (Q k))) :=
  untilI_discharge_opened_forest_all E ps K kids hK hclosed hcovered hX

theorem finallyI_discharge_opened_forest_threads (E : CoPset) (js : List ThreadId)
    (K : ThreadId → Oids) (kids : Oid → Oids) (hK : ∀ j, j ∈ js → K j ⊆ S)
    (hclosed : ∀ k, k ∈ S → kids k ⊆ S)
    (hcovered : ∀ x, x ∈ S → (∃ j, j ∈ js ∧ x ∈ K j) ∨ ∃ k, k ∈ S ∧ x ∈ kids k)
    {X : IProp GF} (hX : ∀ k, k ∈ S → X ⊢ Q k) :
    ([∗list] j ∈ js, thKids j (K j)) ⊢
      ([∗set] k ∈ S, Obl.assigned k 1 ∗ oblKids k (kids k)) -∗ X -∗
        |={E}=>m X ∗ ([∗list] j ∈ js, thKids j ∅) ∗
          [∗set] k ∈ S, Obl.discharged k ∗ Obl.variant k iprop(True)
            (untilDischarged k (TrSpec.canon (Expr := Expr) (State := State) (Q k))) :=
  untilI_discharge_opened_forest_threads E js K kids hK hclosed hcovered hX

end Sets

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
    ⊢@{IProp GF} untilIGuar N k q P Q G₁ G₂ ⊨ₜ (G₁ Uₛ G₂) := by
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W %tc %X ⟨HI, MI, U⟩
  iunfold untilIGuar at U
  icases U with ⟨Oa, U⟩
  iunfold untilIGuarPers at U
  icases U with ⟨%j, %r, %γP, %γQ, %st, %v, %Ω₁, %fu₁, %o₁, #Hj, #HE, #HγP, #HγQ, #OI, -, -, -,
    #AC⟩
  icases Obl.assigned_modelInterp_lookup k _ m i Ω W n tc X $$ [Oa MI] with %hk
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
  iintro %Sys %l %h' %g %v' %Ω' %W' %τf %sched %γ %σ' %tp' #ST %⟨hsch, hfs, hlb, hht⟩ #B
    ⟨HI', MI', Sy'⟩
  icases bundleUntilCert l n j r N k γP γQ G₁ G₂ hrn $$ B Hj HγP HγQ [] with #C
  · iintro %hr'
    subst hr'
    inext
    ileft
    iexact AC
  have hex : TrIProp.strongUntil G₁.internal G₂.internal
      (Ordinals.Ordinal.succ (Ordinals.Ordinal.succ (fairMeasureUb fu))) ⟨n, τf⟩ ⊢
      (G₁ Uₛ G₂).internal ⟨n, τf⟩ :=
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
    · icases Obl.assigned_modelInterp_lookup k _ g v' Ω' W' (n + 1) tp'.length
        (Cfg.crashed (tp', σ')) $$ [Oa' MI'] with %hk'
      · iframe Oa' MI'
      obtain ⟨fu', o', hk'⟩ := hk'
      icases modelInterp_eventObl_lookup g v' Ω' W' (n + 1) tp'.length (Cfg.crashed (tp', σ')) i
        (n, Ω) k (.assigned fu o) $$ [MI' EA] with %⟨-, -, -, -, hle⟩
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
      · iapply record_elim G₁ $$ TrecP ST %⟨hsch, hfs, hlb, hht⟩ B [HI' MI' Sy']
        iframe HI' MI' Sy'
      · iexists Ordinals.Ordinal.succ (fairMeasure (γ (n + 1)) o' fu')
        isplit
        · ipureintro
          refine Ordinals.Ordinal.succ_lt_succ_iff.mpr (Ordinals.Ordinal.lt_succ_iff.mpr ?_)
          exact Ordinals.Ordinal.le_trans (fairMeasure_le_ub _ o' fu') (fairMeasureUb_le_mono hfu)
        · iapply untilRun Sys N k γP γQ j r P G₁ G₂ $$ ST Hj HγP HγQ OI %h' %(n + 1) %σ' %tp' %g
            %v' %Ω' %W' %τf %sched %γ %fu' %o' %⟨by omega, hsch, hfs, hlb, hht, hk'⟩
            [HI' MI' Sy']
          iframe HI' MI' Sy'
    · -- discharged during the step: at `n` (before the step) or at `n + 1` (after)
      iunfold untilDischarged at R
      icases R with ⟨%n', %i', %Ω'', #EF, #TQ'⟩
      icases modelInterp_eventObl_lookup g v' Ω' W' (n + 1) tp'.length (Cfg.crashed (tp', σ'))
        i' (n', Ω'') k .discharged $$ [MI' EF] with %⟨-, -, -, hn₁, -⟩
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
        iapply record_elim G₂ $$ TQ' ST %⟨hsch, hfs, hlb, hht⟩ B [HI' MI' Sy']
        iframe HI' MI' Sy'
      · have hn' : n' = n + 1 := by simp only at hn₁; omega
        subst hn'
        iright
        isplit
        · iapply record_elim G₁ $$ TrecP ST %⟨hsch, hfs, hlb, hht⟩ B [HI' MI' Sy']
          iframe HI' MI' Sy'
        · iexists 0
          isplit
          · ipureintro
            exact Ordinals.Ordinal.zero_lt_succ _
          · iapply untilRunDischarged Sys G₁.internal G₂ 0 h' (n + 1) σ' tp' g v' Ω' W' τf sched γ
              ⟨hsch, hfs, hlb, hht⟩ $$ ST TQ' [HI' MI' Sy']
            iframe HI' MI' Sy'
  · -- `Q` holds at `n`
    imodintro
    ileft
    iapply record_elim G₂ $$ TrecQ ST %⟨hsch, hfs, hlb, hht⟩ B [HI' MI' Sy']
    iframe HI' MI' Sy'
  · -- discharged before the check: the discharge was at `n`
    icases eventObl_assigned_discharged_le $$ [EA EF] with %hn₂
    · iframe EA EF
    have hnn : n' = n := by omega
    subst hnn
    imodintro
    ileft
    iapply record_elim G₂ $$ TQ' ST %⟨hsch, hfs, hlb, hht⟩ B [HI' MI' Sy']
    iframe HI' MI' Sy'

@[lantana_alias guar_untilI]
theorem guar_untilI : ⊢@{IProp GF} untilI N k q P Q ⊨ₜ (TrSpec.canon P Uₛ TrSpec.canon Q) := by
  rw [untilI_eq]; exact guar_untilIGuar

@[lantana_alias guar_untilI_valid]
theorem guar_untilI_valid {G₁ G₂ : TrSpec Expr State GF} (hG₁ : ⊢ P ⊨ₜ G₁) (hG₂ : ⊢ Q ⊨ₜ G₂) :
    ⊢@{IProp GF} untilI N k q P Q ⊨ₜ (G₁ Uₛ G₂) :=
  guar_untilI.trans
    (guar_weaken (TrSpec.strongUntil_mono (@TrSpec.canon_le _ _ _ _ _ _ _ instM instT _ _ _ hG₁)
      (@TrSpec.canon_le _ _ _ _ _ _ _ instM instT _ _ _ hG₂)))

/-! ## Inference -/

instance guarOf_alwaysI (G : TrSpec Expr State GF) [GuarOf P G] : GuarOf (alwaysI N P) (□ₛ G) :=
  ⟨guar_alwaysI_valid GuarOf.guar_of⟩
instance guarOf_untilI (G₁ G₂ : TrSpec Expr State GF) [GuarOf P G₁] [GuarOf Q G₂] :
    GuarOf (untilI N k q P Q) (G₁ Uₛ G₂) :=
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
