/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TemporalFormula

/-! # The run: certification of the temporal formulas, and the loops that read them off a run

Rocq `lantana/trace/temporal_formula_run.v`.

**Certification.** At every position the adequacy proof runs the check `regCheck`: it appends
a marker to the registry, opens every registered invariant and produces a later-guarded record
of its content at the position, the certificate (`certOfEntry`); the contents stay in their
invariants. The marked registry's lower bound and the certificates form the bundle.

**Loops.** For any system with the one-step property (`sysStep`), a registered `alwaysI`
(`alwaysRun`) and a registered `untilI` (`untilRun`) are read off the run position by position
(Löb induction): each iteration (`sysStepIter`) takes the certificate of its entry from the
bundle of the position (`bundleAlwaysCert`, `bundleUntilCert`), whose later the deferred shape
strips, and after the step reads the record against the system at the next position. The
until's rank is the successor of the fair-scheduler measure of its obligation, which drops
across every step (`oblsDrop`); after the step a later credit opens the obligation invariant
to decide the continuation.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open Lantana.Model
open Iris.Std LawfulPartialMap
open scoped Lantana.TrSpec Lantana.TrProp

variable {Expr State Val : Type} {GF : BundledGFunctors} [Language Expr State Val]
variable [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF]

/-- An obligation discharged at an event is discharged after any event at which it is
assigned. -/
theorem eventObl_assigned_discharged_le {v i' n n' : Nat} {Ω Ω' : Obls} {k : Oid} {fu : Fuel}
    {o : ThreadId} :
    eventObl (GF := GF) v (n, Ω) k (.assigned fu o) ∗ eventObl i' (n', Ω') k .discharged ⊢
      ⌜n ≤ n'⌝ := by
  by_cases hle : i' ≤ v
  · iintro ⟨EA, EF⟩
    icases eventObl_compare (n', Ω') (n, Ω) k .discharged (.assigned fu o) hle $$ [EF EA]
      with %⟨-, -, hle'⟩
    · iframe EF EA
    exact absurd hle' (by simp [Model.Obl.le])
  · iintro ⟨EA, EF⟩
    icases eventObl_compare (i := v) (j := i') (n, Ω) (n', Ω') k (.assigned fu o) .discharged
      (by omega) $$ [EA EF]
      with %⟨hn, -, -⟩
    · iframe EA EF
    ipureintro
    exact hn

/-! ## Certification -/

section Certification

@[lantana_alias until_cert_assigned]
theorem untilCert_assigned (k : Oid) (P R : IProp GF) (G₁ G₂ : TrSpec Expr State GF)
    (h : List (HistEntry Expr State)) (n : Nat) (σ : State) (tp : ThreadPool Expr)
    (g : List MEvent) (v : Nat) (Ω : Obls) (W : Witnesses) (fu : Fuel) (o : ThreadId)
    (hk : get? Ω k = some (.assigned fu o)) :
    ▷ (P ⊨ₜ G₁) ⊢ ▷ Obl.variant k P R ∗ historyInterp h n σ tp ∗
      modelInterp g v Ω W n tp.length -∗ ▷ (record G₁ n ∨ record G₂ n) := by
  iintro #HG ⟨Var, HI, MI⟩
  inext
  icases (Obl.variant_unfold k P R).1 $$ Var with (⟨-, HP⟩ | ⟨D, -⟩)
  · ileft
    iapply guar_elim P G₁ h n σ tp g v Ω W $$ HG
    iframe HI MI HP
  · icases Obl.discharged_modelInterp_lookup k g v Ω W n tp.length $$ [D MI] with %hd
    · iframe D MI
    rw [hk] at hd
    cases hd

@[lantana_alias until_cert_discharged]
theorem untilCert_discharged (k : Oid) (P : IProp GF) (G₂ : TrSpec Expr State GF)
    (h : List (HistEntry Expr State)) (n : Nat) (σ : State) (tp : ThreadPool Expr)
    (g : List MEvent) (v : Nat) (Ω : Obls) (W : Witnesses)
    (hk : get? Ω k = some .discharged) :
    ▷ Obl.variant k P (untilDischarged k G₂) ∗ historyInterp h n σ tp ∗
      modelInterp g v Ω W n tp.length ⊢
      ▷ (∃ (n' i' : Nat) (Ω' : Obls), ⌜n' ≤ n⌝ ∗ eventObl i' (n', Ω') k .discharged ∗
        record G₂ n') := by
  iintro ⟨Var, -, MI⟩
  inext
  icases (Obl.variant_unfold k P _).1 $$ Var with (⟨A, -⟩ | ⟨-, R⟩)
  · icases Obl.assigned_modelInterp_lookup k _ g v Ω W n tp.length $$ [A MI] with %ha
    · iframe A MI
    obtain ⟨a, t, ha⟩ := ha
    rw [hk] at ha
    cases ha
  · iunfold untilDischarged at R
    icases R with ⟨%n', %i', %Ω', #EF, #TF⟩
    icases modelInterp_eventObl_lookup g v Ω W n tp.length i' (n', Ω') k .discharged $$ [MI EF]
      with %⟨-, -, -, hn, -⟩
    · iframe MI EF
    iexists n', i', Ω'
    iframe EF TF
    ipureintro
    exact hn

/-- The certificate of one registered item (Rocq `cert_of_entry`): open its invariant, take
a later-guarded record of its content, and close it. -/
@[lantana_alias cert_of_entry]
theorem certOfEntry (n : Nat) (e : RegEntry) (h : List (HistEntry Expr State)) (σ : State)
    (tp : ThreadPool Expr) (g : List MEvent) (v : Nat) (Ω : Obls) (W : Witnesses) :
    regEntryInterp (Expr := Expr) (State := State) e ⊢ historyInterp h n σ tp -∗
      modelInterp g v Ω W n tp.length ={⊤}=∗
      historyInterp h n σ tp ∗ modelInterp g v Ω W n tp.length ∗
        cert (Expr := Expr) (State := State) (GF := GF) n e := by
  rw [cert_eq]
  rcases e with _ | ⟨N, γ⟩ | ⟨N, k, γP, γQ⟩
  · simp only [regEntryInterp, certPre]
    iintro - HI MI
    imodintro
    iframe HI MI
  · simp only [regEntryInterp, certPre]
    iintro #⟨%P, %G, #SP, #Hinv, #HG⟩ HI MI
    imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hinv with ⟨HP, Hclose⟩
    ihave #C : ▷ record G n $$ [HP HI MI]
    · iapply guar_elim_later_guar P G h n σ tp g v Ω W $$ HG
      iframe HP HI MI
    imod Hclose $$ HP with -
    imodintro
    iframe HI MI
    iexists G.internal
    iframe SP
    iunfold record at C
    iexact C
  · simp only [regEntryInterp, certPre]
    iintro #⟨%P, %G₁, %G₂, #SP, #SQ, #OI, #HG⟩ HI MI
    imod Obl.inv_acc ⊤ N k P _ CoPset.subseteq_top $$ OI with ⟨Var, Hclose⟩
    ihave #C : (▷ (record G₁ n ∨ record G₂ n) ∨
        ▷ (∃ (n' i' : Nat) (Ω' : Obls), ⌜n' ≤ n⌝ ∗ eventObl i' (n', Ω') k .discharged ∗
          record G₂ n')) $$ [Var HI MI]
    · rcases hk : get? Ω k with _ | ⟨fu, o⟩ | _
      · ileft
        inext
        icases (Obl.variant_unfold k P _).1 $$ Var with (⟨A, -⟩ | ⟨D, -⟩)
        · icases Obl.assigned_modelInterp_lookup k _ g v Ω W n tp.length $$ [A MI] with %ha
          · iframe A MI
          obtain ⟨a, t, ha⟩ := ha
          rw [hk] at ha
          cases ha
        · icases Obl.discharged_modelInterp_lookup k g v Ω W n tp.length $$ [D MI] with %hd
          · iframe D MI
          rw [hk] at hd
          cases hd
      · ileft
        iapply untilCert_assigned k P _ G₁ G₂ h n σ tp g v Ω W fu o hk $$ HG
        iframe Var HI MI
      · iright
        iapply untilCert_discharged k P G₂ h n σ tp g v Ω W hk
        iframe Var HI MI
    imod Hclose $$ Var with -
    imodintro
    iframe HI MI
    iexists G₁.internal, G₂.internal
    iframe SP SQ
    iunfold record at C
    iexact C

/-- The certificates of all the registered items (Rocq `certify_entries`). -/
@[lantana_alias certify_entries]
theorem certifyEntries (n : Nat) (l : List (Nat × RegEntry)) (h : List (HistEntry Expr State))
    (σ : State) (tp : ThreadPool Expr) (g : List MEvent) (v : Nat) (Ω : Obls) (W : Witnesses) :
    regEntries (regEntryInterp (Expr := Expr) (State := State)) l ⊢ historyInterp h n σ tp -∗
      modelInterp g v Ω W n tp.length ={⊤}=∗
      historyInterp h n σ tp ∗ modelInterp g v Ω W n tp.length ∗
        [∗list] pe ∈ l, cert (Expr := Expr) (State := State) (GF := GF) n pe.2 := by
  induction l with
  | nil =>
    iintro - HI MI
    imodintro
    iframe HI MI
    iapply BigSepL.bigSepL_nil.mpr
    iempintro
  | cons pe l ih =>
    have hcons : regEntries (regEntryInterp (Expr := Expr) (State := State)) (pe :: l) ⊢
        iprop(((∃ st : HistEntry Expr State, histEvent (GF := GF) pe.1 st) ∗
            regEntryInterp (Expr := Expr) (State := State) pe.2) ∗
          regEntries (regEntryInterp (Expr := Expr) (State := State)) l) := by
      unfold regEntries
      exact BigSepL.bigSepL_cons.mp
    iintro #Hl HI MI
    icases hcons $$ Hl with ⟨⟨-, #Hd⟩, #Hl'⟩
    imod certOfEntry n pe.2 h σ tp g v Ω W $$ Hd HI MI with ⟨HI, MI, #C⟩
    imod ih $$ Hl' HI MI with ⟨HI, MI, #Cs⟩
    imodintro
    iframe HI MI
    iapply BigSepL.bigSepL_cons.mpr
    isplitl []
    · iexact C
    · iexact Cs

/-- The check at `n` appends the marker (Rocq `reg_mark`). -/
@[lantana_alias reg_mark]
theorem regMark (n : Nat) (l : List (Nat × RegEntry)) (h : List (HistEntry Expr State))
    (σ : State) (tp : ThreadPool Expr) :
    regAuth (GF := GF) l ⊢ regEntries (regEntryInterp (Expr := Expr) (State := State)) l -∗
      historyInterp h n σ tp ==∗
      historyInterp h n σ tp ∗ regAuth (l ++ [(n, .mark)]) ∗
        regEntries regEntryInterp (l ++ [(n, .mark)]) ∗ regLb (l ++ [(n, .mark)]) := by
  iintro Ha #Hl HI
  ihave %hb := regEntries_bound regEntryInterp l h n σ tp $$ Hl HI
  imod regAuth_append l n .mark hb $$ Ha with ⟨Ha, -⟩
  ihave #Hnow := historyInterp_histEvent_now h n σ tp $$ HI
  ihave #Hlb := regAuth_lb _ $$ Ha
  imodintro
  iframe HI Ha
  isplitl []
  · unfold regEntries
    iapply BigSepL.bigSepL_snoc.mpr
    isplitl []
    · iexact Hl
    · isplitl []
      · iexists (σ, tp)
        iexact Hnow
      · simp only [regEntryInterp]
        itrivial
  · iexact Hlb

@[lantana_alias bundle_intro]
theorem bundleIntro (n : Nat) (l : List (Nat × RegEntry)) (hlast : l.getLast? = some (n, .mark)) :
    regLb (GF := GF) l ⊢ ([∗list] pe ∈ l, cert (Expr := Expr) (State := State) (GF := GF) n pe.2)
      -∗ bundle (Expr := Expr) (State := State) l n := by
  rw [bundle_eq]
  simp only [cert_eq]
  unfold bundlePre
  iintro #Hlb #Cs
  iframe Hlb
  isplitl []
  · ipureintro
    exact hlast
  · iexact Cs

/-- The check as a whole (Rocq `reg_check`): the bundle for `n`, and the registry state
back. -/
@[lantana_alias reg_check]
theorem regCheck (n : Nat) (h : List (HistEntry Expr State)) (σ : State) (tp : ThreadPool Expr)
    (g : List MEvent) (v : Nat) (Ω : Obls) (W : Witnesses) :
    regState (Expr := Expr) (State := State) (GF := GF) ⊢ historyInterp h n σ tp -∗
      modelInterp g v Ω W n tp.length ={⊤}=∗
      regState (Expr := Expr) (State := State) ∗ historyInterp h n σ tp ∗
        modelInterp g v Ω W n tp.length ∗ ∃ l, bundle (Expr := Expr) (State := State) l n := by
  unfold regState regStateWith
  iintro ⟨%l, Ha, #Hl⟩ HI MI
  imod regMark n l h σ tp $$ Ha Hl HI with ⟨HI, Ha, #Hl', #Hlb⟩
  imod certifyEntries n _ h σ tp g v Ω W $$ Hl' HI MI with ⟨HI, MI, #Cs⟩
  ihave #B := bundleIntro n (l ++ [(n, .mark)]) (by simp) $$ Hlb Cs
  imodintro
  iframe HI MI
  isplitl [Ha]
  · iexists l ++ [(n, .mark)]
    iframe Ha
    iexact Hl'
  · iexists l ++ [(n, .mark)]
    iexact B

end Certification

/-! ## Reading the registered structures off a run -/

section Loops

/-- The certificate of a registered always at a position `n` after its registration
position `r`: from the bundle, or, at `r` itself, the allocation record
(Rocq `bundle_always_cert`). -/
@[lantana_alias bundle_always_cert]
theorem bundleAlwaysCert (l : List (Nat × RegEntry)) (n j r : Nat) (N : Namespace) (γ : GName)
    (G : TrSpec Expr State GF) (hrn : r ≤ n) :
    bundle (Expr := Expr) (State := State) l n ⊢ regIdx j r (.always N γ) -∗
      savedTrI γ G.internal -∗ (⌜r = n⌝ -∗ ▷ record G n) -∗ ▷ record G n := by
  rw [bundle_eq]
  unfold bundlePre
  iintro ⟨#Hlb, %hlast, #Cs⟩ #Hj #Hγ AC
  icases regIdx_lb_pos j r _ hlast $$ Hlb Hj with %hpos
  rcases hpos with hin | hle
  · have hc : ([∗list] pe ∈ l, certPre (recordTrI (Expr := Expr) (State := State)) n pe.2) ⊢
        iprop(∃ f : Trace Expr State → IProp GF, savedTrI γ f ∗ ▷ recordTrI f n) :=
      BigSepL.bigSepL_lookup (Φ := fun _ pe =>
        certPre (recordTrI (Expr := Expr) (State := State)) n pe.2) hin
    icases hc $$ Cs with ⟨%f, #Hf, #Cj⟩
    ihave #Heq := savedTrI_agree_fun γ f G.internal $$ Hf Hγ
    inext
    unfold record
    iapply recordTrI_internalEq f G.internal n $$ Heq Cj
  · iapply AC
    ipureintro
    omega

/-- The same for an until (Rocq `bundle_until_cert`). -/
@[lantana_alias bundle_until_cert]
theorem bundleUntilCert (l : List (Nat × RegEntry)) (n j r : Nat) (N : Namespace) (k : Oid)
    (γP γQ : GName) (G₁ G₂ : TrSpec Expr State GF) (hrn : r ≤ n) :
    bundle (Expr := Expr) (State := State) l n ⊢ regIdx j r (.until N k γP γQ) -∗
      savedTrI γP G₁.internal -∗ savedTrI γQ G₂.internal -∗
      (⌜r = n⌝ -∗ ▷ (record G₁ n ∨ record G₂ n)) -∗
      ▷ (record G₁ n ∨ record G₂ n) ∨
        ▷ (∃ (n' i' : Nat) (Ω' : Obls), ⌜n' ≤ n⌝ ∗ eventObl i' (n', Ω') k .discharged ∗
          record G₂ n') := by
  rw [bundle_eq]
  unfold bundlePre
  iintro ⟨#Hlb, %hlast, #Cs⟩ #Hj #HγP #HγQ AC
  icases regIdx_lb_pos j r _ hlast $$ Hlb Hj with %hpos
  rcases hpos with hin | hle
  · have hc : ([∗list] pe ∈ l, certPre (recordTrI (Expr := Expr) (State := State)) n pe.2) ⊢
        iprop(∃ fP fQ : Trace Expr State → IProp GF, savedTrI γP fP ∗ savedTrI γQ fQ ∗
          (▷ (recordTrI fP n ∨ recordTrI fQ n) ∨
            ▷ (∃ (n' i' : Nat) (Ω' : Obls),
              ⌜n' ≤ n⌝ ∗ eventObl i' (n', Ω') k .discharged ∗ recordTrI fQ n'))) :=
      BigSepL.bigSepL_lookup (Φ := fun _ pe =>
        certPre (recordTrI (Expr := Expr) (State := State)) n pe.2) hin
    icases hc $$ Cs with ⟨%fP, %fQ, #HfP, #HfQ, (#Cj | #Cj)⟩
    · ileft
      ihave #HeqP := savedTrI_agree_fun γP fP G₁.internal $$ HfP HγP
      ihave #HeqQ := savedTrI_agree_fun γQ fQ G₂.internal $$ HfQ HγQ
      inext
      unfold record
      icases Cj with (#Cj | #Cj)
      · ileft
        iapply recordTrI_internalEq fP G₁.internal n $$ HeqP Cj
      · iright
        iapply recordTrI_internalEq fQ G₂.internal n $$ HeqQ Cj
    · iright
      ihave #HeqQ := savedTrI_agree_fun γQ fQ G₂.internal $$ HfQ HγQ
      inext
      icases Cj with ⟨%n', %i', %Ω', %hn', #EF, #Cj⟩
      iexists n', i', Ω'
      iframe EF
      isplitl []
      · ipureintro
        exact hn'
      unfold record
      iapply recordTrI_internalEq fQ G₂.internal n' $$ HeqQ Cj
  · ileft
    iapply AC
    ipureintro
    omega

/-- One iteration of a loop, in the deferred shape (Rocq `sys_step_iter`): the check gives the
bundle and the certificate `C`, whose later the shape's later strips; the step gives the
system at `n + 1`, the facts about the step and `c` later credits. -/
@[lantana_alias sys_step_iter]
theorem sysStepIter (Sys : SysT Expr State GF) (c : Nat) (h : List (HistEntry Expr State))
    (n : Nat) (σ : State) (tp : ThreadPool Expr) (g : List MEvent) (v : Nat) (Ω : Obls)
    (W : Witnesses) (τf : Nat → TraceState Expr State) (γ : Nat → ThreadId → Nat)
    (C Φ : IProp GF)
    (hf : IsBehavior (⟨n, τf⟩ : Trace Expr State) ∧ BehFscnt ⟨n, τf⟩ γ ∧
      owitInvLb (fairMeasure (γ n)) Ω W ∧ histTrace h τf) :
    sysStep Sys ⊢ historyInterp h n σ tp ∗ modelInterp g v Ω W n tp.length ∗ Sys n σ tp -∗
      (∀ l, bundle (Expr := Expr) (State := State) l n -∗ ▷ C) -∗
      ▷ (∀ (l : List (Nat × RegEntry)) (σ' : State) (tp' : ThreadPool Expr) (g' : List MEvent)
          (v' : Nat) (Ω' : Obls) (W' : Witnesses),
        ⌜IsBehavior (⟨n + 1, τf⟩ : Trace Expr State) ∧ BehFscnt ⟨n + 1, τf⟩ γ ∧
          owitInvLb (fairMeasure (γ (n + 1))) Ω' W' ∧ histTrace (h ++ [(σ', tp')]) τf ∧
          oblsDrop (fairMeasure (γ n)) (fairMeasure (γ (n + 1))) Ω Ω'⌝ -∗
        bundle (Expr := Expr) (State := State) l n -∗ C -∗ £ₙ c -∗
        historyInterp (h ++ [(σ', tp')]) (n + 1) σ' tp' ∗
          modelInterp g' v' Ω' W' (n + 1) tp'.length ∗ Sys (n + 1) σ' tp' -∗
        |={⊤}=> Φ) -∗
      TrIProp.defer Φ := by
  rw [sysStep_eq]
  unfold sysStepPre TrIProp.defer
  iintro #ST HS HC K
  imod ST $$ %c %h %n %σ %tp %g %v %Ω %W %τf %γ %hf HS with ⟨%l, B, Step⟩
  have hb : bundlePre (recordTrI (Expr := Expr) (State := State) (GF := GF)) l n ⊢
      bundle (Expr := Expr) (State := State) l n := by
    rw [bundle_eq]
  ihave #B' := hb $$ B
  ihave HC := HC $$ %l B'
  imodintro
  inext
  imod Step
  imodintro
  imod Step
  imodintro
  iapply ALC_wand $$ [K HC] Step
  iintro Hs
  imod Hs with ⟨%σ', %tp', %g', %v', %Ω', %W', %hf', LC, HI, MI, Sy⟩
  iapply K $$ %l %σ' %tp' %g' %v' %Ω' %W' %hf' B' HC LC
  iframe HI MI Sy

/-! ### The always loop -/

/-- A registered always, read off a run after its registration (Rocq `always_run`). -/
@[lantana_alias always_run]
theorem alwaysRun (Sys : SysT Expr State GF) (N : Namespace) (γa : GName)
    (G : TrSpec Expr State GF) (j r : Nat) :
    sysStep Sys ⊢ regIdx j r (.always N γa) -∗ savedTrI γa G.internal -∗
      ∀ (h : List (HistEntry Expr State)) (n : Nat) (σ : State) (tp : ThreadPool Expr)
        (g : List MEvent) (v : Nat) (Ω : Obls) (W : Witnesses)
        (τf : Nat → TraceState Expr State) (γ : Nat → ThreadId → Nat),
        ⌜r < n ∧ IsBehavior (⟨n, τf⟩ : Trace Expr State) ∧ BehFscnt ⟨n, τf⟩ γ ∧
          owitInvLb (fairMeasure (γ n)) Ω W ∧ histTrace h τf⌝ -∗
        historyInterp h n σ tp ∗ modelInterp g v Ω W n tp.length ∗ Sys n σ tp -∗
        TrIProp.always G.internal ⟨n, τf⟩ := by
  iintro #ST #Hj #Hγ
  iloeb as IH
  iintro %h %n %σ %tp %g %v %Ω %W %τf %γ %⟨hrn, hbeh, hfs, hlb, hht⟩ HS
  have hU : TrIProp.defer iprop(G.internal ⟨n, τf⟩ ∧ TrIProp.always G.internal ⟨n + 1, τf⟩) ⊢
      TrIProp.always G.internal ⟨n, τf⟩ :=
    (TrIProp.always_unfold G.internal ⟨n, τf⟩).mpr
  iapply hU
  iapply sysStepIter Sys 0 h n σ tp g v Ω W τf γ (record G n)
    iprop(G.internal ⟨n, τf⟩ ∧ TrIProp.always G.internal ⟨n + 1, τf⟩)
    ⟨hbeh, hfs, hlb, hht⟩ $$ ST HS [] []
  · iintro %l #B
    iapply bundleAlwaysCert l n j r N γa G (Nat.le_of_lt hrn) $$ B Hj Hγ
    iintro %hr
    exfalso
    omega
  · inext
    iintro %l %σ' %tp' %g' %v' %Ω' %W' %⟨hbeh', hfs', hlb', hht', -⟩ #B #C - HS'
    imodintro
    isplit
    · iapply record_elim G $$ C ST %⟨hbeh, hfs', hlb', hht'⟩ B HS'
    · iapply IH $$ %(h ++ [(σ', tp')]) %(n + 1) %σ' %tp' %g' %v' %Ω' %W' %τf %γ
        %⟨by omega, hbeh', hfs', hlb', hht'⟩ HS'

/-! ### The until loop -/

/-- With the record of the right reading at hand, one iteration proves the until at once
(Rocq `until_run_discharged`). -/
@[lantana_alias until_run_discharged]
theorem untilRunDischarged (Sys : SysT Expr State GF) (fP : TrIProp Expr State GF)
    (G₂ : TrSpec Expr State GF) (a : Fuel) (h : List (HistEntry Expr State)) (n : Nat)
    (σ : State) (tp : ThreadPool Expr) (g : List MEvent) (v : Nat) (Ω : Obls) (W : Witnesses)
    (τf : Nat → TraceState Expr State) (γ : Nat → ThreadId → Nat)
    (hf : IsBehavior (⟨n, τf⟩ : Trace Expr State) ∧ BehFscnt ⟨n, τf⟩ γ ∧
      owitInvLb (fairMeasure (γ n)) Ω W ∧ histTrace h τf) :
    sysStep Sys ⊢ record G₂ n -∗
      historyInterp h n σ tp ∗ modelInterp g v Ω W n tp.length ∗ Sys n σ tp -∗
      TrIProp.strongUntil fP G₂.internal a ⟨n, τf⟩ := by
  iintro #ST #TQ HS
  have hU : TrIProp.defer iprop(G₂.internal ⟨n, τf⟩ ∨ (fP ⟨n, τf⟩ ∧ ∃ a' : Fuel, ⌜a' < a⌝ ∧
      TrIProp.strongUntil fP G₂.internal a' ⟨n + 1, τf⟩)) ⊢
      TrIProp.strongUntil fP G₂.internal a ⟨n, τf⟩ :=
    (TrIProp.until_unfold fP G₂.internal a ⟨n, τf⟩).mpr
  iapply hU
  iapply sysStepIter Sys 0 h n σ tp g v Ω W τf γ iprop(True)
    iprop(G₂.internal ⟨n, τf⟩ ∨ (fP ⟨n, τf⟩ ∧ ∃ a' : Fuel, ⌜a' < a⌝ ∧
      TrIProp.strongUntil fP G₂.internal a' ⟨n + 1, τf⟩))
    hf $$ ST HS [] []
  · iintro %l -
    inext
    itrivial
  · inext
    iintro %l %σ' %tp' %g' %v' %Ω' %W' %⟨hbeh', hfs', hlb', hht', -⟩ #B - - HS'
    imodintro
    ileft
    iapply record_elim G₂ $$ TQ ST %⟨hf.1, hfs', hlb', hht'⟩ B HS'

/-- A registered until whose obligation is assigned at `n`, read off a run after its
registration, with the rank of the obligation's measure at `n` (Rocq `until_run`). The bundle
decides which content holds at `n`; the obligation at `n + 1`, read with a credit of the step,
decides the continuation. -/
@[lantana_alias until_run]
theorem untilRun (Sys : SysT Expr State GF) (N : Namespace) (k : Oid) (γP γQ : GName)
    (j r : Nat) (P : IProp GF) (G₁ G₂ : TrSpec Expr State GF) :
    sysStep Sys ⊢ regIdx j r (.until N k γP γQ) -∗ savedTrI γP G₁.internal -∗
      savedTrI γQ G₂.internal -∗ Obl.inv N k P (untilDischarged k G₂) -∗
      ∀ (h : List (HistEntry Expr State)) (n : Nat) (σ : State) (tp : ThreadPool Expr)
        (g : List MEvent) (v : Nat) (Ω : Obls) (W : Witnesses)
        (τf : Nat → TraceState Expr State) (γ : Nat → ThreadId → Nat) (fu : Fuel) (o : ThreadId),
        ⌜r < n ∧ IsBehavior (⟨n, τf⟩ : Trace Expr State) ∧ BehFscnt ⟨n, τf⟩ γ ∧
          owitInvLb (fairMeasure (γ n)) Ω W ∧ histTrace h τf ∧
          get? Ω k = some (.assigned fu o)⌝ -∗
        historyInterp h n σ tp ∗ modelInterp g v Ω W n tp.length ∗ Sys n σ tp -∗
        TrIProp.strongUntil G₁.internal G₂.internal
          (Ordinals.Ordinal.succ (fairMeasure (γ n) o fu)) ⟨n, τf⟩ := by
  iintro #ST #Hj #HγP #HγQ #OI
  iloeb as IH
  iintro %h %n %σ %tp %g %v %Ω %W %τf %γ %fu %o %⟨hrn, hbeh, hfs, hlb, hht, hk⟩ ⟨HI, MI, Sy⟩
  ihave #EA := modelInterp_eventObl hk $$ MI
  have hU : TrIProp.defer iprop(G₂.internal ⟨n, τf⟩ ∨ (G₁.internal ⟨n, τf⟩ ∧ ∃ a' : Fuel,
      ⌜a' < Ordinals.Ordinal.succ (fairMeasure (γ n) o fu)⌝ ∧
      TrIProp.strongUntil G₁.internal G₂.internal a' ⟨n + 1, τf⟩)) ⊢
      TrIProp.strongUntil G₁.internal G₂.internal
        (Ordinals.Ordinal.succ (fairMeasure (γ n) o fu)) ⟨n, τf⟩ :=
    (TrIProp.until_unfold G₁.internal G₂.internal _ ⟨n, τf⟩).mpr
  iapply hU
  iapply sysStepIter Sys 1 h n σ tp g v Ω W τf γ
    iprop((record G₁ n ∨ record G₂ n) ∨
      (∃ (n' i' : Nat) (Ω' : Obls), ⌜n' ≤ n⌝ ∗ eventObl i' (n', Ω') k .discharged ∗
        record G₂ n'))
    iprop(G₂.internal ⟨n, τf⟩ ∨ (G₁.internal ⟨n, τf⟩ ∧ ∃ a' : Fuel,
      ⌜a' < Ordinals.Ordinal.succ (fairMeasure (γ n) o fu)⌝ ∧
      TrIProp.strongUntil G₁.internal G₂.internal a' ⟨n + 1, τf⟩))
    ⟨hbeh, hfs, hlb, hht⟩ $$ ST [HI MI Sy] [] []
  · iframe HI MI Sy
  · iintro %l #B
    icases bundleUntilCert l n j r N k γP γQ G₁ G₂ (Nat.le_of_lt hrn) $$ B Hj HγP HγQ []
      with (#C | #C)
    · iintro %hr
      exfalso
      omega
    · inext
      ileft
      iexact C
    · inext
      iright
      iexact C
  inext
  iintro %l %σ' %tp' %g' %v' %Ω' %W' %⟨hbeh', hfs', hlb', hht', hdrop⟩ #B #C LC
    ⟨HI', MI', Sy'⟩
  icases C with ((#TrecP | #TrecQ) | ⟨%n', %i', %Ω'', %hn', #EF, #TQ'⟩)
  · -- `P` holds at `n`: the obligation at `n + 1` decides
    imod Obl.inv_acc ⊤ N k P _ CoPset.subseteq_top $$ OI with ⟨Var, Hclose⟩
    imod lc_fupd_elim_later $$ LC Var with Var
    icases (Obl.variant_unfold k P _).1 $$ Var with (⟨Oa', HP'⟩ | ⟨#Of, #R⟩)
    · icases Obl.assigned_modelInterp_lookup k _ g' v' Ω' W' (n + 1) tp'.length $$ [Oa' MI']
        with %hk'
      · iframe Oa' MI'
      obtain ⟨fu', o', hk'⟩ := hk'
      imod Hclose $$ [Oa' HP'] with -
      · inext
        iapply (Obl.variant_unfold k P _).2
        ileft
        iframe Oa' HP'
      imodintro
      iright
      isplit
      · iapply record_elim G₁ $$ TrecP ST %⟨hbeh, hfs', hlb', hht'⟩ B [HI' MI' Sy']
        iframe HI' MI' Sy'
      · iexists Ordinals.Ordinal.succ (fairMeasure (γ (n + 1)) o' fu')
        isplit
        · ipureintro
          exact Ordinals.Ordinal.succ_lt_succ_iff.mpr (hdrop k fu o fu' o' hk hk')
        · iapply IH $$ %(h ++ [(σ', tp')]) %(n + 1) %σ' %tp' %g' %v' %Ω' %W' %τf %γ %fu' %o'
            %⟨by omega, hbeh', hfs', hlb', hht', hk'⟩ [HI' MI' Sy']
          iframe HI' MI' Sy'
    · -- discharged during the step: at `n` (before the step) or at `n + 1` (after)
      iunfold untilDischarged at R
      icases R with ⟨%n', %i', %Ω'', #EF, #TQ'⟩
      icases modelInterp_eventObl_lookup g' v' Ω' W' (n + 1) tp'.length i' (n', Ω'') k
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
        iframe EF TQ'
      imodintro
      by_cases hnn : n' = n
      · subst hnn
        ileft
        iapply record_elim G₂ $$ TQ' ST %⟨hbeh, hfs', hlb', hht'⟩ B [HI' MI' Sy']
        iframe HI' MI' Sy'
      · have hn' : n' = n + 1 := by simp only at hn₁; omega
        subst hn'
        iright
        isplit
        · iapply record_elim G₁ $$ TrecP ST %⟨hbeh, hfs', hlb', hht'⟩ B [HI' MI' Sy']
          iframe HI' MI' Sy'
        · iexists 0
          isplit
          · ipureintro
            exact Ordinals.Ordinal.zero_lt_succ _
          · iapply untilRunDischarged Sys G₁.internal G₂ 0 (h ++ [(σ', tp')]) (n + 1) σ' tp' g' v'
              Ω' W' τf γ ⟨hbeh', hfs', hlb', hht'⟩ $$ ST TQ' [HI' MI' Sy']
            iframe HI' MI' Sy'
  · -- `Q` holds at `n`
    imodintro
    ileft
    iapply record_elim G₂ $$ TrecQ ST %⟨hbeh, hfs', hlb', hht'⟩ B [HI' MI' Sy']
    iframe HI' MI' Sy'
  · -- discharged before the check: the discharge was at `n`
    icases eventObl_assigned_discharged_le $$ [EA EF] with %hn₂
    · iframe EA EF
    have hnn : n' = n := by omega
    subst hnn
    imodintro
    ileft
    iapply record_elim G₂ $$ TQ' ST %⟨hbeh, hfs', hlb', hht'⟩ B [HI' MI' Sy']
    iframe HI' MI' Sy'

end Loops

end Lantana
