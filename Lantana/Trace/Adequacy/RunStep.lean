/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Trace.Guarantee

/-! # Adequacy: one step of the run

`run_step`: one step of a fair behavior, simulated by the `lWP`s of the threads of the pool
(`threadsRun`), threading the history and temporal interpretation and the model, in the deferred
shape `|={⊤,∅}=> alc (|={∅,⊤}=> …)`; it also gives the facts of the step that safety needs
(`runStepPost`). See `docs/adequacy.md`, §5.3. Rocq: `lantana/trace/adequacy_temporal.v`.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode
open Iris.ProgramLogic (toVal Language PrimStep EvContext EvContextOps)
open Iris.ProgramLogic.PrimStep (primStep)
open Lantana.Model

variable {Expr State Obs Val : Type} [Λ : Language Expr State Obs Val]

/-! ## Pure facts about the run -/

/-- No thread of the pool of `ρ` is stuck: each is a value or can step. -/
@[lantana_alias adequacy_safety.not_stuck]
def Cfg.NotStuck (ρ : Cfg Expr State) : Prop :=
  ∀ (i : ThreadId) (e : Expr), ρ.1[i]? = some e → PrimStep.NotStuck (e, ρ.2)

/-- The inversion of a thread step. -/
theorem ThreadStep.inv {i : ThreadId} {ρ₁ ρ₂ : Cfg Expr State} (h : ThreadStep i ρ₁ ρ₂) :
    ∃ e₁ obs e₂ σ₂ efs, ρ₁.1[i]? = some e₁ ∧ primStep (e₁, ρ₁.2) obs (e₂, σ₂, efs) ∧
      ρ₂ = (ρ₁.1.set i e₂ ++ efs, σ₂) := by
  cases h with
  | step he hs => exact ⟨_, _, _, _, _, he, hs, rfl⟩

/-- The ghost history extended by the configuration of the next position is a prefix of the
run. -/
theorem histTrace_snoc {h : List (HistEntry Expr State)} {τf : Nat → Cfg Expr State}
    {n : Nat} {σ' : State} {tp' : ThreadPool Expr} (hh : HistTrace h τf) (hlen : h.length = n + 1)
    (hcfg : τf (n + 1) = (tp', σ')) : HistTrace (h ++ [(σ', tp')]) τf := by
  intro n' σ'' tp'' hn'
  rcases Nat.lt_or_ge n' h.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hn'
    exact hh n' σ'' tp'' hn'
  · rw [List.getElem?_append_right hge] at hn'
    rcases Nat.lt_or_ge (n' - h.length) 1 with h1 | h1
    · have hn'' : n' = n + 1 := by omega
      rw [show n' - h.length = 0 by omega] at hn'
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hn'
      obtain ⟨rfl, rfl⟩ := hn'
      subst hn''
      exact hcfg
    · rw [List.getElem?_eq_none (by simp; omega)] at hn'
      cases hn'

/-- The fair-scheduler measures of a counter satisfy the requirements of the model's witness
lower bounds. -/
theorem owitInvLbMonoFair_fairMeasure (c : Nat → Nat) : OWitInvLbMonoFair (fairMeasure c) :=
  ⟨fun _ _ _ _ h => fairMeasure_lt_mono h, fairMeasure_le_ub c⟩

section Run

variable {Ectx : Type} [EvContext Expr Ectx]
variable [Crash Expr State Obs Val] {GF : BundledGFunctors} [ModelGS GF]
  [L : LantanaGS Expr State Obs Val GF] [TemporalInterp Expr State GF]

/-! ## The running threads -/

/-- Thread `j` running `e` with postcondition `lwp.liftTerm j Ψ`: a value has its postcondition, a
running thread its `lWP`. -/
def threadRun (j : ThreadId) (e : Expr) (Ψ : ThreadId → Val → IProp GF) : IProp GF :=
  match toVal e with
  | some v => lwp.liftTerm j Ψ v
  | none => lWP e @ j; ⊤ {{ lwp.liftTerm j Ψ }}

/-- The running threads of the pool `tp` with postconditions `Ψ`. -/
@[lantana_alias threads_run]
def threadsRun (tp : ThreadPool Expr) (Ψ : ThreadId → Val → IProp GF) : IProp GF :=
  iprop([∗list] j ↦ e ∈ tp, threadRun j e Ψ)

/-- The postconditions after a step from a pool of length `len`: the old threads keep theirs,
the forked threads get `forkPost`. -/
def postFork (Ψ fp : ThreadId → Val → IProp GF) (len : Nat) : ThreadId → Val → IProp GF :=
  fun j => if j < len then Ψ j else fp j

omit [ModelGS GF] in
theorem postFork_lt {Ψ fp : ThreadId → Val → IProp GF} {len j : Nat} (h : j < len) :
    postFork Ψ fp len j = Ψ j := by
  simp [postFork, h]

omit [ModelGS GF] in
theorem postFork_ge {Ψ fp : ThreadId → Val → IProp GF} {len j : Nat} (h : len ≤ j) :
    postFork Ψ fp len j = fp j := by
  simp [postFork, Nat.not_lt.mpr h]

theorem threadRun_of_toVal {j : ThreadId} {e : Expr} {v : Val} {Ψ : ThreadId → Val → IProp GF}
    (he : toVal e = some v) : threadRun j e Ψ = lwp.liftTerm j Ψ v := by
  simp [threadRun, he]

theorem threadRun_of_toVal_none {j : ThreadId} {e : Expr} {Ψ : ThreadId → Val → IProp GF}
    (he : toVal e = none) : threadRun j e Ψ = lWP e @ j; ⊤ {{ lwp.liftTerm j Ψ }} := by
  simp [threadRun, he]

/-- `threadRun j` only reads the postcondition of `j`. -/
theorem threadRun_congr {j : ThreadId} {e : Expr} {Ψ Ψ' : ThreadId → Val → IProp GF}
    (h : Ψ' j = Ψ j) : threadRun j e Ψ' = threadRun j e Ψ := by
  have hl : lwp.liftTerm j Ψ' = lwp.liftTerm j Ψ := by
    funext v
    simp only [lwp.liftTerm, h]
  simp only [threadRun, hl]

theorem threadsRun_congr {tp : ThreadPool Expr} {Ψ Ψ' : ThreadId → Val → IProp GF}
    (h : ∀ j, j < tp.length → Ψ' j = Ψ j) : threadsRun tp Ψ' = threadsRun tp Ψ := by
  unfold threadsRun
  exact BigSepL.bigSepL_eq fun hk => threadRun_congr (h _ (List.getElem?_eq_some_iff.mp hk).1)

/-- The `Th.done` token of a finished thread. -/
theorem threadRun_doneToken (j : ThreadId) (e : Expr) (Ψ : ThreadId → Val → IProp GF) :
    threadRun j e Ψ ⊢ doneToken j e := by
  rcases he : toVal e with _ | v
  · simp only [doneToken, he]
    exact true_intro
  · simp only [threadRun, doneToken, he, lwp.liftTerm]
    exact sep_elim_left

theorem threadsRun_doneTokens (tp : ThreadPool Expr) (Ψ : ThreadId → Val → IProp GF) :
    threadsRun tp Ψ ⊢ doneTokens tp := by
  unfold threadsRun doneTokens
  exact BigSepL.bigSepL_mono fun _ => threadRun_doneToken _ _ _

/-- The pure content of the postcondition of a finished thread `j`. -/
theorem threadsRun_ifTermVal {tp : ThreadPool Expr} {Ψ : ThreadId → Val → IProp GF}
    {j : ThreadId} {Φ : ThreadId → Val → Prop} (hΨ : ∀ v, Ψ j v ⊢ ⌜Φ j v⌝) :
    threadsRun tp Ψ ⊢ ⌜∀ e v, tp[j]? = some e → toVal e = some v → Φ j v⌝ := by
  rcases hj : tp[j]? with _ | e
  · exact pure_intro fun _ _ h => by cases h
  rcases he : toVal e with _ | v
  · exact pure_intro fun _ _ h h' => by cases h; rw [he] at h'; cases h'
  unfold threadsRun
  refine (BigSepL.bigSepL_lookup hj).trans ?_
  rw [threadRun_of_toVal he]
  unfold lwp.liftTerm
  refine sep_elim_right.trans ((hΨ v).trans (pure_mono fun hv e' v' h h' => ?_))
  cases h
  rw [he] at h'
  cases h'
  exact hv

/-- An `lWP` with postcondition `lwp.liftTerm j Ψ` runs as thread `j`, after the model update of
its postcondition if it is a value. -/
theorem lwp_threadRun (j : ThreadId) (e : Expr) (Ψ : ThreadId → Val → IProp GF) :
    lWP e @ j; ⊤ {{ lwp.liftTerm j Ψ }} ⊢ |={⊤}=>m threadRun j e Ψ := by
  rcases he : toVal e with _ | v
  · rw [threadRun_of_toVal_none he]
    exact mupd_intro
  · rw [threadRun_of_toVal he]
    exact (lwp_value_mupd_of_toVal he).mp

/-- The initial threads run. -/
theorem lwps_threadsRun (tp : ThreadPool Expr) (Ψ : ThreadId → Val → IProp GF) :
    ([∗list] j ↦ e ∈ tp, lWP e @ j; ⊤ {{ lwp.liftTerm j Ψ }}) ⊢ |={⊤}=>m threadsRun tp Ψ := by
  unfold threadsRun
  exact (BigSepL.bigSepL_mono fun _ => lwp_threadRun _ _ _).trans (bigSepL_mupd _ ⊤ _)

/-- The forked threads `len + k` run with the postconditions `postFork Ψ len`. -/
theorem forks_threadsRun (len : Nat) (efs : List Expr) (Ψ : ThreadId → Val → IProp GF) :
    ([∗list] k ↦ ef ∈ efs, lWP ef @ (len + k); ⊤ {{ lwp.liftTerm (len + k) L.forkPost }}) ⊢
      |={⊤}=>m [∗list] k ↦ ef ∈ efs, threadRun (k + len) ef (postFork Ψ L.forkPost len) := by
  refine (BigSepL.bigSepL_mono fun {k ef} _ => ?_).trans (bigSepL_mupd _ ⊤ _)
  rw [threadRun_congr (postFork_ge (Nat.le_add_left len k)), Nat.add_comm k len]
  exact lwp_threadRun _ _ _

/-- The threads after a step of `i` to `e₂` forking `efs`. -/
theorem threadsRun_step (tp : ThreadPool Expr) (i : ThreadId) (e₂ : Expr) (efs : List Expr)
    (Ψ : ThreadId → Val → IProp GF) :
    ([∗list] k ↦ e ∈ tp.set i e₂, threadRun k e Ψ) ∗
        ([∗list] k ↦ ef ∈ efs, threadRun (k + tp.length) ef (postFork Ψ L.forkPost tp.length)) ⊢
      threadsRun (tp.set i e₂ ++ efs) (postFork Ψ L.forkPost tp.length) := by
  have h₁ := threadsRun_congr (tp := tp.set i e₂) (Ψ := Ψ) (Ψ' := postFork Ψ L.forkPost tp.length)
    fun j hj => postFork_lt (by simpa using hj)
  unfold threadsRun at h₁ ⊢
  rw [← h₁]
  refine Entails.trans ?_ BigSepL.bigSepL_append.mpr
  rw [List.length_set]

/-! ## The history and temporal interpretation -/

theorem historyTInterp_wf (h : List (HistEntry Expr State)) (n : Nat) (σ : State)
    (tp : ThreadPool Expr) :
    historyTInterp (GF := GF) h n σ tp ⊢ ⌜h.length = n + 1 ∧ h[n]? = some (σ, tp)⌝ := by
  unfold historyTInterp historyInterp
  iintro ⟨⟨%⟨hlen, hlast⟩, -, -⟩, -⟩
  ipureintro
  exact ⟨hlen, List.getLast?_eq_getElem?_of_length hlen hlast⟩

/-- A stutter appends the current configuration to the history. -/
theorem historyTInterp_stutter (h : List (HistEntry Expr State)) (n : Nat) (σ : State)
    (tp : ThreadPool Expr) :
    historyTInterp (GF := GF) h n σ tp ⊢ |==> historyTInterp (h ++ [(σ, tp)]) (n + 1) σ tp := by
  unfold historyTInterp
  iintro ⟨HH, HT⟩
  icases historyInterp_step h n σ σ tp tp $$ HH with ⟨Hs, Hk⟩
  imod Hk $$ Hs with HH
  imodintro
  iframe HH HT

/-! ## One step of the run -/

/-- What `run_step` gives after the step from `n`: the system at `n + 1`, `c` later credits, the
facts of the one-step property, and those that safety needs. -/
def runStepPost (c : Nat) (h : List (HistEntry Expr State)) (n : Nat)
    (τf : Nat → Cfg Expr State) (γ : Nat → ThreadId → Nat) (tp : ThreadPool Expr)
    (Ψ : ThreadId → Val → IProp GF) (Ω : Obligations) : IProp GF :=
  iprop(∃ (σ' : State) (tp' : ThreadPool Expr) (Ψ' : ThreadId → Val → IProp GF)
      (g' : List MEvent) (v' : Nat) (Ω' : Obligations) (W' : Witnesses),
    ⌜OWitInvLb (fairMeasure (γ (n + 1))) Ω' W' ∧ HistTrace (h ++ [(σ', tp')]) τf ∧
      ObligationsDrop (fairMeasure (γ n)) (fairMeasure (γ (n + 1))) Ω Ω' ∧
      (τf n).NotStuck ∧ tp.length ≤ tp'.length ∧ (∀ j, j < tp.length → Ψ' j = Ψ j)⌝ ∗
    £ₙ c ∗ historyTInterp (h ++ [(σ', tp')]) (n + 1) σ' tp' ∗
    modelInterp g' v' Ω' W' (n + 1) tp'.length (Cfg.Crashed (tp', σ')) ∗ threadsRun tp' Ψ')

/-- One step of `lWP` for a running thread: `lwp.step` at the empty context, mask `⊤`. -/
theorem threadRun_step {i : ThreadId} {e₁ : Expr} {Ψ : ThreadId → Val → IProp GF}
    (he : toVal e₁ = none) :
    threadRun i e₁ Ψ ⊢ ∀ (h : List (HistEntry Expr State)) (n : Nat) (σ : State)
      (tp : ThreadPool Expr), ⌜tp[i]? = some e₁⌝ →
      historyTInterp h n σ tp ={⊤,∅}=∗ |=[n]=>m
        ⌜PrimStep.Reducible (e₁, σ)⌝ ∗
        ∀ (obs : List Obs) (e₂ : Expr) (σ₂ : State) (efs : List Expr),
          ⌜primStep (e₁, σ) obs (e₂, σ₂, efs)⌝ -∗
          mprog n tp.length (Cfg.Crashed (tp, σ)) i
            (mphys n (n + 1) tp.length (tp.length + efs.length) (Cfg.Crashed (tp, σ))
              (Cfg.Crashed (tp.set i e₂ ++ efs, σ₂))
              (|=[n + 1]=>m |={∅,⊤}=>
                historyTInterp (h ++ [(σ₂, tp.set i e₂ ++ efs)]) (n + 1) σ₂
                  (tp.set i e₂ ++ efs) ∗
                lWP e₂ @ i; ⊤ {{ lwp.liftTerm i Ψ }} ∗
                [∗list] k ↦ ef ∈ efs,
                  lWP ef @ (tp.length + k); ⊤ {{ lwp.liftTerm (tp.length + k) L.forkPost }})) := by
  rw [threadRun_of_toVal_none he, lwp_unfold.to_eq]
  simp only [lwp.pre, he]
  unfold lwp.step
  refine (forall_elim (EvContextOps.empty : Ectx)).trans ?_
  simp only [EvContext.fill_empty, Stuckness.MaybeReducible]
  iintro H %h %n %σ %tp %hi
  iapply H $$ %h %n %σ %tp %(Language.Context.fillEmpty (Ectx := Ectx)) %hi

omit L [TemporalInterp Expr State GF] in
/-- `get_obligationsThreadActive`, keeping the model. -/
theorem obligationsThreadActive_keep {tp : ThreadPool Expr} {σ : State} {ρ : Cfg Expr State}
    (hρ : ρ = (tp, σ)) (g : List MEvent) (v : Nat) (Ω : Obligations) (W : Witnesses) (n : Nat) :
    doneTokens tp ∗ modelInterp (GF := GF) g v Ω W n tp.length (Cfg.Crashed (tp, σ)) ⊢
      modelInterp g v Ω W n tp.length (Cfg.Crashed (tp, σ)) ∗ ⌜ObligationsThreadActive Ω ρ⌝ := by
  subst hρ
  exact (persistent_entails_left (get_obligationsThreadActive (ρ := (tp, σ)) rfl g v Ω W n)).trans
    (sep_mono_left sep_elim_right)

/-- The threads after a step of `i` to `e₂` forking `efs`, after the model updates of the
finished threads' postconditions. -/
theorem threadsRun_after_step (tp : ThreadPool Expr) (i : ThreadId) (e₂ : Expr)
    (efs : List Expr) (Ψ : ThreadId → Val → IProp GF) :
    (∀ y, threadRun i y Ψ -∗ [∗list] k ↦ z ∈ tp.set i y, threadRun k z Ψ) ∗
        lWP e₂ @ i; ⊤ {{ lwp.liftTerm i Ψ }} ∗
        ([∗list] k ↦ ef ∈ efs,
          lWP ef @ (tp.length + k); ⊤ {{ lwp.liftTerm (tp.length + k) L.forkPost }}) ⊢
      |={⊤}=>m threadsRun (tp.set i e₂ ++ efs) (postFork Ψ L.forkPost tp.length) := by
  iintro ⟨HT, Hi, Hefs⟩
  imod lwp_threadRun i e₂ Ψ $$ Hi with Hi
  imod forks_threadsRun tp.length efs Ψ $$ Hefs with Hefs
  imodintro
  iapply threadsRun_step
  isplitl [HT Hi]
  · iapply HT $$ Hi
  · iexact Hefs

/-- A thread of the pool is stuck: impossible, its `lWP` proves reducibility. -/
theorem run_step_stuck {h : List (HistEntry Expr State)} {n : Nat} {σ : State}
    {tp : ThreadPool Expr} {Ψ : ThreadId → Val → IProp GF} {g : List MEvent} {v : Nat}
    {Ω : Obligations} {W : Witnesses} {i : ThreadId} {c' : Nat → Nat}
    (hLb : OWitInvLb (fairMeasure c') Ω W) (hst : ∃ e, tp[i]? = some e ∧ PrimStep.Stuck (e, σ))
    (P : IProp GF) :
    historyTInterp h n σ tp ∗ modelInterp g v Ω W n tp.length (Cfg.Crashed (tp, σ)) ∗
      threadsRun tp Ψ ⊢ |={⊤,∅}=> P := by
  obtain ⟨e, he, hv, hirr⟩ := hst
  iintro ⟨HH, HM, HT⟩
  unfold threadsRun
  ihave Hi := BigSepL.bigSepL_lookup he $$ HT
  ihave Hi := threadRun_step hv $$ Hi
  imod Hi $$ %h %n %σ %tp %he HH with Hi
  imod mupdBase_modelInterp_steps n (fairMeasure c') (owitInvLbMonoFair_fairMeasure c')
    _ $$ Hi %g %v %Ω %W %tp.length %(Cfg.Crashed (tp, σ)) %hLb HM with ⟨⟨%hred, -⟩, -⟩
  exact (Language.not_reducible_iff_irreducible.mpr hirr hred).elim

/-- The thread the schedule names is a value: the configuration stutters. -/
theorem run_step_done (c : Nat) {h : List (HistEntry Expr State)} {n : Nat} {σ : State}
    {tp : ThreadPool Expr} {Ψ : ThreadId → Val → IProp GF} {g : List MEvent} {v : Nat}
    {Ω : Obligations} {W : Witnesses} {τf : Nat → Cfg Expr State} {sched : Nat → ThreadId}
    {γ : Nat → ThreadId → Nat} {i : ThreadId} (hcnt : schedCounters sched γ ⟨0, τf⟩)
    (hLb : OWitInvLb (fairMeasure (γ n)) Ω W) (hh : HistTrace h τf) (hlen : h.length = n + 1)
    (hnow : τf n = (tp, σ)) (hi : sched n = i) (hns : (τf n).NotStuck)
    (hd : ThreadDone i (tp, σ) (τf (n + 1))) :
    historyTInterp h n σ tp ∗ modelInterp g v Ω W n tp.length (Cfg.Crashed (tp, σ)) ∗
      threadsRun tp Ψ ⊢
      |={⊤,∅}=> alc iprop(|={∅,⊤}=> runStepPost c h n τf γ tp Ψ Ω) := by
  obtain ⟨e, he, hv, hcfg⟩ := hd
  simp only at he hcfg
  have hna : (τf n).Inactive (sched n) := by
    rw [hnow, hi]
    exact .inr (.inl ⟨e, he, hv⟩)
  iintro ⟨HH, HM, HT⟩
  icases persistent_entails_left (threadsRun_doneTokens tp Ψ) $$ HT with ⟨HT, #HD⟩
  icases obligationsThreadActive_keep hnow g v Ω W n $$ [$HD $HM] with ⟨HM, %hact⟩
  have hLb' := owitInvLb_step_inactive_turn hcnt hna hact hLb
  have hdrop := obligationsDrop_inactive hcnt hna hact
  imod historyTInterp_stutter h n σ tp $$ HH with HH
  imod modelInterp_step_idx g v Ω W n tp.length _ $$ HM with HM
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  iapply (alc_credits (Ordinals.Ordinal.ofNat c)).mpr
  iapply alc_intro
  iintro Hc
  imod Hclose with -
  imodintro
  unfold runStepPost
  iexists σ, tp, Ψ, g ++ [(n + 1, Ω)], v + 1, Ω, W
  iframe Hc HH HM HT
  ipureintro
  exact ⟨hLb', histTrace_snoc hh hlen hcfg, hdrop, hns, Nat.le_refl _, fun _ _ => rfl⟩

/-- The thread the schedule names steps, crashed or not: its `lWP` takes the step. -/
theorem run_step_step (c : Nat) {h : List (HistEntry Expr State)} {n : Nat} {σ : State}
    {tp : ThreadPool Expr} {Ψ : ThreadId → Val → IProp GF} {g : List MEvent} {v : Nat}
    {Ω : Obligations} {W : Witnesses} {τf : Nat → Cfg Expr State} {sched : Nat → ThreadId}
    {γ : Nat → ThreadId → Nat} {i : ThreadId} (hcnt : schedCounters sched γ ⟨0, τf⟩)
    (hLb : OWitInvLb (fairMeasure (γ n)) Ω W) (hh : HistTrace h τf) (hlen : h.length = n + 1)
    (hnow : τf n = (tp, σ)) (hi : sched n = i) (hns : (τf n).NotStuck)
    (hstep : ThreadStep i (tp, σ) (τf (n + 1))) :
    historyTInterp h n σ tp ∗ modelInterp g v Ω W n tp.length (Cfg.Crashed (tp, σ)) ∗
      threadsRun tp Ψ ⊢
      |={⊤,∅}=> alc iprop(|={∅,⊤}=> runStepPost c h n τf γ tp Ψ Ω) := by
  obtain ⟨e₁, obs, e₂, σ₂, efs, he₁, hprim, hcfg⟩ := hstep.inv
  simp only at he₁ hprim
  have hv₁ : toVal e₁ = none := Language.val_stuck hprim
  have hγn := owitInvLbMonoFair_fairMeasure (γ n)
  have hγn1 := owitInvLbMonoFair_fairMeasure (γ (n + 1))
  iintro ⟨HH, HM, HT⟩
  icases persistent_entails_left (threadsRun_doneTokens tp Ψ) $$ HT with ⟨HT, #HD⟩
  unfold threadsRun
  icases BigSepL.bigSepL_insert_acc he₁ $$ HT with ⟨Hi, HT⟩
  ihave Hi := threadRun_step hv₁ $$ Hi
  imod Hi $$ %h %n %σ %tp %he₁ HH with Hi
  imod mupdBase_modelInterp_steps n (fairMeasure (γ n)) hγn _ $$
    Hi %g %v %Ω %W %tp.length %(Cfg.Crashed (tp, σ)) %hLb HM
    with ⟨⟨%_, Hi⟩, %g₀, %v₀, %Ω₀, %W₀, %⟨hle₀, hLb₀⟩, HM⟩
  icases Model.modelInterp_owitInv' _ _ _ _ _ _ _ $$ HM with ⟨HM, %hI₀⟩
  icases obligationsThreadActive_keep hnow _ _ Ω₀ W₀ n $$ [$HD $HM] with ⟨HM, %hact₀⟩
  ispecialize Hi $$ %obs %e₂ %σ₂ %efs %hprim
  imod mprog_modelInterp n tp.length _ i _ $$ Hi %(g ++ g₀) %(v + v₀) %Ω₀ %W₀ HM
    with ⟨%Ω₂, %hprog, Hk⟩
  obtain ⟨W₂, hW₂, hI₂, hLb₂⟩ := mprog_exists_step hi hact₀ hI₀ hLb₀ hcnt hprog
  imod Hk $$ %W₂ %(⟨hW₂, hI₂⟩) with ⟨HM, Hi⟩
  icases obligationsThreadActive_keep hnow _ _ Ω₂ W₂ n $$ [$HD $HM] with ⟨HM, %hact₂⟩
  imod mphys_modelInterp_run n (n + 1) tp.length (tp.length + efs.length) _ _
    (fairMeasure (γ (n + 1))) hγn1 _ $$ Hi %_ %_ %Ω₂ %W₂ %hLb₂ HM with Hi
  imodintro
  iapply (alc_credits (Ordinals.Ordinal.ofNat c)).mpr
  iapply alc_wand $$ [HT] Hi
  iintro Hi Hc
  imod Hi with ⟨Hi, %g₃, %v₃, %Ω₃, %W₃, %⟨hle₃, hLb₃⟩, HM⟩
  imod mupdBase_modelInterp_steps (n + 1) (fairMeasure (γ (n + 1))) hγn1 _ $$
    Hi %_ %_ %Ω₃ %W₃ %(tp.length + efs.length) %_ %hLb₃ HM
    with ⟨Hi, %g₄, %v₄, %Ω₄, %W₄, %⟨hle₄, hLb₄⟩, HM⟩
  imod Hi with ⟨HH, Hi, Hefs⟩
  ihave Hth := threadsRun_after_step tp i e₂ efs Ψ $$ [HT Hi Hefs]
  · iframe HT Hi Hefs
  imod mupd_modelInterp_steps (fairMeasure (γ (n + 1))) hγn1 ⊤ ⊤
    (h ++ [(σ₂, tp.set i e₂ ++ efs)]) (n + 1) σ₂ (tp.set i e₂ ++ efs) _ _ Ω₄ W₄ _ _ _ hLb₄
    $$ Hth HH HM with ⟨HT, HH, %g₅, %v₅, %Ω₅, %W₅, %⟨hle₅, hLb₅⟩, HM⟩
  imodintro
  unfold runStepPost
  iexists σ₂, tp.set i e₂ ++ efs, postFork Ψ L.forkPost tp.length, _, _, Ω₅, W₅
  rw [show (tp.set i e₂ ++ efs).length = tp.length + efs.length by simp]
  iframe Hc HH HM HT
  ipureintro
  exact ⟨hLb₅, histTrace_snoc hh hlen hcfg,
    obligationsDrop_step hi hcnt hle₀ hprog
      (Obligations.le_trans hle₃ (Obligations.le_trans hle₄ hle₅)) hact₂, hns,
    by omega, fun _ hj => postFork_lt hj⟩

/-- **One step of the run**: from the system at `n`, the system at `n + 1` with the facts about
the step (`runStepPost`), in the deferred shape. -/
@[lantana_alias run_step]
theorem run_step (c : Nat) {h : List (HistEntry Expr State)} {n : Nat} {σ : State}
    {tp : ThreadPool Expr} {Ψ : ThreadId → Val → IProp GF} {g : List MEvent} {v : Nat}
    {Ω : Obligations} {W : Witnesses} {τf : Nat → Cfg Expr State} {sched : Nat → ThreadId}
    {γ : Nat → ThreadId → Nat} (hsch : schedule sched ⟨0, τf⟩)
    (hcnt : schedCounters sched γ ⟨0, τf⟩)
    (hLb : OWitInvLb (fairMeasure (γ n)) Ω W) (hh : HistTrace h τf) :
    historyTInterp h n σ tp ∗ modelInterp g v Ω W n tp.length (Cfg.Crashed (tp, σ)) ∗
      threadsRun tp Ψ ⊢
      |={⊤,∅}=> alc iprop(|={∅,⊤}=> runStepPost c h n τf γ tp Ψ Ω) := by
  iintro ⟨HH, HM, HT⟩
  icases persistent_entails_left (historyTInterp_wf h n σ tp) $$ HH with ⟨HH, %⟨hlen, hlast⟩⟩
  have hnow := hh n σ tp hlast
  -- no thread of the pool is stuck
  by_cases hns : (τf n).NotStuck
  case neg =>
    rw [hnow] at hns
    simp only [Cfg.NotStuck, Classical.not_forall] at hns
    obtain ⟨j, e, he, hst⟩ := hns
    iapply run_step_stuck hLb ⟨e, he, Language.not_not_suck.mp hst⟩
    iframe HH HM HT
  have hts := (schedule_iff.mp hsch) n (Nat.zero_le n)
  simp only [ThreadSystem.step_def, TraceStep, hnow] at hts
  rcases hts with hs | hd | hst
  · iapply run_step_step c hcnt hLb hh hlen hnow rfl hns hs
    iframe HH HM HT
  · iapply run_step_done c hcnt hLb hh hlen hnow rfl hns hd
    iframe HH HM HT
  · obtain ⟨e, he, hst, -⟩ := hst
    iapply run_step_stuck hLb ⟨e, he, hst⟩
    iframe HH HM HT

end Run

end Lantana
