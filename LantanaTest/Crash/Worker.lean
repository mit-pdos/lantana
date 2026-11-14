/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LantanaTest.Crash.Kill

/-! # A language whose threads crash: the worker

The worker (thread `0`) keeps privately its bill (`{k}`, or `∅` once it has stepped crashed) and
the fuel of `k`. Each step it sees the state: alive, it pays its bill and works; alive at `work 0`
it opens the shared invariant (with a later credit of its own) and, in the physical round, at the
new configuration where it has finished, discharges `k'` and `k` with the first disjunct of their
formulas and ends its thread; crashed, it takes its silent step for free (the crashed branch of
`lwp_step`) and gets its bill back empty. The loop is a Löb induction, each step giving the later
credit that strips the later of the induction hypothesis.
-/

@[expose] public noncomputable section

namespace LantanaTest.Crash

open Iris Iris.BI Iris.ProofMode Iris.Std
open Ordinals Ordinal Lantana
open Iris.ProgramLogic (toVal Language PrimStep EvContext EvContextOps)

/-! ## The worker's entry of the pool -/

theorem fin_of_work {tp : ThreadPool Exp} {n : Nat} (hi : tp[0]? = some (.work n)) :
    fin tp = false := by
  unfold fin
  rw [hi]
  simp

theorem fin_set_zero {tp : ThreadPool Exp} {e₁ : Exp} (hi : tp[0]? = some e₁) (e : Exp) :
    fin (tp.set 0 e) = decide (e = .ret) := by
  unfold fin
  rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hi).1]
  simp

theorem fin_set_work {tp : ThreadPool Exp} {e₁ : Exp} (hi : tp[0]? = some e₁) (n : Nat) :
    fin (tp.set 0 (.work n)) = false := by
  rw [fin_set_zero hi]
  simp

theorem fin_set_ret {tp : ThreadPool Exp} {e₁ : Exp} (hi : tp[0]? = some e₁) :
    fin (tp.set 0 .ret) = true := by
  rw [fin_set_zero hi]
  simp

theorem set_self {tp : ThreadPool Exp} {i : ThreadId} {e : Exp} (hi : tp[i]? = some e) :
    tp.set i e = tp := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hi
  rw [← heq, List.set_getElem_self hlt]

/-! ## The worker -/

section Worker
variable {GF : BundledGFunctors} [ModelGS GF] [CrashGS GF]

omit [CrashGS GF] in
/-- The worker pays its bill `B` (`∅` or `{k}`) out of the fuel of `k`. -/
theorem worker_pay (k : Oid) (B : Oids) (hB : B = ∅ ∨ B = {k}) (tp : ThreadPool Exp) (σ : St)
    (m : Nat) :
    oblFuels {k} ((m + 1 : Nat) : Measure) ⊢@{IProp GF}
      oblFuels {k} (m : Measure) ∗ (oblFuels B 1 ∗ ⌜B = B⌝ ∨ ⌜Cfg.crashed (tp, σ) 0 ∧ B = ∅⌝) := by
  iintro HF
  icases oblFuels_succ {k} m $$ HF with ⟨HF, HF1⟩
  iframe HF
  ileft
  rcases hB with rfl | rfl
  · isplitl
    · iunfold oblFuels
      iapply BigSepS.bigSepS_empty.mpr
      iempintro
    · ipureintro
      rfl
  · iframe HF1
    ipureintro
    rfl

/-- The worker: from `work m`, with its bill `B` and the fuel of `k` for `m + 1` steps, it works
until it finishes, or loops for ever while crashed. -/
theorem worker_spec (k k' : Oid) :
    inv Ninv (crashInv (GF := GF) k k') ⊢ ∀ (m : Nat) (B : Oids), £ₙ 1 -∗ thCarriers 0 B -∗
      ⌜B = ∅ ∨ B = {k}⌝ -∗ oblFuels {k} ((m + 1 : Nat) : Measure) -∗
      lWP (Exp.work m) @ 0; ⊤ {{ fun _ => Th.done 0 }} := by
  iintro #HI
  iloeb as IH
  iintro %m %B Hc HG %hB HF
  iapply lwp_step (rfl : toVal (Exp.work m) = none)
  simp only [stateInterp_eq]
  iintro %σ₁ %tp %hi ⟨%hS, Hs⟩
  have hS' : ∀ e, ((∃ n, e = .work n) ∨ e = .ret) → Shape (tp.set 0 e) :=
    fun _ h => hS.set_zero h
  have hkeep : ∀ e₂ σ₂, Step (.work m) σ₁ e₂ σ₂ →
      Cfg.crashed (tp.set 0 e₂, σ₂) = Cfg.crashed (tp, σ₁) :=
    fun _ _ h => crashed_set_eq_worker hi h
  rw [fin_of_work hi]
  cases σ₁
  · -- crashed: a free step, and the bill comes back empty
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hcl
    isplitr
    · ipureintro
      exact ⟨[], .work m, false, [], .idle m, rfl⟩
    iexists B, ∅
    iframe HG
    isplitr
    · iright
      ipureintro
      exact ⟨crashed_cfg_iff.mpr ⟨⟨m, hi⟩, rfl⟩, rfl⟩
    iintro %e₂ %σ₂ %hst
    cases hst with
    | idle =>
      imodintro
      isplitl [Hs]
      · rw [set_self hi, fin_of_work hi]
        iframe Hs
        ipureintro
        exact hS
      iintro HG
      iapply (ALC_credits 1).mpr
      iapply ALC_intro
      iintro Hc₁
      imodintro
      iapply Th.nodes_unchanged _ (hkeep _ _ (.idle m))
      imod Hcl with -
      imodintro
      imodintro
      iapply lwp_credit_later $$ Hc₁
      inext
      iapply IH $$ %m %∅ Hc HG %(.inl rfl) HF
  · cases m with
    | succ m =>
      -- alive: it works, paying its bill
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hcl
      isplitr
      · ipureintro
        exact ⟨[], .work m, true, [], .work m, rfl⟩
      icases worker_pay k B hB tp true (m + 1) $$ HF with ⟨HF, HP⟩
      iexists B, B
      iframe HG HP
      iintro %e₂ %σ₂ %hst
      cases hst with
      | work =>
        imodintro
        isplitl [Hs]
        · rw [fin_set_work hi]
          iframe Hs
          ipureintro
          exact hS' _ (.inl ⟨m, rfl⟩)
        iintro HG
        iapply (ALC_credits 1).mpr
        iapply ALC_intro
        iintro Hc₁
        imodintro
        iapply Th.nodes_unchanged _ (hkeep _ _ (.work m))
        imod Hcl with -
        imodintro
        imodintro
        iapply lwp_credit_later $$ Hc₁
        inext
        iapply IH $$ %m %B Hc HG %hB HF
    | zero =>
      -- alive at `work 0`: it finishes, discharging its obligations and ending its thread
      imod inv_acc Ninv_subseteq $$ HI with ⟨HC, Hclose⟩
      imod Lantana.lc_fupd_elim_later $$ Hc HC with HC
      iunfold crashInv at HC
      icases HC with ⟨%b, %f, Hv, HC⟩
      icombine Hs Hv gives %⟨-, hbf⟩
      obtain ⟨rfl, rfl⟩ : true = b ∧ false = f := Prod.mk.inj hbf
      simp only [crashProto]
      icases HC with (HW | ⟨Ha0, Hk0, #Dk, #Dk'⟩)
      · -- with its obligations: the invariants of `k'` and `k` are opened before the step
        iunfold workerObls at HW
        icases HW with ⟨Ha0, Hk0, HU, Hkk, HU', Hkk'⟩
        imod finallyI_acc_assigned Nk'_subseteq $$ HU' with ⟨>Oa', Hcl'⟩
        imod finallyI_acc_assigned Nk_subseteq $$ HU with ⟨>Oa, Hcl⟩
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hcl₀
        isplitr
        · ipureintro
          exact ⟨[], .ret, true, [], .finish, rfl⟩
        icases worker_pay k B hB tp true 0 $$ HF with ⟨-, HP⟩
        iexists B, B
        iframe HG HP
        iintro %e₂ %σ₂ %hst
        cases hst with
        | finish =>
          imod ghost_var_update_halves (true, true) _ _ _ $$ Hs Hv with ⟨Hs, Hv⟩
          imodintro
          isplitl [Hs]
          · rw [fin_set_ret hi]
            iframe Hs
            ipureintro
            exact hS' _ (.inr rfl)
          iintro HG
          iapply ALC_intro
          imod finallyI_discharge_opened ∅ (.obl k) {k'} (mem_singleton k')
            (stVar_doneOrCrashed_fin (Qp.half 1) true) $$ Oa' Hkk Hkk' Hv with ⟨Hv, Hkk, -, V'⟩
          rw [erase_singleton]
          imod finallyI_discharge_opened ∅ (.thread 0) {k} (mem_singleton k)
            (stVar_doneOrCrashed_fin (Qp.half 1) true) $$ Oa Hk0 Hkk Hv with ⟨Hv, Hk0, -, V⟩
          rw [erase_singleton]
          imod Th.terminate ∅ 0 $$ Ha0 Hk0 with #Hd
          imodintro
          iapply Th.nodes_unchanged _ (hkeep _ _ .finish)
          imod Hcl₀ with -
          imod Hcl $$ [V] with -
          · inext
            iexact V
          imod Hcl' $$ [V'] with -
          · inext
            iexact V'
          imod Hclose $$ [Hv] with -
          · inext
            iunfold crashInv
            iexists true, true
            iframe Hv
            simp only [crashProto]
            itrivial
          imodintro
          iapply (lwp_value_mupd_of_toVal rfl).mpr
          imodintro
          iexact Hd
      · -- revived: its empty node
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hcl
        isplitr
        · ipureintro
          exact ⟨[], .ret, true, [], .finish, rfl⟩
        icases worker_pay k B hB tp true 0 $$ HF with ⟨-, HP⟩
        iexists B, B
        iframe HG HP
        iintro %e₂ %σ₂ %hst
        cases hst with
        | finish =>
          imod ghost_var_update_halves (true, true) _ _ _ $$ Hs Hv with ⟨Hs, Hv⟩
          imodintro
          isplitl [Hs]
          · rw [fin_set_ret hi]
            iframe Hs
            ipureintro
            exact hS' _ (.inr rfl)
          iintro HG
          iapply ALC_intro
          imod Th.terminate ∅ 0 $$ Ha0 Hk0 with #Hd
          imodintro
          iapply Th.nodes_unchanged _ (hkeep _ _ .finish)
          imod Hcl with -
          imod Hclose $$ [Hv] with -
          · inext
            iunfold crashInv
            iexists true, true
            iframe Hv
            simp only [crashProto]
            itrivial
          imodintro
          iapply (lwp_value_mupd_of_toVal rfl).mpr
          imodintro
          iexact Hd

end Worker

end LantanaTest.Crash
