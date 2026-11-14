/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LantanaTest.Crash.Kill

/-! # A language whose threads crash: the reviver

The reviver sets the state to `true`. Reviving a crashed worker recovers thread `0`, so the
physical round hands the reviver the worker's node `thActive 0 ∗ thKids 0 ∅`, which it puts back
in the shared invariant: the worker goes on with no obligation. Its other steps keep the
statuses.
-/

@[expose] public noncomputable section

namespace LantanaTest.Crash

open Iris Iris.BI Iris.ProofMode Iris.Std
open Ordinals Ordinal Lantana
open Iris.ProgramLogic (toVal Language PrimStep EvContext EvContextOps)

section Reviver
variable {GF : BundledGFunctors} [ModelGS GF] [CrashGS GF]

/-- The reviver: from any state of the protocol it revives; reviving a crashed worker receives
its node from the model and puts it back in the shared invariant. -/
theorem reviver_spec (k k' : Oid) :
    inv Ninv (crashInv (GF := GF) k k') ⊢ £ₙ 1 -∗ thActive 2 -∗ thKids 2 ∅ -∗ thCarriers 2 ∅ -∗
      lWP Exp.revive @ 2; ⊤ {{ fun _ => Th.done 2 }} := by
  iintro #HI Hc Ha2 Hk2 HG
  iapply lwp_step (rfl : toVal Exp.revive = none)
  simp only [stateInterp_eq]
  iintro %σ₁ %tp %hi ⟨%hS, Hs⟩
  imod inv_acc Ninv_subseteq $$ HI with ⟨HC, Hclose⟩
  imod Lantana.lc_fupd_elim_later $$ Hc HC with HC
  iunfold crashInv at HC
  icases HC with ⟨%b, %f, Hv, HC⟩
  icombine Hs Hv gives %⟨-, hbf⟩
  obtain ⟨hb, hf⟩ : σ₁ = b ∧ fin tp = f := Prod.mk.inj hbf
  subst hb
  have hred : Stuckness.maybeReducible .NotStuck Exp.revive σ₁ :=
    ⟨[], .ret, true, [], .revive σ₁, rfl⟩
  have hfin : fin (tp.set 2 .ret) = fin tp := fin_set_ne (by decide) _
  have hS' : Shape (tp.set 2 .ret) := hS.set_ne (by decide) fun _ h => Exp.noConfusion h
  have hkeep : ∀ σ, Cfg.crashed (tp.set 2 .ret, σ) = Cfg.crashed (tp, σ) := fun _ =>
    crashed_set_eq hi (fun _ h => Exp.noConfusion h) (fun _ h => Exp.noConfusion h)
  have hlen : 0 < tp.length := by
    rcases hS.2 with ⟨n, h⟩ | h <;> exact (List.getElem?_eq_some_iff.mp h).1
  rw [hf] at hfin
  rw [hf]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hcl
  isplitr
  · ipureintro
    exact hred
  iexists ∅, ∅
  iframe HG
  isplitr
  · iapply bill_empty
  iintro %e₂ %σ₂ %hst
  cases hst with
  | revive =>
    imod ghost_var_update_halves (true, f) _ _ _ $$ Hs Hv with ⟨Hs, Hv⟩
    imodintro
    isplitl [Hs]
    · rw [hfin]
      iframe Hs
      ipureintro
      exact hS'
    iintro HG
    iapply ALC_intro
    imodintro
    cases f <;> cases σ₁
    · -- crashed: the step recovers the worker, whose node comes out of the model
      obtain ⟨n, hn⟩ := hS.work_of_fin hf
      isplitl []
      · iapply nodes_none _ fun j h => not_crashed_true _ j h.2
      iintro Hout
      icases nodes_zero_out hlen
        ⟨crashed_cfg_iff.mpr ⟨⟨n, hn⟩, rfl⟩, not_crashed_true _ 0⟩ $$ Hout with ⟨Ha0, Hk0⟩
      imod Hcl with -
      imod Hclose $$ [Hv Ha0 Hk0 HC] with -
      · inext
        iunfold crashInv
        iexists true, false
        iframe Hv
        simp only [crashProto]
        iright
        iframe Ha0 Hk0 HC
      iapply ret_done ⊤ 2 $$ Ha2 Hk2
    · -- alive and unfinished: nothing changes
      iapply nodes_keep _ (hkeep true)
      imod Hcl with -
      imod Hclose $$ [Hv HC] with -
      · inext
        iunfold crashInv
        iexists true, false
        iframe Hv HC
      iapply ret_done ⊤ 2 $$ Ha2 Hk2
    all_goals
      -- finished: no thread is crashed, before or after
      iapply nodes_keep _ (Cfg.crashed_eq_of_iff fun j =>
        ⟨fun h => (not_crashed_fin hS' hfin _ j h).elim,
          fun h => (not_crashed_fin hS hf _ j h).elim⟩)
      imod Hcl with -
      imod Hclose $$ [Hv] with -
      · inext
        iunfold crashInv
        iexists true, true
        iframe Hv
        simp only [crashProto]
        itrivial
      iapply ret_done ⊤ 2 $$ Ha2 Hk2

end Reviver

end LantanaTest.Crash
