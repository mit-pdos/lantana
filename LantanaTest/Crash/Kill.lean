/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LantanaTest.Crash.Step

/-! # A language whose threads crash: the shared invariant and the killer

The worker (thread `0`) owes two nested obligations, `k` under its thread and `k'` under `k`,
each a `finallyI` of `doneOrCrashed` ("the worker has finished, or it is crashed"). The shared
invariant `crashInv` holds half of the ghost variable of the state and, by its value: while the
worker is alive and unfinished, its node and both finallies with their children, or (after a
revival) its empty node and the discharges; while it is crashed, the discharges (the model holds
the node); once it has finished, nothing.

The killer's step from an alive, unfinished worker with its obligations crashes it, so it must
hand the worker's emptied node to the model. Before the step it opens the shared invariant (with a
later credit of its own) and the obligation invariants of `k'` and `k` (whose contents, `True`
and halves of the assignments, are timeless), then goes to the empty mask. Inside the physical
round, at the new configuration (the state already `false`), it discharges `k'` and then `k` with
the crash disjunct (`finallyI_discharge_opened`), which empties the node, and hands it in; the
invariants are closed after the round. The killer's other steps keep the statuses.
-/

@[expose] public noncomputable section

namespace LantanaTest.Crash

open Iris Iris.BI Iris.ProofMode Iris.Std
open Ordinals Ordinal Lantana
open Iris.ProgramLogic (toVal Language PrimStep EvContext EvContextOps)

/-! ## Namespaces -/

/-- The namespaces of the shared invariant and of the two finallies. -/
def Ncr : Namespace := nroot.@"crash"
def Ninv : Namespace := Ncr.@"inv"
def Nk : Namespace := Ncr.@"k"
def Nk' : Namespace := Ncr.@"k'"

theorem Ninv_subseteq : (↑Ninv : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full

theorem Nk'_subseteq : (↑Nk' : CoPset) ⊆ ⊤ \ ↑Ninv := by
  intro p hp
  refine Iris.Std.LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun h' => ?_⟩
  exact ndot_ne_disjoint Ncr (by decide : "k'" ≠ "inv") p ⟨hp, h'⟩

theorem Nk_subseteq : (↑Nk : CoPset) ⊆ (⊤ \ ↑Ninv) \ ↑Nk' := by
  intro p hp
  refine Iris.Std.LawfulSet.mem_diff.mpr ⟨?_, fun h' => ?_⟩
  · refine Iris.Std.LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun h' => ?_⟩
    exact ndot_ne_disjoint Ncr (by decide : "k" ≠ "inv") p ⟨hp, h'⟩
  · exact ndot_ne_disjoint Ncr (by decide : "k" ≠ "k'") p ⟨hp, h'⟩

/-! ## The shared invariant -/

section Inv
variable {GF : BundledGFunctors} [ModelGS GF] [CrashGS GF]

/-- The worker's obligations while it runs: its node holding `k`, the finally on `k` (which
holds `k'`) and the finally on `k'`. -/
def workerObls (k k' : Oid) : IProp GF :=
  iprop(thActive 0 ∗ thKids 0 {k} ∗ finallyI Nk k 1 doneOrCrashed ∗ oblKids k {k'} ∗
    finallyI Nk' k' 1 doneOrCrashed ∗ oblKids k' ∅)

/-- The protocol, by the state `b` and "the worker has finished" `f`. -/
def crashProto (k k' : Oid) : Bool → Bool → IProp GF
  | _, true => iprop(True)
  | false, false => iprop(Obl.discharged k ∗ Obl.discharged k')
  | true, false => iprop(workerObls k k' ∨
      (thActive 0 ∗ thKids 0 ∅ ∗ Obl.discharged k ∗ Obl.discharged k'))

/-- The shared invariant: half of the ghost variable of the state, and the protocol. -/
def crashInv (k k' : Oid) : IProp GF :=
  iprop(∃ b f : Bool, stVar (Qp.half 1) b f ∗ crashProto k k' b f)

end Inv

section
variable {GF : BundledGFunctors} [CrashGS GF]

/-- A crashed state says `doneOrCrashed`. -/
theorem stVar_doneOrCrashed (q : Qp) (f : Bool) : stVar q false f ⊢@{IProp GF} doneOrCrashed := by
  unfold doneOrCrashed
  iintro H
  iexists q, false, f
  iframe H
  ipureintro
  exact .inl rfl

/-- A finished worker says `doneOrCrashed`. -/
theorem stVar_doneOrCrashed_fin (q : Qp) (b : Bool) :
    stVar q b true ⊢@{IProp GF} doneOrCrashed := by
  unfold doneOrCrashed
  iintro H
  iexists q, b, true
  iframe H
  ipureintro
  exact .inr rfl

end

/-! ## Discharging inside the physical round -/

section Discharge
variable {GF : BundledGFunctors} [ModelGS GF] [CrashGS GF]

/-- Discharging the obligation `k` of a finally of `Q` whose invariant has been opened, at the
current position: `k` (a childless child of `p`) is discharged with a resource `X` that implies
`Q` (and is given back), and the content of the invariant becomes the discharged one, with the
record of `Q` at the discharge. This is the discharge of `untilI_discharge_done` without the
closing of the invariant, so that it runs at the empty mask. -/
theorem finallyI_discharge_opened (k : Oid) {Q X : IProp GF} (hX : X ⊢ Q) (p : Parent)
    (K : Oids) (hk : k ∈ K) :
    Obl.assigned k 1 ⊢ Par.kids p K -∗ oblKids k ∅ -∗ X -∗
      |={∅}=>m X ∗ Par.kids p (K.erase k) ∗ Obl.discharged k ∗
        Obl.variant k iprop(True) (untilDischarged k (TrSpec.canon Q)) := by
  iintro Oa Kp Kk HX
  imod Obl.discharge_leaf ∅ p K k hk $$ Kp Kk Oa with ⟨Kp, #D⟩
  ihave #HG := guar_canon (Expr := Exp) (State := St) Q
  imod mupd_read (E := ∅) (P := iprop(X ∗ untilDischarged k (TrSpec.canon Q))) $$ [HX]
    with ⟨HX, #R⟩
  · iintro %h %n %σ %tp %g %i %Ω %W %tc %Y HI TI MI
    ihave #TQ : record (TrSpec.canon (Expr := Exp) (State := St) Q) n $$ [HI MI HX]
    · iapply guar_elim Q _ h n σ tp g i Ω W tc Y $$ HG
      iframe HI MI
      iapply hX $$ HX
    icases Obl.discharged_modelInterp_lookup k g i Ω W n tc Y $$ [D MI] with %hkd
    · iframe D MI
    ihave #EF := Model.modelInterp_eventObl hkd $$ MI
    iframe MI
    imodintro
    iframe HI TI HX
    iunfold untilDischarged
    iexists n, i, Ω
    iframe EF
    iexact TQ
  imodintro
  iframe HX Kp D
  iapply (Obl.variant_unfold k _ _).2
  iright
  iframe D R

end Discharge

/-! ## The killer -/

section Killer
variable {GF : BundledGFunctors} [ModelGS GF] [CrashGS GF]

theorem erase_singleton (k : Oid) : ({k} : Oids).erase k = ∅ :=
  Std.ExtTreeSet.ext_mem fun _ => by simp

theorem mem_singleton (k : Oid) : k ∈ ({k} : Oids) := by simp

omit [CrashGS GF] in
/-- A thread that pays nothing: its bill is empty. -/
theorem bill_empty (i : ThreadId) (tp : ThreadPool Exp) (σ : St) :
    ⊢@{IProp GF} oblFuels ∅ 1 ∗ ⌜(∅ : Oids) = ∅⌝ ∨ ⌜Cfg.crashed (tp, σ) i ∧ (∅ : Oids) = ∅⌝ := by
  ileft
  isplitl
  · iunfold oblFuels
    iapply BigSepS.bigSepS_empty.mpr
    iempintro
  · ipureintro
    rfl

/-- A thread at the value ends its thread. -/
theorem ret_done (E : CoPset) (i : ThreadId) :
    thActive i ⊢@{IProp GF} thKids i ∅ -∗ |={E}=>m lWP Exp.ret @ i; E {{ fun _ => Th.done i }} := by
  iintro Ha Hk
  imodintro
  iapply (lwp_value_mupd_of_toVal rfl).mpr
  iapply Th.terminate E i $$ Ha Hk

/-- The killer: from any state of the protocol it kills or gives up; killing an alive, unfinished
worker discharges the worker's obligations inside the physical round and hands its node in. -/
theorem killer_spec (k k' : Oid) :
    inv Ninv (crashInv (GF := GF) k k') ⊢ £ₙ 1 -∗ thActive 1 -∗ thKids 1 ∅ -∗ thCarriers 1 ∅ -∗
      lWP Exp.kill @ 1; ⊤ {{ fun _ => Th.done 1 }} := by
  iintro #HI Hc Ha1 Hk1 HG
  iapply lwp_step (rfl : toVal Exp.kill = none)
  simp only [stateInterp_eq]
  iintro %σ₁ %tp %hi ⟨%hS, Hs⟩
  imod inv_acc Ninv_subseteq $$ HI with ⟨HC, Hclose⟩
  imod Lantana.lc_fupd_elim_later $$ Hc HC with HC
  iunfold crashInv at HC
  icases HC with ⟨%b, %f, Hv, HC⟩
  icombine Hs Hv gives %⟨-, hbf⟩
  obtain ⟨hb, hf⟩ : σ₁ = b ∧ fin tp = f := Prod.mk.inj hbf
  subst hb
  have hred : Stuckness.maybeReducible .NotStuck Exp.kill σ₁ :=
    ⟨[], .ret, σ₁, [], .giveUp σ₁, rfl⟩
  have hfin : fin (tp.set 1 .ret) = fin tp := fin_set_ne (by decide) _
  have hS' : Shape (tp.set 1 .ret) := hS.set_ne (by decide) fun _ h => Exp.noConfusion h
  have hkeep : ∀ σ, Cfg.crashed (tp.set 1 .ret, σ) = Cfg.crashed (tp, σ) := fun _ =>
    crashed_set_eq hi (fun _ h => Exp.noConfusion h) (fun _ h => Exp.noConfusion h)
  have hφ : ∀ j, ¬Cfg.crashed (tp, true) j ∧ Cfg.crashed (tp.set 1 .ret, false) j → j = 0 :=
    fun j ⟨_, h⟩ => by
      obtain ⟨⟨n, hn⟩, -⟩ := crashed_cfg_iff.mp h
      exact hS'.1 j n hn
  rw [hf] at hfin
  rw [hf]
  cases f <;> cases σ₁
  · -- crashed: the model holds the node, and the state stays `false`
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
    obtain ⟨rfl, rfl⟩ : e₂ = .ret ∧ σ₂ = false := by
      cases hst <;> exact ⟨rfl, rfl⟩
    imodintro
    isplitl [Hs]
    · rw [hfin]
      iframe Hs
      ipureintro
      exact hS'
    iintro HG
    iapply ALC_intro
    imodintro
    iapply nodes_keep _ (hkeep false)
    imod Hcl with -
    imod Hclose $$ [Hv HC] with -
    · inext
      iunfold crashInv
      iexists false, false
      iframe Hv HC
    iapply ret_done ⊤ 1 $$ Ha1 Hk1
  · -- alive and unfinished: with its obligations, or revived without
    simp only [crashProto]
    icases HC with (HW | ⟨Ha0, Hk0, #Dk, #Dk'⟩)
    · -- its obligations: the invariants of `k'` and `k` are opened before the step
      iunfold workerObls at HW
      icases HW with ⟨Ha0, Hk0, HU, Hkk, HU', Hkk'⟩
      simp only [finallyI, untilI_unfold]
      icases HU with ⟨Oa, #U⟩
      icases HU' with ⟨Oa', #U'⟩
      ihave #OI := untilIPers_inv Nk k _ _ $$ U
      ihave #OI' := untilIPers_inv Nk' k' _ _ $$ U'
      imod Obl.inv_acc_assigned (⊤ \ ↑Ninv) Nk' k' _ _ Nk'_subseteq $$ OI' with H'
      icases H' $$ %(Qp.half 1) Oa' with ⟨H', Hcl'⟩
      imod H' with ⟨Oa', Ob', -⟩
      imod Obl.inv_acc_assigned ((⊤ \ ↑Ninv) \ ↑Nk') Nk k _ _ Nk_subseteq $$ OI with H
      icases H $$ %(Qp.half 1) Oa with ⟨H, Hcl⟩
      imod H with ⟨Oa, Ob, -⟩
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hcl₀
      isplitr
      · ipureintro
        exact hred
      iexists ∅, ∅
      iframe HG
      isplitr
      · iapply bill_empty
      iintro %e₂ %σ₂ %hst
      cases hst with
      | kill =>
        -- the step crashes the worker: discharge `k'` and `k`, hand the node in
        imod ghost_var_update_halves (false, false) _ _ _ $$ Hs Hv with ⟨Hs, Hv⟩
        imodintro
        isplitl [Hs]
        · rw [hfin]
          iframe Hs
          ipureintro
          exact hS'
        iintro HG
        iapply ALC_intro
        ihave Oa := (Obl.assigned_halves k).mpr $$ [Oa Ob]
        · iframe Oa Ob
        ihave Oa' := (Obl.assigned_halves k').mpr $$ [Oa' Ob']
        · iframe Oa' Ob'
        imod finallyI_discharge_opened k' (stVar_doneOrCrashed (Qp.half 1) false) (.obl k) {k'}
          (mem_singleton k') $$ Oa' Hkk Hkk' Hv with ⟨Hv, Hkk, #Dk', V'⟩
        rw [erase_singleton]
        imod finallyI_discharge_opened k (stVar_doneOrCrashed (Qp.half 1) false) (.thread 0) {k}
          (mem_singleton k) $$ Oa Hk0 Hkk Hv with ⟨Hv, Hk0, #Dk, V⟩
        rw [erase_singleton]
        imodintro
        isplitl [Ha0 Hk0]
        · iapply nodes_zero _ hφ
          iframe Ha0 Hk0
        iintro -
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
          iexists false, false
          iframe Hv
          simp only [crashProto]
          iframe Dk Dk'
        iapply ret_done ⊤ 1 $$ Ha1 Hk1
      | giveUp =>
        -- the statuses do not change: everything is closed as it was
        imodintro
        isplitl [Hs]
        · rw [hfin]
          iframe Hs
          ipureintro
          exact hS'
        iintro HG
        iapply ALC_intro
        imodintro
        iapply nodes_keep _ (hkeep true)
        imod Hcl₀ with -
        imod Hcl $$ [Oa] with -
        · inext
          iapply (Obl.variant_unfold k _ _).2
          ileft
          iframe Oa
        imod Hcl' $$ [Oa'] with -
        · inext
          iapply (Obl.variant_unfold k' _ _).2
          ileft
          iframe Oa'
        imod Hclose $$ [Hv Ha0 Hk0 Ob Hkk Ob' Hkk'] with -
        · inext
          iunfold crashInv
          iexists true, false
          iframe Hv
          simp only [crashProto]
          ileft
          iunfold workerObls
          simp only [finallyI, untilI_unfold]
          iframe Ha0 Hk0 Ob Hkk Ob' Hkk' U U'
        iapply ret_done ⊤ 1 $$ Ha1 Hk1
    · -- revived: its empty node, no obligations
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
      | kill =>
        imod ghost_var_update_halves (false, false) _ _ _ $$ Hs Hv with ⟨Hs, Hv⟩
        imodintro
        isplitl [Hs]
        · rw [hfin]
          iframe Hs
          ipureintro
          exact hS'
        iintro HG
        iapply ALC_intro
        imodintro
        isplitl [Ha0 Hk0]
        · iapply nodes_zero _ hφ
          iframe Ha0 Hk0
        iintro -
        imod Hcl with -
        imod Hclose $$ [Hv] with -
        · inext
          iunfold crashInv
          iexists false, false
          iframe Hv
          simp only [crashProto]
          iframe Dk Dk'
        iapply ret_done ⊤ 1 $$ Ha1 Hk1
      | giveUp =>
        imodintro
        isplitl [Hs]
        · rw [hfin]
          iframe Hs
          ipureintro
          exact hS'
        iintro HG
        iapply ALC_intro
        imodintro
        iapply nodes_keep _ (hkeep true)
        imod Hcl with -
        imod Hclose $$ [Hv Ha0 Hk0] with -
        · inext
          iunfold crashInv
          iexists true, false
          iframe Hv
          simp only [crashProto]
          iright
          iframe Ha0 Hk0 Dk Dk'
        iapply ret_done ⊤ 1 $$ Ha1 Hk1
  all_goals
    -- finished: no thread is crashed, before or after
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
    have he₂ : e₂ = .ret := by cases hst <;> rfl
    subst he₂
    imod ghost_var_update_halves (σ₂, true) _ _ _ $$ Hs Hv with ⟨Hs, Hv⟩
    imodintro
    isplitl [Hs]
    · rw [hfin]
      iframe Hs
      ipureintro
      exact hS'
    iintro HG
    iapply ALC_intro
    imodintro
    iapply nodes_keep _ (Cfg.crashed_eq_of_iff fun j =>
      ⟨fun h => (not_crashed_fin hS' hfin _ j h).elim,
        fun h => (not_crashed_fin hS hf _ j h).elim⟩)
    imod Hcl with -
    imod Hclose $$ [Hv] with -
    · inext
      iunfold crashInv
      iexists σ₂, true
      iframe Hv
      cases σ₂ <;> simp only [crashProto] <;> itrivial
    iapply ret_done ⊤ 1 $$ Ha1 Hk1

end Killer

end LantanaTest.Crash
