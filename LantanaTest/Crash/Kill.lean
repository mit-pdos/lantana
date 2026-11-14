/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LantanaTest.Crash.Step

/-! # A language whose threads crash: the shared invariant and the killer

The worker (thread `0`) owes a forest of obligations `S` with their children `kids`: one
obligation `k` under its thread and, below it, the others (a chain of any length, allocated in
`Adequacy.lean`), each a `finallyI` of `doneOrCrashed` ("the worker has finished, or it is
crashed") in the namespace `Nobl.@j` of its obligation `j`. The shared invariant `crashInv` holds
half of the ghost variable of the state and, by its value: while the worker is alive and
unfinished, its node and every finally with its children, or (after a revival) its empty node and
the discharges; while it is crashed, the discharges (the model holds the node); once it has
finished, nothing.

The killer's step from an alive, unfinished worker with its obligations crashes it, so it must
hand the worker's emptied node to the model. Before the step it opens the shared invariant (with a
later credit of its own) and the obligation invariants of all of `S` at once
(`finallyI_acc_assigned_set_ndot`; their contents are timeless), then goes to the empty mask.
Inside the physical round, at the new configuration (the state already `false`), it discharges
the whole forest with the crash disjunct (`finallyI_discharge_opened_forest_threads`), which
empties the node, and hands it in; the invariants are closed after the round. When it gives up,
the closing rebuilds every finally. The killer's other steps keep the statuses.
-/

@[expose] public noncomputable section

namespace LantanaTest.Crash

open Iris Iris.BI Iris.ProofMode Iris.Std
open Ordinals Ordinal Lantana
open Iris.ProgramLogic (toVal Language PrimStep EvContext EvContextOps)

/-! ## Namespaces -/

/-- The namespaces of the shared invariant and of the finallies: the finally on `j` is in
`Nobl.@j`. -/
def Ncr : Namespace := nroot.@"crash"
def Ninv : Namespace := Ncr.@"inv"
def Nobl : Namespace := Ncr.@"obl"

theorem Ninv_subseteq : (↑Ninv : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full

theorem Nobl_subseteq : (↑Nobl : CoPset) ⊆ ⊤ \ ↑Ninv := by
  intro p hp
  refine Iris.Std.LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun h' => ?_⟩
  exact ndot_ne_disjoint Ncr (by decide : "obl" ≠ "inv") p ⟨hp, h'⟩

/-! ## The forest of the worker -/

/-- The obligations `T`, with their children `kids`, hang below the children `c` of a parent:
`c ⊆ T`, `T` is closed under children, and each of `T` is in `c` or a child of one of `T`. -/
def HangsBelow (c T : Oids) (kids : Oid → Oids) : Prop :=
  c ⊆ T ∧ (∀ j, j ∈ T → kids j ⊆ T) ∧ ∀ x, x ∈ T → x ∈ c ∨ ∃ j, j ∈ T ∧ x ∈ kids j

/-- A new obligation `k` above the obligations `T` hanging below `c`, with the children `c`. -/
theorem HangsBelow.insert {k : Oid} {c T : Oids} {kids : Oid → Oids} (h : HangsBelow c T kids)
    (hk : k ∉ T) : HangsBelow {k} ({k} ∪ T) (fun j => if j = k then c else kids j) := by
  obtain ⟨hc, hcl, hcov⟩ := h
  have hin : ∀ {x}, x ∈ T → x ∈ ({k} ∪ T : Oids) := fun hx => mem_union.2 (.inr hx)
  refine ⟨fun x hx => mem_union.2 (.inl hx), fun j hj x hx => ?_, fun x hx => ?_⟩
  · by_cases hjk : j = k
    · simp only [hjk, ↓reduceIte] at hx
      exact hin (hc x hx)
    · simp only [hjk, ↓reduceIte] at hx
      rcases mem_union.1 hj with hj | hj
      · exact (hjk (mem_singleton.1 hj)).elim
      · exact hin (hcl j hj x hx)
  · rcases mem_union.1 hx with hx | hx
    · exact .inl hx
    · refine .inr ?_
      rcases hcov x hx with hxc | ⟨j, hj, hxj⟩
      · exact ⟨k, mem_union.2 (.inl (mem_singleton.2 rfl)), by simpa using hxc⟩
      · have hjk : j ≠ k := fun h => hk (h ▸ hj)
        exact ⟨j, hin hj, by simpa [hjk] using hxj⟩

/-- The worker's thread is the only root of a forest hanging below `{k}`. -/
theorem HangsBelow.roots {k : Oid} {S : Oids} {kids : Oid → Oids} (h : HangsBelow {k} S kids) :
    ∀ j, j ∈ ([0] : List ThreadId) → ({k} : Oids) ⊆ S :=
  fun _ _ => h.1

theorem HangsBelow.covered {k : Oid} {S : Oids} {kids : Oid → Oids} (h : HangsBelow {k} S kids) :
    ∀ x, x ∈ S → (∃ j, j ∈ ([0] : List ThreadId) ∧ x ∈ ({k} : Oids)) ∨
      ∃ j, j ∈ S ∧ x ∈ kids j :=
  fun x hx => (h.2.2 x hx).imp_left fun hxk => ⟨_, List.mem_singleton_self _, hxk⟩

/-! ## The shared invariant -/

section Inv
variable {GF : BundledGFunctors} [ModelGS GF] [CrashGS GF]

/-- The worker's obligations while it runs: its node holding `k`, and for each obligation of `S`
its finally and its children. -/
def workerObls (k : Oid) (S : Oids) (kids : Oid → Oids) : IProp GF :=
  iprop(thActive 0 ∗ thKids 0 {k} ∗
    [∗set] j ∈ S, finallyI (Nobl.@j) j 1 doneOrCrashed ∗ oblKids j (kids j))

/-- The protocol, by the state `b` and "the worker has finished" `f`. -/
def crashProto (k : Oid) (S : Oids) (kids : Oid → Oids) : Bool → Bool → IProp GF
  | _, true => iprop(True)
  | false, false => iprop([∗set] j ∈ S, Obl.discharged j)
  | true, false => iprop(workerObls k S kids ∨
      (thActive 0 ∗ thKids 0 ∅ ∗ [∗set] j ∈ S, Obl.discharged j))

/-- The shared invariant: half of the ghost variable of the state, and the protocol. -/
def crashInv (k : Oid) (S : Oids) (kids : Oid → Oids) : IProp GF :=
  iprop(∃ b f : Bool, stVar (Qp.half 1) b f ∗ crashProto k S kids b f)

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

/-! ## The killer -/

section Killer
variable {GF : BundledGFunctors} [ModelGS GF] [CrashGS GF]

omit [CrashGS GF] in
/-- Half of the assignment of `j` closes its invariant as it was. -/
theorem variant_half (j : Oid) (R : IProp GF) :
    Obl.assigned j (Qp.half 1) ⊢ ▷ Obl.variant j iprop(True) R := by
  iintro Oa
  inext
  iapply (Obl.variant_unfold j _ _).2
  ileft
  iframe Oa

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
theorem killer_spec (k : Oid) (S : Oids) (kids : Oid → Oids) (hF : HangsBelow {k} S kids) :
    inv Ninv (crashInv (GF := GF) k S kids) ⊢ £ₙ 1 -∗ thActive 1 -∗ thKids 1 ∅ -∗
      thCarriers 1 ∅ -∗ lWP Exp.kill @ 1; ⊤ {{ fun _ => Th.done 1 }} := by
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
    iapply Th.nodes_unchanged _ (hkeep false)
    imod Hcl with -
    imod Hclose $$ [Hv HC] with -
    · inext
      iunfold crashInv
      iexists false, false
      iframe Hv HC
    iapply ret_done ⊤ 1 $$ Ha1 Hk1
  · -- alive and unfinished: with its obligations, or revived without
    simp only [crashProto]
    icases HC with (HW | ⟨Ha0, Hk0, #HD⟩)
    · -- its obligations: the invariants of all of `S` are opened before the step
      iunfold workerObls at HW
      icases HW with ⟨Ha0, Hk0, HW⟩
      icases BigSepS.bigSepS_sep.1 $$ HW with ⟨HU, Hkk⟩
      imod finallyI_acc_assigned_set_ndot Nobl_subseteq $$ HU with ⟨Oa, Hcl⟩
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
        -- the step crashes the worker: discharge the forest, hand the node in
        imod ghost_var_update_halves (false, false) _ _ _ $$ Hs Hv with ⟨Hs, Hv⟩
        imodintro
        isplitl [Hs]
        · rw [hfin]
          iframe Hs
          ipureintro
          exact hS'
        iintro HG
        iapply ALC_intro
        imod finallyI_discharge_opened_forest_threads ∅ [0] (fun _ => {k}) kids hF.roots
          hF.2.1 hF.covered (fun _ _ => stVar_doneOrCrashed (Qp.half 1) false)
          $$ [Hk0] [Oa Hkk] Hv with ⟨Hv, Hk0, HD⟩
        · iapply BigSepL.bigSepL_singleton.2
          iexact Hk0
        · iapply BigSepS.bigSepS_sep.2
          iframe Oa Hkk
        icases BigSepL.bigSepL_singleton.1 $$ Hk0 with Hk0
        icases BigSepS.bigSepS_sep.1 $$ HD with ⟨#HD, HV⟩
        imodintro
        isplitl [Ha0 Hk0]
        · iapply Th.nodes_single _ fun j _ => hφ j
          iframe Ha0 Hk0
        iintro -
        imod Hcl₀ with -
        imod Hcl $$ [HV] with -
        · iapply BigSepS.bigSepS_mono_of_forall (fun _ => later_intro) $$ HV
        imod Hclose $$ [Hv] with -
        · inext
          iunfold crashInv
          iexists false, false
          iframe Hv
          simp only [crashProto]
          iexact HD
        iapply ret_done ⊤ 1 $$ Ha1 Hk1
      | giveUp =>
        -- the statuses do not change: the closing rebuilds every finally
        imodintro
        isplitl [Hs]
        · rw [hfin]
          iframe Hs
          ipureintro
          exact hS'
        iintro HG
        iapply ALC_intro
        imodintro
        iapply Th.nodes_unchanged _ (hkeep true)
        icases BigSepS.bigSepS_sep.1 $$ [Oa] with ⟨Oa, Ob⟩
        · iapply BigSepS.bigSepS_mono_of_forall (fun j => (Obl.assigned_halves j).1) $$ Oa
        imod Hcl₀ with -
        imod Hcl $$ [Oa] with HU
        · iapply BigSepS.bigSepS_mono_of_forall (fun j => variant_half j _) $$ Oa
        ihave HU := BigSepS.bigSepS_wand $$ Ob HU
        imod Hclose $$ [Hv Ha0 Hk0 HU Hkk] with -
        · inext
          iunfold crashInv
          iexists true, false
          iframe Hv
          simp only [crashProto]
          ileft
          iunfold workerObls
          iframe Ha0 Hk0
          iapply BigSepS.bigSepS_sep.2
          iframe HU Hkk
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
        · iapply Th.nodes_single _ fun j _ => hφ j
          iframe Ha0 Hk0
        iintro -
        imod Hcl with -
        imod Hclose $$ [Hv] with -
        · inext
          iunfold crashInv
          iexists false, false
          iframe Hv
          simp only [crashProto]
          iexact HD
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
        iapply Th.nodes_unchanged _ (hkeep true)
        imod Hcl with -
        imod Hclose $$ [Hv Ha0 Hk0] with -
        · inext
          iunfold crashInv
          iexists true, false
          iframe Hv
          simp only [crashProto]
          iright
          iframe Ha0 Hk0 HD
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
    iapply Th.nodes_unchanged _ (Cfg.crashed_eq_of_iff fun j =>
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
