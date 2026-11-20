/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LantanaTest.Crash.Step

/-! # A language whose threads crash: the shared invariant and the killer

The worker's forest of obligations (`HangsBelow`), the shared invariant `crashInv`, and
`killer_spec`: the killer's step that crashes the worker discharges the whole forest inside the
physical round and hands the worker's node in. See `docs/adequacy.md`, §7.
-/

@[expose] public noncomputable section

namespace LantanaTest.Crash

open Iris Iris.BI Iris.ProofMode Iris.Std
open Ordinals Ordinal Lantana
open Iris.ProgramLogic (toVal Language PrimStep EvContext EvContextOps)

/-! ## Namespaces -/

/-- The namespaces of the shared invariant and of the finallies: the finally on `j` is in
`oblN.@j`. -/
def crashN : Namespace := nroot.@"crash"
def invN : Namespace := crashN.@"inv"
def oblN : Namespace := crashN.@"obl"

theorem invN_subset : (↑invN : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full

theorem oblN_subset : (↑oblN : CoPset) ⊆ ⊤ \ ↑invN := by
  intro p hp
  refine Iris.Std.LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun h' => ?_⟩
  exact ndot_ne_disjoint crashN (by decide : "obl" ≠ "inv") p ⟨hp, h'⟩

/-! ## The forest of the worker -/

/-- The obligations `T`, with their children `kids`, hang below the children `c` of a parent. -/
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
def workerObligations (k : Oid) (S : Oids) (kids : Oid → Oids) : IProp GF :=
  iprop(thActive 0 ∗ thKids 0 {k} ∗
    [∗set] j ∈ S, finallyI (oblN.@j) j 1 doneOrCrashed ∗ oblKids j (kids j))

/-- The protocol, by the state `b` and "the worker has finished" `f`. -/
def crashProto (k : Oid) (S : Oids) (kids : Oid → Oids) : Bool → Bool → IProp GF
  | _, true => iprop(True)
  | false, false => iprop([∗set] j ∈ S, Obl.discharged j)
  | true, false => iprop(workerObligations k S kids ∨
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
    ⊢@{IProp GF} Obl.fuels ∅ 1 ∗ ⌜(∅ : Oids) = ∅⌝ ∨ ⌜Cfg.Crashed (tp, σ) i ∧ (∅ : Oids) = ∅⌝ := by
  ileft
  isplitl
  · iunfold Obl.fuels
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

/-- The killer kills or gives up, from any state of the protocol. -/
theorem killer_spec (k : Oid) (S : Oids) (kids : Oid → Oids) (hF : HangsBelow {k} S kids) :
    inv invN (crashInv (GF := GF) k S kids) ⊢ £ₙ 1 -∗ thActive 1 -∗ thKids 1 ∅ -∗
      thCarriers 1 ∅ -∗ lWP Exp.kill @ 1; ⊤ {{ fun _ => Th.done 1 }} := by
  iintro #HI Hc Ha1 Hk1 HG
  iapply lwp_step (rfl : toVal Exp.kill = none)
  simp only [stateInterp_eq]
  iintro %σ₁ %tp %hi ⟨%hS, Hs⟩
  imod inv_acc invN_subset $$ HI with ⟨HC, Hclose⟩
  imod Lantana.lc_fupd_elim_later $$ Hc HC with HC
  iunfold crashInv at HC
  icases HC with ⟨%b, %f, Hv, HC⟩
  icombine Hs Hv gives %⟨-, hbf⟩
  obtain ⟨hb, hf⟩ : σ₁ = b ∧ fin tp = f := Prod.mk.inj hbf
  subst hb
  have hred : Stuckness.MaybeReducible .NotStuck (Exp.kill, σ₁) :=
    ⟨[], .ret, σ₁, [], .giveUp σ₁, rfl⟩
  have hfin : fin (tp.set 1 .ret) = fin tp := fin_set_ne (by decide) _
  have hS' : Shape (tp.set 1 .ret) := hS.set_ne (by decide) fun _ h => Exp.noConfusion h
  have hkeep : ∀ σ, Cfg.Crashed (tp.set 1 .ret, σ) = Cfg.Crashed (tp, σ) := fun _ =>
    crashed_set_eq hi (fun _ h => Exp.noConfusion h) (fun _ h => Exp.noConfusion h)
  have hφ : ∀ j, ¬Cfg.Crashed (tp, true) j ∧ Cfg.Crashed (tp.set 1 .ret, false) j → j = 0 :=
    fun j ⟨_, h⟩ => by
      obtain ⟨⟨n, hn⟩, -⟩ := crashed_cfg_iff.mp h
      exact hS'.1 j n hn
  rw [hf] at hfin
  rw [hf]
  cases f <;> cases σ₁
  · -- crashed
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
    iapply alc_intro
    imodintro
    iapply Th.nodes_unchanged _ (hkeep false)
    imod Hcl with -
    imod Hclose $$ [Hv HC] with -
    · inext
      iunfold crashInv
      iexists false, false
      iframe Hv HC
    iapply ret_done ⊤ 1 $$ Ha1 Hk1
  · -- alive and unfinished
    simp only [crashProto]
    icases HC with (HW | ⟨Ha0, Hk0, #HD⟩)
    · -- with its obligations
      iunfold workerObligations at HW
      icases HW with ⟨Ha0, Hk0, HW⟩
      icases BigSepS.bigSepS_sep.1 $$ HW with ⟨HU, Hkk⟩
      imod finallyI_acc_assigned_set_ndot oblN_subset $$ HU with ⟨Oa, Hcl⟩
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
        -- the step crashes the worker
        imod ghost_var_update_halves (false, false) _ _ _ $$ Hs Hv with ⟨Hs, Hv⟩
        imodintro
        isplitl [Hs]
        · rw [hfin]
          iframe Hs
          ipureintro
          exact hS'
        iintro HG
        iapply alc_intro
        imod finallyI_discharge_opened_forest_threads (Q := fun _ => doneOrCrashed) ∅ [0]
          (fun _ => {k}) kids hF.roots hF.2.1 hF.covered $$ [Hk0] [Oa Hkk] Hv with ⟨Hv, Hk0, HD⟩
        · iapply BigSepL.bigSepL_singleton.2
          iexact Hk0
        · iapply BigSepS.bigSepS_sep.2
          iframe Oa
          iapply BigSepS.bigSepS_sep.2
          iframe Hkk
          iapply Oids.bigSepS_wand_intro fun _ _ => stVar_doneOrCrashed (Qp.half 1) false
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
        -- the statuses do not change
        imodintro
        isplitl [Hs]
        · rw [hfin]
          iframe Hs
          ipureintro
          exact hS'
        iintro HG
        iapply alc_intro
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
          iunfold workerObligations
          iframe Ha0 Hk0
          iapply BigSepS.bigSepS_sep.2
          iframe HU Hkk
        iapply ret_done ⊤ 1 $$ Ha1 Hk1
    · -- revived, without obligations
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
        iapply alc_intro
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
        iapply alc_intro
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
    -- finished
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
    iapply alc_intro
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
