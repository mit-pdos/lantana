/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Examples.Flag
public import Lantana.Examples.TaskQueue
public import Lantana.Examples.World

/-! # A client of the task queue: a reentrant task

Rocq `examples/task_queue_client.v` (§7.3 of the paper): the main thread creates a task queue
(whose worker thread is forked) and a flag, picks a number `n`, and runs the task
`decrReentrant ((q, x), n)`, which puts itself back into the queue `n` times (decrementing
`n`) and then sets the flag; the main thread waits on the flag and returns its value `1`.

## Layers and measures

The task queue is at layer `ℓq = 2` (`isTask` in `putTask_spec` needs a task layer `1 < ℓq`),
the flag's obligation `k` at `ℓf = ℓq.succ.succ` (Rocq `ℓq ⊕ 2`, the layer `putTask_spec`
asks of the queued obligations) and the main thread's commitments at `ℓf.succ` (Rocq
`ℓq ⊕ 3`), above the flag for the `wait`. The reentrancy is paid by the flag's obligation
itself: it is allocated with fuel `ℵ` before `n` is chosen, lowered to `n` once it is known,
and each re-enqueue pays one unit (the remaining fuel decreases with `n`).

`decrReentrant_spec` is proved by Löb induction on the whole specification: the induction
hypothesis is the task's own specification (`taskAt`), stored in the queue. Rocq strips its
later where the task is run; here the task's resource `P` carries one later credit for it
(`P` is the task's own resource, hidden in `isTask`). The measure is
`100 + (μ_set + μ_putTask)`, and `main_spec`'s is `100 + μ_init + μ_flagInit + μ_decr +
μ_wait`.

## Adequacy

In the closed world `ExGF` (with the cameras of the ticket lock and of the queue in slots
`50`–`55`, instances `TicketLockG ExGF` and `QueueG ExGF` below): `taskQueueClient_adequacy`
(the main thread returns `1`, a flag gets created that is `0` until it is `1` and then `1`,
and a task queue gets created whose lock makes release progress), through
`lwp_adequacy_temporal`; `taskQueueClient_safety_adequacy` through `lwp_adequacy_safety`;
and `taskQueueClient_liveness_safety`.

Everything here is proved; the end-to-end corollaries depend only on the standard axioms
(checked in `LantanaTest.ExamplesQueue`).
-/

@[expose] public noncomputable section

namespace Lantana.Examples.TaskQueueClient

open Iris Iris.BI Iris.Std Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.Flag (flagTk isFlag isFlagTr flagTrSpec v1)
open Lantana.Examples.TicketLock (TicketLockG releaseProgress)
open Lantana.Examples.Queue (QueueG QueueName)
open Lantana.Examples.TaskQueue (isTaskQueue taskQueueTrSpec)
open Lantana.Examples.Handoff (isTask taskAt)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The program -/

/-- `rec f a := let q := fst (fst a); let x := snd (fst a); let n := snd a;
if n ≤ 0 then Flag.set x else TaskQueue.putTask q f ((q, x), n - 1)`. -/
@[lantana_alias task_queue_client.decr_reentrant]
def decrReentrant : Val :=
  hl_val(rec f a :=
    let q := fst(fst(a));
    let x := snd(fst(a));
    let n := snd(a);
    if n ≤ #0 then v(&Flag.set) x else v(&TaskQueue.putTask) q f ((q, x), n - #1))

/-- `λ _, let q := TaskQueue.init (); let x := Flag.init (); let n := chooseNat ();
decrReentrant ((q, x), n); let r := Flag.wait x; r`. -/
@[lantana_alias task_queue_client.main]
def main : Val :=
  hl_val(λ _,
    let q := v(&TaskQueue.init) #();
    let x := v(&Flag.init) #();
    let n := chooseNat();
    v(&decrReentrant) ((q, x), n);
    let r := v(&Flag.wait) x;
    r)

/-- The argument `((q, x), n)` of the task. -/
abbrev vArg (ql : Val) (x : Loc) (n : Int) : Val := hl_val(((&ql, #x), #n))

/-- The namespaces of the main thread's commitments: to return, and to create a flag and a
task queue. -/
def Nl : Namespace := nroot.@"return"
def Nc : Namespace := nroot.@"flag"

/-- The layer of the task queue (Rocq `ℓq := 1 ⊕ 1`). -/
abbrev ℓq : Layer := 2

/-- The layer of the flag's obligation (Rocq `ℓq ⊕ 2`). -/
abbrev ℓf : Layer := ℓq.succ.succ

/-- The tasks of the queue are at layer `1 < ℓq` (Rocq `ℓq_cond`). -/
@[lantana_alias task_queue_client.ℓq_cond]
theorem ℓq_cond : (1 : Layer) < ℓq := Ordinals.Ordinal.ofNat_lt_ofNat_iff.mpr (by decide)

theorem one_le_ℓf : (1 : Layer) ≤ ℓf :=
  (Ordinals.Ordinal.ofNat_le_ofNat_iff (m := 1) (n := 4)).mpr (by decide)

theorem one_le_ℓf_succ : (1 : Layer) ≤ ℓf.succ :=
  (Ordinals.Ordinal.ofNat_le_ofNat_iff (m := 1) (n := 5)).mpr (by decide)

/-! ## The specifications -/

section Spec
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLockG GF] [QueueG GF]

/-- The persistent part of the task's argument: the flag and the task queue (Rocq
`is_decr_reentrant`). -/
@[lantana_alias task_queue_client.is_decr_reentrant]
def isDecrReentrant (arg : Val) (γ : QueueName) (k : Oid) : IProp GF :=
  iprop(∃ (ql : Val) (x : Loc) (n : Int), ⌜arg = vArg ql x n⌝ ∧ isFlag x k ℓf ∗
    isTaskQueue ql γ ℓq)

@[lantana_alias task_queue_client.is_decr_reentrant_persistent]
instance isDecrReentrant_persistent (arg : Val) (γ : QueueName) (k : Oid) :
    Persistent (isDecrReentrant (GF := GF) arg γ k) := by
  unfold isDecrReentrant; infer_instance

/-- The reentrant task: with `n ≤ 0` it sets the flag, discharging its obligation `k`; else it
puts itself back into the queue with `n - 1`, moving `k` into the queue at the price of one
of its `n` units of fuel. By Löb induction: the specification itself is the task's
(Rocq `decr_reentrant_spec`). -/
@[lantana_alias task_queue_client.decr_reentrant_spec]
theorem decrReentrant_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids)
    (p : Parent) (k : Oid) (K : Oids) (γ : QueueName) (arg : Val) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&decrReentrant) v(&arg)) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 1 μ) ∗ Par.kids p K ∗ ⌜k ∈ K⌝ ∗ oblKids k ∅ ∗
          (∃ (ql : Val) (x : Loc) (n : Int), ⌜arg = vArg ql x n⌝ ∗
            Obl.fuel k ℓf (n.toNat : Measure) ∗ flagTk x k ∗ isDecrReentrant arg γ k) }}}
        hl(v(&decrReentrant) v(&arg)) @ i
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i G ∗
        Par.kids p (K \ {k}) }}} := by
  obtain ⟨μs, hs⟩ := Flag.set_spec (GF := GF)
  obtain ⟨μp, hp⟩ := TaskQueue.putTask_spec (GF := GF)
  refine ⟨100 + (μs + μp), ?_⟩
  suffices H : ⊢@{IProp GF} iprop(∀ (lc : Fuel) (i : ThreadId) (G : Oids) (p : Parent)
      (k : Oid) (K : Oids) (γ : QueueName) (arg : Val) (C : List ECtxItem),
      l{{{ threadExpr i C hl(v(&decrReentrant) v(&arg)) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 1 (100 + (μs + μp))) ∗ Par.kids p K ∗ ⌜k ∈ K⌝ ∗
          oblKids k ∅ ∗
          (∃ (ql : Val) (x : Loc) (n : Int), ⌜arg = vArg ql x n⌝ ∗
            Obl.fuel k ℓf (n.toNat : Measure) ∗ flagTk x k ∗ isDecrReentrant arg γ k) }}}
        hl(v(&decrReentrant) v(&arg)) @ i
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i G ∗
        Par.kids p (K \ {k}) }}}) by
    intro lc i G p k K γ arg C
    iapply H
  iloeb as IH
  iintro %lc %i %G %p %k %K %γ %arg %C %Φ !>
    ⟨HT, HG, HF, HK, %hk, Kk, %ql, %x, %n, %harg, Fk, Htk, #DRI⟩ HΦ
  subst harg
  icases (Obl.fuel_add_set G _ 100 (μs + μp)).mp $$ HF with ⟨HF, Fm⟩
  icases (Obl.fuel_add_set G _ μs μp).mp $$ Fm with ⟨Fs, Fp⟩
  ihave HF := oblFuels_init G 100 _ $$ HF
  iunfold isDecrReentrant at DRI
  icases DRI with ⟨%ql', %x', %n', %h, #Hflag, #ITQ⟩
  simp only [vArg, Val.pair.injEq, Val.lit.injEq, BaseLit.loc.injEq, BaseLit.int.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  unfold decrReentrant
  lwp_step HT HG HF with Hlc : lc +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc1⟩
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  by_cases hn : n ≤ 0
  · -- Set the flag.
    simp only [hn, decide_true]
    lwp_step HT HG HF
    lwp_expr_simp
    imod Obl.fuel_layer_mono_set (ℓ₁ := 0) (ℓ₂ := 1) G μs (Ordinals.Ordinal.zero_le _) $$ Fs
      with Fs
    iapply hs 0 i x G p K k ℓf C $$ [HT HG Fs HK Kk Htk]
    · iframe HT HG Fs HK Kk Htk Hflag
      ipureintro
      exact hk
    iintro ⟨HT, -, HG, HK, -⟩
    iapply HΦ
    iframe HT Hlc HG
    rw [← Oids.erase_eq_diff]
    iexact HK
  · -- Put the task back, with `n - 1`: the flag's obligation moves into the queue.
    simp only [hn, decide_false]
    lwp_step HT HG HF
    lwp_expr_simp
    lwp_step HT HG HF
    lwp_expr_simp
    lwp_step HT HG HF
    lwp_step HT HG HF
    lwp_expr_simp
    have hn' : n.toNat = 1 + (n - 1).toNat := by omega
    icases (Obl.fuel_add_nat k ℓf hn').mp $$ Fk with ⟨Fk1, Fk⟩
    iapply hp 0 i G p K {k} γ ℓq ql _ (vArg ql x (n - 1)) C $$
      [HT HG Fp HK Fk1 Fk Htk Kk Hc1]
    · iframe HT HG Fp HK ITQ
      isplitr
      · ipureintro
        intro z hz
        rw [LawfulSet.mem_singleton] at hz
        subst hz
        exact hk
      isplitl [Fk1]
      · iapply BigSepS.bigSepS_singleton.mpr
        iexact Fk1
      unfold isTask
      iexists 1, iprop(Obl.fuel k ℓf ((n - 1).toNat : Measure) ∗ flagTk x k ∗ oblKids k ∅ ∗
        £ₒ 1)
      isplitr
      · ipureintro
        exact ℓq_cond
      iframe Fk Htk Kk Hc1
      iexists (100 + (μs + μp))
      unfold taskAt
      iintro %lc' %i' %G' %p' %K' %C' %Φ' !> ⟨HT', HG', HF', HK', %hK', Fk', Htk', Kk', Hc'⟩
        HΦ'
      iapply lwp_credit_later $$ Hc'
      inext
      iapply IH $$ %lc' %i' %G' %p' %k %K' %γ %(vArg ql x (n - 1)) %C' %Φ'
        [HT' HG' HF' HK' Kk' Fk' Htk'] [HΦ']
      · iframe HT' HG' HF' HK' Kk'
        isplitr
        · ipureintro
          exact hK' k (LawfulSet.mem_singleton.mpr rfl)
        iexists ql, x, n - 1
        iframe Fk' Htk'
        isplitr
        · ipureintro
          rfl
        unfold isDecrReentrant
        iexists ql, x, n - 1
        isplitr
        · ipureintro
          rfl
        iframe Hflag ITQ
      · iintro HQ
        iapply HΦ'
        iexact HQ
    iintro ⟨HT, -, HG, HK⟩
    iapply HΦ
    iframe

/-- What the main thread commits to: a flag and a task queue exist. -/
abbrev flagAndQueue : IProp GF :=
  iprop((∃ (x : Loc) (k : Oid) (ℓ : Layer), isFlag x k ℓ) ∗
    (∃ (ql : Val) (γ : QueueName) (ℓ : Layer), isTaskQueue ql γ ℓ))

/-- The main proof. Besides returning `1`, the main thread commits to creating a flag and a task
queue (`kc`). The flag's obligation `k` is allocated in a container `g0` at the flag's layer,
with fuel `ℵ` lowered to `n` once `n` is chosen (Rocq `main_spec`). -/
@[lantana_alias task_queue_client.main_spec]
theorem main_spec : ∃ μ : Measure, ∀ (i : ThreadId) (kl kc : Oid),
    ⊢@{IProp GF} l{{{ threadExpr i [] hl(v(&main) #()) ∗ thKids i {kl, kc} ∗
          ([∗set] g ∈ ({kl, kc} : Oids), Obl.fuel g ℓf.succ μ) ∗ ⌜kl ≠ kc⌝ ∗ oblKids kl ∅ ∗
          oblKids kc ∅ ∗ finallyI Nl kl 1 (exits v1 @ i) ∗ finallyI Nc kc 1 flagAndQueue }}}
        hl(v(&main) #()) @ i
      l{{{ (v : Val), RET v; threadExpr i [] hl(&v) ∗
        liftTerm i (fun _ v => iprop(⌜v = v1⌝)) v }}} := by
  obtain ⟨μti, hti⟩ := TaskQueue.init_spec (GF := GF)
  obtain ⟨μfi, hfi⟩ := Flag.init_spec (GF := GF)
  obtain ⟨μd, hd⟩ := decrReentrant_spec (GF := GF)
  obtain ⟨μfw, hfw⟩ := Flag.wait_spec (GF := GF)
  refine ⟨100 + μti + μfi + μd + μfw, fun i kl kc => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hne, Hkl, Hkc, HFl, HFc⟩ HΦ
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Ffw⟩
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Fd⟩
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Ffi⟩
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Fti⟩
  ihave HF := oblFuels_init _ _ _ $$ HF
  unfold main
  lwp_step HT HG HF with Hlc : 1 +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hc1, Hc2⟩
  lwp_expr_simp
  -- The task queue, at layer `ℓq`.
  lwp_bind hl(v(&TaskQueue.init) #()) HT
  imod Obl.fuel_layer_mono_set _ (ℓ₁ := 0) μti (Ordinals.Ordinal.zero_le _) $$ Fti with Fti
  iapply hti 0 i {kl, kc} ℓq _ $$ [HT HG Fti]
  · iframe
    ipureintro
    exact Ordinals.Ordinal.le_of_lt ℓq_cond
  iintro %ql %γ ⟨HT, -, HG, #ITQ⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- A container for the flag's obligation, at the flag's layer.
  imod Obl.new ⊤ (.thread i) {kl, kc} ℓf (((7 : Nat) : Measure) + (μfi + μd)) $$ [] HG with
    ⟨%g0, %hg0, HG, Kg0, Ag0, Fg0, #Wg0⟩
  · iapply parLe_thread
  icases (Obl.fuel_add g0 _ _ _).mp $$ Fg0 with ⟨F0, Fg0⟩
  icases (Obl.fuel_add g0 _ _ _).mp $$ Fg0 with ⟨F0fi, F0d⟩
  imod Obl.fuel_layer_mono_set _ (ℓ₁ := 0) μfi (Ordinals.Ordinal.zero_le _) $$ Ffi with Ffi
  imod Obl.fuel_layer_mono g0 (ℓ₁ := 0) μfi (Ordinals.Ordinal.zero_le _) $$ F0fi with F0fi
  -- The flag, with fuel `ℵ` for its obligation: `n` is not known yet.
  lwp_bind hl(v(&Flag.init) #()) HT
  iapply hfi 0 i (({kl, kc} : Oids).insert g0) (.obl g0) ∅ ℓf ℵ _ $$ [HT HG Ffi F0fi Kg0]
  · iframe HT HG Kg0
    isplitl [Ffi F0fi]
    · iapply (bigSepS_insert_oids hg0).mpr
      iframe
    · iapply parLe_obl (ℓq := ℓf) g0 (Ordinals.Ordinal.le_refl _) $$ Wg0
  iintro %x %k ⟨HT, -, HG, -, Kg0, Hkk, Fk, Htk, #Hflag⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  -- Keep the commitment: the flag and the task queue exist.
  ihave Hc1 := tlc_one_nat.mpr $$ Hc1
  imod finallyI_discharge (E := ⊤) (.thread i) (({kl, kc} : Oids).insert g0)
    (fun _ _ => CoPset.mem_full) (by simp) $$ Hc1 HG Hkc HFc [] with ⟨-, HG, -⟩
  · isplitl
    · iexists x, k, ℓf
      iexact Hflag
    · iexists ql, γ, ℓq
      iexact ITQ
  ihave HG := Par.kids_congr (B := ({kl} : Oids).insert g0) ?_ $$ HG
  · intro z
    simp at hg0 ⊢
    grind
  ihave HF := oblFuels_subset _ (B := {kl}) (fun z hz => by simp_all) $$ HF
  icases oblFuels_add 7 90 _ $$ HF with ⟨HF7, HF⟩
  ihave HF7 := oblFuels_add_obl _ g0 ℓf _ $$ F0 HF7
  lwp_step HT HG HF7
  lwp_step HT HG HF7
  lwp_expr_simp
  -- Choose `n`.
  lwp_bind hl(chooseNat()) HT
  icases oblFuels_add 1 4 _ $$ HF7 with ⟨HF1, HF7⟩
  iapply lwp_chooseNat (o := 0) (G := ({kl} : Oids).insert g0) (R := ∅) $$ [HT HG HF1]
  · iframe HT
    iapply stepPre_nil $$ HG HF1
  iintro %n ⟨HT, ⟨-, HG, -⟩⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF7
  lwp_step HT HG HF7
  lwp_expr_simp
  lwp_step HT HG HF7
  lwp_step HT HG HF7
  lwp_expr_simp
  -- The task, with the flag's obligation `k` and fuel `n` for it.
  lwp_bind hl(v(&decrReentrant) v(&(vArg ql x n))) HT
  have hg0' : g0 ∉ ({kl} : Oids) := fun h => hg0 (by simp_all)
  ihave Fd := BigSepS.bigSepS_subseteq (Y := ({kl} : Oids)) (fun z hz => by simp_all) $$ Fd
  imod Obl.fuel_layer_mono_set {kl} μd one_le_ℓf_succ $$ Fd with Fd
  imod Obl.fuel_layer_mono g0 μd one_le_ℓf $$ F0d with F0d
  imod Obl.fuel_mono k ℓf (μ₁ := (((n : Int).toNat : Nat) : Measure))
    (Ordinals.Ordinal.le_of_lt (Measure.rep_large_lt _ _ _)) $$ Fk with Fk
  iapply hd 0 i (({kl} : Oids).insert g0) (.obl g0) k ((∅ : Oids).insert k) γ (vArg ql x n) _
    $$ [HT HG Fd F0d Kg0 Hkk Fk Htk]
  · iframe HT HG Kg0 Hkk
    isplitl [Fd F0d]
    · iapply (bigSepS_insert_oids hg0').mpr
      iframe
    isplitr
    · ipureintro
      exact Std.ExtTreeSet.mem_insert_self
    iexists ql, x, n
    iframe Fk Htk
    isplitr
    · ipureintro
      rfl
    unfold isDecrReentrant
    iexists ql, x, n
    isplitr
    · ipureintro
      rfl
    iframe Hflag ITQ
  iintro ⟨HT, -, HG, Kg0⟩
  -- The container is empty: discharge it.
  imod Obl.discharge_leaf ⊤ (.thread i) _ g0 Std.ExtTreeSet.mem_insert_self $$ HG [Kg0] Ag0
    with ⟨HG, -⟩
  · iapply Par.kids_congr _ $$ Kg0
    intro z
    simp
  ihave HG := Par.kids_congr (B := {kl}) ?_ $$ HG
  · intro z
    simp at hg0' ⊢
    grind
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- Wait for the flag, above its layer.
  lwp_bind hl(v(&Flag.wait) #x) HT
  ihave Ffw := BigSepS.bigSepS_subseteq (Y := ({kl} : Oids)) (fun z hz => by simp_all) $$ Ffw
  iapply hfw 0 i x {kl} k ℓf _ $$ [HT HG Ffw]
  · iframe HT HG Ffw
    iexact Hflag
  iintro ⟨HT, -, HG, -⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  unfold v1
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  rw [show (hl(#1) : Exp) = .val hl_val(#1) from rfl]
  iapply lwp_value_mupd'.mpr
  ihave Hc2 := tlc_one_nat.mpr $$ Hc2
  imod threadExpr_terminate_finally i ⊤ hl_val(#1) kl Nl (fun _ _ => CoPset.mem_full)
    $$ HT Hc2 HG Hkl HFl with ⟨HT, #Hd⟩
  imodintro
  iapply HΦ
  iframe HT
  unfold liftTerm
  isplitl
  · iexact Hd
  · ipureintro
    rfl

/-- The commitments of the main thread `i` and its resources (Rocq `Φ_P`). -/
def mainRes (i : ThreadId) (μ : Measure) : IProp GF :=
  iprop(∃ kl kc : Oid, finallyI Nl kl 1 (exits v1 @ i) ∗ finallyI Nc kc 1 flagAndQueue ∗
    (thKids i {kl, kc} ∗ oblKids kl ∅ ∗ oblKids kc ∅ ∗ ⌜kl ≠ kc⌝ ∗
      [∗set] g ∈ ({kl, kc} : Oids), Obl.fuel g ℓf.succ μ))

/-- The postcondition of the main thread. -/
abbrev mainPost : ThreadId → Val → IProp GF := fun _ v => iprop(⌜v = v1⌝)

/-- From the main thread's token and its empty set of children: its commitments, and its
`lWP` from them (Rocq `main_pre`). -/
@[lantana_alias task_queue_client.main_pre]
theorem main_pre (i : ThreadId) :
    threadExpr (GF := GF) i [] hl(v(&main) #()) ⊢ thKids i ∅ -∗
      |={⊤}=>m ∃ μ : Measure, mainRes i μ ∗
        (mainRes i μ -∗ |={⊤}=>m lWP hl(v(&main) #()) @ i; ⊤ {{ liftTerm i mainPost }}) := by
  obtain ⟨μ, hmain⟩ := main_spec (GF := GF)
  iintro HT HG
  imod untilI_alloc (E := ⊤) (.thread i) ∅ ℓf.succ μ $$ [] HG with
    ⟨%kl, -, HG, Hkl, Fkl, -, Akl⟩
  · iapply parLe_thread
  imod Akl $$ %⊤ %Nl %iprop(True) %(exits v1 @ i) [] with Ul
  · inext
    ipureintro
    trivial
  imod untilI_alloc (E := ⊤) (.thread i) _ ℓf.succ μ $$ [] HG with
    ⟨%kc, %hkc, HG, Hkc, Fkc, -, Akc⟩
  · iapply parLe_thread
  imod Akc $$ %⊤ %Nc %iprop(True) %(flagAndQueue (GF := GF)) [] with Uc
  · inext
    ipureintro
    trivial
  have hne : kl ≠ kc := by
    rintro rfl
    exact hkc Std.ExtTreeSet.mem_insert_self
  imodintro
  iexists μ
  isplitl [Ul Uc HG Hkl Hkc Fkl Fkc]
  · unfold mainRes finallyI
    iexists kl, kc
    iframe Ul Uc Hkl Hkc
    isplitl [HG]
    · iapply Par.kids_congr _ $$ HG
      intro z
      simp
      grind
    isplitr
    · ipureintro
      exact hne
    iapply (bigSepS_pair hne).mpr
    iframe
  iintro HP
  unfold mainRes
  icases HP with ⟨%kl, %kc, HFl, HFc, HG, Hkl, Hkc, %hne, HF⟩
  imodintro
  iapply hmain i kl kc $$ [HT HG HF Hkl Hkc HFl HFc]
  · iframe
    ipureintro
    exact hne
  iintro %v ⟨-, Hd⟩
  iexact Hd

end Spec

/-! ## Traces and the guarantee -/

section Guarantee
variable {GF : BundledGFunctors}

/-- The main thread `i` returns `1`, and a flag gets created that is `0` until it is `1` and
then stays `1`; in particular, the task chain run by the worker sets it (Rocq `R_main`). -/
def rMain (i : ThreadId) : TrProp Exp State :=
  ◇ₜ TrProp.state (threadExprSat i [] (.val v1)) ∧ₜ ◇ₜ (∃ₜ x : Loc, isFlagTr x)

/-- Moreover, a task queue gets created whose lock makes release progress: whenever its lock
is held, it is eventually released (Rocq `R_queue`, whose two existentials over the queue's
pointers are unused and dropped). -/
def rQueue : TrProp Exp State :=
  ◇ₜ (∃ₜ (next : Loc) (curr : Loc), releaseProgress next curr)

/-- What the commitments guarantee (Rocq `G_main`). -/
def gMain (i : ThreadId) : TrSpec Exp State GF :=
  ◇ₛ TrSpec.state (threadExprSat i [] (.val v1)) ∧ₛ
    ◇ₛ ((∃ₛ x : Loc, flagTrSpec x) ∧ₛ (∃ₛ ql : Val, taskQueueTrSpec ql)) ∧ₛ TrSpec.true

@[lantana_alias task_queue_client.G_main_impl]
theorem gMain_impl (i : ThreadId) :
    (gMain (GF := GF) i).external ⊆ (rMain i ∧ₜ rQueue) := by
  intro τ ⟨hr, ⟨m, hm, ⟨⟨x, hx⟩, ⟨ql, hq⟩⟩, hbef⟩, _⟩
  obtain ⟨-, -, next, curr, -, hrp⟩ := TaskQueue.taskQueue_release_progress ql _ hq
  exact ⟨⟨hr, m, hm, ⟨x, Flag.flagTrSpec_impl x _ hx⟩, hbef⟩, m, hm, ⟨next, curr, hrp⟩, hbef⟩

variable [ModelGS GF] [HeapGS GF] [TicketLockG GF] [QueueG GF]

/-- A task queue exists: its value is trace-visible, its ghost names and layer are not
(inferred). -/
theorem guar_exTaskQueue :
    ⊢@{IProp GF} iprop(∃ (ql : Val) (γ : QueueName) (ℓ : Layer), isTaskQueue ql γ ℓ) ⊨ₜ
      (∃ₛ ql : Val, taskQueueTrSpec ql) := by
  exact IntoGuar.into_guar

/-- Inferred (`IntoGuar`), with the guarantees of the flag and of the task queue as instances:
the flag's location and the queue are trace-visible, the names and layers ghost. -/
@[lantana_alias task_queue_client.guar_Φ_P]
theorem guar_mainRes (i : ThreadId) (μ : Measure) :
    ⊢@{IProp GF} mainRes i μ ⊨ₜ gMain i := by
  unfold mainRes gMain
  exact IntoGuar.into_guar

end Guarantee

/-! ## Adequacy -/

section Adequacy

/-- The initial pool: the main thread `0`. -/
abbrev tp0 : ThreadPool Exp := [hl(v(&main) #())]

/-- The initial state: the empty heap. -/
abbrev σ0 : State := ⟨∅⟩

/-- The initial resources and the `lWP` of the main thread, in the closed world (the common
part of the adequacy proofs). -/
theorem taskQueueClient_init [ModelGS ExGF] [TemporalGS Exp State ExGF]
    (hs : HeapStateGS ExGF) :
    letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
    ([∗list] j ↦ e ∈ tp0, threadExpr j [] e) ⊢
      ([∗list] j ∈ List.range tp0.length, thKids j ∅) -∗
      |={⊤}=>m ∃ μ : Measure, mainRes (GF := ExGF) 0 μ ∗
        (mainRes 0 μ -∗
          |={⊤}=>m [∗list] j ↦ e ∈ tp0, lWP e @ j; ⊤ {{ liftTerm j (mainPost (GF := ExGF)) }}) := by
  letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
  iintro HT HG
  rw [show List.range (List.length tp0) = [0] from rfl]
  ihave HG := BigSepL.bigSepL_singleton.mp $$ HG
  ihave HT := BigSepL.bigSepL_singleton.mp $$ HT
  imod main_pre 0 $$ HT HG with ⟨%μ, HP, Hwp⟩
  imodintro
  iexists μ
  iframe HP
  iintro HP
  imod Hwp $$ HP with Hwp
  imodintro
  iapply BigSepL.bigSepL_singleton.mpr
  iexact Hwp

/-- In every fair behavior from the initial configuration, the main thread returns `1`, a flag
gets created that is `0` until it is `1` and then `1`, and a task queue gets created whose lock
makes release progress (Rocq `task_queue_client_adequacy`). -/
@[lantana_alias task_queue_client_adequacy]
theorem taskQueueClient_adequacy (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    rMain 0 τ ∧ rQueue τ := by
  refine lwp_adequacy_temporal (GF := ExGF) σ0 tp0 0 (gMain 0) (rMain 0 ∧ₜ rQueue)
    (gMain_impl 0) τ hbeh hfair hpos hinit ?_
  intro _ _
  refine ⟨2, ?_⟩
  imod heapState_init σ0 tp0 with ⟨%hs, Hσ, -, HT⟩
  letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
  imodintro
  iexists instStateInterp, (fun _ _ => iprop(True)), mainPost
  isplitl [Hσ]
  · iexact Hσ
  iintro - HG
  imod taskQueueClient_init hs $$ HT HG with ⟨%μ, HP, Hwp⟩
  imodintro
  iexists mainRes 0 μ
  isplitr
  · iapply guar_mainRes
  iframe

/-- Safety: in every fair behavior from the initial configuration, the scheduled thread is never
stuck, and once the main thread has returned, its value is `1` (Rocq
`task_queue_client_safety_adequacy`). -/
@[lantana_alias task_queue_client_safety_adequacy]
theorem taskQueueClient_safety_adequacy (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    safetyIris 0 (fun _ v => v = v1) τ := by
  refine lwp_adequacy_safety (GF := ExGF) σ0 tp0 0 0 _ τ hbeh hfair hpos hinit (by decide) ?_
  intro _ _
  refine ⟨2, ?_⟩
  imod heapState_init σ0 tp0 with ⟨%hs, Hσ, -, HT⟩
  letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
  imodintro
  iexists instStateInterp, (fun _ _ => iprop(True)), mainPost
  isplit
  · ipureintro
    exact fun _ => .rfl
  isplitl [Hσ]
  · iexact Hσ
  iintro - HG
  imod taskQueueClient_init hs $$ HT HG with ⟨%μ, HP, Hwp⟩
  iapply Hwp $$ HP

/-- Liveness and safety together, over the same fair behaviors (Rocq
`task_queue_client_liveness_safety`). -/
@[lantana_alias task_queue_client_liveness_safety]
theorem taskQueueClient_liveness_safety (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    (rMain 0 τ ∧ rQueue τ) ∧ safetyIris 0 (fun _ v => v = v1) τ :=
  ⟨taskQueueClient_adequacy τ hbeh hfair hpos hinit,
    taskQueueClient_safety_adequacy τ hbeh hfair hpos hinit⟩

end Adequacy

end Lantana.Examples.TaskQueueClient
