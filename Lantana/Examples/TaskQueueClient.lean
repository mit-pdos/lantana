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

end Spec

end Lantana.Examples.TaskQueueClient
