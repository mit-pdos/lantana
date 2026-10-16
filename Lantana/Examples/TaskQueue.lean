/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Examples.Handoff
public import Lantana.Examples.Queue

/-! # A task queue, run by a forked worker thread

Rocq `examples/task_queue.v` (§7.3 of the paper): a queue (`Lantana.Examples.Queue`) of tasks
`f a` as in the handoff (`Handoff.isTask`), with `putTask q f a` (enqueue the pair `(f, a)`),
`runTask q` (dequeue and run a task, if any) and a worker thread running `runTask` forever,
forked by `init`.

The task's obligations are those of the queued element: while the task waits in the queue
they are children of the worker's inbox, and `runTask` runs the task with the fuel of the
fresh container they move into (`Queue.dequeue_spec`), lifted to the task's layer
(`Obl.fuel_extend_set`), then discharges the container.

## Specifications

All proved, with Rocq's statements (thread `i`, mask `⊤`, `∃ μ` in front): `putTask_spec`
(measure `100 + μ_enqueue`), `runTask_spec` (`100 + μ_dequeue`; the dequeued container and
the new inbox get `m + 99 + 1`), `worker_spec` (`10 + (μ_runTask + 1)`; the worker never
returns: `RET #(); False`, by Löb induction; with its inbox it renews it at every iteration,
without it it pays nothing) and `init_spec` (`100 + μ_init`). The step counts differ from
Rocq's, as the Lean programs' do.

Unlike Rocq, which forks with `lwp_fork_step` and creates the worker's inbox in the child,
`init` creates the inbox below the main thread just before the fork (with the fuel of the fork
step, of its move and of the worker, `1 + (1 + μ_worker)`; a new obligation's fuel is free),
installs the queue's invariant with it, and `lwp_fork` moves it to the worker (as
`HandoffClient` does).

## Guarantees and traces

`taskQueueTrSpec ql := Queue.queueTrSpec ql` (the tasks are Hoare triples with ghost
resources; that every task runs is expressed by obligations), `guar_isTaskQueue`, and
`taskQueue_release_progress`.

Everything here is proved.
-/

@[expose] public noncomputable section

namespace Lantana.Examples.TaskQueue

open Iris Iris.BI Iris.Std Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.TicketLock (TicketLockG vLock releaseProgress)
open Lantana.Examples.Queue (QueueG QueueName isQueue isQueueInit queueTrSpec dequeueRes vQueue)
open Lantana.Examples.Handoff (isTask taskAt)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The program -/

/-- `λ q f a, enqueue q (f, a)`. -/
@[lantana_alias task_queue.TaskQueue.put_task]
def putTask : Val := hl_val(λ q f a, v(&Queue.enqueue) q (f, a))

/-- `λ q, match dequeue q with none => () | some fa => (fst fa) (snd fa)`. -/
@[lantana_alias task_queue.TaskQueue.run_task]
def runTask : Val :=
  hl_val(λ q, match v(&Queue.dequeue) q with | none() => #() | some(fa) => (fst(fa)) (snd(fa)))

/-- `rec loop q := runTask q; loop q`. -/
@[lantana_alias task_queue.TaskQueue.worker]
def worker : Val := hl_val(rec loop q := v(&runTask) q; loop q)

/-- `λ _, let q := Queue.init (); fork (worker q); q`. -/
@[lantana_alias task_queue.TaskQueue.init]
def init : Val := hl_val(λ _, let q := v(&Queue.init) #(); fork(v(&worker) q); q)

/-! ## The task queue -/

section Defs
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLockG GF] [QueueG GF]

/-- The elements of a task queue: tasks `(f, a)` below the layer `ℓ`. -/
abbrev taskElem (ℓ : Layer) (v : Val) (B : Oids) : IProp GF :=
  iprop(∃ f a : Val, ⌜v = hl_val((&f, &a))⌝ ∗ isTask ℓ f a B)

/-- A task queue: a queue of tasks below its layer `ℓ` (Rocq `is_task_queue`). -/
@[lantana_alias task_queue.is_task_queue]
def isTaskQueue (ql : Val) (γ : QueueName) (ℓ : Layer) : IProp GF :=
  isQueue ql γ ℓ (taskElem ℓ)

@[lantana_alias task_queue.is_task_queue_persistent]
instance isTaskQueue_persistent (ql : Val) (γ : QueueName) (ℓ : Layer) :
    Persistent (isTaskQueue (GF := GF) ql γ ℓ) := by
  unfold isTaskQueue; infer_instance

end Defs

/-! ## Specifications -/

section Specs
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLockG GF] [QueueG GF]

/-- Putting a task: its obligations `B` move into the queue (Rocq
`TaskQueue_put_task_spec`). -/
@[lantana_alias task_queue.TaskQueue_put_task_spec]
theorem putTask_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids) (p : Parent)
    (K B : Oids) (γ : QueueName) (ℓ : Layer) (ql f a : Val) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&putTask) v(&ql) v(&f) v(&a)) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 1 μ) ∗ Par.kids p K ∗ ⌜B ⊆ K⌝ ∗
          ([∗set] b ∈ B, Obl.fuel b ℓ.succ.succ 1) ∗ isTask ℓ f a B ∗ isTaskQueue ql γ ℓ }}}
        hl(v(&putTask) v(&ql) v(&f) v(&a)) @ i
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i G ∗
        Par.kids p (K \ B) }}} := by
  obtain ⟨μe, he⟩ := Queue.enqueue_spec (GF := GF)
  refine ⟨100 + μe, fun lc i G p K B γ ℓ ql f a C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, HK, %hBK, HFB, Htask, #IQ⟩ HΦ
  icases (Obl.fuel_add_set G _ 100 μe).mp $$ HF with ⟨HF, Fe⟩
  ihave HF := oblFuels_init G 100 _ $$ HF
  unfold putTask
  lwp_step HT HG HF with Hlc : lc
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  iapply he 0 i G p K B (taskElem ℓ) γ ℓ ql hl_val((&f, &a)) C $$ [HT HG Fe HK HFB Htask]
  · iframe HT HG Fe HK HFB
    isplitr
    · ipureintro
      exact hBK
    isplitl [Htask]
    · iexists f, a
      iframe Htask
      ipureintro
      rfl
    · iunfold isTaskQueue at IQ
      iexact IQ
  iintro ⟨HT, -, HG, HK⟩
  iapply HΦ
  iframe

/-- Running a task, if any: the dequeued task runs with one unit of fuel at layer `ℓ` of each
child of the thread (lifted to the task's layer), then its container is discharged. The worker
(`b = true`) renews its inbox (Rocq `TaskQueue_run_task_spec`). -/
@[lantana_alias task_queue.TaskQueue_run_task_spec]
theorem runTask_spec : ∃ μ : Measure, ∀ (lc : Fuel) (m : Measure) (b : Bool) (wg : Oid)
    (i : ThreadId) (G : Oids) (γ : QueueName) (ℓ : Layer) (ql : Val) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&runTask) v(&ql)) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 1 μ) ∗ ([∗set] g ∈ G, Obl.fuel g ℓ 1) ∗
          (if b then Queue.worker γ wg else iprop(True)) ∗ isTaskQueue ql γ ℓ }}}
        hl(v(&runTask) v(&ql)) @ i
      l{{{ (rv : Val), RET rv; threadExpr i C hl(&rv) ∗ £ₒ lc ∗
        (if b then iprop(∃ ng : Oid, thKids i (G.insert ng) ∗ ⌜ng ∉ G⌝ ∗ Queue.worker γ ng ∗
          oblKids wg ∅ ∗ Obl.assigned wg 1 ∗ Obl.fuel ng ℓ m)
        else thKids i G) }}} := by
  obtain ⟨μd, hd⟩ := Queue.dequeue_spec (GF := GF)
  refine ⟨100 + μd, fun lc m b wg i G γ ℓ ql C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, Ft, HW, #IQ⟩ HΦ
  icases (Obl.fuel_add_set G _ 100 μd).mp $$ HF with ⟨HF, Fd⟩
  ihave HF := oblFuels_init G 100 _ $$ HF
  unfold runTask
  lwp_step HT HG HF with Hlc : lc
  lwp_expr_simp
  lwp_bind hl(v(&Queue.dequeue) v(&ql)) HT
  iapply hd 0 (m + ((99 : Nat) : Measure) + 1) b wg i G (taskElem ℓ) γ ℓ ql _ $$
    [HT HG Fd HW]
  · iframe HT HG Fd HW
    iunfold isTaskQueue at IQ
    iexact IQ
  iintro %x ⟨HT, -, Hx⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  ihave %hx := Queue.dequeueRes_cases _ _ _ _ _ _ _ _ x $$ Hx
  rcases hx with rfl | ⟨v, rfl⟩
  · -- No task.
    cases b with
    | false =>
      simp only [dequeueRes, Bool.false_eq_true, ↓reduceIte]
      lwp_step HT Hx HF
      lwp_step HT Hx HF
      lwp_expr_simp
      lwp_step HT Hx HF
      lwp_expr_simp
      iapply lwp_value'
      iapply HΦ
      iframe
    | true =>
      simp only [dequeueRes, ↓reduceIte]
      icases Hx with ⟨%ng, HG, %hng, HW, Kwg, Awg, Fng⟩
      icases (Obl.fuel_add ng ℓ _ 1).mp $$ Fng with ⟨Fng, -⟩
      icases (Obl.fuel_add ng ℓ m _).mp $$ Fng with ⟨Fng, Fng99⟩
      ihave HF := oblFuels_add_obl G ng ℓ _ $$ Fng99 HF
      lwp_step HT HG HF
      lwp_step HT HG HF
      lwp_expr_simp
      lwp_step HT HG HF
      lwp_expr_simp
      iapply lwp_value'
      iapply HΦ
      iframe HT Hlc
      iexists ng
      iframe
      ipureintro
      exact hng
  · -- A task `f a`: it runs with the fuel of the children of the thread, among them its
    -- container `g`.
    simp only [dequeueRes]
    icases Hx with ⟨%g, %B, ⟨%f, %a, %hv, Htask⟩, Kg, Ag, Fg, %hg, Hb⟩
    subst hv
    unfold isTask
    icases Htask with ⟨%ℓt, %P, %hlt, HP, %μt, #Task⟩
    icases (Obl.fuel_add g ℓ _ 1).mp $$ Fg with ⟨Fg, Fg1⟩
    icases (Obl.fuel_add g ℓ m _).mp $$ Fg with ⟨-, Fg99⟩
    ihave HF := oblFuels_add_obl G g ℓ _ $$ Fg99 HF
    ihave Ft := (bigSepS_insert_oids (Φ := fun g => Obl.fuel g ℓ 1) hg).mpr $$ [Fg1 Ft]
    · iframe Fg1 Ft
    have hgg : g ∈ G.insert g := Std.ExtTreeSet.mem_insert_self
    unfold taskAt
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      lwp_step HT Hb HF
      lwp_step HT Hb HF
      lwp_expr_simp
      lwp_step HT Hb HF
      lwp_expr_simp
      lwp_step HT Hb HF
      lwp_step HT Hb HF
      lwp_expr_simp
      imod Obl.fuel_extend_set (G.insert g) hlt μt $$ Ft with Ft
      iapply lwp_mupd
      iapply Task $$ %(0 : Fuel) %i %(G.insert g) %(Parent.obl g) %B %C [HT Hb Ft Kg HP]
      · iframe HT Hb Ft Kg HP
        ipureintro
        exact fun _ h => h
      iintro %rv ⟨HT, -, HG, Kg⟩
      imod Obl.discharge_leaf ⊤ (.thread i) (G.insert g) g hgg $$ HG [Kg] Ag with ⟨HG, -⟩
      · iapply Par.kids_congr _ $$ Kg
        intro z
        rw [LawfulSet.diff_all]
      imodintro
      iapply HΦ
      iframe HT Hlc
      iapply Par.kids_congr _ $$ HG
      intro z
      simp only [Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.mem_insert]
      grind
    | true =>
      simp only [↓reduceIte]
      icases Hb with ⟨%ng, HG, %⟨hng, hgn⟩, HW, Kwg, Awg, Fng⟩
      have hng' : ng ∉ G.insert g := by
        simp only [Std.ExtTreeSet.mem_insert]
        grind
      icases (Obl.fuel_add ng ℓ _ 1).mp $$ Fng with ⟨Fng, Fng1⟩
      icases (Obl.fuel_add ng ℓ m _).mp $$ Fng with ⟨Fng, Fng99⟩
      ihave HF := oblFuels_add_obl (G.insert g) ng ℓ _ $$ Fng99 HF
      ihave Ft := (bigSepS_insert_oids (Φ := fun g => Obl.fuel g ℓ 1) hng').mpr $$ [Fng1 Ft]
      · iframe Fng1 Ft
      lwp_step HT HG HF
      lwp_step HT HG HF
      lwp_expr_simp
      lwp_step HT HG HF
      lwp_expr_simp
      lwp_step HT HG HF
      lwp_step HT HG HF
      lwp_expr_simp
      imod Obl.fuel_extend_set ((G.insert g).insert ng) hlt μt $$ Ft with Ft
      iapply lwp_mupd
      iapply Task $$ %(0 : Fuel) %i %((G.insert g).insert ng) %(Parent.obl g) %B %C
        [HT HG Ft Kg HP]
      · iframe HT HG Ft Kg HP
        ipureintro
        exact fun _ h => h
      iintro %rv ⟨HT, -, HG, Kg⟩
      imod Obl.discharge_leaf ⊤ (.thread i) ((G.insert g).insert ng) g
        (Std.ExtTreeSet.mem_insert.mpr (.inr hgg)) $$ HG [Kg] Ag with ⟨HG, -⟩
      · iapply Par.kids_congr _ $$ Kg
        intro z
        rw [LawfulSet.diff_all]
      imodintro
      iapply HΦ
      iframe HT Hlc
      iexists ng
      iframe HW Kwg Awg Fng
      isplitl [HG]
      · iapply Par.kids_congr _ $$ HG
        intro z
        simp only [Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.mem_insert]
        grind
      · ipureintro
        exact hng

omit [HeapGS GF] [TicketLockG GF] [QueueG GF] in
/-- A thread without children pays nothing. -/
theorem oblFuels_empty (n : Measure) : ⊢ oblFuels (GF := GF) ∅ n := by
  unfold oblFuels
  iapply BigSepS.bigSepS_empty.mpr
  iempintro

/-- The worker runs tasks forever (it never returns: the postcondition is `False`). With its
inbox `g` (`b = true`), each iteration renews the inbox, whose fuel pays for the iteration;
without (`G = ∅`), it pays nothing. By Löb induction (Rocq `TaskQueue_worker_spec`). -/
@[lantana_alias task_queue.TaskQueue_worker_spec]
theorem worker_spec : ∃ μ : Measure, ∀ (b : Bool) (i : ThreadId) (G : Oids) (γ : QueueName)
    (ℓ : Layer) (ql : Val) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&worker) v(&ql)) ∗ thKids i G ∗
          (if b then iprop(∃ g : Oid, ⌜G = {g} ∧ 1 ≤ ℓ⌝ ∧ (Obl.fuel g ℓ μ ∗ Queue.worker γ g))
           else iprop(⌜G = ∅⌝)) ∗ isTaskQueue ql γ ℓ }}}
        hl(v(&worker) v(&ql)) @ i
      l{{{ RET hl_val(#()); iprop(False) }}} := by
  obtain ⟨μr, hr⟩ := runTask_spec (GF := GF)
  refine ⟨((10 : Nat) : Measure) + (μr + 1), fun b i G γ ℓ ql C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HW, #IQ⟩ -
  cases b with
  | true =>
    simp only [↓reduceIte]
    icases HW with ⟨%g, %⟨hG, hℓ⟩, Fg, Wk⟩
    subst hG
    iloeb as IH generalizing %g
    icases (Obl.fuel_add g ℓ _ _).mp $$ Fg with ⟨Fs, Fr⟩
    ihave Fs : oblFuels {g} ((10 : Nat) : Measure) $$ [Fs]
    · unfold oblFuels
      iapply BigSepS.bigSepS_singleton.mpr
      iexists ℓ
      iexact Fs
    unfold worker
    lwp_step HT HG Fs
    lwp_expr_simp
    lwp_bind hl(v(&runTask) v(&ql)) HT
    icases (Obl.fuel_add g ℓ μr 1).mp $$ Fr with ⟨Fmr, F1⟩
    imod Obl.fuel_layer_mono (ℓ₁ := 1) g μr hℓ $$ Fmr with Fmr
    iapply hr 1 (((2 : Nat) : Measure) + (((10 : Nat) : Measure) + (μr + 1))) true g i {g} γ ℓ
      ql _ $$ [HT HG Fmr F1 Wk]
    · simp only [↓reduceIte]
      iframe HT HG Wk IQ
      isplitl [Fmr]
      · iapply BigSepS.bigSepS_singleton.mpr
        iexact Fmr
      · iapply BigSepS.bigSepS_singleton.mpr
        iexact F1
    simp only [↓reduceIte]
    iintro %rv ⟨HT, Hc, %ng, HG, %hng, Wk, Kg, Ag, Fng⟩
    imod Obl.discharge_leaf ⊤ (.thread i) (({g} : Oids).insert ng) g
      (Std.ExtTreeSet.mem_insert.mpr (.inr (LawfulSet.mem_singleton.mpr rfl))) $$ HG Kg Ag
      with ⟨HG, -⟩
    ihave HG := Par.kids_congr (B := {ng}) ?_ $$ HG
    · intro z
      simp only [Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.mem_insert, LawfulSet.mem_singleton]
      simp only [LawfulSet.mem_singleton] at hng
      grind
    icases (Obl.fuel_add ng ℓ _ _).mp $$ Fng with ⟨F2, Fng⟩
    ihave F2 : oblFuels {ng} ((2 : Nat) : Measure) $$ [F2]
    · unfold oblFuels
      iapply BigSepS.bigSepS_singleton.mpr
      iexists ℓ
      iexact F2
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    lwp_step HT HG F2
    lwp_step HT HG F2
    lwp_expr_simp
    iapply lwp_credit_later $$ Hc
    inext
    iapply IH $$ %ng HT HG Fng Wk
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases HW with %hG
    subst hG
    iloeb as IH
    unfold worker
    ihave HF := oblFuels_empty (GF := GF) ((1 : Nat) : Measure)
    lwp_step HT HG HF
    lwp_expr_simp
    lwp_bind hl(v(&runTask) v(&ql)) HT
    iapply hr 1 0 false 0 i ∅ γ ℓ ql _ $$ [HT HG]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iframe HT HG IQ
      isplitl []
      · iapply BigSepS.bigSepS_empty.mpr
        iempintro
      iapply BigSepS.bigSepS_empty.mpr
      iempintro
    simp only [Bool.false_eq_true, ↓reduceIte]
    iintro %rv ⟨HT, Hc, HG⟩
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    ihave HF := oblFuels_empty (GF := GF) ((2 : Nat) : Measure)
    lwp_step HT HG HF
    lwp_step HT HG HF
    lwp_expr_simp
    iapply lwp_credit_later $$ Hc
    inext
    iapply IH $$ HT HG

/-- Creating a task queue at layer `ℓ ≥ 1`, with its worker thread (Rocq
`TaskQueue_init_spec`). The worker's inbox is created below this thread before the fork, and
the fork moves it to the worker. -/
@[lantana_alias task_queue.TaskQueue_init_spec]
theorem init_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids) (ℓ : Layer)
    (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&init) #()) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ ⌜1 ≤ ℓ⌝ }}}
        hl(v(&init) #()) @ i
      l{{{ (ql : Val) (γ : QueueName), RET ql; threadExpr i C hl(&ql) ∗ £ₒ lc ∗ thKids i G ∗
        isTaskQueue ql γ ℓ }}} := by
  obtain ⟨μi, hi⟩ := Queue.init_spec (GF := GF)
  obtain ⟨μw, hw⟩ := worker_spec (GF := GF)
  refine ⟨100 + μi, fun lc i G ℓ C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hℓ⟩ HΦ
  icases (Obl.fuel_add_set G _ 100 μi).mp $$ HF with ⟨HF, Fi⟩
  ihave HF := oblFuels_init G 100 _ $$ HF
  unfold init
  lwp_step HT HG HF with Hlc : lc
  lwp_expr_simp
  lwp_bind hl(v(&Queue.init) #()) HT
  iapply hi 0 (taskElem ℓ) i G _ $$ [HT HG Fi]
  · iframe
  iintro %ql %γ ⟨HT, -, HG, IQI⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- The worker's inbox, at the queue's layer: a child of this thread until the fork moves it
  -- to the worker. It pays the fork step, its move, and the worker.
  imod Obl.new ⊤ (.thread i) G ℓ (((1 : Nat) : Measure) + (((1 : Nat) : Measure) + μw)) $$ []
    HG with ⟨%gj, %hgj, HG, Kgj, Agj, Fgj, #Wgj⟩
  · iapply parLe_thread
  imod Queue.isQueue_initialize ⊤ ql γ ℓ (taskElem ℓ) gj $$ IQI Kgj Wgj Agj with ⟨#IQ, Wk⟩
  icases (Obl.fuel_add gj _ _ _).mp $$ Fgj with ⟨F1, Fgj⟩
  icases (Obl.fuel_add gj _ _ _).mp $$ Fgj with ⟨Fmv, Fw⟩
  icases oblFuels_add 1 96 _ $$ HF with ⟨HF1, HF⟩
  ihave HF1 := oblFuels_add_obl _ gj ℓ _ $$ F1 HF1
  lwp_bind hl(fork(v(&worker) v(&ql))) HT
  have hsub : ({gj} : Oids) ⊆ G.insert gj := fun z hz => by
    rw [LawfulSet.mem_singleton] at hz
    subst hz
    exact Std.ExtTreeSet.mem_insert_self
  iapply lwp_fork (o := 0) (G := G.insert gj) (R := ∅) {gj}
    iprop(Obl.fuel gj ℓ μw ∗ Queue.worker γ gj) hl(v(&worker) v(&ql)) hsub $$ []
    [HT HG HF1 Fmv Fw Wk]
  · -- The worker thread runs forever.
    iintro %j %Φ' !> ⟨HTj, HGj, Fw, Wk⟩ -
    iapply hw true j {gj} γ ℓ ql [] $$ [HTj HGj Fw Wk]
    · simp only [↓reduceIte]
      iframe HTj HGj
      isplitl [Fw Wk]
      · iexists gj
        isplitr
        · ipureintro
          exact ⟨rfl, hℓ⟩
        iframe
      · unfold isTaskQueue
        iexact IQ
    iintro H
    iexfalso
    iexact H
  · iframe HT Fw Wk
    isplitl [HG HF1]
    · iapply stepPre_nil $$ HG HF1
    · unfold oblFuels
      iapply BigSepS.bigSepS_singleton.mpr
      iexists _
      iexact Fmv
  iintro ⟨HT, -, HG, -⟩
  ihave HG := Par.kids_congr (B := G) ?_ $$ HG
  · intro z
    simp only [Std.ExtTreeSet.mem_diff_iff, Std.ExtTreeSet.mem_insert, LawfulSet.mem_singleton]
    grind
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  iapply lwp_value'
  iapply HΦ
  iframe HT Hlc HG
  unfold isTaskQueue
  iexact IQ

end Specs

/-! ## Temporal guarantees

A task queue guarantees what its queue does: the tasks (`isTask`) are Hoare triples with
ghost resources. That every task runs is expressed by obligations. -/

section Guarantee
variable {GF : BundledGFunctors}

/-- The guarantee of a task queue (Rocq `task_queue_trSpec`). -/
@[lantana_alias task_queue.task_queue_trSpec]
def taskQueueTrSpec (ql : Val) : TrSpec Exp State GF := queueTrSpec ql

variable [ModelGS GF] [HeapGS GF] [TicketLockG GF] [QueueG GF]

@[lantana_alias task_queue.guar_is_task_queue]
theorem guar_isTaskQueue (ql : Val) (γ : QueueName) (ℓ : Layer) :
    ⊢@{IProp GF} isTaskQueue ql γ ℓ ⊨ₜ taskQueueTrSpec ql :=
  Queue.guar_isQueue ql γ ℓ _

@[lantana_alias task_queue.into_guar_is_task_queue]
instance intoGuar_isTaskQueue (ql : Val) (γ : QueueName) (ℓ : Layer) :
    IntoGuar (Expr := Exp) (State := State) (isTaskQueue (GF := GF) ql γ ℓ)
      (taskQueueTrSpec ql) :=
  ⟨guar_isTaskQueue ql γ ℓ⟩

end Guarantee

/-! ## Progress of the task queue's lock, at the level of traces -/

/-- Every `putTask` or `runTask` that takes the queue's lock eventually releases it (Rocq
`task_queue_release_progress`). -/
@[lantana_alias task_queue.task_queue_release_progress]
theorem taskQueue_release_progress {GF : BundledGFunctors} (ql : Val) (τ : Trace Exp State)
    (h : (taskQueueTrSpec (GF := GF) ql).external τ) :
    ∃ lhptr ltptr next curr : Loc,
      ql = vQueue lhptr ltptr (vLock next curr) ∧ releaseProgress next curr τ :=
  Queue.queue_release_progress ql τ h

end Lantana.Examples.TaskQueue
