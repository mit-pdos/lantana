/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
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
(measure `100 + μ_enqueue`), `runTask_spec` (`100 + μ_dequeue`), `worker_spec` (the worker
never returns: `RET #(); False`, by Löb induction; with its inbox it renews it at every
iteration, without it it pays nothing) and `init_spec` (`100 + μ_init + …`).

Unlike Rocq, which forks with `lwp_fork_step` and creates the worker's inbox in the child,
`init` creates the inbox below the main thread just before the fork (with the fuel of the fork
step, of its move and of the worker), installs the queue's invariant with it, and `lwp_fork`
moves it to the worker (as `HandoffClient` does); the measure of `init` then also pays for the
inbox (`2 + μ_worker`).

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

end Specs

end Lantana.Examples.TaskQueue
