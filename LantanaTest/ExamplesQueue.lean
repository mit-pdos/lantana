module

public import Lantana

/-! Tests of the queue (`queue.v`), the task queue (`task_queue.v`) and its clients
(`task_queue_client.v`, `task_queue_flag_stable_client.v`): the lists of sets, the programs,
the trace-level corollaries, the end-to-end statements and the axioms of the specifications
and of the corollaries. -/

namespace LantanaTest.ExamplesQueue

open Iris.Std Lantana Lantana.HeapLang Lantana.Examples
open scoped Lantana.TrProp Lantana.TrSpec

/-! ## Lists of sets -/

/-- Rocq's definition of `disjoint_list_of_sets` is the lemma `disjointList_iff_lookup`. -/
example (L : List Oids) :
    disjointList L ↔ ∀ (j₁ j₂ : Nat) (s₁ s₂ : Oids), j₁ ≠ j₂ → L[j₁]? = some s₁ →
      L[j₂]? = some s₂ → s₁ ## s₂ :=
  disjointList_iff_lookup

/-- Appending a set disjoint from the union keeps the list disjoint. -/
example (L : List Oids) (B : Oids) (h : disjointList L) (hB : unionList L ## B) :
    disjointList (L ++ [B]) := by
  refine disjointList_append_disjoint_iff.mpr ⟨h, disjointList_singleton B, ?_⟩
  rwa [unionList_singleton]

/-! ## The programs -/

/-- `enqueue` appends a cell under the lock. -/
example : Queue.enqueue = hl_val(λ q x, let lock := snd(q); v(&TicketLock.acquire) lock;
    let tptr := snd(fst(q)); let t := !tptr; let newt := ref(none()); t ← some((x, newt));
    tptr ← newt; v(&TicketLock.release) lock) := rfl

/-- The queue is the triple `((hptr, tptr), lock)`, nested to the left as in Rocq. -/
example (lhptr ltptr : Loc) (tl : Val) :
    Queue.vQueue lhptr ltptr tl = .pair (.pair (.lit (.loc lhptr)) (.lit (.loc ltptr))) tl :=
  rfl

/-- The worker runs `runTask` forever. -/
example : TaskQueue.worker = hl_val(rec loop q := v(&TaskQueue.runTask) q; loop q) := rfl

/-- The flag-stable client runs the same program. -/
example : TaskQueueClient.main = hl_val(λ _, let q := v(&TaskQueue.init) #();
    let x := v(&Flag.init) #(); let n := chooseNat(); v(&TaskQueueClient.decrReentrant) ((q, x), n);
    let r := v(&Flag.wait) x; r) := rfl

/-! ## Traces -/

/-- The lock of a task queue makes release progress. -/
example {GF : Iris.BundledGFunctors} (ql : Val) (τ : Trace Exp State)
    (h : (TaskQueue.taskQueueTrSpec (GF := GF) ql).external τ) :
    ∃ lhptr ltptr next curr : Loc,
      ql = Queue.vQueue lhptr ltptr (TicketLock.vLock next curr) ∧
        TicketLock.releaseProgress next curr τ :=
  TaskQueue.taskQueue_release_progress ql τ h

/-- The end-to-end statement of `task_queue_client.v`, liveness and safety. -/
example (τ : Trace Exp State) (hbeh : IsBehavior τ) (hfair : fairScheduling τ) (hpos : τ.pos = 0)
    (hinit : τ.seq 0 = ⟨(TaskQueueClient.tp0, TaskQueueClient.σ0), 0⟩) :
    (TaskQueueClient.rMain 0 τ ∧ TaskQueueClient.rQueue τ) ∧
      safetyIris 0 (fun _ v => v = Flag.v1) τ :=
  TaskQueueClient.taskQueueClient_liveness_safety τ hbeh hfair hpos hinit

/-- Over the stable flag, the flag stays set once set. -/
example (τ : Trace Exp State) (hbeh : IsBehavior τ) (hfair : fairScheduling τ) (hpos : τ.pos = 0)
    (hinit : τ.seq 0 = ⟨(TaskQueueClient.tp0, TaskQueueClient.σ0), 0⟩) :
    (◇ₜ (∃ₜ x : Loc, FlagStable.flagStaysTr x)) τ :=
  TaskQueueFlagStableClient.taskQueueClient_flag_stays τ hbeh hfair hpos hinit

set_option linter.deprecated false in
example : @RocqLantana.queue.Queue_dequeue_spec = @Queue.dequeue_spec := rfl

set_option linter.deprecated false in
example : @RocqLantana.task_queue_client_adequacy =
    @TaskQueueClient.taskQueueClient_adequacy := rfl

/-! The specifications and the end-to-end corollaries depend only on the standard axioms. -/

/--
info: 'Lantana.Examples.Queue.enqueue_spec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Queue.enqueue_spec

/--
info: 'Lantana.Examples.Queue.dequeue_spec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Queue.dequeue_spec

/--
info: 'Lantana.Examples.TaskQueue.init_spec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TaskQueue.init_spec

/--
info: 'Lantana.Examples.TaskQueueClient.taskQueueClient_liveness_safety' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TaskQueueClient.taskQueueClient_liveness_safety

/--
info: 'Lantana.Examples.TaskQueueFlagStableClient.taskQueueClient_liveness_safety' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TaskQueueFlagStableClient.taskQueueClient_liveness_safety

/--
info: 'Lantana.Examples.TaskQueueFlagStableClient.taskQueueClient_flag_stays' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TaskQueueFlagStableClient.taskQueueClient_flag_stays

end LantanaTest.ExamplesQueue
