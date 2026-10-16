/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.Instances.Lib.GhostVar
public import Lantana.Algebra.ListOfSets
public import Lantana.Examples.TicketLock

/-! # A queue protected by a ticket lock, whose elements carry obligations

Rocq `examples/queue.v` (§7.2 of the paper; after Iron's queue and Transfinite Iris's
`eventloop.v`). The queue `((hptr, tptr), lock)` is a linked list of cells `some (x, next)`
ending with `none`, from `!hptr` to `!tptr`, protected by the ticket lock of
`Lantana.Examples.TicketLock` (which cannot be deleted: `isFairLockAlive`). `enqueue q x`
appends `x`, `dequeue q` removes the head (`none` when empty).

Each element `x` comes with a set `B` of obligations (and the client's resource `φ x B`).
While the element is in the queue, its obligations are children of the *inbox* `g` of the
worker, an obligation owned by the worker (`worker γ g`): enqueuing moves `B` from its parent
into the inbox, dequeuing moves it into a fresh container below the dequeuing thread.

## Ghost state (Rocq `queueG`)

* `γq`: the list of the elements and their obligations, a ghost variable of
  `List (Val × Oids)` (Iris-Lean's `GhostVarG`, which is Rocq's `dfrac_agreeR`), half in the
  invariant `queueInv` and half in the lock's resource `queueLock`;
* `γd`: the current inbox, a ghost variable of `Oid`, half in the invariant and half with the
  worker.

## The invariants

`queueInv ℓ γq γd` (a plain invariant, its content is ghost) holds the inbox `g` at layer `ℓ`
with exactly the obligations of the queued elements below it (pairwise disjoint sets,
`Lantana.Algebra.ListOfSets`), and the fuel of the obligations of the `n`-th element: `n + 1`
units at layer `ℓ.succ`, one for each move to a new inbox before it is dequeued. `queueLock`
is the lock's resource: the two pointers, the cells (`contents`) and the other half of `γq`.

## Specifications

All proved, with Rocq's statements (thread `i`, mask `⊤`, `∃ μ` in front): `init_spec`
(measure `20 + μ_init`), `enqueue_spec` and `dequeue_spec` (`100 + μ_acquire + μ_release`;
the callers' fuel is at layer `1` since the lock is at layer `0`); `isQueue_initialize`
installs the invariant once the worker's inbox exists. Rocq's layers `ℓ ⊕ 1` and `ℓ ⊕ 2` are
`ℓ.succ` and `ℓ.succ.succ`; Rocq's `inhabitant : oid` is `0`.

## Guarantees and traces

`guar_isQueue`, `guar_isQueueInit`: the queue guarantees what its lock does
(`aliveFairLockTrSpec`); `queue_release_progress`: every `enqueue` or `dequeue` that takes
the lock eventually releases it.

Everything here is proved.
-/

@[expose] public noncomputable section

namespace Lantana.Examples.Queue

open Iris Iris.BI Iris.Std Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.TicketLock (TicketLockG TicketLockName isFairLock isFairLockAlive
  lockToken aliveFairLockTrSpec ownAlive ownLayer vLock releaseProgress)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The program -/

/-- `λ _, let node := ref none; ((ref node, ref node), TicketLock.init ())` (the triple
`(hptr, tptr, lock)` of Rocq, nested to the left). -/
@[lantana_alias queue.Queue.init]
def init : Val :=
  hl_val(λ _, let node := ref(none()); ((ref(node), ref(node)), v(&TicketLock.init) #()))

/-- `λ q x, acquire; let t := !tptr; let newt := ref none; t ← some (x, newt); tptr ← newt;
release`. -/
@[lantana_alias queue.Queue.enqueue]
def enqueue : Val :=
  hl_val(λ q x,
    let lock := snd(q);
    v(&TicketLock.acquire) lock;
    let tptr := snd(fst(q));
    let t := !tptr;
    let newt := ref(none());
    t ← some((x, newt));
    tptr ← newt;
    v(&TicketLock.release) lock)

/-- `λ q, acquire; let h := !hptr; match !h with none => release; none
| some node => hptr ← snd node; free h; release; some (fst node)`. -/
@[lantana_alias queue.Queue.dequeue]
def dequeue : Val :=
  hl_val(λ q,
    let lock := snd(q);
    v(&TicketLock.acquire) lock;
    let hptr := fst(fst(q));
    let h := !hptr;
    match !h with
    | none() => v(&TicketLock.release) lock; none()
    | some(node) => hptr ← snd(node); free(h); v(&TicketLock.release) lock; some(fst(node)))

/-- The empty cell. -/
abbrev vNone : Val := hl_val(none())

/-- The cell holding `x`, followed by the cell at `l`. -/
abbrev vCell (x : Val) (l : Loc) : Val := hl_val(some((&x, #l)))

/-- The queue `((hptr, tptr), lock)`. -/
abbrev vQueue (lhptr ltptr : Loc) (tl : Val) : Val := hl_val(((#lhptr, #ltptr), &tl))

/-- The namespaces of the queue and of its invariant. -/
def N : Namespace := nroot.@"queue"
def Ni : Namespace := N.@"invariant"

/-! ## Ghost state -/

/-- The cameras of the queue (Rocq `queueGpreS`/`queueG`): the list of the queued elements with
their obligations, and the worker's inbox. Both are ghost variables (Rocq's
`dfrac_agreeR (list (val * oids))` is Iris-Lean's `GhostVarG`). -/
@[lantana_alias queue.queueG]
class QueueG (GF : BundledGFunctors) where
  [queueG : GhostVarG GF (List (Val × Oids))]
  [dataG : GhostVarG GF Oid]

attribute [reducible, instance] QueueG.queueG QueueG.dataG

#lantana_ignore queue.queueGpreS "`QueueG` serves before allocation (it has no ghost names)."
#lantana_ignore queue.«queueΣ» "Subsumed by the `BundledGFunctors` worlds (`Examples.ExGF`)."
#lantana_ignore queue.«subG_queueΣ» "Subsumed by the `BundledGFunctors` worlds (`Examples.ExGF`)."
#lantana_ignore queue.queueGpreS_queue "The field `QueueG.queueG`."
#lantana_ignore queue.queueGpreS_data_inG "The field `QueueG.dataG`."
#lantana_ignore queue.queue_inG "`QueueG` itself."

/-- The ghost names of a queue (Rocq `queue_γ`). -/
@[lantana_alias queue.queue_γ]
structure QueueName where
  /-- The ticket lock. -/
  tl : TicketLockName
  /-- The list of the queued elements. -/
  γq : GName
  /-- The worker's inbox. -/
  γd : GName

attribute [lantana_alias queue.QueueName] QueueName.mk
attribute [lantana_alias queue.queue_ticketlock_γ] QueueName.tl
attribute [lantana_alias queue.queue_γq] QueueName.γq
attribute [lantana_alias queue.queue_γd] QueueName.γd

/-! ## Definitions -/

section Defs
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLockG GF] [QueueG GF]

/-- A share of the list of queued elements (Rocq `qG_queue`). -/
@[lantana_alias queue.qG_queue]
def qgQueue (γ : GName) (l : List (Val × Oids)) (q : Qp) : IProp GF :=
  γ ↪VAR{.own q} l

/-- The worker owns its inbox, the obligation whose children are the obligations of the queued
elements: its name in the invariant and the right to discharge it (Rocq `queue_worker`). -/
@[lantana_alias queue.queue_worker]
def worker (γ : QueueName) (g : Oid) : IProp GF :=
  iprop((γ.γd ↪VAR{.own (1 : Qp).half} g) ∗ Obl.assigned g 1)

/-- The cells of the queue, from `lh` to `lt`, holding the elements `vs` (Rocq
`queue_contents`). -/
@[lantana_alias queue.queue_contents]
def contents (φ : Val → Oids → IProp GF) : List (Val × Oids) → Loc → Loc → IProp GF
  | [], lh, lt => iprop(⌜lh = lt⌝ ∗ lh ↦ some vNone)
  | (v, B) :: vs, lh, lt => iprop(∃ l : Loc, lh ↦ some (vCell v l) ∗ φ v B ∗ contents φ vs l lt)

/-- The invariant: the inbox `g` (at layer `ℓ`) has the obligations of the queued elements as
children, and the obligations of the `n`-th element have `n + 1` units of fuel at layer
`ℓ.succ` (Rocq `queue_inv`). -/
@[lantana_alias queue.queue_inv]
def queueInv (ℓ : Layer) (γq γd : GName) : IProp GF :=
  iprop(∃ (vs : List (Val × Oids)) (g : Oid), qgQueue γq vs (1 : Qp).half ∗
    (γd ↪VAR{.own (1 : Qp).half} g) ∗ ⌜disjointList (vs.map Prod.snd)⌝ ∗
    oblKids g (unionList (vs.map Prod.snd)) ∗ Wit.layer g ℓ ∗
    [∗list] n ↦ B ∈ vs.map Prod.snd, [∗set] b ∈ B, Obl.fuel b ℓ.succ ((n + 1 : Nat) : Measure))

/-- The resource of the lock: the pointers, the cells and the other half of the list (Rocq
`queue_lock`). -/
@[lantana_alias queue.queue_lock]
def queueLock (φ : Val → Oids → IProp GF) (γq : GName) (lhptr ltptr : Loc) : IProp GF :=
  iprop(∃ (lh lt : Loc) (vs : List (Val × Oids)), lhptr ↦ some hl_val(#lh) ∗
    ltptr ↦ some hl_val(#lt) ∗ qgQueue γq vs (1 : Qp).half ∗ contents φ vs lh lt)

/-- The queue `ql` (Rocq `is_queue`): its invariant, and its lock, which is alive and at
layer `0`. -/
@[lantana_alias queue.is_queue]
def isQueue (ql : Val) (γ : QueueName) (ℓ : Layer) (φ : Val → Oids → IProp GF) : IProp GF :=
  iprop(∃ (lhptr ltptr : Loc) (tl : Val), ⌜ql = vQueue lhptr ltptr tl⌝ ∧
    inv Ni (queueInv ℓ γ.γq γ.γd) ∗ (γ.tl ↪LOCK_AL{.discard}) ∗
    (γ.tl ↪LOCK_CF{.discard} 0) ∗ isFairLockAlive tl γ.tl (queueLock φ γ.γq lhptr ltptr))

/-- A queue whose invariant is not installed yet: this enables delayed initialization after
picking a worker thread (Rocq `is_queue_init`). -/
@[lantana_alias queue.is_queue_init]
def isQueueInit (ql : Val) (γ : QueueName) (φ : Val → Oids → IProp GF) : IProp GF :=
  iprop(∃ (lhptr ltptr : Loc) (tl : Val), ⌜ql = vQueue lhptr ltptr tl⌝ ∧
    qgQueue γ.γq [] (1 : Qp).half ∗ (γ.γd ↪VAR (0 : Oid)) ∗ (γ.tl ↪LOCK_AL{.discard}) ∗
    (γ.tl ↪LOCK_CF{.discard} 0) ∗ isFairLockAlive tl γ.tl (queueLock φ γ.γq lhptr ltptr))

omit [ModelGS GF] [HeapGS GF] [QueueG GF] in
/-- The discarded layer of a lock is persistent (Rocq: `↪LOCK_CF□` is persistent). -/
instance ownLayer_discard_persistent (γ : TicketLockName) (ℓ : Layer) :
    Persistent (ownLayer (GF := GF) γ ℓ .discard) := by
  unfold ownLayer; infer_instance

@[lantana_alias queue.is_queue_persistent]
instance isQueue_persistent (ql : Val) (γ : QueueName) (ℓ : Layer)
    (φ : Val → Oids → IProp GF) : Persistent (isQueue ql γ ℓ φ) := by
  unfold isQueue; infer_instance

end Defs

end Lantana.Examples.Queue
