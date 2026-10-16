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

omit [ModelGS GF] [TicketLockG GF] [QueueG GF] in
theorem contents_nil (φ : Val → Oids → IProp GF) (lh lt : Loc) :
    contents φ [] lh lt ⊣⊢ iprop(⌜lh = lt⌝ ∗ lh ↦ some vNone) := by
  rw [contents]
  exact .rfl

omit [ModelGS GF] [TicketLockG GF] [QueueG GF] in
theorem contents_cons (φ : Val → Oids → IProp GF) (v : Val) (B : Oids)
    (vs : List (Val × Oids)) (lh lt : Loc) :
    contents φ ((v, B) :: vs) lh lt ⊣⊢
      iprop(∃ l : Loc, lh ↦ some (vCell v l) ∗ φ v B ∗ contents φ vs l lt) := by
  rw [contents]
  exact .rfl

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

/-- What `dequeue` gives back, by the shape of its result (Rocq: the `match` in the
postcondition of `Queue_dequeue_spec`). The worker (`b = true`) gets a fresh inbox `ng` and
gives back its old inbox `wg`, now without children; a dequeued element comes with a fresh
container `g` of its obligations, a child of the thread. Rocq's `{[ng]} ∪ G` is
`G.insert ng` and `{[g; ng]} ∪ G` is `(G.insert g).insert ng`. -/
def dequeueRes (m : Measure) (b : Bool) (wg : Oid) (i : ThreadId) (G : Oids)
    (φ : Val → Oids → IProp GF) (γ : QueueName) (ℓ : Layer) : Val → IProp GF
  | .injL (.lit .unit) =>
    if b then iprop(∃ ng : Oid, thKids i (G.insert ng) ∗ ⌜ng ∉ G⌝ ∗ worker γ ng ∗
      oblKids wg ∅ ∗ Obl.assigned wg 1 ∗ Obl.fuel ng ℓ m)
    else thKids i G
  | .injR v => iprop(∃ (g : Oid) (B : Oids), φ v B ∗ oblKids g B ∗ Obl.assigned g 1 ∗
      Obl.fuel g ℓ m ∗ ⌜g ∉ G⌝ ∗
      if b then iprop(∃ ng : Oid, thKids i ((G.insert g).insert ng) ∗ ⌜ng ∉ G ∧ g ≠ ng⌝ ∗
        worker γ ng ∗ oblKids wg ∅ ∗ Obl.assigned wg 1 ∗ Obl.fuel ng ℓ m)
      else thKids i (G.insert g))
  | _ => iprop(False)

omit [HeapGS GF] [TicketLockG GF] in
/-- The result of `dequeue` is `none` or `some v`. -/
theorem dequeueRes_cases (m : Measure) (b : Bool) (wg : Oid) (i : ThreadId) (G : Oids)
    (φ : Val → Oids → IProp GF) (γ : QueueName) (ℓ : Layer) (x : Val) :
    dequeueRes m b wg i G φ γ ℓ x ⊢ ⌜x = vNone ∨ ∃ v, x = .injR v⌝ := by
  match x with
  | .injL (.lit .unit) => exact pure_intro (.inl rfl)
  | .injR v => exact pure_intro (.inr ⟨v, rfl⟩)
  | .lit _ | .rec_ _ _ _ | .pair _ _ | .injL (.lit (.int _)) | .injL (.lit (.bool _))
  | .injL (.lit .poison) | .injL (.lit (.loc _)) | .injL (.rec_ _ _ _) | .injL (.pair _ _)
  | .injL (.injL _) | .injL (.injR _) => exact false_elim

omit [ModelGS GF] [HeapGS GF] [TicketLockG GF] [QueueG GF] in
/-- A big separating conjunction over a list of sets gives one over their union. -/
theorem bigSepL_bigSepS_unionList (L : List Oids) (P : Oid → IProp GF) :
    ([∗list] B ∈ L, [∗set] b ∈ B, P b) ⊢ [∗set] b ∈ unionList L, P b := by
  induction L with
  | nil =>
    rw [unionList_nil]
    iintro -
    iapply BigSepS.bigSepS_empty.mpr
    iempintro
  | cons B L ih =>
    rw [unionList_cons]
    iintro H
    icases BigSepL.bigSepL_cons.mp $$ H with ⟨HB, HL⟩
    ihave HL := ih $$ HL
    iapply BigSepS.bigSepS_union_elim $$ HB HL

omit [HeapGS GF] [TicketLockG GF] [QueueG GF] in
/-- The fuel of the elements behind the head, which move up one position: one unit each pays
for their move to a new inbox. -/
theorem queueFuels_shift (L : List Oids) (ℓ : Layer) :
    ([∗list] n ↦ B ∈ L, [∗set] b ∈ B, Obl.fuel (GF := GF) b ℓ ((n + 1 + 1 : Nat) : Measure)) ⊢
      ([∗list] n ↦ B ∈ L, [∗set] b ∈ B, Obl.fuel b ℓ ((n + 1 : Nat) : Measure)) ∗
      ([∗list] B ∈ L, [∗set] b ∈ B, Obl.fuel b ℓ 1) :=
  (BigSepL.bigSepL_mono_of_forall fun {n _} =>
    (BigSepS.bigSepS_mono fun {b} _ =>
      (Obl.fuel_add_nat b ℓ (m₁ := n + 1) (m₂ := 1) rfl).mp).trans
      BigSepS.bigSepS_sep.mp).trans BigSepL.bigSepL_sep_eqv.mp

omit [ModelGS GF] [HeapGS GF] [QueueG GF] in
/-- The discarded layer of a lock is persistent (Rocq: `↪LOCK_CF□` is persistent). -/
instance ownLayer_discard_persistent (γ : TicketLockName) (ℓ : Layer) :
    Persistent (ownLayer (GF := GF) γ ℓ .discard) := by
  unfold ownLayer; infer_instance

@[lantana_alias queue.is_queue_persistent]
instance isQueue_persistent (ql : Val) (γ : QueueName) (ℓ : Layer)
    (φ : Val → Oids → IProp GF) : Persistent (isQueue ql γ ℓ φ) := by
  unfold isQueue; infer_instance

/-- Installing the invariant once the worker's inbox `g` (at layer `ℓ`, without children)
exists (Rocq `is_queue_initialize`). -/
@[lantana_alias queue.is_queue_initialize]
theorem isQueue_initialize (E : CoPset) (ql : Val) (γ : QueueName) (ℓ : Layer)
    (φ : Val → Oids → IProp GF) (g : Oid) :
    isQueueInit ql γ φ ⊢ oblKids g ∅ -∗ Wit.layer g ℓ -∗ Obl.assigned g 1 -∗
      |={E}=> isQueue ql γ ℓ φ ∗ worker γ g := by
  unfold isQueueInit
  iintro ⟨%lhptr, %ltptr, %tl, %hq, Q, Gd, #AL, #CF, #IFL⟩ Kg #Wg Ag
  imod ghost_var_update g $$ Gd with Gd
  icases TicketLock.ghostVar_halves _ _ $$ Gd with ⟨Gd, Gd0⟩
  imod inv_alloc Ni E (queueInv ℓ γ.γq γ.γd) $$ [Q Gd0 Kg] with #I
  · inext
    unfold queueInv
    iexists [], g
    simp only [List.map_nil, unionList_nil]
    iframe Q Gd0 Wg Kg
    isplitr
    · ipureintro
      exact disjointList_nil
    · iempintro
  imodintro
  unfold isQueue worker
  iframe Gd Ag
  iexists lhptr, ltptr, tl
  isplitr
  · ipureintro
    exact hq
  iframe I AL CF IFL

end Defs

/-! ## Specifications -/

section Specs
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLockG GF] [QueueG GF]

@[lantana_alias queue.Queue_init_spec]
theorem init_spec : ∃ μ : Measure, ∀ (lc : Fuel) (φ : Val → Oids → IProp GF) (i : ThreadId)
    (G : Oids) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&init) #()) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) }}}
        hl(v(&init) #()) @ i
      l{{{ (ql : Val) (γ : QueueName), RET ql; threadExpr i C hl(&ql) ∗ £ₒ lc ∗ thKids i G ∗
        isQueueInit ql γ φ }}} := by
  obtain ⟨μi, hi⟩ := TicketLock.init_spec (GF := GF)
  refine ⟨20 + μi, fun lc φ i G C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF⟩ HΦ
  icases (Obl.fuel_add_set G 0 20 μi).mp $$ HF with ⟨HF, Fi⟩
  ihave HF := oblFuels_init G 20 0 $$ HF
  unfold init
  lwp_step HT HG HF with Hlc : lc
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(allocn(#1, v(none()))) HT
  icases oblFuels_add 1 17 G $$ HF with ⟨HF1, HF⟩
  iapply lwp_alloc (o := 0) (G := G) (R := ∅) $$ [HT HG HF1]
  · iframe HT
    iapply stepPre_nil $$ HG HF1
  iintro %node ⟨HT, ⟨-, HG, -⟩, Hnode⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(v(&TicketLock.init) #()) HT
  iapply hi 0 0 i G ⊤ _ $$ [HT HG Fi]
  · iframe
  iintro %tl %γl ⟨HT, -, HG, AL, CF, Hmk⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  imod TicketLock.lock_alive_persist γl _ $$ AL with #AL
  imod TicketLock.lock_config_persist γl _ 0 $$ CF with #CF
  lwp_bind hl(allocn(#1, #node)) HT
  icases oblFuels_add 1 14 G $$ HF with ⟨HF1, HF⟩
  iapply lwp_alloc (o := 0) (G := G) (R := ∅) $$ [HT HG HF1]
  · iframe HT
    iapply stepPre_nil $$ HG HF1
  iintro %ltptr ⟨HT, ⟨-, HG, -⟩, Hlt⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_bind hl(allocn(#1, #node)) HT
  icases oblFuels_add 1 13 G $$ HF with ⟨HF1, HF⟩
  iapply lwp_alloc (o := 0) (G := G) (R := ∅) $$ [HT HG HF1]
  · iframe HT
    iapply stepPre_nil $$ HG HF1
  iintro %lhptr ⟨HT, ⟨-, HG, -⟩, Hlh⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  imod ghost_var_alloc (GF := GF) ([] : List (Val × Oids)) with ⟨%γq, Q⟩
  icases TicketLock.ghostVar_halves γq _ $$ Q with ⟨Q, Q0⟩
  imod ghost_var_alloc (GF := GF) (0 : Oid) with ⟨%γd, Gd⟩
  imod Hmk $$ %⊤ %(queueLock φ γq lhptr ltptr) [Hlh Hlt Hnode Q0] with #IFL
  · unfold queueLock qgQueue
    iexists node, node, []
    iframe Hlh Hlt Q0
    unfold contents
    iframe Hnode
    ipureintro
    rfl
  imod TicketLock.isFairLock_register_alive ⊤ tl γl _ (fun _ _ => CoPset.mem_full) $$ IFL AL
    with #IFLA
  iapply lwp_value'
  iapply HΦ $$ %(vQueue lhptr ltptr tl) %⟨γl, γq, γd⟩
  iframe HT Hlc HG
  unfold isQueueInit qgQueue
  iexists lhptr, ltptr, tl
  isplitr
  · ipureintro
    rfl
  iframe Q Gd AL CF IFLA

omit [ModelGS GF] [TicketLockG GF] [QueueG GF] in
/-- The last cell of the queue, and the cells with one more element once it is filled (Rocq
`queue_contents_enqueue`). -/
@[lantana_alias queue.queue_contents_enqueue]
theorem contents_enqueue (φ : Val → Oids → IProp GF) (vs : List (Val × Oids)) (lh lt : Loc) :
    contents φ vs lh lt ⊢ lt ↦ some vNone ∗
      (∀ (v : Val) (B : Oids) (l : Loc), lt ↦ some (vCell v l) -∗ φ v B -∗ l ↦ some vNone -∗
        contents φ (vs ++ [(v, B)]) lh l) := by
  induction vs generalizing lh with
  | nil =>
    unfold contents
    iintro ⟨%h, Hlh⟩
    subst h
    iframe Hlh
    iintro %v %B %l Hlt Hφ Hl
    simp only [List.nil_append]
    unfold contents
    iexists l
    iframe Hlt Hφ Hl
    ipureintro
    rfl
  | cons a vs ih =>
    obtain ⟨v, B⟩ := a
    unfold contents
    iintro ⟨%l, Hlh, Hφ, HC⟩
    icases ih l $$ HC with ⟨Hlt, Hacc⟩
    iframe Hlt
    iintro %v' %B' %l' Hlt Hφ' Hl'
    simp only [List.cons_append]
    unfold contents
    iexists l
    iframe Hlh Hφ
    iapply Hacc $$ Hlt Hφ' Hl'

/-- Enqueuing `x` with its obligations `B`: they move from their parent `p` into the worker's
inbox, each paying one unit of fuel at layer `ℓ.succ.succ`, which leaves room for one move per
element ahead (Rocq `Queue_enqueue_spec`). -/
@[lantana_alias queue.Queue_enqueue_spec]
theorem enqueue_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids) (p : Parent)
    (K B : Oids) (φ : Val → Oids → IProp GF) (γ : QueueName) (ℓ : Layer) (ql x : Val)
    (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&enqueue) v(&ql) v(&x)) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 1 μ) ∗ Par.kids p K ∗ ⌜B ⊆ K⌝ ∗
          ([∗set] b ∈ B, Obl.fuel b ℓ.succ.succ 1) ∗ φ x B ∗ isQueue ql γ ℓ φ }}}
        hl(v(&enqueue) v(&ql) v(&x)) @ i
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i G ∗
        Par.kids p (K \ B) }}} := by
  obtain ⟨μa, ha⟩ := TicketLock.acquire_spec (GF := GF)
  obtain ⟨μr, hr⟩ := TicketLock.release_spec (GF := GF)
  refine ⟨100 + μa + μr, fun lc i G p K B φ γ ℓ ql x C => ?_⟩
  rw [Ordinals.Ordinal.one_eq_succ_zero]
  iintro %Φ !> ⟨HT, HG, HF, HK, %hBK, HFB, Hφ, #IQ⟩ HΦ
  icases (Obl.fuel_add_set G _ (100 + μa) μr).mp $$ HF with ⟨HF, Fr⟩
  icases (Obl.fuel_add_set G _ 100 μa).mp $$ HF with ⟨HF, Fa⟩
  ihave HF := oblFuels_init G 100 _ $$ HF
  unfold isQueue
  icases IQ with ⟨%lhptr, %ltptr, %tl, %hql, #IQ, #AL, #CF, #IFLA⟩
  subst hql
  ihave #IFL := TicketLock.isFairLockAlive_isFairLock _ _ _ $$ IFLA
  unfold enqueue
  lwp_step HT HG HF with Hlc : lc +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc1⟩
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- Take the lock: the unlock obligation `κu` gets fuel for the critical section and release.
  lwp_bind hl(v(&TicketLock.acquire) v(&tl)) HT
  iapply ha 0 (((94 : Nat) : Measure) + μr) i G tl γ.tl .discard .discard 0
    (queueLock φ γ.γq lhptr ltptr) ⊤ (fun _ _ => CoPset.mem_full) _ $$ [HT HG Fa]
  · iframe HT HG Fa AL CF IFL
  iintro %κu ⟨HT, -, %hκu, HG, Kκ, Fκ, -, -, LT, HR⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  icases (Obl.fuel_add κu 0 _ _).mp $$ Fκ with ⟨Fκ, Fκr⟩
  ihave HF := oblFuels_add_obl G κu 0 _ $$ Fκ HF
  unfold queueLock
  icases HR with ⟨%lh, %lt, %vs, Plh, Plt, Q, QC⟩
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(!#ltptr) HT
  icases oblFuels_add 1 87 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_load (o := 0) (G := G.insert κu) (R := ∅) $$ [HT HG HF1 Plt]
  · iframe HT Plt
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, Plt⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(allocn(#1, v(none()))) HT
  icases oblFuels_add 1 83 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_alloc (o := 0) (G := G.insert κu) (R := ∅) $$ [HT HG HF1]
  · iframe HT
    iapply stepPre_nil $$ HG HF1
  iintro %newt ⟨HT, ⟨-, HG, -⟩, Pnewt⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- The physical enqueue.
  icases contents_enqueue φ vs lh lt $$ QC with ⟨Plt', QC⟩
  lwp_bind hl(#lt ← v(injr((&x, #newt)))) HT
  icases oblFuels_add 1 78 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_store (o := 0) (G := G.insert κu) (R := ∅) $$ [HT HG HF1 Plt']
  · iframe HT Plt'
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, Plt'⟩
  ihave QC := QC $$ %x %B %newt Plt' Hφ Pnewt
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(#ltptr ← #newt) HT
  icases oblFuels_add 1 75 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_store (o := 0) (G := G.insert κu) (R := ∅) $$ [HT HG HF1 Plt]
  · iframe HT Plt
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, Plt⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- The ghost enqueue, in the invariant: the obligations `B` move into the inbox, and the
  -- element gets `n + 1` units of fuel at layer `ℓ.succ` for its position `n`.
  ihave Hup : |={⊤}=>m (qgQueue γ.γq (vs ++ [(x, B)]) (1 : Qp).half ∗ Par.kids p (K \ B)) $$
    [Q HK HFB Hc1]
  · ihave Hacc := inv_acc (E := ⊤) (N := Ni) (P := queueInv ℓ γ.γq γ.γd)
      (fun _ _ => CoPset.mem_full) $$ IQ
    ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
    imod Hacc with ⟨Hinv, Hclose⟩
    ihave Hc1 := tlc_one_nat.mpr $$ Hc1
    iapply lc_mupd_add_later $$ Hc1
    inext
    unfold queueInv
    icases Hinv with ⟨%vs0, %g, Q0, Gd, %hdis, Kg, #Wg, Fq⟩
    unfold qgQueue
    ihave %h := ghost_var_agree _ _ _ _ _ $$ Q Q0
    subst h
    imod ghost_var_update_halves (vs ++ [(x, B)]) γ.γq vs vs $$ Q Q0 with ⟨Q, Q0⟩
    imod Obl.fuel_extend_set B (Ordinals.Ordinal.lt_succ ℓ.succ) (1 + ℵ) $$ HFB with HFB
    icases (Obl.fuel_add_set B _ 1 ℵ).mp $$ HFB with ⟨HFB1, HFBq⟩
    imod obl_move_obl_set (⊤ \ ↑Ni) p g K _ B ℓ hBK $$ Wg HK Kg [HFB1] with ⟨%hdisB, HK, Kg⟩
    · iapply BigSepS.bigSepS_impl $$ HFB1
      imodintro
      iintro %b %_ Hb
      iexists ℓ.succ
      iframe Hb
      ipureintro
      exact Ordinals.Ordinal.lt_succ ℓ
    imod Obl.fuel_mono_set B ℓ.succ (μ₁ := (((vs.map Prod.snd).length + 1 : Nat) : Measure))
      (Ordinals.Ordinal.le_of_lt (Measure.rep_large_lt _ _ _)) $$ HFBq with HFBq
    imod Hclose $$ [Q0 Gd Kg Fq HFBq] with -
    · inext
      iexists vs ++ [(x, B)], g
      iframe Q0 Gd Wg
      rw [List.map_append, unionList_append, List.map_singleton, unionList_singleton]
      isplitr
      · ipureintro
        refine disjointList_append_disjoint_iff.mpr ⟨hdis, disjointList_singleton B, ?_⟩
        rw [unionList_singleton]
        exact LawfulSet.disjoint_symm hdisB
      isplitl [Kg]
      · iapply Par.kids_congr _ $$ Kg
        intro z
        rw [LawfulSet.mem_union, LawfulSet.mem_union]
        exact Or.comm
      iapply BigSepL.bigSepL_snoc.mpr
      iframe Fq HFBq
    imodintro
    iframe Q HK
  imod Hup with ⟨Q, HK⟩
  -- Release, with the fuel of `G` (lowered to the lock's layer `0`) and of `κu`.
  imod Obl.fuel_layer_mono_set (ℓ₁ := 0) (ℓ₂ := Ordinals.Ordinal.succ 0) G μr
    (Ordinals.Ordinal.zero_le _) $$ Fr with Fr
  ihave Fr := (bigSepS_insert_oids (Φ := fun g => Obl.fuel g 0 μr) hκu).mpr $$ [Fκr Fr]
  · iframe Fκr Fr
  iapply hr 0 i (G.insert κu) tl γ.tl .discard (queueLock φ γ.γq lhptr ltptr) κu ⊤
    (fun _ _ => CoPset.mem_full) C $$ [HT HG Fr Kκ LT Plh Plt Q QC]
  · unfold queueLock
    iframe HT HG Fr Kκ LT AL IFL
    isplitr
    · ipureintro
      simp
    iexists lh, newt, vs ++ [(x, B)]
    iframe
  iintro ⟨HT, -, HG, -⟩
  iapply HΦ
  iframe HT Hlc HK
  iapply Par.kids_congr _ $$ HG
  intro z
  simp only [Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.mem_insert]
  grind

/-- Dequeuing. The worker (`b = true`, with its inbox `wg`) gets a fresh inbox `ng` (with fuel
`m`), into which the obligations of the remaining elements move, and gets back `wg` without
children; a dequeued element's obligations move into a fresh container `g` (with fuel `m`)
below the thread (Rocq `Queue_dequeue_spec`). -/
@[lantana_alias queue.Queue_dequeue_spec]
theorem dequeue_spec : ∃ μ : Measure, ∀ (lc : Fuel) (m : Measure) (b : Bool) (wg : Oid)
    (i : ThreadId) (G : Oids) (φ : Val → Oids → IProp GF) (γ : QueueName) (ℓ : Layer)
    (ql : Val) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&dequeue) v(&ql)) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 1 μ) ∗ (if b then worker γ wg else iprop(True)) ∗
          isQueue ql γ ℓ φ }}}
        hl(v(&dequeue) v(&ql)) @ i
      l{{{ (x : Val), RET x; threadExpr i C hl(&x) ∗ £ₒ lc ∗
        dequeueRes m b wg i G φ γ ℓ x }}} := by
  obtain ⟨μa, ha⟩ := TicketLock.acquire_spec (GF := GF)
  obtain ⟨μr, hr⟩ := TicketLock.release_spec (GF := GF)
  refine ⟨100 + μa + μr, fun lc m b wg i G φ γ ℓ ql C => ?_⟩
  rw [Ordinals.Ordinal.one_eq_succ_zero]
  iintro %Φ !> ⟨HT, HG, HF, HW, #IQ⟩ HΦ
  icases (Obl.fuel_add_set G _ (100 + μa) μr).mp $$ HF with ⟨HF, Fr⟩
  icases (Obl.fuel_add_set G _ 100 μa).mp $$ HF with ⟨HF, Fa⟩
  ihave HF := oblFuels_init G 100 _ $$ HF
  imod Obl.fuel_layer_mono_set (ℓ₁ := 0) (ℓ₂ := Ordinals.Ordinal.succ 0) G μr
    (Ordinals.Ordinal.zero_le _) $$ Fr with Fr
  unfold isQueue
  icases IQ with ⟨%lhptr, %ltptr, %tl, %hql, #IQ, #AL, #CF, #IFLA⟩
  subst hql
  ihave #IFL := TicketLock.isFairLockAlive_isFairLock _ _ _ $$ IFLA
  unfold dequeue
  lwp_step HT HG HF with Hlc : lc +ₕ 1 +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc2⟩
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc1⟩
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- Take the lock: the unlock obligation `κu` gets fuel for the critical section and release.
  lwp_bind hl(v(&TicketLock.acquire) v(&tl)) HT
  iapply ha 0 (((96 : Nat) : Measure) + μr) i G tl γ.tl .discard .discard 0
    (queueLock φ γ.γq lhptr ltptr) ⊤ (fun _ _ => CoPset.mem_full) _ $$ [HT HG Fa]
  · iframe HT HG Fa AL CF IFL
  iintro %κu ⟨HT, -, %hκu, HG, Kκ, Fκ, -, -, LT, HR⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  icases (Obl.fuel_add κu 0 _ _).mp $$ Fκ with ⟨Fκ, Fκr⟩
  ihave HF := oblFuels_add_obl G κu 0 _ $$ Fκ HF
  ihave Fr := (bigSepS_insert_oids (Φ := fun g => Obl.fuel g 0 μr) hκu).mpr $$ [Fκr Fr]
  · iframe Fκr Fr
  unfold queueLock
  icases HR with ⟨%lh, %lt, %vs, Plh, Plt, Q, QC⟩
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(!#lhptr) HT
  icases oblFuels_add 1 89 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_load (o := 0) (G := G.insert κu) (R := ∅) $$ [HT HG HF1 Plh]
  · iframe HT Plh
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, Plh⟩
  ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  cases vs with
  | nil =>
    icases (contents_nil φ lh lt).mp $$ QC with ⟨%hlt, Pl⟩
    subst hlt
    lwp_bind hl(!#lh) HT
    icases oblFuels_add 1 86 _ $$ HF with ⟨HF1, HF⟩
    iapply lwp_load (o := 0) (G := G.insert κu) (R := ∅) $$ [HT HG HF1 Pl]
    · iframe HT Pl
      iapply stepPre_nil $$ HG HF1
    iintro ⟨HT, ⟨-, HG, -⟩, Pl⟩
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    lwp_step HT HG HF
    lwp_step HT HG HF
    lwp_step HT HG HF
    lwp_expr_simp
    lwp_bind hl(v(&TicketLock.release) v(&tl)) HT
    cases b with
    | false =>
      iapply hr 0 i (G.insert κu) tl γ.tl .discard (queueLock φ γ.γq lhptr ltptr) κu ⊤
        (fun _ _ => CoPset.mem_full) _ $$ [HT HG Fr Kκ LT Plh Plt Q Pl]
      · unfold queueLock
        iframe HT HG Fr Kκ LT AL IFL
        isplitr
        · ipureintro
          simp
        iexists lh, lh, []
        iframe Plh Plt Q
        iapply (contents_nil φ lh lh).mpr
        iframe Pl
        ipureintro
        rfl
      iintro ⟨HT, -, HG, -⟩
      ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
      lwp_expr_simp
      ihave HG := Par.kids_congr (B := G) ?_ $$ HG
      · intro z
        simp only [Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.mem_insert]
        grind
      ihave HF := oblFuels_subset (B := G) _
        (fun z hz => Std.ExtTreeSet.mem_insert.mpr (.inr hz)) $$ HF
      lwp_step HT HG HF
      lwp_step HT HG HF
      lwp_expr_simp
      lwp_step HT HG HF
      iapply lwp_value'
      iapply HΦ
      iframe HT Hlc
      simp only [dequeueRes, Bool.false_eq_true, ite_false]
      iexact HG
    | true =>
      -- The worker renews its inbox: the old one `wg` has no children.
      simp only [↓reduceIte]
      unfold worker
      icases HW with ⟨Gw, Aw⟩
      ihave Hup : |={⊤}=>m (∃ ng : Oid, ⌜ng ∉ G.insert κu⌝ ∗
          thKids i ((G.insert κu).insert ng) ∗ oblKids wg ∅ ∗
          (γ.γd ↪VAR{.own (1 : Qp).half} ng) ∗ Obl.assigned ng 1 ∗
          Obl.fuel ng ℓ (m + ((83 : Nat) : Measure) + μr) ∗ qgQueue γ.γq [] (1 : Qp).half) $$
          [HG Gw Q Hc1]
      · ihave Hacc := inv_acc (E := ⊤) (N := Ni) (P := queueInv ℓ γ.γq γ.γd)
          (fun _ _ => CoPset.mem_full) $$ IQ
        ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
        imod Hacc with ⟨Hinv, Hclose⟩
        ihave Hc1 := tlc_one_nat.mpr $$ Hc1
        iapply lc_mupd_add_later $$ Hc1
        inext
        unfold queueInv
        icases Hinv with ⟨%vs0, %g, Q0, Gd, %hdis, Kg, #Wg, Fq⟩
        unfold qgQueue
        ihave %h := ghost_var_agree γ.γq [] _ vs0 _ $$ Q Q0
        subst vs0
        ihave %h := ghost_var_agree γ.γd wg _ g _ $$ Gw Gd
        subst g
        imod Obl.new (⊤ \ ↑Ni) (.thread i) (G.insert κu) ℓ (m + ((83 : Nat) : Measure) + μr)
          $$ [] HG with ⟨%ng, %hng, HG, Kng, Ang, Fng, #Wng⟩
        · iapply parLe_thread
        imod ghost_var_update_halves ng γ.γd wg wg $$ Gw Gd with ⟨Gw, Gd⟩
        imod Hclose $$ [Q0 Gd Kng Fq] with -
        · inext
          iexists [], ng
          iframe Q0 Gd Wng Fq
          isplitr
          · ipureintro
            exact disjointList_nil
          iapply Par.kids_congr _ $$ Kng
          intro z
          exact Iff.rfl
        imodintro
        iexists ng
        iframe HG Gw Ang Fng Q
        isplitr
        · ipureintro
          exact hng
        iapply Par.kids_congr _ $$ Kg
        intro z
        exact Iff.rfl
      imod Hup with ⟨%ng, %hng, HG, Kwg, Gw, Ang, Fng, Q⟩
      icases (Obl.fuel_add ng ℓ _ μr).mp $$ Fng with ⟨Fng, Fngr⟩
      icases (Obl.fuel_add ng ℓ m _).mp $$ Fng with ⟨Fng, Fng83⟩
      ihave HF := oblFuels_add_obl (G.insert κu) ng ℓ _ $$ Fng83 HF
      imod Obl.fuel_layer_mono (ℓ₁ := 0) ng μr (Ordinals.Ordinal.zero_le ℓ) $$ Fngr with Fngr
      ihave Fr := (bigSepS_insert_oids (Φ := fun g => Obl.fuel g 0 μr) hng).mpr $$ [Fngr Fr]
      · iframe Fngr Fr
      iapply hr 0 i ((G.insert κu).insert ng) tl γ.tl .discard (queueLock φ γ.γq lhptr ltptr)
        κu ⊤ (fun _ _ => CoPset.mem_full) _ $$ [HT HG Fr Kκ LT Plh Plt Q Pl]
      · unfold queueLock
        iframe HT HG Fr Kκ LT AL IFL
        isplitr
        · ipureintro
          simp
        iexists lh, lh, []
        iframe Plh Plt Q
        iapply (contents_nil φ lh lh).mpr
        iframe Pl
        ipureintro
        rfl
      iintro ⟨HT, -, HG, -⟩
      ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
      lwp_expr_simp
      ihave HG := Par.kids_congr (B := G.insert ng) ?_ $$ HG
      · intro z
        simp only [Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.mem_insert]
        grind
      ihave HF := oblFuels_subset (B := G.insert ng) _
        (fun z hz => by simp only [Std.ExtTreeSet.mem_insert] at hz ⊢; grind) $$ HF
      lwp_step HT HG HF
      lwp_step HT HG HF
      lwp_expr_simp
      lwp_step HT HG HF
      iapply lwp_value'
      iapply HΦ
      iframe HT Hlc
      simp only [dequeueRes, ↓reduceIte]
      iexists ng
      unfold worker
      iframe HG Gw Ang Kwg Aw Fng
      ipureintro
      intro h
      exact hng (Std.ExtTreeSet.mem_insert.mpr (.inr h))
  | cons a vs =>
    obtain ⟨v, B⟩ := a
    icases (contents_cons φ v B vs lh lt).mp $$ QC with ⟨%ln, Pl, Hφ, QC⟩
    lwp_bind hl(!#lh) HT
    icases oblFuels_add 1 86 _ $$ HF with ⟨HF1, HF⟩
    iapply lwp_load (o := 0) (G := G.insert κu) (R := ∅) $$ [HT HG HF1 Pl]
    · iframe HT Pl
      iapply stepPre_nil $$ HG HF1
    iintro ⟨HT, ⟨-, HG, -⟩, Pl⟩
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    lwp_step HT HG HF
    lwp_step HT HG HF
    lwp_step HT HG HF
    lwp_expr_simp
    lwp_step HT HG HF
    lwp_expr_simp
    lwp_bind hl(#lhptr ← #ln) HT
    icases oblFuels_add 1 81 _ $$ HF with ⟨HF1, HF⟩
    iapply lwp_store (o := 0) (G := G.insert κu) (R := ∅) $$ [HT HG HF1 Plh]
    · iframe HT Plh
      iapply stepPre_nil $$ HG HF1
    iintro ⟨HT, ⟨-, HG, -⟩, Plh⟩
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    lwp_step HT HG HF
    lwp_step HT HG HF
    lwp_expr_simp
    lwp_bind hl(free(#lh)) HT
    icases oblFuels_add 1 78 _ $$ HF with ⟨HF1, HF⟩
    iapply lwp_free (o := 0) (G := G.insert κu) (R := ∅) $$ [HT HG HF1 Pl]
    · iframe HT Pl
      iapply stepPre_nil $$ HG HF1
    iintro ⟨HT, ⟨-, HG, -⟩, -⟩
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    lwp_step HT HG HF
    lwp_step HT HG HF
    lwp_expr_simp
    -- The ghost dequeue, in the invariant: the obligations `B` of the head move from the inbox
    -- into a fresh container `g` below the thread, and the other elements move up one position
    -- (one unit of fuel each is left for a move to a new inbox).
    ihave Hup : |={⊤}=>m (∃ g : Oid, ⌜g ∉ G.insert κu⌝ ∗ thKids i ((G.insert κu).insert g) ∗
        oblKids g B ∗ Obl.assigned g 1 ∗ Obl.fuel g ℓ (m + ((76 : Nat) : Measure) + μr) ∗
        qgQueue γ.γq vs (1 : Qp).half ∗
        ([∗list] B' ∈ vs.map Prod.snd, [∗set] b ∈ B', Obl.fuel b ℓ.succ 1)) $$ [HG Q Hc1]
    · ihave Hacc := inv_acc (E := ⊤) (N := Ni) (P := queueInv ℓ γ.γq γ.γd)
        (fun _ _ => CoPset.mem_full) $$ IQ
      ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
      imod Hacc with ⟨Hinv, Hclose⟩
      ihave Hc1 := tlc_one_nat.mpr $$ Hc1
      iapply lc_mupd_add_later $$ Hc1
      inext
      unfold queueInv
      icases Hinv with ⟨%vs0, %g0, Q0, Gd, %hdis, Kg0, #Wg0, Fq⟩
      unfold qgQueue
      ihave %h := ghost_var_agree γ.γq ((v, B) :: vs) _ vs0 _ $$ Q Q0
      subst vs0
      obtain ⟨hdisB, hdis⟩ := disjointList_cons.mp hdis
      imod ghost_var_update_halves vs γ.γq _ _ $$ Q Q0 with ⟨Q, Q0⟩
      imod Obl.new (⊤ \ ↑Ni) (.thread i) (G.insert κu) ℓ (m + ((76 : Nat) : Measure) + μr)
        $$ [] HG with ⟨%g, %hg, HG, Kg, Ag, Fg, #Wg⟩
      · iapply parLe_thread
      simp only [List.map_cons, unionList_cons]
      icases BigSepL.bigSepL_cons.mp $$ Fq with ⟨FB, Fq⟩
      icases queueFuels_shift (vs.map Prod.snd) ℓ.succ $$ Fq with ⟨Fq, F1⟩
      imod obl_move_obl_set (⊤ \ ↑Ni) (.obl g0) g (B ∪ unionList (vs.map Prod.snd)) ∅ B ℓ
        LawfulSet.union_subset_left $$ Wg Kg0 Kg [FB] with ⟨-, Kg0, Kg⟩
      · iapply BigSepS.bigSepS_impl $$ FB
        imodintro
        iintro %b %_ Hb
        iexists ℓ.succ
        isplitr
        · ipureintro
          exact Ordinals.Ordinal.lt_succ ℓ
        · iexact Hb
      imod Hclose $$ [Q0 Gd Kg0 Fq] with -
      · inext
        iexists vs, g0
        iframe Q0 Gd Wg0 Fq
        isplitr
        · ipureintro
          exact hdis
        iapply Par.kids_congr _ $$ Kg0
        intro z
        rw [LawfulSet.mem_diff, LawfulSet.mem_union]
        constructor
        · rintro ⟨h | h, hn⟩
          · exact absurd h hn
          · exact h
        · intro h
          exact ⟨.inr h, fun hB => hdisB z ⟨hB, h⟩⟩
      imodintro
      iexists g
      iframe HG Ag Fg Q F1
      isplitr
      · ipureintro
        exact hg
      iapply Par.kids_congr _ $$ Kg
      intro z
      rw [LawfulSet.union_empty_right]
    imod Hup with ⟨%g, %hg, HG, Kg, Ag, Fg, Q, F1⟩
    icases (Obl.fuel_add g ℓ _ μr).mp $$ Fg with ⟨Fg, Fgr⟩
    icases (Obl.fuel_add g ℓ m _).mp $$ Fg with ⟨Fg, Fg76⟩
    ihave HF := oblFuels_add_obl (G.insert κu) g ℓ _ $$ Fg76 HF
    imod Obl.fuel_layer_mono (ℓ₁ := 0) g μr (Ordinals.Ordinal.zero_le ℓ) $$ Fgr with Fgr
    ihave Fr := (bigSepS_insert_oids (Φ := fun g => Obl.fuel g 0 μr) hg).mpr $$ [Fgr Fr]
    · iframe Fgr Fr
    lwp_bind hl(v(&TicketLock.release) v(&tl)) HT
    cases b with
    | false =>
      iapply hr 0 i ((G.insert κu).insert g) tl γ.tl .discard (queueLock φ γ.γq lhptr ltptr)
        κu ⊤ (fun _ _ => CoPset.mem_full) _ $$ [HT HG Fr Kκ LT Plh Plt Q QC]
      · unfold queueLock
        iframe HT HG Fr Kκ LT AL IFL
        isplitr
        · ipureintro
          simp
        iexists ln, lt, vs
        iframe Plh Plt Q QC
      iintro ⟨HT, -, HG, -⟩
      ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
      lwp_expr_simp
      ihave HG := Par.kids_congr (B := G.insert g) ?_ $$ HG
      · intro z
        simp only [Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.mem_insert]
        grind
      ihave HF := oblFuels_subset (B := G.insert g) _
        (fun z hz => by simp only [Std.ExtTreeSet.mem_insert] at hz ⊢; grind) $$ HF
      lwp_step HT HG HF
      lwp_step HT HG HF
      lwp_expr_simp
      lwp_step HT HG HF
      lwp_expr_simp
      lwp_step HT HG HF
      iapply lwp_value'
      iapply HΦ
      iframe HT Hlc
      simp only [dequeueRes, Bool.false_eq_true, ↓reduceIte]
      iexists g, B
      iframe Hφ Kg Ag Fg HG
      ipureintro
      intro h
      exact hg (Std.ExtTreeSet.mem_insert.mpr (.inr h))
    | true =>
      -- The worker renews its inbox: the remaining elements move from `wg` to the new inbox
      -- `ng`, each paying one unit of fuel.
      simp only [↓reduceIte]
      unfold worker
      icases HW with ⟨Gw, Aw⟩
      ihave Hup : |={⊤}=>m (∃ ng : Oid, ⌜ng ∉ (G.insert κu).insert g⌝ ∗
          thKids i (((G.insert κu).insert g).insert ng) ∗ oblKids wg ∅ ∗
          (γ.γd ↪VAR{.own (1 : Qp).half} ng) ∗ Obl.assigned ng 1 ∗
          Obl.fuel ng ℓ (m + ((76 : Nat) : Measure) + μr) ∗ qgQueue γ.γq vs (1 : Qp).half) $$
          [HG Gw Q Hc2 F1]
      · ihave Hacc := inv_acc (E := ⊤) (N := Ni) (P := queueInv ℓ γ.γq γ.γd)
          (fun _ _ => CoPset.mem_full) $$ IQ
        ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
        imod Hacc with ⟨Hinv, Hclose⟩
        ihave Hc2 := tlc_one_nat.mpr $$ Hc2
        iapply lc_mupd_add_later $$ Hc2
        inext
        unfold queueInv
        icases Hinv with ⟨%vs0, %g0, Q0, Gd, %hdis, Kg0, #Wg0, Fq⟩
        unfold qgQueue
        ihave %h := ghost_var_agree γ.γq vs _ vs0 _ $$ Q Q0
        subst vs0
        ihave %h := ghost_var_agree γ.γd wg _ g0 _ $$ Gw Gd
        subst g0
        imod Obl.new (⊤ \ ↑Ni) (.thread i) ((G.insert κu).insert g) ℓ
          (m + ((76 : Nat) : Measure) + μr) $$ [] HG with ⟨%ng, %hng, HG, Kng, Ang, Fng, #Wng⟩
        · iapply parLe_thread
        ihave F1 := bigSepL_bigSepS_unionList (vs.map Prod.snd)
          (fun b => Obl.fuel b ℓ.succ 1) $$ F1
        imod obl_move_obl_set (⊤ \ ↑Ni) (.obl wg) ng (unionList (vs.map Prod.snd)) ∅
          (unionList (vs.map Prod.snd)) ℓ LawfulSet.subset_refl $$ Wng Kg0 Kng [F1]
          with ⟨-, Kg0, Kng⟩
        · iapply BigSepS.bigSepS_impl $$ F1
          imodintro
          iintro %b %_ Hb
          iexists ℓ.succ
          isplitr
          · ipureintro
            exact Ordinals.Ordinal.lt_succ ℓ
          · iexact Hb
        imod ghost_var_update_halves ng γ.γd wg wg $$ Gw Gd with ⟨Gw, Gd⟩
        imod Hclose $$ [Q0 Gd Kng Fq] with -
        · inext
          iexists vs, ng
          iframe Q0 Gd Wng Fq
          isplitr
          · ipureintro
            exact hdis
          iapply Par.kids_congr _ $$ Kng
          intro z
          rw [LawfulSet.union_empty_right]
        imodintro
        iexists ng
        iframe HG Gw Ang Fng Q
        isplitr
        · ipureintro
          exact hng
        iapply Par.kids_congr _ $$ Kg0
        intro z
        rw [LawfulSet.diff_all]
      imod Hup with ⟨%ng, %hng, HG, Kwg, Gw, Ang, Fng, Q⟩
      icases (Obl.fuel_add ng ℓ _ μr).mp $$ Fng with ⟨Fng, Fngr⟩
      icases (Obl.fuel_add ng ℓ m _).mp $$ Fng with ⟨Fng, Fng76⟩
      ihave HF := oblFuels_add_obl ((G.insert κu).insert g) ng ℓ _ $$ Fng76 HF
      imod Obl.fuel_layer_mono (ℓ₁ := 0) ng μr (Ordinals.Ordinal.zero_le ℓ) $$ Fngr with Fngr
      ihave Fr := (bigSepS_insert_oids (Φ := fun g => Obl.fuel g 0 μr) hng).mpr $$ [Fngr Fr]
      · iframe Fngr Fr
      iapply hr 0 i (((G.insert κu).insert g).insert ng) tl γ.tl .discard
        (queueLock φ γ.γq lhptr ltptr) κu ⊤ (fun _ _ => CoPset.mem_full) _ $$
        [HT HG Fr Kκ LT Plh Plt Q QC]
      · unfold queueLock
        iframe HT HG Fr Kκ LT AL IFL
        isplitr
        · ipureintro
          simp
        iexists ln, lt, vs
        iframe Plh Plt Q QC
      iintro ⟨HT, -, HG, -⟩
      ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
      lwp_expr_simp
      ihave HG := Par.kids_congr (B := (G.insert g).insert ng) ?_ $$ HG
      · intro z
        simp only [Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.mem_insert]
        grind
      ihave HF := oblFuels_subset (B := (G.insert g).insert ng) _
        (fun z hz => by simp only [Std.ExtTreeSet.mem_insert] at hz ⊢; grind) $$ HF
      lwp_step HT HG HF
      lwp_step HT HG HF
      lwp_expr_simp
      lwp_step HT HG HF
      lwp_expr_simp
      lwp_step HT HG HF
      iapply lwp_value'
      iapply HΦ
      iframe HT Hlc
      simp only [dequeueRes, ↓reduceIte]
      iexists g, B
      iframe Hφ Kg Ag Fg
      isplitr
      · ipureintro
        intro h
        exact hg (Std.ExtTreeSet.mem_insert.mpr (.inr h))
      iexists ng
      unfold worker
      iframe HG Gw Ang Kwg Aw Fng
      ipureintro
      simp only [Std.ExtTreeSet.mem_insert] at hng
      grind

end Specs

end Lantana.Examples.Queue
