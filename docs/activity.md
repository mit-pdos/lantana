# Crashed threads and the thread node

A thread can stop taking part in a program without finishing: a process is killed, a machine
loses power.  Fair scheduling says nothing about such a thread, so it must owe nothing.  This
note describes how a language declares its crashed threads, what the obligation logic keeps for
each thread, and what a proof does at a step that crashes or recovers one.  HeapLang never
crashes; for it the notions below are constant and the lemmas that mention them are discharged
once (`HeapLang.keepsCrashed`, `HeapLang.not_crashed`, `Examples.initThreads`).

| Where | What |
|---|---|
| `ProgramLogic/Language.lean` | `class Crash`: the crashed threads of a language |
| `ProgramLogic/Configuration.lean` | `Cfg.crashed`, `Cfg.active`, `Cfg.staysCrashed`, convexity of activity |
| `BaseLogic/Model/OForest.lean`, `MUpd.lean` | the forest at a view, the bill, the rounds of a step |
| `ProgramLogic/OblForest.lean` | the sealed interface: `thKids`, `thCarriers`, `thActive`, `Th.done`, `step_progress`, `step_physical` |
| `ProgramLogic/WeakestPre.lean`, `Lifting.lean` | `lwpStep`, the lifting lemmas, `KeepsCrashed` |
| `Trace/Adequacy/Step.lean`, `Temporal.lean` | the owners of obligations are active; the premise of adequacy |

## 1. Crashed, finished, active

A language says which threads are crashed, from a thread's own expression and the state:

```lean
class Crash (Expr State : Type) (Obs Val : outParam Type) [Language Expr State Obs Val] where
  crashed : Expr → State → Prop
  crashed_not_val {e : Expr} {σ : State} : crashed e σ → toVal e = none
```

`Cfg.crashed ρ i` holds when thread `i` of the pool of `ρ` is crashed.  A thread is *finished*
when it is a value, and a finished thread is not crashed.  A thread is *active*
(`Cfg.active i ρ`) when it is in the pool, not finished and not crashed.

Fair scheduling (`fairScheduling`) is the strong fairness of each thread's scheduling action,
enabled where the thread is active: it demands nothing for a crashed thread.  A crashed thread
still has the steps the language gives it, and may be scheduled; a crashed thread may also
recover, that is, be active again later.  Activity is convex, and fair scheduling is the usual
weak fairness, for a thread that stays crashed once it is (`Cfg.staysCrashed`,
`Cfg.sched_sf_iff_wf`).

## 2. The node of a thread, in three pieces

Every live obligation is a child of a thread or of another obligation.  For a thread `i`:

| Piece | Meaning | Used to |
|---|---|---|
| `thKids i K` | the children of `i` are exactly `K` | create, move or discharge a child |
| `thCarriers i B` | the bill: `B` contains the children of `i` | take a step (`step_progress`) |
| `thActive i` | the thread's node is open | end the thread (`Th.terminate`), hand the node in |
| `Th.done i` | the node is closed for good (persistent) | the postcondition of a finished thread |

A step of `i` costs one unit of fuel of each obligation of its bill.  Creating a child under
`i` needs the children and the bill, and adds the child to both (`Obl.new`, `Obl.move`,
`Obl.move_up`, with `Par.bill p B`, which is the bill for a thread and nothing for an
obligation).  Removing a child needs the children alone, so the bill may be larger than the
children: `Th.carriers_resync` brings it back to the children, and
`Th.carriers_erase_discharged` drops a discharged obligation from it.  The children of a thread
can therefore be shared with other threads, which can only remove from them, while the thread
keeps its bill.

## 3. What the model knows of the pool

The obligation model keeps its own view of the pool: the thread count `tc` and the crashed bits
`X : ThreadId → Prop`.  **For a thread whose bit is set, the forest itself holds the thread's
node, `thActive i ∗ thKids i ∅`.**  Nobody else can then create a child under it, so a crashed
thread owns no obligation (`Th.crashed_modelInterp_not_owner`).

Model updates (`|=[n]=>m` and `|={E}=>m`) neither read nor change the view: a round takes the
model at any view and gives it back at the same one, so the updates carry only the position `n`.
Two things mention the view:

- the progress round `mprog n tc X i` reads it: a thread pays its bill (`step_progress`), and a
  thread whose bit is set pays nothing (`step_progress_crashed`);
- the physical round `mphys n₁ n₂ tc₁ tc₂ X₁ X₂` changes it.

## 4. A step

One step of `lWP` for thread `i` (`lwpStep`), from the configuration `ρ₁` to `ρ₂`:

1. a model update at position `n`;
2. the progress round, at the view of `ρ₁`;
3. the physical round, from the view of `ρ₁` to the view of `ρ₂`, in three stages:
   - the model moves to position `n + 1` and to the new thread count; the forked threads'
     pieces come out; the later credits of the step are granted;
   - a model update at `n + 1`, with the bits of `ρ₁`;
   - the bits change: the nodes of the threads crashed in `ρ₂` and not in `ρ₁` go in, the nodes
     of the threads crashed in `ρ₁` and not in `ρ₂` come out (`step_physical`; `step_fork`
     when the bits are the same);
4. a model update at `n + 1`;
5. the invariants are closed.

So a step that leaves a thread crashed can be proved only by handing in that thread's node,
open and empty.  The thread that takes the step must first discharge the obligations below the
node, or move them under a thread that stays active; it does so in the update of stage 3, at
the new position, where a formula such as "… or the worker is crashed" already holds.  This is
why an obligation of a thread that may be crashed by another carries such a disjunct, and why
its token and its children are kept where the other thread can reach them.

A step that recovers a thread receives its node, and can put obligations under it again.

## 5. Lifting lemmas

- `lwp_lift_step` and the lemmas derived from it (atomic, base, pure) are for a step that
  keeps every thread's status, `KeepsCrashed i e₁`: for every context, pool and step,
  `Cfg.crashed ρ₂ = Cfg.crashed ρ₁`.  In a language that never crashes this is
  `KeepsCrashed.of_never`.
- `lwp_lift_step_crashed` is the same for a thread that is crashed in the current
  configuration: it takes its bill, pays nothing, and gets the bill back empty.
- `lwp_lift_step_gen` is the general one: the stepping thread pays its bill or is crashed, and
  after the step it hands in the nodes of the threads the step crashes and receives those of
  the threads it recovers.

## 6. Adequacy

The adequacy theorems (`lwp_adequacy_temporal`, `lwp_adequacy_safety`) keep the model at the
view of the current configuration.  Their measure decreases at a step because every owner of an
obligation is active (`getOblsThreadActive`): a finished thread owns nothing by its `Th.done`,
a crashed one by its bit.  The model is allocated at the crashed threads of the initial
configuration, so the premise hands every initial thread `j` its bill `thCarriers j ∅`, and its
node `thActive j ∗ thKids j ∅` if it is not crashed; `initThreads_of_not_crashed` gives the
plain list when no thread is.
