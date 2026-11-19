# Crashed threads and the thread node

A thread can stop taking part in a program without finishing: a process is killed, a machine
loses power.  Fair scheduling says nothing about such a thread, so it must owe nothing.  This
note is the overview of how Lantana handles it; the details are in `docs/model.md` (the
obligation model), `docs/program-logic.md` (the step and the lifting lemmas) and
`docs/adequacy.md` (the discharge rules and adequacy).  HeapLang never crashes: the notions
below are constant for it (`HeapLang.keepsCrashed`, `HeapLang.not_crashed`,
`Examples.init_threads`).

## 1. Crashed, finished, active

A language declares its crashed threads, from a thread's expression and the state:

```lean
class Crash (Expr State : Type) (Obs Val : outParam Type) [Language Expr State Obs Val] where
  crashed : Expr → State → Prop
  crashed_not_val {e : Expr} {σ : State} : crashed e σ → toVal e = none
```

A thread is *finished* when it is a value, *crashed* when `Cfg.Crashed ρ i`, and *active*
(`Cfg.Active i ρ`) when it is in the pool, not finished and not crashed.  Fair scheduling is
required of active threads only.  A crashed thread may still step, and may recover
(`docs/program-logic.md`, §1).

## 2. The node of a thread

| Piece | Meaning | Needed to |
|---|---|---|
| `thKids i K` | the children of `i` are exactly `K` | create, move or discharge a child |
| `thCarriers i B` | the bill: `B` contains the children of `i` | take a step |
| `thActive i` | the node of `i` is open | end the thread, hand the node in |
| `Th.done i` | the node is closed for good (persistent) | the postcondition of a finished thread |

A step pays one unit of fuel of each obligation of the bill.  Creating a child needs the
children and the bill; removing one needs the children alone, so other threads can share a
thread's children and only remove from them (`docs/model.md`, §2).

## 3. A crashed thread owns nothing

The model records which threads are crashed, and for each of them it holds the thread's node,
open and empty: nobody can create a child under it, so it owns no obligation, and its steps are
free (`docs/model.md`, §4).  The physical round of a step changes this crash map: it takes the node
of each thread the step crashes and gives back the node of each thread it recovers
(`step_physical`; `docs/model.md`, §5).

So a step that crashes a thread can be proved only by handing in that thread's node with no
children.  Before that, in the model update inside the physical round, the stepping thread
discharges every obligation below the node, or moves it under a thread that stays active.  It
does so after the step, where a formula such as "… or the worker is crashed" already holds:
this is why an obligation of a thread that another may crash carries such a disjunct, and why
its token and its children are kept where the other thread can reach them.

That update runs at the empty mask, so the invariants of the obligations are opened before the
step and closed after it, in pairwise disjoint namespaces.  The rules discharge a whole forest
of obligations, of any size and shape, in one update: `Obl.discharge_forest`,
`untilIGuar_acc_assigned_set`, `untilIGuar_discharge_opened_forest` and their forms for thread
roots (`docs/adequacy.md`, §4.1–§4.2).

## 4. Proofs

- **Steps.**  The usual lifting lemmas take `KeepsCrashed i e₁` (the step changes no thread's
  status); `lwp_lift_step_or_crashed` serves a thread that learns only at the step whether it
  is crashed; `lwp_lift_step_gen` and `lwp_lift_step_gen_si` serve steps that crash or recover
  threads (`docs/program-logic.md`, §3).
- **Adequacy.**  Every owner of an obligation is active: a finished thread owns nothing by its
  `Th.done`, a crashed one by the crash map of the model.  The premise of the adequacy theorems
  gives every initial thread its bill, and its node if it is not crashed (`docs/adequacy.md`,
  §5).
- **Example.**  `LantanaTest/Crash/` verifies a worker with any number of obligations, a killer
  that crashes it or gives up, and a reviver, end to end (`docs/adequacy.md`, §7).
