# The program logic

The program logic of Lantana is a weakest precondition `lWP` for one thread of a language with a
thread pool, in which every step pays for the obligations of the thread.  This note describes
the configurations and their steps, one step of `lWP` and its evaluation contexts, the lifting
lemmas, HeapLang's laws, and the tactics that take HeapLang's steps.  What a step does to the
obligation model (the rounds, the nodes of crashed threads) is described in `docs/model.md`,
§4–§5.

| module | contents |
|---|---|
| `ProgramLogic/Language.lean` | `Crash`; additions to Iris-Lean's language interface (§1) |
| `ProgramLogic/Configuration.lean` | configurations, thread steps, activity (§1) |
| `ProgramLogic/WeakestPre.lean` | `lWP`, its step `lwp.step`, its rules (§2), `lwp_bind` (§2.1) |
| `ProgramLogic/Lifting.lean`, `EctxLifting.lean` | the lifting lemmas (§3) |
| `HeapLang/Instances.lean` | HeapLang as a language, its class instances (§4) |
| `HeapLang/Context.lean` | the evaluation contexts of `lWP` against HeapLang's context items (§4) |
| `HeapLang/PrimitiveLaws.lean` | HeapLang's ghost state, the token, the primitive laws (§4) |
| `HeapLang/ProofMode.lean` | the step tactics (§5) |

## 1. Configurations, thread steps and activity

Languages are Iris-Lean's (`Language`, `EctxLanguage`, `EctxItemLanguage`), used as they are,
and the program logic (`lWP`, the lifting lemmas, adequacy) needs a `Language` only.
`Language.lean` records the Rocq declarations that Iris-Lean provides and adds four things.  A
language declares its crashed threads by the class `Crash`: whether the thread running an
expression is crashed in a state, which is never the case for a value.
`Stuckness.MaybeReducible s (e, σ)` is the reducibility that the stuckness `s` requires: a step for
`NotStuck`, nothing for `MaybeStuck`.  For the evaluation contexts, which are the functions
`K : Expr → Expr` with Iris-Lean's `Language.Context K` (§2.1), it adds their composition
`Language.Context.comp` and two lemmas on contexts that agree before a step,
`Language.Context.exists_eq_of_primStep` and `eq_of_primStep`; they are proposed for Iris-Lean
in `docs/iris-lean-proposal.md`, §7.  Last, `EctxItemLanguage.fill_ctx_step_inj`: an expression
that can step determines the list of context items around it.

A configuration `Cfg Expr State` is a thread pool, `List Expr`, and a state; a thread id is a
position in the pool.  A step of thread `i` (`ThreadStep i`) is Iris-Lean's `primStep` of its
expression, with any observation: it replaces the expression and appends the forked threads,
which so get fresh ids (Rocq's `fork_thread_ids` is not needed).  Entries are never removed
(`Cfg.isSome_mono`) and a value is never rewritten (`TraceStep.get?_of_val`).  A trace step
`TraceStep i` is a step, or a stutter when the thread is a value (`ThreadDone`) or stuck
(`ThreadStuck`): stuck executions are behaviors too, and adequacy shows that a verified program
never takes a stuck step.

Thread `i` is crashed at `ρ` (`Cfg.Crashed ρ i`) when it is in the pool and the language declares
its expression crashed in the state of `ρ`.  The configuration comes first so that
`Cfg.Crashed ρ : ThreadId → Prop` is the set of crashed threads that the obligation model keeps
as its view of the pool (`docs/model.md`, §4).  A step *keeps the statuses* when
`Cfg.Crashed ρ₂ = Cfg.Crashed ρ₁`, which `Cfg.crashed_eq_of_iff` proves pointwise; in a language
that never crashes every step does (`Cfg.crashed_eq_of_never`).

Thread `i` is active (`Cfg.Active i ρ`) when it is in the pool, not a value and not crashed, and
inactive (`Cfg.Inactive`) otherwise.  The configurations form a thread system (`ThreadSystem`,
`docs/temporal.md`) whose step of thread `i` is `TraceStep i` and whose activity is
`Cfg.Active i`; traces carry no thread label, and the adequacy proof chooses the schedule.

A crashed thread may recover, so activity is not convex in general.  It is convex along a run on
which thread `i`, once crashed, stays crashed (`Cfg.StaysCrashed`, which holds in a language that
never crashes): the thread is active from its fork until it becomes a value or crashes, and
never again (`Cfg.active_convex`).  The proof rests on an inactive thread of the pool staying
inactive, since a value is never rewritten and a crashed thread stays crashed
(`Cfg.inactive_of_step_of_isSome`); the thread must be in the pool, because a fork may fill a
missing entry.  On behaviors this is `Cfg.convex_of_isBehavior`, and there fair scheduling
(`fairScheduling`, the strong fairness of each thread's scheduling action) is weak fairness
(`Cfg.sched_strongFair_iff_weakFair`).

## 2. `lWP` and the phases of a step

The ghost state of the program logic, `LantanaGS`, is the temporal layer, a state interpretation
`stateInterp σ tp` and the postcondition `forkPost` of forked threads (`True` for HeapLang).
`lWP e @ s; i; E {{ Φ }}` is the weakest precondition of the expression `e` run by thread `i`.
It is the least fixpoint of `lwp.pre` (`lwp.Internal.lfp`, over the uncurried arguments of
`lwp.Internal.pre'`), as in Iris-Lean's `TotalWeakestPre`, and it is not sealed: `lwp_unfold`
unfolds it and `lwp_ne` is its non-expansiveness.  `lwp.pre` gives the postcondition of a value
under a model update, `|={E}=>m Φ v`; otherwise one step `lwp.step`, after which the thread
continues with `lWP` and each forked thread `len + j` runs with the postcondition
`lwp.liftTerm (len + j) forkPost`, that is `Th.done (len + j) ∗ forkPost (len + j) v`: a forked
thread closes its node before it ends.

`lwp.step s i E e₁ ν` quantifies over every evaluation context `K : Expr → Expr` (with
`Language.Context K`) and every pool `tp` in which thread `i` runs `K e₁` (§2.1).  For a history
`h`, a position `n` and a state `σ₁`, the step runs in phases:

1. the invariants are opened, `historyTInterp h n σ₁ tp ={E,∅}=∗`;
2. a model update at position `n`, `|=[n]=>m`, which may discharge an until and which proves
   `s.MaybeReducible (e₁, σ₁)`;
3. for every step of `e₁` to `e₂` that forks the threads `efs`, with any observation, the
   progress round `mprog` at the view of the old configuration (its thread count and its crashed
   threads `Cfg.Crashed (tp, σ₁)`), where the thread pays its bill, or nothing if it is crashed;
4. the physical round `mphys` from that view to the view of the new configuration: the model
   moves to position `n + 1`, the forked threads' pieces come out and the later credits of the
   step are granted, a model update runs, and the crashed threads change;
5. a model update at position `n + 1`;
6. the invariants are closed with the history extended by the new configuration, and
   `ν e₂ tp.length efs` holds: the forked threads have the ids `tp.length`, `tp.length + 1`, ….

What the rounds do to the model is in `docs/model.md`, §5.  Compared with Iris-Lean's
weakest preconditions, `lWP` thus has a thread id, sees the history, quantifies over the context
of the thread, runs the rounds of the obligation model between model updates, and ignores
observations.

Induction on `lWP`, `lwp_ind_strong`, takes any predicate `Ψ`, non-expansive or not.  It applies
the induction principle of the least fixpoint to the closure `fun x => ∀ y, x ≡ y → Ψ y`, which
is non-expansive, and a rewriting along the internal equality brings each case back to `Ψ`
(`lwp.Internal.lfp_ind_strong`).  `lwp_ind` is its form without the fixpoint in the hypothesis.

The rules are those of a weakest precondition: the updates around `lWP` (`fupd_lwp`, `mupd_lwp`,
`lwp_fupd`, `lwp_mupd`), monotonicity (`lwp_strong_mono_mupd`, from which the other forms
follow), `lwp_bind` (§2.1), the atomic rule `lwp_atomic_mupd`, framing and the wands, and the
later credits (`lwp_credit_later` for a transfinite credit `£ₒ 1`, `lwp_credit_laterN`).  Rocq's
`sfmupd` is `mupd` in the Lean names, and there are no `Proper` instances, only a `NonExpansive`
instance and dist lemmas.  The proof-mode instances, after Iris-Lean's `WeakestPre`, frame into
the postcondition, eliminate fancy, basic and model updates in front of `lWP` (mask-changing ones
in front of an atomic expression, with error messages for a wrong mask), and open accessors
(`ElimAcc`).

### 2.1 Evaluation contexts

An evaluation context is a function `K : Expr → Expr` with Iris-Lean's `Language.Context K`:
`K e` is not a value when `e` is not, a step of `e` is a step of `K e`, and every step of `K e`,
for `e` not a value, is a step of `e`.  The identity is a context (`Language.instContext_id`),
contexts compose (`Language.Context.comp`), and the evaluation contexts of an `EctxLanguage` are
contexts (`EctxLanguage.instContextFill`).  This is the notion of Iris-Lean's `wp_bind`, and
`lwp_bind` is stated in the same way:

```lean
theorem lwp_bind (K : Expr → Expr) [Language.Context K] :
    lWP e @ s; i; E {{ v, lWP (K v) @ s; i; E {{ Φ }} }} ⊢ lWP (K e) @ s; i; E {{ Φ }}
```

Iris-Lean's weakest preconditions do not mention contexts in their definition, because their
state interpretation does not see the expressions of the threads.  Lantana's does: the history
holds the pools, and a language may hold the pool in its state interpretation.  So a step says
where the expression is in the pool: `lwp.step` quantifies over every context `K` and every pool
with `tp[i]? = some (K e₁)`, and the pool after the step holds `K e₂`.  `lwp_bind K` composes
the context of the step with `K`, and adequacy takes the step at the context `id`
(`threadRun_step`).  In Rocq, a language has its own type of contexts (`ctx`,
`LanguageCtxMixin`), over which `lwp_step` quantifies; here a language has no such type, as in
Iris-Lean, and the program logic needs nothing beyond `Language`.

**What a language owes.**  A law of a language is proved for every context, also for the
functions that no program puts around an expression.  A law that does not look at the expression
of the thread in the pool never uses `K`.  A law that does must know `K e₂` from what it knows
of `K e₁`.  This is the case of a state interpretation that holds the pool (HeapLang's token of
the thread's expression, §4; the class `PureExecSI`, §3), and of the crashed threads of a
language whose threads crash, since `Cfg.Crashed` reads the expression in the pool
(`KeepsCrashed`, §3).  The laws of a context give it up to the choice of the result:

- two contexts that agree on `e₁` agree on the result of a step of `e₁` up to the results with
  the same observations, state and forked threads (`Language.Context.exists_eq_of_primStep`);
- so they agree on it when these determine the result (`Language.Context.eq_of_primStep`), which
  covers a deterministic step and a step whose choice the state records;
- for its other steps, a language proves it from its semantics: HeapLang for `chooseNat`
  (`HeapLang.context_eq_fill_of_primStep`, §4), and the crashing test language by showing that
  its only context is the identity (`LantanaTest.Crash.context_eq_id`, `docs/adequacy.md`, §7).

**Limits.**  `lwp.step` quantifies over more contexts than the derivations use: adequacy starts
at `id` and each `lwp_bind` composes with the context it is given, so only compositions of bound
contexts occur.  Two things follow.

- Such a proof is about the language, not about the step: HeapLang's law for `chooseNat` holds
  because the language can also read the heap (§4).
- A language could have two contexts that agree on an expression and differ on a result of its
  step, with no other expression to tell them apart.  A law that follows the thread across that
  step is then not provable, even if every derivation binds at only one of the two.  No
  language of the development is of this kind.

Both come from quantifying over all contexts, and the forms without them choose the contexts
otherwise.  One is a class of contexts that the language declares, as Rocq's `ctx`: for an
Iris-Lean `EctxLanguage` with its own contexts, two contexts that agree on an expression agree
after each of its steps (by `EctxLanguage.base_redex_unique`), so its laws owe nothing; the
logic then has a parameter, and its bind is not Iris-Lean's.  The other makes the context an
argument of `lWP`, which every specification then names.  Lantana keeps Iris-Lean's contexts.

## 3. The lifting lemmas

The lifting lemmas turn the steps of the language into rules of `lWP`, after Iris-Lean's
`Lifting` and `EctxLifting`, and each step carries the obligation interface.  A step of thread `i`
takes its bill `thCarriers i G` with one unit of fuel of each obligation of the bill,
`Obl.fuels G 1`, and the layers `Wit.layers R` of a set `R` of witnesses.  It gives back the bill, a
credit to each witness (`Wit.creds R`), later credits (`alc`), and to each forked thread `j` its
running handle `thActive j`, no children `thKids j ∅` and an empty bill `thCarriers j ∅`.

The lemmas come at two levels.  `lwp_lift_step_gen`, `lwp_lift_step_or_crashed`,
`lwp_lift_step` and `lwp_lift_step_crashed` see the history and the position,
`historyTInterp h n σ₁ tp`, and take a model update before and after the step.  The others see
only the state interpretation and take no model update around the step.  The lemmas of a step
other than `lwp_lift_step_gen` and `lwp_lift_step_gen_si` take the hypothesis
`KeepsCrashed i e₁`: every step of `i` from `e₁`, in any context and any pool, keeps the
statuses.  It holds in a language that never crashes (`KeepsCrashed.of_never`;
`HeapLang.keepsCrashed`).

Which lemma to use:

- A step of a running thread that keeps the statuses: `lwp_lift_step_si`, or `lwp_lift_step`
  for a proof that needs the history or a model update around the step; `lwp_lift_atomic_step`
  for a step to a value.
- A step of a thread crashed in the current configuration: `lwp_lift_step_crashed`.  The thread
  takes its bill, pays nothing and gets the bill back empty.
- A step of a thread that learns only at the step whether it is crashed, because another thread
  may crash it: `lwp_lift_step_or_crashed`.  Having seen the configuration, the thread pays its
  bill or steps for free.
- A step that crashes or recovers threads: `lwp_lift_step_gen_si`, or `lwp_lift_step_gen`.
  After the step, the thread hands in the nodes (`Th.nodes`) of the threads the step crashes and
  receives those of the threads it recovers.  In `lwp_lift_step_gen_si` this happens in a model
  update at the empty mask inside the physical round, run against the history of the new
  configuration, where a thread can discharge obligations whose formulas hold only after the
  step, with their invariants opened before it (`docs/activity.md`, §3).
- A stuck thread, for `MaybeStuck`: `lwp_lift_stuck`, `lwp_lift_pure_stuck`.
- Pure steps: `lwp_lift_pure_step_no_fork`, `lwp_lift_pure_det_step_no_fork`, `lwp_pure_step`,
  `lwp_pure_step_simple` (below).

For an `EctxLanguage`, `EctxLifting.lean` states these lemmas with base steps and base
reducibility (`lwp_lift_base_step`, `lwp_lift_atomic_base_step`,
`lwp_lift_atomic_base_step_no_fork`, `lwp_lift_pure_det_base_step_no_fork`, the stuck forms).
They hand the law every context `K` of `lwp.step`, with `Language.Context K`, not only the
evaluation contexts of the language (§2.1).  `lwp_bind_fill` binds at an evaluation context of
the language, which is a context (`EctxLanguage.instContextFill`).

A pure step changes the expression of the thread, which the state interpretation may know:
HeapLang's holds the pool, and the thread holds a token of its own expression.  The class
`PureExecSI ς i` says that a pure step of thread `i`, in any context, updates the token `ς i e`
and the state interpretation together.  The pure lemmas take the safety condition
`Stuckness.PureSafe`, Rocq's inline condition: reducible for `NotStuck`, not a value for
`MaybeStuck`.
`lwp_lift_pure_step_no_fork` and `lwp_lift_pure_det_step_no_fork` take one step, `lwp_pure_step`
takes `n` steps paid one by one, and `lwp_pure_step_simple` pays for `n > 0` steps at once with
`n` units of fuel of each obligation of the bill, and gives back `n` credits to each witness and
`£ₒ (o ×ⱼ n)`: the paper's STEP-PURE, STEP-PURE-LC and STEP-PURE-WIT in one rule.  Its proof
splits the fuel one unit per step (`Obl.fuels_succ`) and adds up the credits (`Wit.creds_succ`,
`credits_succ`).

## 4. HeapLang's laws

HeapLang is an Iris-Lean `EctxItemLanguage` (`instEctxItemLanguageExp`), from which Iris-Lean
derives its evaluation contexts `EvContext Exp (List ECtxItem)` (lists of items, innermost
first), the `EctxLanguage` and the `Language`.  HeapLang has no observations (`Obs := Empty`):
its base step ignores the observation argument, which can only be `[]` (`obs_eq_nil`).  No
thread of HeapLang is ever crashed (`instCrash`, `HeapLang.not_crashed`), so its steps keep the
statuses (`HeapLang.keepsCrashed`) and crashing is permanent (`HeapLang.staysCrashed`).  The
fields of the instance are what Rocq states as separate lemmas and packages into
`heap_lang_mixin`.

The class instances are adapted from Iris-Lean's, for the labels and `chooseNat` of Lantana's
HeapLang and without prophecies: `Atomic` for each operation on values (by
`atomic_of_subredexes`), and `PureExec` for each pure base step (by `pureStep_of_baseStep`), with
`instPureExecEqOp` tried before the generic `instPureExecBinOp`.  `atomic_of_baseStep_ofVal` is a
theorem, not an instance, since `BaseStep` is not a class (Rocq has a `Hint Extern`).

The ghost state `HeapGS` is the temporal layer and `HeapStateGS`: the heap, Iris-Lean's `genHeap`
from locations to `Option Val`, and the thread-expression map, a ghost map from thread ids to
expressions.  The state interpretation `stateInterp σ tp` holds the heap of `σ` and the map of
the pool `tp`, so the map is the pool.  Points-to is `l ↦{dq} v` at `Option Val`: `l ↦ some v`
holds a value, and a freed location is `l ↦{q} none` (Rocq's `freed l q`).

The token `threadExpr i C e` is exact ownership of the expression `fill C e` of thread `i`, split
into the caller's context `C` and the current subexpression `e`; `threadExpr_fill` moves a
context between the two, and `exits v @ i` is `threadExpr i [] (.val v)`.  Since `lwp.step`
quantifies over the contexts `K` that put the thread's expression in the pool, a law relates `K`
to the token's `C`: the token and the pool give `K e = fill C e` (`threadExpr_ctx`), and then
`K e' = fill C e'` for the result `e'` of a step of `e` (`context_eq_fill_of_primStep`).  So the
pool after the step is `tp.set i (fill C e')`, and the token and the map change together
(`threadMapAuth_update`, and `threadExpr_pureExecSI` for pure steps).

`context_eq_fill_of_primStep` (`HeapLang/Context.lean`) is about an arbitrary function `K` with
the laws of `Language.Context`, which need not be a list of items.  The step is a base step of
a redex under items, which join `K` and `C`.  The final state determines the result of every
base step but `chooseNat`'s (`BaseStep.eq_or_eq_chooseNat`; `allocN` picks a location, which the
state records), and then `Language.Context.exists_eq_of_primStep` gives the result.  `chooseNat`
steps to every number with the same state, so the laws of a context only say that `K` maps the
numbers onto the numbers under `C`.  That it maps each number to itself is read off another
expression: `K (!ℓ)` steps as `!ℓ` does, to `K n` in a state whose cell `ℓ` holds `n`, so it is
a redex under some items `D` whose result is read from the state
(`BaseStep.exists_eq_ofVal_of_ne`), and `K n = fill D n`; then `D = C`, since two lists of items
that agree on two different values are equal (`eq_of_fill_ofVal_eq`).  This is the one law of
HeapLang whose proof uses another construct of the language (§2.1).

Every step law takes the token and `stepPre i G R` (the bill, one unit of fuel of each of its
obligations, the witness layers) and gives back the token and `stepPost i G R o` (the later
credits `£ₒ o`, the bill, the witnesses' credits): the paper's STEP rules.  `stepPre_nil` and
`stepPre_wit` (in `ProofMode.lean`) build `stepPre` for no witness or one, and
`Wit.creds_singleton` reads back the credit of one witness.

`lwp_heap_step` is the common part of the laws of a step that forks no thread and ends in a
value (`lwp_alloc`, `lwp_free`, `lwp_load`, `lwp_store`, `lwp_xchg`, `lwp_cmpXchg_fail`,
`lwp_cmpXchg_suc`, `lwp_faa`, `lwp_chooseNat`), which supply only the effect on the heap.
`HeapLang.lwp_pure_step` is `lwp_pure_step_simple` for the token.  In `lwp_fork`, the children
`K ⊆ G` of the parent move to the new thread with one unit of fuel each and become its children
and its bill; the parent keeps `G \ K` as both (`Th.carriers_resync`), and the new thread starts
with its token, its running handle, and the postcondition `lwp.liftTerm j (fun _ _ => True)`.

## 5. The step tactics

The tactics of `HeapLang/ProofMode.lean` take HeapLang's pure steps and binds in the proof mode.
They rest on three lemmas: `tac_lwp_pure` takes the `n` pure steps of the redex of `e`, paid with
`n` of the `n + m` units of fuel of the bill; `tac_lwp_step` takes one pure step that observes
no witness; `tac_lwp_bind` focuses on a subexpression and moves its context into the token.

The redex is found by instance search.  `PureExecCtx φ n e e'` says that `e` reaches `e'` by `n`
pure steps of its redex, under `φ`.  Its instances go down the context items of `e` in HeapLang's
right-to-left evaluation order (into a left operand only once the right one is a value), and the
redex itself comes from the `PureExec` instances of `Instances.lean` (`PureExecCtx.ofPureExec`);
this replaces Rocq's `reshape_expr` and its search for `PureExec`.  `InCtx e' e K` finds the
context `K` with `e = fill K e'` in the same way, for `tac_lwp_bind`.  The result of `PureExec`
is an output of the search, so the generic `instPureExecUnOp` and `instPureExecBinOp`, which
leave the result `v'` to their pure condition `op.eval v = some v'`, cannot serve; instances for
`~#b`, and for `+`, `-`, `≤` and `<` on integers, give the result directly.

The tactics that take the hypotheses by name:

- `lwp_pure H` (Rocq's `lwp_pure`) applies `tac_lwp_pure` with the token `H`, proves `0 < n`,
  tries the pure condition with `trivial` and `decide`, and leaves the premise of `tac_lwp_pure`,
  `∃ G m R o, (thCarriers i G ∗ Obl.fuels G (n + m) ∗ Wit.layers R) ∗ (thCarriers i G -∗
  Obl.fuels G m -∗ Wit.creds R -∗ £ₒ o -∗ threadExpr i C e' -∗ |={E}=>m lWP e' …)`.
- `lwp_step H HG HF` applies `tac_lwp_step` with the token, the bill and its fuel, and
  introduces them again under their names; `with Hc : o` also introduces the later credits.
- `lwp_bind e' H` (Rocq's `lwp_bind`) applies `tac_lwp_bind`.
- `lwp_expr_simp` (Rocq's `lwp_expr_simpl`) computes the substitutions, the contexts and the
  negations of the goal, as needed after `lwp_pure` of a `rec` application or of `~#b`, or after
  `lwp_bind`.  It then writes the values back as `Exp.ofVal v` (`val_to_ofVal`), the form that
  the instances of `PureExecCtx`, `InCtx` and `Atomic` expect, so that the step tactics and the
  opening of invariants around atomic expressions apply afterwards.
- `lwp_expr_eval` also computes the comparisons `v₁ == v₂` of closed values (`reduceValBEq`, for
  the result of `instPureExecEqOp`), `decide` of decided propositions (the results of `≤` and
  `<`) and the arithmetic of integer literals.

`lwp_step`, `lwp_step with Hc : o`, `lwp_pure` and `lwp_bind e'` without names find their
hypotheses in the context of the goal `lWP e @ s; i; E {{ Φ }}` by their shape: the token is the
spatial hypothesis `threadExpr i C e` with the goal's thread and expression, the bill the spatial
hypothesis `thCarriers i G` (also written `Par.bill (.thread i) G`), and the fuel the spatial
hypothesis `Obl.fuels G n` with the same `G`.  The most recent such hypothesis is taken, and terms
are compared up to reducible unfolding without assigning metavariables.

Before a step, `lwp_step` checks that the expression is not a value and finds the redex
`PureExecCtx φ 1 e e'` itself, after `lwp_expr_eval` if there is none and the expression has
something to compute.  It must: the named tactic, applied to a value or to an unsimplified
`Exp.subst`, fails its instance search with an error that elaboration recovers from, and then
`trivial`, searching a proof of the unknown pure condition, exceeds the maximum recursion depth,
an exception that `try` and `repeat` do not catch.  The errors name what is missing (the token,
the bill, its fuel, a redex), and a failing step asks whether fuel is left in `HF`.

`lwp_pures` repeats `lwp_step` until the expression is a value, has no one-step pure redex, or
has one whose pure condition `trivial` and `decide` do not prove; it computes the expression with
`lwp_expr_eval` between steps.  It fails if it takes no step, and a missing hypothesis or a lack
of fuel is an error.  The `lWP` of a value is left to the caller (`lwp_value'`).
