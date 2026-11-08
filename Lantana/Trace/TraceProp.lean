/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.ProgramLogic.Trace

/-! # The state atoms of Lantana's trace properties

Trace properties (`TrProp`, Rocq `trProp`), their connectives and notations are generic, over
any configuration type (`Lantana.Temporal.Trace`). Lantana's traces are `Trace (Cfg Expr State)`,
and this module adds the language's atoms: a predicate on the current state and thread pool
(`TrProp.state`). Their rules are in `Lantana.Trace.TracePropRules`, fair scheduling in
`Lantana.Trace.FairScheduling`.
-/

@[expose] public section

namespace Lantana

namespace TrProp

variable {Expr : Type} {State : Type}

/-- A predicate on the current state and thread pool: the state atoms. -/
@[lantana_alias tr_state]
def state (φ : State → ThreadPool Expr → Prop) : TrProp (Cfg Expr State) :=
  fun τ => φ τ.cfg.2 τ.cfg.1

end TrProp
end Lantana
