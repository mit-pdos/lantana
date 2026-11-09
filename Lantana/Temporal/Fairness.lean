/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Temporal.Fairness.MissHit
public import Lantana.Temporal.Fairness.AttemptGrant
public import Lantana.Temporal.Fairness.Assumption
public import Lantana.Temporal.Fairness.Action
public import Lantana.Temporal.Fairness.OwnView
public import Lantana.Temporal.Fairness.Scheduling
public import Lantana.Temporal.Fairness.FairLabel

/-! # The attempt–grant theory of fairness

Fairness is about attempts and grants: infinitely many refused attempts force infinitely many
granted ones, which is the existence of a counter, the budget of refusals before the next grant.
The modules: the engine `MissHit`, the core `AttemptGrant`, the declared notion `Assumption`, the
recipes (`Action` with `strong` and `weak`, `OwnView` with `own`), fair scheduling (`Scheduling`)
and fair labelling (`FairLabel`).
See `docs/temporal.md`.
-/
