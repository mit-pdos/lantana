/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LantanaTest.Crash.Lang
public import LantanaTest.Crash.Step
public import LantanaTest.Crash.Kill
public import LantanaTest.Crash.Worker
public import LantanaTest.Crash.Reviver
public import LantanaTest.Crash.Adequacy

/-! A language whose threads crash, verified end to end: the language and its world
(`LantanaTest.Crash.Lang`), the step rule and the facts about the pool (`LantanaTest.Crash.Step`),
the shared invariant and the killer, whose step crashes the worker (`LantanaTest.Crash.Kill`), the
worker, which finishes or loops while crashed (`LantanaTest.Crash.Worker`), the reviver, whose
step recovers it (`LantanaTest.Crash.Reviver`), and the liveness of the closed systems by
`lwp_adequacy_temporal` (`LantanaTest.Crash.Adequacy`). -/
