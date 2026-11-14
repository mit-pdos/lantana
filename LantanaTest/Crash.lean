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

/-! A language whose threads crash, verified end to end: the language (`Lang`), the step rule
(`Step`), the killer (`Kill`), the worker (`Worker`), the reviver (`Reviver`) and the liveness of
the closed systems (`Adequacy`). See `docs/adequacy.md`, §7. -/
