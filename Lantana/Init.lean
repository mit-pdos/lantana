/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Iris.Init
public meta import Lantana.Std.Porting

/-! # `Lantana.Init`

The initial module of Lantana: every module of the library imports it, directly or
transitively, so that the environment (Iris-Lean's attributes, notations and linters, and
Lantana's porting attribute) is the same everywhere. Lantana builds on Transfinite Iris-Lean
(`Iris`, with `Iris.SI := Ordinal.{3}`).
-/
