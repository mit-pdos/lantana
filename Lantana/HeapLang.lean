/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.HeapLang.Syntax
public import Lantana.HeapLang.Semantics
public import Lantana.HeapLang.Notation
public import Lantana.HeapLang.Instances

/-! # HeapLang

Lantana's HeapLang (Rocq `lantana_heap_lang/`), a fork of Iris-Lean's HeapLang (D22) with labels
and `chooseNat`, without prophecies (D15), and with the state predicates that the atoms of
temporal properties observe. The program logic (`lwp` laws, tactics) comes in M7.
-/
