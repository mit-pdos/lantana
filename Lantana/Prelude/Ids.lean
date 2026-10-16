/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.Std.GenSetsInstances
public import Iris.Std.HeapInstances
public import Lantana.Init

/-! # Identifiers: threads, obligations, parents

Shared by the language layer (thread ids are positions in the pool, D14), the obligation
model and the obligation-forest interface (Rocq `obligation.v`'s `oid`, `parent.v`).
-/

@[expose] public section

namespace Lantana

/-- Thread ids are positions in the thread pool. -/
@[lantana_alias thread_id]
abbrev ThreadId := Nat

/-- Obligation ids. -/
@[lantana_alias oid]
abbrev Oid := Nat

/-- Finite sets of obligation ids. -/
@[lantana_alias oids]
abbrev Oids := Std.ExtTreeSet Oid compare

/-- Finite maps from obligation ids. -/
abbrev OidMap (V : Type _) := Std.ExtTreeMap Oid V compare

/-- A parent in the obligation forest: a thread or an obligation. -/
@[lantana_alias parent]
inductive Parent where
  | thread (i : ThreadId)
  | obl (k : Oid)
  deriving DecidableEq

attribute [lantana_alias PThread] Parent.thread
attribute [lantana_alias PObl] Parent.obl

end Lantana
