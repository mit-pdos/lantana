/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
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

namespace Parent

/-- An injection into `Nat` (threads even, obligations odd), for the ordering below. -/
def toNat : Parent → Nat
  | .thread i => 2 * i
  | .obl k => 2 * k + 1

theorem toNat_injective : Function.Injective toNat := by
  intro p q h
  cases p <;> cases q <;> simp only [toNat] at h
  · exact congrArg Parent.thread (Nat.eq_of_mul_eq_mul_left Nat.two_pos h)
  · omega
  · omega
  · exact congrArg Parent.obl (Nat.eq_of_mul_eq_mul_left Nat.two_pos (Nat.add_right_cancel h))

/-- Parents are ordered through `toNat`, so that `Std.ExtTreeMap Parent · compare` is a lawful
finite map (the key type of the children ghost map). -/
instance : Ord Parent where
  compare p q := compare p.toNat q.toNat

theorem compare_def (p q : Parent) : compare p q = compare p.toNat q.toNat := rfl

instance : Std.TransOrd Parent where
  eq_swap := by
    intro a b
    rw [compare_def, compare_def]
    exact Std.OrientedOrd.eq_swap
  isLE_trans := by
    intro a b c
    rw [compare_def, compare_def, compare_def]
    exact Std.TransOrd.isLE_trans

instance : Std.LawfulEqOrd Parent where
  eq_of_compare h := toNat_injective (Std.LawfulEqOrd.eq_of_compare (α := Nat) h)
  compare_self := by
    intro a
    rw [compare_def]
    exact Std.ReflOrd.compare_self

example : Iris.Std.LawfulFiniteMap (Std.ExtTreeMap Parent · compare) Parent := inferInstance

end Parent

end Lantana
