/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Init

/-! # Facts on `List` and `Option`

General lemmas used by the histories (`Lantana.BaseLogic.Model.ModelHistory`,
`Lantana.ProgramLogic.HistoryInterp`), the thread pools (`Lantana.ProgramLogic.WeakestPre`) and
the obligation maps (`Lantana.BaseLogic.Obligation`), in the namespaces of their types.
-/

@[expose] public section

theorem List.lt_length_of_getElem? {α : Type _} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : i < l.length :=
  (List.getElem?_eq_some_iff.mp h).1

/-- The last entry of a list of length `i + 1` is its `i`-th. -/
theorem List.getLast?_eq_getElem?_of_length {α : Type _} {l : List α} {i : Nat} {a : α}
    (hlen : l.length = i + 1) (hlast : l.getLast? = some a) : l[i]? = some a := by
  rw [List.getLast?_eq_getElem?, hlen] at hlast
  simpa using hlast

theorem List.getLast?_take_succ_of_getElem? {α : Type _} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : (l.take (i + 1)).getLast? = some a := by
  have hlt := List.lt_length_of_getElem? h
  rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left (by omega),
    Nat.add_sub_cancel, List.getElem?_take_of_lt (Nat.lt_succ_self i)]
  exact h

/-- Setting the `i`-th entry of a list and appending: the `i`-th entry is the new one. -/
theorem List.getElem?_set_append {α : Type _} {l l' : List α} {i : Nat} {a b : α}
    (h : l[i]? = some a) : (l.set i b ++ l')[i]? = some b := by
  have hlt : i < l.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left (by simpa using hlt)]
  simp [hlt]

/-- Inversion of `Option.Rel` (in its namespace, `none` and `some` are its constructors). -/
theorem Option.Rel.inv {α β : Type _} {r : α → β → Prop} {o₁ : Option α} {o₂ : Option β}
    (h : Option.Rel r o₁ o₂) :
    (o₁ = Option.none ∧ o₂ = Option.none) ∨
      ∃ a b, o₁ = Option.some a ∧ o₂ = Option.some b ∧ r a b := by
  cases h with
  | none => exact .inl ⟨rfl, rfl⟩
  | some hab => exact .inr ⟨_, _, rfl, rfl, hab⟩
