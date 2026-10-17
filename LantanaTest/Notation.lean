/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.ProgramLogic.Notation
public import Iris.Instances.IProp

/-! Tests of the `lWP` notations with a dummy instance. -/

open Iris Lantana

noncomputable section
variable {GF : BundledGFunctors}

local instance : Lwp (IProp GF) Nat Nat Stuckness Nat := ⟨fun _ _ _ _ _ => iprop(True)⟩

example (e : Nat) (Φ : Nat → IProp GF) : IProp GF := lWP e @ 3; ⊤ {{ v, Φ v }}
example (e : Nat) (Φ : Nat → IProp GF) : IProp GF := lWP e @ 3 {{ Φ }}
example (e : Nat) (Φ : Nat → IProp GF) : IProp GF := lWP e @ 3 ?{{ Φ }}
example (e : Nat) (Φ : Nat → IProp GF) : IProp GF := lWP e @ Stuckness.NotStuck; 3; ⊤ {{ Φ }}
example (e : Nat) (Φ : Nat → IProp GF) : IProp GF := lWP e @ 3; ⊤ ?{{ v, Φ v }}

/-- Texan triples inside `iprop` (persistent); as a bare term the carrier must be known. -/
example : IProp GF := iprop(l{{{ True }}} (5 : Nat) @ 3; ⊤ l{{{ RET 5; True }}})
example : IProp GF := iprop(l{{{ True }}} (5 : Nat) @ 3 l{{{ (v : Nat) (w : Nat), RET v + w; True }}})
example : Prop := ⊢@{IProp GF} l{{{ True }}} (5 : Nat) @ 3 l{{{ (v : Nat), RET v; True }}}

/-- The unexpander shows the notation. -/
example (e : Nat) (Φ : Nat → IProp GF) : (lWP e @ 3; ⊤ {{ v, Φ v }}) = (lWP e @ 3 {{ Φ }}) := by
  rfl

end
