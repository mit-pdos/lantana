/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.HeapLang.ProofMode
public import Lantana.Trace.TemporalFormula

/-! # Integers extended with `±∞`

Rocq `examples/extended_int.v` (module `Int`): the integers extended with `-∞` and `+∞`, their
representation as HeapLang values (a tag `0`, `1`, `2` paired with `()` or the integer), the
strict order `ltRel`, and the program `lt` that compares two representations, with its
specification `lwp_lt`: from `100` units of fuel of the children of the calling thread (as in
Rocq; the comparison takes at most `18` pure steps), `lt` returns whether `ltRel` holds.

The type is `ExtInt` (Rocq `Int.t`; `Int` is Lean's), with the coercion from `Int` and the
scoped notations `-∞`, `+∞`. The proof goes by cases on the two arguments, with the result
computed by `ltb`, the order as a Boolean by cases (`decide_ltRel`).

Everything here is proved.
-/

@[expose] public noncomputable section

namespace Lantana.Examples.ExtendedInt

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language

/-! ## The extended integers -/

/-- Integers extended with `±∞`. -/
@[lantana_alias Int.t]
inductive ExtInt where
  | negInf
  | fin (z : Int)
  | posInf
deriving DecidableEq, Inhabited, Repr

#lantana_ignore Int.NegInf "`ExtInt.negInf`."
#lantana_ignore Int.Fin "`ExtInt.fin`."
#lantana_ignore Int.PosInf "`ExtInt.posInf`."

instance : Coe Int ExtInt := ⟨ExtInt.fin⟩

/-- `-∞`. -/
scoped notation "-∞" => ExtInt.negInf
/-- `+∞`. -/
scoped notation "+∞" => ExtInt.posInf

namespace ExtInt

/-- The representation as a value: a tag, and the integer for a finite one. -/
@[lantana_alias Int.into_val]
def intoVal : ExtInt → Val
  | negInf => hl_val((#0, #()))
  | fin z => hl_val((#1, #z))
  | posInf => hl_val((#2, #()))

/-- The strict order. -/
@[lantana_alias Int.lt_rel]
def ltRel : ExtInt → ExtInt → Prop
  | negInf, negInf => False
  | negInf, _ => True
  | fin _, negInf => False
  | fin a, fin b => a < b
  | fin _, posInf => True
  | posInf, _ => False

@[lantana_alias Int.lt_rel_dec]
instance ltRel_dec : (x y : ExtInt) → Decidable (ltRel x y)
  | negInf, negInf => inferInstanceAs (Decidable False)
  | negInf, fin _ => inferInstanceAs (Decidable True)
  | negInf, posInf => inferInstanceAs (Decidable True)
  | fin _, negInf => inferInstanceAs (Decidable False)
  | fin a, fin b => inferInstanceAs (Decidable (a < b))
  | fin _, posInf => inferInstanceAs (Decidable True)
  | posInf, _ => inferInstanceAs (Decidable False)

/-- The strict order as a Boolean, by cases (the result of `lt`). -/
def ltb : ExtInt → ExtInt → Bool
  | negInf, negInf => false
  | negInf, fin _ => true
  | negInf, posInf => true
  | fin _, negInf => false
  | fin a, fin b => decide (a < b)
  | fin _, posInf => true
  | posInf, negInf => false
  | posInf, fin _ => false
  | posInf, posInf => false

theorem decide_ltRel (x y : ExtInt) : decide (ltRel x y) = ltb x y := by
  cases x <;> cases y <;> rfl

end ExtInt

open ExtInt

/-! ## The comparison -/

/-- Compare the tags, then the integers of two finite ones. -/
@[lantana_alias Int.lt]
def lt : Val :=
  hl_val(λ a b,
    let ta := fst(a);
    let tb := fst(b);
    if ta < tb then #true
    else if tb < ta then #false
    else if ta = #1 then snd(a) < snd(b)
    else #false)

section Proof
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]

#lantana_ignore Int.post_wp "A tactic; `lwp_step` closes each pure step."
#lantana_ignore Int.lwp_pures "A tactic; `HeapLang.lwp_pures`."

/-- `lt` returns whether `ltRel` holds. -/
@[lantana_alias Int.lwp_lt]
theorem lwp_lt : ∃ μ : Measure, ∀ (x y : ExtInt) (i : ThreadId) (G : Oids) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&lt) v(&(intoVal x)) v(&(intoVal y))) ∗ thKids i G ∗
          oblFuels G μ }}}
        hl(v(&lt) v(&(intoVal x)) v(&(intoVal y))) @ i
      l{{{ RET hl_val(#(decide (ltRel x y))); threadExpr i C hl(#(decide (ltRel x y))) ∗
        thKids i G }}} := by
  refine ⟨100, fun x y i G C => ?_⟩
  rw [decide_ltRel]
  iintro %Φ !> ⟨HT, HG, HF⟩ HΦ
  unfold lt
  -- The pure steps up to the value, at most `18`.
  rcases x with _ | a | _ <;> rcases y with _ | b | _ <;> simp only [intoVal, ltb] <;>
    lwp_pures <;> iapply lwp_value' <;> iapply HΦ <;> iframe

end Proof

end Lantana.Examples.ExtendedInt
