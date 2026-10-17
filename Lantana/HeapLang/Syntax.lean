/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from Iris-Lean's `Iris.HeapLang.Syntax`, whose header reads:
  Copyright (c) The Iris-Lean Contributors
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Michael Sammler
Modified by the Lantana-Lean Contributors; the module documentation describes the changes.
-/
module

public import Iris.Std.Infinite
public import Lantana.ProgramLogic.Language

/-! # HeapLang: syntax

The syntax of Lantana's HeapLang (Rocq `lantana_heap_lang/lang.v`, `locations.v`), a fork of
Iris-Lean's `Iris.HeapLang.Syntax` with the same declaration names (D22). Compared with
Iris-Lean's HeapLang, expressions gain `label t e` (a trace-visible label, which evaluates `e`)
and `chooseNat` (unbounded nondeterminism in one step), and lose the prophecy constructs
`newProph`/`resolve` and the `prophecy` literal (D15).

The Rocq declarations of `lantana_heap_lang/` (logical path `lantana.heap_lang`) are recorded
as `heap_lang.X`; for those inside `lang.v`'s `Module heap_lang`, the module and the directory
prefix are written once (`heap_lang.base_step`, not `heap_lang.heap_lang.base_step`, which the
duplicated-namespace linter rejects).
-/

@[expose] public section
namespace Lantana.HeapLang

open Iris.ProgramLogic (ToVal)

#lantana_ignore heap_lang.proph_id "prophecies dropped (D15)"
#lantana_ignore heap_lang.observation "prophecies dropped (D15)"

@[ext, lantana_alias heap_lang.loc]
structure Loc where
  mk ::
  n : Int
deriving Inhabited, Repr, DecidableEq

attribute [lantana_alias heap_lang.Loc.inhabited] instInhabitedLoc
attribute [lantana_alias heap_lang.Loc.eq_dec] instDecidableEqLoc

@[lantana_alias heap_lang.Loc.infinite]
instance : InfiniteType Loc where
  enum n := .mk n
  enum_inj n m := by grind

instance : Ord Loc where
  compare l₁ l₂ := compare l₁.n l₂.n

instance : Std.TransOrd Loc where
  eq_swap := by
    intros l₁ l₂; unfold compare; unfold instOrdLoc; simp;
    apply Int.instTransOrd.eq_swap
  isLE_trans := by
    intros l₁ l₂ l₃; unfold compare; unfold instOrdLoc; simp;
    apply Int.instTransOrd.isLE_trans

instance : Std.LawfulEqOrd Loc where
  eq_of_compare := by
    intros l₁ l₂; unfold compare; unfold instOrdLoc; simp;
    intros h; ext; assumption

attribute [lantana_alias heap_lang.Loc.eq_spec] Loc.ext_iff

@[lantana_alias heap_lang.Loc.add]
instance : HAdd Loc Int Loc where
  hAdd l i := ⟨l.n + i⟩

instance : HAdd Loc Nat Loc where
  hAdd l i := ⟨l.n + i⟩

-- The order on locations is the `Int` order on the `Loc.n` field. It is a `Prop`-valued order,
-- as in Rocq, and is what `BinOp.eval` compares locations with; the `Ord Loc` instance above is
-- the separate, `Ordering`-valued comparison that the heap's `ExtTreeMap` is keyed by.

@[lantana_alias heap_lang.Loc.le]
instance : LE Loc where
  le l₁ l₂ := l₁.n ≤ l₂.n

@[lantana_alias heap_lang.Loc.lt]
instance : LT Loc where
  lt l₁ l₂ := l₁.n < l₂.n

@[simp]
theorem Loc.le_iff {l₁ l₂ : Loc} : l₁ ≤ l₂ ↔ l₁.n ≤ l₂.n := .rfl

@[simp]
theorem Loc.lt_iff {l₁ l₂ : Loc} : l₁ < l₂ ↔ l₁.n < l₂.n := .rfl

@[lantana_alias heap_lang.Loc.le_dec]
instance (l₁ l₂ : Loc) : Decidable (l₁ ≤ l₂) := inferInstanceAs (Decidable (l₁.n ≤ l₂.n))

@[lantana_alias heap_lang.Loc.lt_dec]
instance (l₁ l₂ : Loc) : Decidable (l₁ < l₂) := inferInstanceAs (Decidable (l₁.n < l₂.n))

@[lantana_alias heap_lang.Loc.le_po]
instance : Std.IsPartialOrder Loc where
  le_refl _ := Int.le_refl _
  le_trans _ _ _ h₁ h₂ := Int.le_trans h₁ h₂
  le_antisymm _ _ h₁ h₂ := Loc.ext (Int.le_antisymm h₁ h₂)

@[lantana_alias heap_lang.Loc.le_total]
instance : Std.Total ((· ≤ ·) : Loc → Loc → Prop) where
  total l₁ l₂ := Int.le_total l₁.n l₂.n

@[lantana_alias heap_lang.Loc.le_ngt]
theorem Loc.le_ngt {l₁ l₂ : Loc} : l₁ ≤ l₂ ↔ ¬ l₂ < l₁ := by simp

@[lantana_alias heap_lang.Loc.le_lteq]
theorem Loc.le_lteq {l₁ l₂ : Loc} : l₁ ≤ l₂ ↔ l₁ < l₂ ∨ l₁ = l₂ := by
  simp only [Loc.le_iff, Loc.lt_iff, Loc.ext_iff]; omega

instance : Zero Loc where
  zero := ⟨0⟩

@[simp]
theorem loc_add_n (l : Loc) n :
  (l + n).n = l.n + n := by simp [HAdd.hAdd]

@[lantana_alias heap_lang.Loc.add_assoc]
theorem loc_add_assoc (l : Loc) (i j : Int) : l + i + j = l + (i + j) := by
  ext; simp [Int.add_assoc]

@[simp, lantana_alias heap_lang.Loc.add_0]
theorem loc_add_zero (l : Loc) : l + (0 : Int) = l := by ext; simp

@[lantana_alias heap_lang.Loc.add_inj]
theorem loc_add_inj {l : Loc} {i j : Int} (h : l + i = l + j) : i = j := by
  have := congrArg Loc.n h; simp only [loc_add_n] at this; omega

@[lantana_alias heap_lang.Loc.add_le_mono]
theorem Loc.add_le_mono {l₁ l₂ : Loc} {i₁ i₂ : Int} (hl : l₁ ≤ l₂) (hi : i₁ ≤ i₂) :
    l₁ + i₁ ≤ l₂ + i₂ := Int.add_le_add hl hi

/-- A location that is fresh for `ls`, and stays fresh at every non-negative offset
(`Loc.fresh_fresh`). Rocq folds over a `gset loc`; here the argument is the key list of
a heap, as produced by `Std.ExtTreeMap.keys`. -/
@[lantana_alias heap_lang.Loc.fresh]
def Loc.fresh (ls : List Loc) : Loc := ⟨(ls.map Loc.n).foldr max 0 + 1⟩

@[lantana_alias heap_lang.Loc.fresh_fresh]
theorem Loc.fresh_fresh (ls : List Loc) {i : Int} (hi : 0 ≤ i) : Loc.fresh ls + i ∉ ls :=
  fun hmem => by
    have := List.mem_le_foldr_max _ _ (List.mem_map_of_mem (f := Loc.n) hmem)
    simp only [loc_add_n, Loc.fresh] at this; omega

@[lantana_alias heap_lang.Loc.countable]
instance : Pos.Countable Loc where
  encode l := Pos.Countable.encode l.n
  decode p := ((Pos.Countable.decode p : Option Int)).map Loc.mk
  decode_encode _ := by simp [Pos.Countable.decode_encode]

-- Rocq registers a canonical Leibniz OFE on `loc`. In Lean the discrete OFE is the generic
-- `DiscreteO` from `Iris.Algebra.OFE`, applied to `Loc` at its use sites.
#lantana_ignore heap_lang.locO
  "Canonical Leibniz OFE on `loc`; Lean uses `DiscreteO Loc`."

inductive Binder where
  | anon
  | named (name : String)
deriving Inhabited, Repr, DecidableEq

instance : Pos.Countable Binder where
  encode
    | .anon    => Pos.Countable.encode ([] : List Pos)
    | .named s => Pos.Countable.encode [Pos.Countable.encode s]
  decode p :=
    match (Pos.Countable.decode p : Option (List Pos)) with
    | some []  => some .anon
    | some [s] => ((Pos.Countable.decode s : Option String)).map .named
    | _ => none
  decode_encode b := by cases b <;> simp [Pos.Countable.decode_encode]

/-- Literals. There is no prophecy literal (Rocq `LitrProphecy`, D15). `poison` is a unit that
compares with nothing. -/
@[lantana_alias heap_lang.base_lit]
inductive BaseLit where
  | int (n : Int)
  | bool (b : Bool)
  | unit
  | poison
  | loc (l : Loc)
deriving Inhabited, Repr, DecidableEq

attribute [lantana_alias heap_lang.base_lit_eq_dec] instDecidableEqBaseLit

/-- A literal is encoded as the list `[tag]`, or `[tag, payload]` for the literals that carry
one. -/
@[lantana_alias heap_lang.base_lit_countable]
instance : Pos.Countable BaseLit where
  encode
    | .int n      => Pos.Countable.encode [Pos.Countable.encode (0 : Nat), Pos.Countable.encode n]
    | .bool b     => Pos.Countable.encode [Pos.Countable.encode (1 : Nat), Pos.Countable.encode b]
    | .unit       => Pos.Countable.encode [Pos.Countable.encode (2 : Nat)]
    | .poison     => Pos.Countable.encode [Pos.Countable.encode (3 : Nat)]
    | .loc l      => Pos.Countable.encode [Pos.Countable.encode (4 : Nat), Pos.Countable.encode l]
  decode p :=
    match (Pos.Countable.decode p : Option (List Pos)) with
    | some [t] =>
      match (Pos.Countable.decode t : Option Nat) with
      | some 2 => some .unit
      | some 3 => some .poison
      | _ => none
    | some [t, x] =>
      match (Pos.Countable.decode t : Option Nat) with
      | some 0 => ((Pos.Countable.decode x : Option Int)).map .int
      | some 1 => ((Pos.Countable.decode x : Option Bool)).map .bool
      | some 4 => ((Pos.Countable.decode x : Option Loc)).map .loc
      | _ => none
    | _ => none
  decode_encode l := by cases l <;> simp [Pos.Countable.decode_encode]

@[lantana_alias heap_lang.un_op]
inductive UnOp where
  | neg
  | minus
deriving Inhabited, Repr, DecidableEq

attribute [lantana_alias heap_lang.un_op_eq_dec] instDecidableEqUnOp

-- Rocq calls this instance `un_op_finite`, but states it as countability.
@[lantana_alias heap_lang.un_op_finite]
instance : Pos.Countable UnOp where
  encode
    | .neg   => Pos.Countable.encode (0 : Nat)
    | .minus => Pos.Countable.encode (1 : Nat)
  decode p :=
    match (Pos.Countable.decode p : Option Nat) with
    | some 0 => some .neg
    | some 1 => some .minus
    | _ => none
  decode_encode op := by cases op <;> simp [Pos.Countable.decode_encode]

@[lantana_alias heap_lang.bin_op]
inductive BinOp where
  /- We use "tdiv" and "tmod" instead of "div" and "mod" to
      better match the behavior of 'real' languages:
      e.g., in Rust, -30 / -4 == 7. ("div" would return 8.) -/
  | plus | minus | mult | tdiv | tmod /- arithmetic -/
  | and | or | xor /- bitwise -/
  | shiftl | shiftr /- shifts -/
  | le | lt | eq /- relations -/
  | offset /- pointer offset -/
deriving Inhabited, Repr, DecidableEq

attribute [lantana_alias heap_lang.bin_op_eq_dec] instDecidableEqBinOp

@[lantana_alias heap_lang.bin_op_countable]
instance : Pos.Countable BinOp where
  encode
    | .plus   => Pos.Countable.encode (0 : Nat)
    | .minus  => Pos.Countable.encode (1 : Nat)
    | .mult   => Pos.Countable.encode (2 : Nat)
    | .tdiv   => Pos.Countable.encode (3 : Nat)
    | .tmod   => Pos.Countable.encode (4 : Nat)
    | .and    => Pos.Countable.encode (5 : Nat)
    | .or     => Pos.Countable.encode (6 : Nat)
    | .xor    => Pos.Countable.encode (7 : Nat)
    | .shiftl => Pos.Countable.encode (8 : Nat)
    | .shiftr => Pos.Countable.encode (9 : Nat)
    | .le     => Pos.Countable.encode (10 : Nat)
    | .lt     => Pos.Countable.encode (11 : Nat)
    | .eq     => Pos.Countable.encode (12 : Nat)
    | .offset => Pos.Countable.encode (13 : Nat)
  decode p :=
    match (Pos.Countable.decode p : Option Nat) with
    | some 0  => some .plus
    | some 1  => some .minus
    | some 2  => some .mult
    | some 3  => some .tdiv
    | some 4  => some .tmod
    | some 5  => some .and
    | some 6  => some .or
    | some 7  => some .xor
    | some 8  => some .shiftl
    | some 9  => some .shiftr
    | some 10 => some .le
    | some 11 => some .lt
    | some 12 => some .eq
    | some 13 => some .offset
    | _ => none
  decode_encode op := by cases op <;> simp [Pos.Countable.decode_encode]

mutual
  @[lantana_alias heap_lang.expr]
  inductive Exp : Type where
    /- values -/
    -- This constructor should not be used directly. Use Exp.ofVal instead.
    | val (v : Val)
    /- Base lambda calculus -/
    | var (x : String)
    | rec_ (f x : Binder) (e : Exp)
    | app (e₁ e₂ : Exp)
    /- Base types and their operations -/
    | unop (op : UnOp) (e : Exp)
    | binop (op : BinOp) (e₁ e₂ : Exp)
    | if (e₀ e₁ e₂ : Exp)
    /- Products -/
    | pair (e₁ e₂ : Exp)
    | fst (e : Exp)
    | snd (e : Exp)
    /- Sums -/
    | injL (e : Exp)
    | injR (e : Exp)
    | case (e₀ e₁ e₂ : Exp)
    /- Heap -/
    | allocN (e₁ e₂ : Exp) /- array length, initial value -/
    | free (e : Exp)
    | load (e : Exp)
    | store (e₁ e₂ : Exp)
    | cmpXchg (e₀ e₁ e₂ : Exp) /- compare exchange -/
    | xchg (e₁ e₂ : Exp) /- exchange -/
    | faa (e₁ e₂ : Exp) /- fetch and add -/
    /- Concurrency -/
    | fork (e : Exp)
    /- Labels: `label t e` evaluates `e`, then steps to its value -/
    | label (t : String) (e : Exp)
    /- Nondeterminism: steps to any natural number -/
    | chooseNat
  deriving Inhabited, Repr, DecidableEq
  @[lantana_alias heap_lang.val]
  inductive Val : Type where
    | lit (l : BaseLit)
    | rec_ (f x : Binder) (e : Exp)
    | pair (v₁ v₂ : Val)
    | injL (v : Val)
    | injR (v : Val)
  deriving Inhabited, Repr, DecidableEq
end

attribute [lantana_alias heap_lang.Label] Exp.label
attribute [lantana_alias heap_lang.ChooseNat] Exp.chooseNat
attribute [lantana_alias heap_lang.expr_eq_dec] instDecidableEqExp
attribute [lantana_alias heap_lang.val_eq_dec] instDecidableEqVal
attribute [lantana_alias heap_lang.expr_inhabited] instInhabitedExp
attribute [lantana_alias heap_lang.val_inhabited] instInhabitedVal

#lantana_ignore heap_lang.NewProph "prophecies dropped (D15)"
#lantana_ignore heap_lang.Resolve "prophecies dropped (D15)"
#lantana_ignore heap_lang.LitrProphecy "prophecies dropped (D15)"

/-! ### Countability of expressions and values

Rocq encodes expressions and values into `gen_tree` and inherits countability from there. The
encoding below plays the same role: every node becomes the `Pos` code of the list holding its
constructor tag and the codes of its arguments. -/

/-- One node of the `Exp`/`Val` encoding: a constructor tag followed by the codes of that
constructor's arguments. -/
def encNode (tag : Nat) (args : List Pos) : Pos :=
  Pos.Countable.encode (Pos.Countable.encode tag :: args)

@[simp]
theorem encNode_eq_iff {t₁ t₂ : Nat} {a₁ a₂ : List Pos} :
    encNode t₁ a₁ = encNode t₂ a₂ ↔ t₁ = t₂ ∧ a₁ = a₂ := by
  simp [encNode]

mutual

/-- Injective encoding of expressions into `Pos`; see `Exp.enc_inj`. -/
def Exp.enc : Exp → Pos
  | .val v            => encNode 0 [v.enc]
  | .var x            => encNode 1 [Pos.Countable.encode x]
  | .rec_ f x e       => encNode 2 [Pos.Countable.encode f, Pos.Countable.encode x, e.enc]
  | .app e₁ e₂        => encNode 3 [e₁.enc, e₂.enc]
  | .unop op e        => encNode 4 [Pos.Countable.encode op, e.enc]
  | .binop op e₁ e₂   => encNode 5 [Pos.Countable.encode op, e₁.enc, e₂.enc]
  | .if e₀ e₁ e₂      => encNode 6 [e₀.enc, e₁.enc, e₂.enc]
  | .pair e₁ e₂       => encNode 7 [e₁.enc, e₂.enc]
  | .fst e            => encNode 8 [e.enc]
  | .snd e            => encNode 9 [e.enc]
  | .injL e           => encNode 10 [e.enc]
  | .injR e           => encNode 11 [e.enc]
  | .case e₀ e₁ e₂    => encNode 12 [e₀.enc, e₁.enc, e₂.enc]
  | .allocN e₁ e₂     => encNode 13 [e₁.enc, e₂.enc]
  | .free e           => encNode 14 [e.enc]
  | .load e           => encNode 15 [e.enc]
  | .store e₁ e₂      => encNode 16 [e₁.enc, e₂.enc]
  | .cmpXchg e₀ e₁ e₂ => encNode 17 [e₀.enc, e₁.enc, e₂.enc]
  | .xchg e₁ e₂       => encNode 18 [e₁.enc, e₂.enc]
  | .faa e₁ e₂        => encNode 19 [e₁.enc, e₂.enc]
  | .fork e           => encNode 20 [e.enc]
  | .label t e        => encNode 21 [Pos.Countable.encode t, e.enc]
  | .chooseNat        => encNode 22 []

/-- Injective encoding of values into `Pos`; see `Val.enc_inj`. -/
def Val.enc : Val → Pos
  | .lit l      => encNode 0 [Pos.Countable.encode l]
  | .rec_ f x e => encNode 1 [Pos.Countable.encode f, Pos.Countable.encode x, e.enc]
  | .pair v₁ v₂ => encNode 2 [v₁.enc, v₂.enc]
  | .injL v     => encNode 3 [v.enc]
  | .injR v     => encNode 4 [v.enc]

end

/- By mutual induction and cases on the other side: the different constructors are told apart by
their tags (`decide`), the same ones by the codes of their arguments (`grind`, with the induction
hypotheses). A `simp_all` on every pair of constructors costs 6.5 s here. -/
theorem Exp.enc_inj : Exp.enc.Injective := by
  intro e₁
  induction e₁ using Exp.enc.induct (motive_2 := fun v => ∀ v', Val.enc v = Val.enc v' → v = v') <;>
    (try intro _ _) <;> rename_i e₂ h <;> cases e₂ <;>
    simp only [Exp.enc, Val.enc, encNode_eq_iff] at h <;>
    first
    | exact absurd h.1 (by decide)
    | (try simp only [List.cons.injEq, Pos.encode_eq_iff, and_true, true_and] at h); grind

/- From `Exp.enc_inj` at `Exp.val` (the mutual induction again would cost as much). -/
theorem Val.enc_inj : Val.enc.Injective := fun v₁ v₂ h => by
  have : Exp.val v₁ = Exp.val v₂ := Exp.enc_inj (by simp only [Exp.enc, h])
  injection this

@[lantana_alias heap_lang.expr_countable]
noncomputable instance : Pos.Countable Exp := .ofInjective Exp.enc Exp.enc_inj

@[lantana_alias heap_lang.val_countable]
noncomputable instance : Pos.Countable Val := .ofInjective Val.enc Val.enc_inj

def Exp.isVal : Exp → Bool
  | .val _ => true
  | _ => false

instance instToVal : ToVal Exp Val where
  toVal
  | .val v => some v
  | _ => none
  ofVal := .val
  coe_of_toVal_eq_some {e v} h := by
    cases e <;> simp_all
  toVal_coe _ := rfl

-- Rocq's `to_val`/`of_val` and their round-trip lemmas are stand-alone declarations. Here they
-- are the fields of `instToVal` above, and the round-trip lemmas are Iris-Lean's generic ones
-- for any `ToVal` instance.
#lantana_ignore heap_lang.to_val
  "The `toVal` field of `instToVal`; `of_val` is its `ofVal` field."
#lantana_ignore heap_lang.of_to_val
  "The `coe_of_toVal_eq_some` field of `instToVal`."
#lantana_ignore heap_lang.to_of_val "The `toVal_coe` field of `instToVal`."
#lantana_ignore heap_lang.of_val_inj
  "Iris-Lean's generic `ToVal.TovVal.ofVal_inj`, applied to `instToVal`."

-- Rocq registers canonical Leibniz OFEs on `expr` and `val`. In Lean the generic `exprO`/`valO`
-- of `Iris.ProgramLogic.Language` are `DiscreteO` abbreviations, applied at their use sites.
#lantana_ignore heap_lang.exprO
  "Canonical Leibniz OFE on `expr`; Lean uses `DiscreteO Exp`."
#lantana_ignore heap_lang.valO
  "Canonical Leibniz OFE on `val`; Lean uses `DiscreteO Val`."

namespace Exp
export Iris.ProgramLogic.ToVal (ofVal)
end Exp

@[simp]
theorem val_to_ofVal : Exp.val = Exp.ofVal := rfl

instance : Coe Nat BaseLit where
  coe n := .int n

instance : Coe Int BaseLit where
  coe n := .int n

instance : Coe Bool BaseLit where
  coe b := .bool b

instance : Coe Loc BaseLit where
  coe l := .loc l

instance : Coe Unit BaseLit where
  coe _ := .unit

attribute [coe] BaseLit.int BaseLit.bool BaseLit.loc

@[lantana_alias heap_lang.subst]
def Exp.substStr (x : String) (v : Val) (e : Exp) : Exp :=
  match e with
  | .val _ => e
  | .var x' => if x == x' then .val v else e
  | .rec_ f x' e => .rec_ f x' <| if .named x != f && .named x != x' then e.substStr x v else e
  | .app e₁ e₂ => .app (e₁.substStr x v) (e₂.substStr x v)
  | .unop op e' => .unop op (e'.substStr x v)
  | .binop op e₁ e₂ => .binop op (e₁.substStr x v) (e₂.substStr x v)
  | .if e₀ e₁ e₂ => .if (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)
  | .pair e₁ e₂ => .pair (e₁.substStr x v) (e₂.substStr x v)
  | .fst e' => .fst (e'.substStr x v)
  | .snd e' => .snd (e'.substStr x v)
  | .injL e' => .injL (e'.substStr x v)
  | .injR e' => .injR (e'.substStr x v)
  | .case e₀ e₁ e₂ => .case (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)
  | .allocN e₁ e₂ => .allocN (e₁.substStr x v) (e₂.substStr x v)
  | .free e' => .free (e'.substStr x v)
  | .load e' => .load (e'.substStr x v)
  | .store e₁ e₂ => .store (e₁.substStr x v) (e₂.substStr x v)
  | .cmpXchg e₀ e₁ e₂ => .cmpXchg (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)
  | .xchg e₁ e₂ => .xchg (e₁.substStr x v) (e₂.substStr x v)
  | .faa e₁ e₂ => .faa (e₁.substStr x v) (e₂.substStr x v)
  | .fork e' => .fork (e'.substStr x v)
  | .label t e' => .label t (e'.substStr x v)
  | .chooseNat => .chooseNat

@[lantana_alias heap_lang.subst']
def Exp.subst (x : Binder) (v : Val) (e : Exp) : Exp :=
  if let .named x := x then Exp.substStr x v e else e

/-- Unboxed literals; poison counts as boxed, so that it compares with nothing. -/
@[lantana_alias heap_lang.lit_is_unboxed]
def BaseLit.isUnboxed : BaseLit → Bool
  | .poison => false
  | _ => true

@[lantana_alias heap_lang.val_is_unboxed]
def Val.isUnboxed : Val → Bool
  | .lit l => l.isUnboxed
  | .injL (.lit l) => l.isUnboxed
  | .injR (.lit l) => l.isUnboxed
  | _ => false

/-- Comparison compares words without looking into boxed data: it is safe when one of the two
values is unboxed. -/
@[lantana_alias heap_lang.vals_compare_safe]
def Val.compareSafe (v1 v2 : Val) : Bool :=
  v1.isUnboxed || v2.isUnboxed

-- Rocq states unboxedness as a `Prop` and derives decidability; here it is `Bool`-valued.
#lantana_ignore heap_lang.lit_is_unboxed_dec
  "`BaseLit.isUnboxed` is `Bool`-valued; decidability is definitional."
#lantana_ignore heap_lang.val_is_unboxed_dec
  "`Val.isUnboxed` is `Bool`-valued; decidability is definitional."

section Derived
def Exp.stuck : Exp := Exp.app (.ofVal <| .lit <| .int 0) (.ofVal <| .lit <| .int 0)

@[simp]
theorem Exp.stuck_subst {x v} : Exp.substStr x v Exp.stuck = Exp.stuck := by
  simp [Exp.stuck, Exp.substStr]
  simp only [substStr, ofVal]

def Exp.assert (e : Exp) := Exp.if e (.ofVal <| .lit .unit) Exp.stuck

@[simp]
theorem Exp.assert_subst {x v} e :
    Exp.substStr x v (Exp.assert e) = Exp.assert (Exp.substStr x v e) := by
  simp [Exp.assert, Exp.substStr]
  simp only [substStr, ofVal]

end Derived

end Lantana.HeapLang
