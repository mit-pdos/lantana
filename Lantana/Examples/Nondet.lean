/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Examples.Flag

/-! # Nested waits to a nondeterministic depth

Rocq `examples/nondet.v`: `nest x n` sets the flag `x` after waiting for a flag `y` that a
forked `nest y (n - 1)` sets, so the waits are nested `n` deep; `nondet` chooses `n` with
`chooseNat`. Since `wait` raises the layer by one, `nest x n` needs fuel at layer `n`, and
`nondet` at layer `ω`: the only use of `chooseNat` and of an infinite layer in the examples.
Both specifications put the flag's obligation under the running thread (`Flag.init_thread_spec`,
`Flag.set_thread_spec`); `nest_spec` is proved by Löb induction on the whole `∃ μ, ∀ …`
statement (the layer `n` drops).

**Skeleton:** the specifications are `sorry` until the HeapLang laws (M7).
-/

@[expose] public noncomputable section

namespace Lantana.Examples.Nondet

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.Flag (flagTk isFlag v1)
open Ordinals.Ordinal (ofNat)
open scoped Ordinals.Ordinal

/-! ## The program -/

/-- `rec fn x n := if n ≤ 0 then set x else let y := init (); fork (fn y (n - 1)); wait y;
set x`. -/
@[lantana_alias Nondet.nest]
def nest : Val :=
  hl_val(rec fn x n :=
    if n ≤ #0 then v(&Flag.set) x
    else
      let y := v(&Flag.init) #();
      fork(fn y (n - #1));
      v(&Flag.wait) y;
      v(&Flag.set) x)

/-- `λ _, let n := chooseNat; let x := init (); fork (nest x n); wait x`. -/
@[lantana_alias Nondet.nondet]
def nondet : Val :=
  hl_val(λ _,
    let n := chooseNat();
    let x := v(&Flag.init) #();
    fork(v(&nest) x n);
    v(&Flag.wait) x)

/-! ## Specifications -/

section Specs
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]

/-- The layer grows with the nested `wait`s: `nest x n` needs fuel at layer `n`, the witness
layer of its flag `x`, whose obligation `k` is a child of the running thread. -/
@[lantana_alias Nondet_nest_spec]
theorem nest_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (x : Loc) (n : Int) (G : Oids)
    (k : Oid) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&nest) #x #n) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g (ofNat n.toNat) μ) ∗ ⌜k ∈ G⌝ ∗ oblKids k ∅ ∗
          flagTk x k ∗ isFlag x k (ofNat n.toNat) }}}
        hl(v(&nest) #x #n) @ i
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i (G.erase k) ∗
        Obl.discharged k }}} := sorry

/-- `nondet` terminates with `1`; the layer of `nest` depends on the chosen `n`, so the
caller's fuel is at layer `ω`. -/
@[lantana_alias Nondet_nondet_spec]
theorem nondet_spec : ∃ μ : Measure, ∀ (i : ThreadId) (G : Oids) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&nondet) #()) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g ω μ) }}}
        hl(v(&nondet) #()) @ i
      l{{{ (v : Val), RET v; threadExpr i C hl(&v) ∗ ⌜v = v1⌝ }}} := sorry

end Specs

end Lantana.Examples.Nondet
