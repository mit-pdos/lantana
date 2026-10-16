/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.HeapLang.TemporalLaws
public import Lantana.Trace

/-! # The flag

Rocq `examples/flag.v`: a flag is a location holding `0` until it is set to `1`. Its invariant
`isFlag l k ℓ` is an `alwaysI` holding half of an until on the obligation `k` (`0` until `1`),
or its discharge; the setter holds the other half (`flagTk l k`) and discharges `k` when it
sets the flag; `wait` spins until the flag is `1`, which is fair by witness-layer induction on
`k`'s witness layer `ℓ`.

At the level of traces (`isFlagTr`), the flag is `0` until `1` and `1` afterwards. The guarantee
does not say that the flag stays `1`: `flagRun` (`0, 1, 0, 1, 1, …`) satisfies it.

**Skeleton (M1):** statements only; the proofs are M8.
-/

@[expose] public noncomputable section

namespace Lantana.Examples.Flag

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open scoped Lantana.TrSpec Lantana.TrProp

/-! ## The program -/

/-- `λ _, ref 0`. -/
def init : Val := hl_val(λ _, ref(#0))

/-- `λ x, x ← 1`. -/
def set : Val := hl_val(λ x, x ← #1)

/-- `rec wait x := if !x ≠ 1 then wait x else 1`. -/
def wait : Val := hl_val(rec wait x := if ~(!x = #1) then wait x else #1)

/-- The values `0` and `1`. -/
def v0 : Val := hl_val(#0)
def v1 : Val := hl_val(#1)

/-- The namespaces of the flag's invariant and of its until. -/
def N : Namespace := nroot.@"flag"
def Na : Namespace := N.@"always"
def Np : Namespace := N.@"pointsto"

/-! ## The invariant -/

section Invariant
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]

/-- The flag is `0` until it is `1` (half of the until on `k`), after which it stays `1`. -/
@[lantana_alias flag_inv]
def flagInv (l : Loc) (k : Oid) : IProp GF :=
  iprop(untilI Np k (1 : Qp).half iprop(l ↦ some v0) iprop(l ↦ some v1) ∨
    (Obl.discharged k ∗ l ↦ some v1))

/-- The flag `l` on the obligation `k` with witness layer `ℓ` (persistent). -/
@[lantana_alias is_flag]
def isFlag (l : Loc) (k : Oid) (ℓ : Layer) : IProp GF :=
  iprop(Wit.layer k ℓ ∗ alwaysI Na (flagInv l k))

/-- The setter's token: the other half of the until. -/
@[lantana_alias flag_tk]
def flagTk (l : Loc) (k : Oid) : IProp GF :=
  untilI Np k (1 : Qp).half iprop(l ↦ some v0) iprop(l ↦ some v1)

instance isFlag_persistent (l : Loc) (k : Oid) (ℓ : Layer) :
    Persistent (isFlag (GF := GF) l k ℓ) := by
  unfold isFlag; infer_instance

/-- `l ↦ v` as a trace specification. -/
abbrev pointsToSpec (l : Loc) (v : Val) : TrSpec Exp State GF :=
  TrSpec.state (pointstoSat l (DFrac.own 1) v)

/-- The specification inferred from `isFlag`: always, `0` until `1` or `1`. -/
@[lantana_alias flag_trSpec]
def flagTrSpec (l : Loc) : TrSpec Exp State GF :=
  TrSpec.true ∧ₛ □ₛ ((pointsToSpec l v0 𝒰ₛ pointsToSpec l v1) ∨ₛ (TrSpec.true ∧ₛ pointsToSpec l v1))

instance guarOf_flagInv (l : Loc) (k : Oid) :
    GuarOf (flagInv (GF := GF) l k)
      ((pointsToSpec l v0 𝒰ₛ pointsToSpec l v1) ∨ₛ (TrSpec.true ∧ₛ pointsToSpec l v1)) := by
  unfold flagInv; infer_instance

@[lantana_alias guar_is_flag]
theorem guar_isFlag (l : Loc) (k : Oid) (ℓ : Layer) :
    ⊢@{IProp GF} isFlag l k ℓ ⊨ₜ flagTrSpec l := by
  unfold isFlag flagTrSpec; exact IntoGuar.into_guar

@[lantana_alias guar_flag_tk]
theorem guar_flagTk (l : Loc) (k : Oid) :
    ⊢@{IProp GF} flagTk l k ⊨ₜ (pointsToSpec l v0 𝒰ₛ pointsToSpec l v1) := by
  unfold flagTk; exact IntoGuar.into_guar

/-- `l ↦ v` as a trace property. -/
abbrev pointsToTr (l : Loc) (v : Val) : TrProp Exp State :=
  TrProp.state (pointstoSat l (DFrac.own 1) v)

/-- The response property: whenever the flag is `0`, it is eventually `1`. -/
@[lantana_alias flag_response]
def flagResponse (l : Loc) : TrProp Exp State :=
  □ₜ (pointsToTr l v0 →ₜ ◇ₜ pointsToTr l v1)

@[lantana_alias flag_response_ext]
theorem flagResponse_ext (l : Loc) : (flagTrSpec (GF := GF) l).external ⊆ flagResponse l := sorry

@[lantana_alias is_flag_response]
theorem isFlag_response (l : Loc) (k : Oid) (ℓ : Layer) :
    ⊢@{IProp GF} isFlag l k ℓ ⊨ₜ (flagTrSpec l).cast (flagResponse l) (flagResponse_ext l) :=
  (guar_isFlag l k ℓ).trans (guar_cast _ _)

/-- Initialization: a new obligation below `p` carrying the flag. -/
@[lantana_alias is_flag_init]
theorem isFlag_init (E : CoPset) (l : Loc) (p : Parent) (K : Oids) (ℓ : Layer) (μ : Measure) :
    parLe (GF := GF) p ℓ ⊢ l ↦ some v0 -∗ Par.kids p K -∗
      |={E}=>m ∃ k : Oid, ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ oblKids k ∅ ∗ Obl.fuel k ℓ μ ∗
        flagTk l k ∗ isFlag l k ℓ := sorry

end Invariant

/-! ## Specifications -/

section Specs
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]

@[lantana_alias Flag_init_spec]
theorem init_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids) (p : Parent) (K : Oids)
    (ℓ : Layer) (m : Measure) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&init) #()) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ parLe p ℓ ∗ Par.kids p K }}}
        hl(v(&init) #()) @ i
      l{{{ (x : Loc) (k : Oid), RET hl_val(#x); threadExpr i C hl(#x) ∗ £ₒ lc ∗ thKids i G ∗
        ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ oblKids k ∅ ∗ Obl.fuel k ℓ m ∗
        flagTk x k ∗ isFlag x k ℓ }}} := sorry

@[lantana_alias Flag_set_spec]
theorem set_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (l : Loc) (G : Oids) (p : Parent)
    (K : Oids) (k : Oid) (ℓ : Layer) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&set) #l) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ Par.kids p K ∗ ⌜k ∈ K⌝ ∗ oblKids k ∅ ∗
          flagTk l k ∗ isFlag l k ℓ }}}
        hl(v(&set) #l) @ i
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i G ∗
        Par.kids p (K.erase k) ∗ Obl.discharged k }}} := sorry

/-- The same operations when the flag's obligation is a child of the calling thread itself. -/
@[lantana_alias Flag_init_thread_spec]
theorem init_thread_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids) (ℓ : Layer)
    (m : Measure) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&init) #()) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) }}}
        hl(v(&init) #()) @ i
      l{{{ (x : Loc) (k : Oid), RET hl_val(#x); threadExpr i C hl(#x) ∗ £ₒ lc ∗
        ⌜k ∉ G⌝ ∗ thKids i (G.insert k) ∗ oblKids k ∅ ∗ Obl.fuel k ℓ m ∗
        flagTk x k ∗ isFlag x k ℓ }}} := sorry

@[lantana_alias Flag_set_thread_spec]
theorem set_thread_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (l : Loc) (G : Oids)
    (k : Oid) (ℓ : Layer) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&set) #l) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ ⌜k ∈ G⌝ ∗ oblKids k ∅ ∗
          flagTk l k ∗ isFlag l k ℓ }}}
        hl(v(&set) #l) @ i
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i (G.erase k) ∗
        Obl.discharged k }}} := sorry

/-- Waiting is fair: the caller's fuel is at the layer above the flag's witness layer. -/
@[lantana_alias Flag_wait_spec]
theorem wait_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (l : Loc) (G : Oids) (k : Oid)
    (ℓ : Layer) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&wait) #l) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g ℓ.succ μ) ∗ isFlag l k ℓ }}}
        hl(v(&wait) #l) @ i
      l{{{ RET v1; threadExpr i C hl(#1) ∗ £ₒ lc ∗ thKids i G ∗ Obl.discharged k }}} := sorry

end Specs

/-! ## Traces -/

section Traces
variable {GF : BundledGFunctors}

/-- The flag at the level of traces: `0` until `1`, and `1` from then on. -/
@[lantana_alias is_flag_tr]
def isFlagTr (l : Loc) : TrProp Exp State :=
  □ₜ ((pointsToTr l v0 𝒰ₜ pointsToTr l v1) ∨ₜ pointsToTr l v1)

@[lantana_alias flag_trSpec_impl]
theorem flagTrSpec_impl (l : Loc) : (flagTrSpec (GF := GF) l).external ⊆ isFlagTr l := sorry

/-- The run `0, 1, 0, 1, 1, …` of a single idle thread. -/
@[lantana_alias flag_run]
def flagRun (l : Loc) (n : Nat) : TraceState Exp State :=
  { cfg := ([], ⟨(∅ : Std.ExtTreeMap Loc (Option Val) compare).insert l
      (some (if n = 0 ∨ n = 2 then v0 else v1))⟩),
    thread := 0 }

@[lantana_alias flag_run_at]
theorem flagRun_at (l : Loc) (m : Nat) (v : Val) :
    pointsToTr l v ⟨m, flagRun l⟩ ↔ v = if m = 0 ∨ m = 2 then v0 else v1 := sorry

/-- The run satisfies the flag's guarantee … -/
@[lantana_alias flag_run_satisfies_guarantee]
theorem flagRun_satisfies_guarantee (l : Loc) :
    (flagTrSpec (GF := GF) l).external ⟨0, flagRun l⟩ := sorry

/-- … although the flag goes back to `0`: the guarantee describes each state, not the history
(see `flag_stable.v`). -/
@[lantana_alias flag_run_goes_back]
theorem flagRun_goes_back (l : Loc) :
    ¬ (□ₜ (pointsToTr l v1 →ₜ □ₜ pointsToTr l v1)) ⟨0, flagRun l⟩ := sorry

end Traces

end Lantana.Examples.Flag
