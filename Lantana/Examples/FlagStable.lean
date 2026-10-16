/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Examples.Flag

/-! # The stable flag

Rocq `examples/flag_stable.v`: the flag of `Lantana.Examples.Flag`, with the set flag an
invariant of its own. The until of the invariant `flagInv l k` has the right formula
`alwaysI Nv (l ↦ 1)`, which `set` allocates after its store, so the guarantee describes the
history and not only each state: once the flag is `1`, it stays `1` (`flagTrSpec_stays`), and
the run `Flag.flagRun` (`0, 1, 0, 1, 1, …`), which satisfies the guarantee of `Flag`, violates
this one (`flagRun_violates_guarantee`).

The code is `Flag.init`, `Flag.set` and `Flag.wait` (Rocq redefines it identically), and the
run is `Flag.flagRun`. The Rocq names carry the prefix `flag_stable.` (they are those of
`flag.v`).

**Skeleton:** the trace-level lemmas are proved; `isFlag_init` and the specifications are
`sorry` until the HeapLang laws (M7).
-/

@[expose] public noncomputable section

namespace Lantana.Examples.FlagStable

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.Flag (init set wait v0 v1 N Na Np pointsToSpec pointsToTr flagRun)
open scoped Lantana.TrSpec Lantana.TrProp

/-- The namespace of the invariant of the set flag. -/
def Nv : Namespace := N.@"value"

/-! ## The invariant -/

section Invariant
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]

/-- The flag is `0` until it is `1` forever (half of the until on `k`), or `k` is discharged
and the flag is `1` forever. -/
@[lantana_alias flag_stable.flag_inv]
def flagInv (l : Loc) (k : Oid) : IProp GF :=
  iprop(untilI Np k (1 : Qp).half iprop(l ↦ some v0) (alwaysI Nv iprop(l ↦ some v1)) ∨
    (Obl.discharged k ∗ alwaysI Nv iprop(l ↦ some v1)))

/-- The flag `l` on the obligation `k` with witness layer `ℓ` (persistent). -/
@[lantana_alias flag_stable.is_flag]
def isFlag (l : Loc) (k : Oid) (ℓ : Layer) : IProp GF :=
  iprop(Wit.layer k ℓ ∗ alwaysI Na (flagInv l k))

/-- The setter's token: the other half of the until. -/
@[lantana_alias flag_stable.flag_tk]
def flagTk (l : Loc) (k : Oid) : IProp GF :=
  untilI Np k (1 : Qp).half iprop(l ↦ some v0) (alwaysI Nv iprop(l ↦ some v1))

@[lantana_alias flag_stable.is_flag_persistent]
instance isFlag_persistent (l : Loc) (k : Oid) (ℓ : Layer) :
    Persistent (isFlag (GF := GF) l k ℓ) := by
  unfold isFlag; infer_instance

/-- The specification inferred from `isFlag`: always, `0` until always `1`, or always `1`. -/
@[lantana_alias flag_stable.flag_trSpec]
def flagTrSpec (l : Loc) : TrSpec Exp State GF :=
  TrSpec.true ∧ₛ
    □ₛ ((pointsToSpec l v0 𝒰ₛ □ₛ pointsToSpec l v1) ∨ₛ
      (TrSpec.true ∧ₛ □ₛ pointsToSpec l v1))

instance guarOf_flagInv (l : Loc) (k : Oid) :
    GuarOf (flagInv (GF := GF) l k)
      ((pointsToSpec l v0 𝒰ₛ □ₛ pointsToSpec l v1) ∨ₛ
        (TrSpec.true ∧ₛ □ₛ pointsToSpec l v1)) := by
  unfold flagInv; infer_instance

@[lantana_alias flag_stable.guar_is_flag]
theorem guar_isFlag (l : Loc) (k : Oid) (ℓ : Layer) :
    ⊢@{IProp GF} isFlag l k ℓ ⊨ₜ flagTrSpec l := by
  unfold isFlag flagTrSpec; exact IntoGuar.into_guar

@[lantana_alias flag_stable.guar_flag_tk]
theorem guar_flagTk (l : Loc) (k : Oid) :
    ⊢@{IProp GF} flagTk l k ⊨ₜ (pointsToSpec l v0 𝒰ₛ □ₛ pointsToSpec l v1) := by
  unfold flagTk; exact IntoGuar.into_guar

/-- The response property: whenever the flag is `0`, it is eventually `1` forever. -/
@[lantana_alias flag_stable.flag_response]
def flagResponse (l : Loc) : TrProp Exp State :=
  □ₜ (pointsToTr l v0 →ₜ ◇ₜ □ₜ pointsToTr l v1)

omit [ModelGS GF] [HeapGS GF] in
/-- The until gives the eventually, and an always holds now: unlike in `Flag`, the antecedent
is not needed. -/
@[lantana_alias flag_stable.flag_response_ext]
theorem flagResponse_ext (l : Loc) : (flagTrSpec (GF := GF) l).external ⊆ flagResponse l := by
  intro τ ⟨_, h⟩ m hm _
  rcases h m hm with hU | ⟨_, h₁⟩
  · exact TrProp.until_eventually _ hU
  · exact TrProp.eventually_intro _ h₁

@[lantana_alias flag_stable.is_flag_response]
theorem isFlag_response (l : Loc) (k : Oid) (ℓ : Layer) :
    ⊢@{IProp GF} isFlag l k ℓ ⊨ₜ
      (flagTrSpec l).cast (flagResponse l) (flagResponse_ext l) :=
  (guar_isFlag l k ℓ).trans (guar_cast _ _)

/-- Initialization: a new obligation below `p` carrying the flag. -/
@[lantana_alias flag_stable.is_flag_init]
theorem isFlag_init (E : CoPset) (l : Loc) (p : Parent) (K : Oids) (ℓ : Layer) (μ : Measure) :
    parLe (GF := GF) p ℓ ⊢ l ↦ some v0 -∗ Par.kids p K -∗
      |={E}=>m ∃ k : Oid, ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ oblKids k ∅ ∗
        Obl.fuel k ℓ μ ∗ flagTk l k ∗ isFlag l k ℓ := sorry

end Invariant

/-! ## Specifications

The statements of `Flag`'s, for the stable flag. -/

section Specs
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]

@[lantana_alias flag_stable.Flag_init_spec]
theorem init_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids) (p : Parent)
    (K : Oids) (ℓ : Layer) (m : Measure) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&init) #()) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ parLe p ℓ ∗ Par.kids p K }}}
        hl(v(&init) #()) @ i
      l{{{ (x : Loc) (k : Oid), RET hl_val(#x); threadExpr i C hl(#x) ∗ £ₒ lc ∗
        thKids i G ∗ ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ oblKids k ∅ ∗
        Obl.fuel k ℓ m ∗
        flagTk x k ∗ isFlag x k ℓ }}} := sorry

/-- `set` allocates the invariant of the set flag after its store. -/
@[lantana_alias flag_stable.Flag_set_spec]
theorem set_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (l : Loc) (G : Oids)
    (p : Parent) (K : Oids) (k : Oid) (ℓ : Layer) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&set) #l) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ Par.kids p K ∗ ⌜k ∈ K⌝ ∗
          oblKids k ∅ ∗ flagTk l k ∗ isFlag l k ℓ }}}
        hl(v(&set) #l) @ i
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i G ∗
        Par.kids p (K.erase k) ∗ Obl.discharged k }}} := sorry

/-- The same operations when the flag's obligation is a child of the calling thread itself. -/
@[lantana_alias flag_stable.Flag_init_thread_spec]
theorem init_thread_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids) (ℓ : Layer)
    (m : Measure) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&init) #()) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) }}}
        hl(v(&init) #()) @ i
      l{{{ (x : Loc) (k : Oid), RET hl_val(#x); threadExpr i C hl(#x) ∗ £ₒ lc ∗
        ⌜k ∉ G⌝ ∗ thKids i (G.insert k) ∗ oblKids k ∅ ∗ Obl.fuel k ℓ m ∗
        flagTk x k ∗ isFlag x k ℓ }}} := sorry

@[lantana_alias flag_stable.Flag_set_thread_spec]
theorem set_thread_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (l : Loc) (G : Oids)
    (k : Oid) (ℓ : Layer) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&set) #l) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ ⌜k ∈ G⌝ ∗ oblKids k ∅ ∗
          flagTk l k ∗ isFlag l k ℓ }}}
        hl(v(&set) #l) @ i
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i (G.erase k) ∗
        Obl.discharged k }}} := sorry

/-- Waiting is fair: the caller's fuel is at the layer above the flag's witness layer. -/
@[lantana_alias flag_stable.Flag_wait_spec]
theorem wait_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (l : Loc) (G : Oids) (k : Oid)
    (ℓ : Layer) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&wait) #l) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g ℓ.succ μ) ∗ isFlag l k ℓ }}}
        hl(v(&wait) #l) @ i
      l{{{ RET v1; threadExpr i C hl(#1) ∗ £ₒ lc ∗ thKids i G ∗ Obl.discharged k }}} :=
  sorry

end Specs

/-! ## Traces -/

section Traces
variable {GF : BundledGFunctors}

/-- The flag at the level of traces: `0` until `1` forever, or `1` forever. -/
@[lantana_alias flag_stable.is_flag_tr]
def isFlagTr (l : Loc) : TrProp Exp State :=
  □ₜ ((pointsToTr l v0 𝒰ₜ □ₜ pointsToTr l v1) ∨ₜ □ₜ pointsToTr l v1)

@[lantana_alias flag_stable.flag_trSpec_impl]
theorem flagTrSpec_impl (l : Loc) : (flagTrSpec (GF := GF) l).external ⊆ isFlagTr l :=
  fun _ ⟨_, h⟩ m hm => (h m hm).imp id And.right

/-- Once the flag is `1`, it stays `1`. -/
@[lantana_alias flag_stable.flag_stays_tr]
def flagStaysTr (l : Loc) : TrProp Exp State :=
  □ₜ (pointsToTr l v1 →ₜ □ₜ pointsToTr l v1)

/-- When the flag is `1`, the until (whose left formula is `0`) is fulfilled. -/
@[lantana_alias flag_stable.is_flag_tr_stays]
theorem isFlagTr_stays (l : Loc) : isFlagTr l ⊆ flagStaysTr l := by
  intro τ h m hm h₁
  rcases h m hm with hU | hA
  · rcases TrProp.until_unfold _ hU with hA | ⟨h₀, _⟩
    · exact hA
    · exact absurd (Flag.pointsToTr_agree l (.own 1) (.own 1) v0 v1 _ ⟨h₀, h₁⟩)
        Flag.v0_ne_v1
  · exact hA

/-- Unlike in `Flag`, the guarantee says that once the flag is `1`, it stays `1`. -/
@[lantana_alias flag_stable.flag_trSpec_stays]
theorem flagTrSpec_stays (l : Loc) : (flagTrSpec (GF := GF) l).external ⊆ flagStaysTr l :=
  TrProp.le_trans (flagTrSpec_impl l) (isFlagTr_stays l)

#lantana_ignore flag_stable.flag_run "The run is `Flag.flagRun`."
#lantana_ignore flag_stable.flag_run_at "`Flag.flagRun_at`."

/-- The run `0, 1, 0, 1, 1, …` goes back to `0` … -/
@[lantana_alias flag_stable.flag_run_goes_back]
theorem flagRun_goes_back (l : Loc) : ¬ flagStaysTr l ⟨0, flagRun l⟩ :=
  Flag.flagRun_goes_back l

/-- … so it satisfies the guarantee of `Flag` (`Flag.flagRun_satisfies_guarantee`), but not
this one. -/
@[lantana_alias flag_stable.flag_run_violates_guarantee]
theorem flagRun_violates_guarantee (l : Loc) :
    ¬ (flagTrSpec (GF := GF) l).external ⟨0, flagRun l⟩ :=
  fun h => flagRun_goes_back l (flagTrSpec_stays l _ h)

end Traces

end Lantana.Examples.FlagStable
