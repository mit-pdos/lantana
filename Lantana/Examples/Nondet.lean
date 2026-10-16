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
        Obl.discharged k }}} := by
  obtain ⟨μfi, hfi⟩ := Flag.init_thread_spec (GF := GF)
  obtain ⟨μfs, hfs⟩ := Flag.set_thread_spec (GF := GF)
  obtain ⟨μfw, hfw⟩ := Flag.wait_spec (GF := GF)
  refine ⟨100 + μfi + μfs + μfw, fun lc i x n => ?_⟩
  generalize hm : n.toNat = m
  induction m generalizing lc i x n with
  | zero =>
    intro G k C
    iintro %Φ !> ⟨HT, HG, HF, %hk, Hkk, Htk, #Hflag⟩ HΦ
    icases (Obl.fuel_add_set G _ _ _).mp $$ HF with ⟨HF, Hfw⟩
    icases (Obl.fuel_add_set G _ _ _).mp $$ HF with ⟨HF, Hfs⟩
    icases (Obl.fuel_add_set G _ _ _).mp $$ HF with ⟨HF, Hfi⟩
    ihave HF := oblFuels_init G _ _ $$ HF
    unfold nest
    lwp_step HT HG HF
    lwp_expr_simp
    lwp_step HT HG HF
    lwp_step HT HG HF
    lwp_expr_simp
    lwp_step HT HG HF
    rw [decide_eq_true (by omega : n ≤ 0)]
    lwp_step HT HG HF
    imod Obl.fuel_layer_mono_set G (ℓ₁ := 0) μfs (Ordinals.Ordinal.zero_le _) $$ Hfs with Hfs
    iapply hfs lc i x G k (ofNat 0) C $$ [HT HG Hfs Hkk Htk] HΦ
    iframe
    isplitl
    · ipureintro
      exact hk
    · iexact Hflag
  | succ m IH =>
    intro G k C
    iintro %Φ !> ⟨HT, HG, HF, %hk, Hkk, Htk, #Hflag⟩ HΦ
    icases (Obl.fuel_add_set G _ _ _).mp $$ HF with ⟨HF, Hfw⟩
    icases (Obl.fuel_add_set G _ _ _).mp $$ HF with ⟨HF, Hfs⟩
    icases (Obl.fuel_add_set G _ _ _).mp $$ HF with ⟨HF, Hfi⟩
    ihave HF := oblFuels_init G _ _ $$ HF
    unfold nest
    lwp_step HT HG HF
    lwp_expr_simp
    rw [← nest.eq_1]
    lwp_step HT HG HF
    lwp_step HT HG HF
    lwp_expr_simp
    lwp_step HT HG HF
    rw [decide_eq_false (by omega : ¬ n ≤ 0)]
    lwp_step HT HG HF
    lwp_bind hl(v(&Flag.init) #()) HT
    imod Obl.fuel_layer_mono_set G (ℓ₁ := 0) μfi (Ordinals.Ordinal.zero_le _) $$ Hfi with Hfi
    -- The obligation `k₀` of the new flag pays the steps of this thread until the fork, its
    -- move to the forked thread, and the steps of the forked thread.
    iapply hfi 0 i G (ofNat m) (((3 : Nat) : Measure) + (1 + (1 + (100 + μfi + μfs + μfw)))) _
      $$ [HT HG Hfi]
    · iframe
    iintro %y %k₀ ⟨HT, -, %hk₀, HG, Hkk₀, Hf₀, Htk₀, #Hflag₀⟩
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    icases (Obl.fuel_add k₀ _ _ _).mp $$ Hf₀ with ⟨Hf₀, Hfr⟩
    icases (Obl.fuel_add k₀ _ _ _).mp $$ Hfr with ⟨Hmv, Hfj⟩
    icases oblFuels_add 3 92 G $$ HF with ⟨Hf₃, HF⟩
    ihave Hf₃ := oblFuels_add_obl G k₀ (ofNat m) _ $$ Hf₀ Hf₃
    lwp_step HT HG Hf₃
    lwp_step HT HG Hf₃
    lwp_expr_simp
    lwp_bind hl(fork(v(&nest) #y (#n - #1))) HT
    have hsub : ({k₀} : Oids) ⊆ G.insert k₀ := fun z hz => by
      rw [Iris.Std.LawfulSet.mem_singleton] at hz
      subst hz
      exact Std.ExtTreeSet.mem_insert_self
    iapply lwp_fork (o := 0) (G := G.insert k₀) (R := ∅) {k₀}
      iprop(oblKids k₀ ∅ ∗ Obl.fuel k₀ (ofNat m) (1 + (100 + μfi + μfs + μfw)) ∗ flagTk y k₀)
      hl(v(&nest) #y (#n - #1)) hsub $$ [] [HT HG Hf₃ Hmv Hkk₀ Hfj Htk₀]
    · -- The forked thread: `n - 1`, then `nest y (n - 1)` by induction.
      iintro %j %Φ' !> ⟨HTj, HGj, Hkk₀, Hfj, Htk₀⟩ HΦ'
      icases (Obl.fuel_add k₀ _ _ _).mp $$ Hfj with ⟨Hf1, Hfj⟩
      ihave Hf1 : oblFuels {k₀} ((0 + 1 : Nat) : Measure) $$ [Hf1]
      · unfold oblFuels
        iapply BigSepS.bigSepS_singleton.mpr
        iexists _
        iexact Hf1
      lwp_step HTj HGj Hf1
      iapply lwp_mupd
      iapply IH 0 j y (n - 1) (by omega) {k₀} k₀ [] $$ [HTj HGj Hkk₀ Htk₀ Hfj]
      · iframe HTj HGj Hkk₀ Htk₀
        isplitl [Hfj]
        · iapply BigSepS.bigSepS_singleton.mpr
          iexact Hfj
        isplitl
        · ipureintro
          exact Iris.Std.LawfulSet.mem_singleton.mpr rfl
        · iexact Hflag₀
      iintro ⟨-, -, HGj, -⟩
      imod Th.terminate ⊤ j $$ [HGj] with #Hdone
      · iapply Par.kids_congr _ $$ HGj
        intro z
        simp only [Std.ExtTreeSet.mem_erase, Iris.Std.LawfulSet.mem_singleton,
          Std.ExtTreeSet.not_mem_empty]
        grind
      imodintro
      iapply HΦ'
      unfold liftTerm
      isplitl
      · iexact Hdone
      · ipureintro
        trivial
    · iframe HT Hkk₀ Hfj Htk₀
      isplitl [HG Hf₃]
      · iapply stepPre_nil $$ HG Hf₃
      · unfold oblFuels
        iapply BigSepS.bigSepS_singleton.mpr
        iexists _
        iexact Hmv
    iintro ⟨HT, -, HG, -⟩
    ihave HG := Par.kids_congr (B := G) ?_ $$ HG
    · intro z
      simp only [Std.ExtTreeSet.mem_diff_iff, Std.ExtTreeSet.mem_insert, Nat.compare_eq_eq,
        Iris.Std.LawfulSet.mem_singleton]
      grind
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    lwp_step HT HG HF
    lwp_step HT HG HF
    lwp_expr_simp
    lwp_bind hl(v(&Flag.wait) #y) HT
    rw [Ordinals.Ordinal.ofNat_succ]
    iapply hfw 0 i y G k₀ (ofNat m) _ $$ [HT HG Hfw]
    · iframe
      iexact Hflag₀
    iintro ⟨HT, -, HG, -⟩
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    unfold v1
    lwp_step HT HG HF
    lwp_step HT HG HF
    lwp_expr_simp
    imod Obl.fuel_layer_mono_set G (ℓ₁ := 0) μfs (Ordinals.Ordinal.zero_le _) $$ Hfs with Hfs
    iapply hfs lc i x G k _ C $$ [HT HG Hfs Hkk Htk] HΦ
    iframe
    isplitl
    · ipureintro
      exact hk
    · iexact Hflag

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
