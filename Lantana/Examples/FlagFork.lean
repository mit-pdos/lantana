/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Examples.Flag
public import Lantana.Examples.World

/-! # A flag set by a forked thread

Rocq `examples/flag_fork.v`, the program `main` of the paper (§2): the main thread creates a
flag, forks a thread that sets it, waits for it and returns `42`.
-/

@[expose] public noncomputable section

namespace Lantana.Examples.FlagFork

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.Flag (flagTk isFlag isFlagTr flagTrSpec v1)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The program -/

/-- `λ _, let x := init (); fork (set x); wait x; 42`. -/
@[lantana_alias FlagFork.main]
def main : Val :=
  hl_val(λ _,
    let x := v(&Flag.init) #();
    fork(v(&Flag.set) x);
    v(&Flag.wait) x;
    #42)

/-- The value `42`. -/
def v42 : Val := hl_val(#42)

/-- The namespaces of the two commitments of the main thread: to return, to create a flag. -/
def Nr : Namespace := nroot.@"flag_fork_ret"
def Nc : Namespace := nroot.@"flag_fork_flag"

/-! ## The specification -/

section Spec
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]

/-- The main proof. Besides returning, the main thread commits to creating a flag. -/
@[lantana_alias FlagFork_main_spec]
theorem main_spec : ∃ μ : Measure, ∀ (i : ThreadId) (kr kc : Oid),
    ⊢@{IProp GF} l{{{ threadExpr i [] hl(v(&main) #()) ∗ thKids i {kr, kc} ∗
          ([∗set] g ∈ ({kr, kc} : Oids), Obl.fuel g 1 μ) ∗ ⌜kr ≠ kc⌝ ∗ oblKids kr ∅ ∗
          oblKids kc ∅ ∗ finallyI Nr kr 1 (exits v42 @ i) ∗
          finallyI Nc kc 1 iprop(∃ (x : Loc) (k : Oid) (ℓ : Layer), isFlag x k ℓ) }}}
        hl(v(&main) #()) @ i
      l{{{ (v : Val), RET v; threadExpr i [] hl(&v) ∗ ⌜v = v42⌝ ∗
        liftTerm i (fun _ _ => iprop(True)) v }}} := by
  obtain ⟨μfi, hfi⟩ := Flag.init_thread_spec (GF := GF)
  obtain ⟨μfs, hfs⟩ := Flag.set_thread_spec (GF := GF)
  obtain ⟨μfw, hfw⟩ := Flag.wait_spec (GF := GF)
  refine ⟨10 + μfi + μfw, fun i kr kc => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hne, Hkr, Hkc, HFr, HFc⟩ HΦ
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Hfw⟩
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Hfi⟩
  ihave HF := oblFuels_init _ _ _ $$ HF
  unfold main
  lwp_step HT HG HF with Hlc : 1 +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hc1, Hc2⟩
  lwp_expr_simp
  lwp_bind hl(v(&Flag.init) #()) HT
  imod Obl.fuel_layer_mono_set _ (ℓ₁ := 0) μfi (Ordinals.Ordinal.zero_le _) $$ Hfi with Hfi
  -- The flag's obligation `k` pays the steps until the fork, its move to the forked thread,
  -- and the forked thread.
  iapply hfi 0 i {kr, kc} 0 (((3 : Nat) : Measure) + (1 + μfs)) _ $$ [HT HG Hfi]
  · iframe
  iintro %x %k ⟨HT, -, %hk, HG, Hkk, Hf, Htk, #Hflag⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  -- Keep the commitment: the flag exists.
  ihave Hc1 := tlc_one_nat.mpr $$ Hc1
  imod finallyI_discharge (E := ⊤) (.thread i) (({kr, kc} : Oids).insert k)
    (fun _ _ => CoPset.mem_full) (by simp) $$ Hc1 HG Hkc HFc [] with ⟨-, HG, -⟩
  · iexists x, k, 0
    iexact Hflag
  ihave HG := Par.kids_congr (B := ({kr} : Oids).insert k) ?_ $$ HG
  · intro z
    simp at hk ⊢
    grind
  ihave HF := oblFuels_subset _ (B := {kr}) (fun z hz => by simp_all) $$ HF
  icases (Obl.fuel_add k _ _ _).mp $$ Hf with ⟨Hf, Hfr⟩
  icases (Obl.fuel_add k _ _ _).mp $$ Hfr with ⟨Hmv, Hfj⟩
  icases oblFuels_add 3 6 _ $$ HF with ⟨Hf₃, HF⟩
  ihave Hf₃ := oblFuels_add_obl _ k 0 _ $$ Hf Hf₃
  lwp_step HT HG Hf₃
  lwp_step HT HG Hf₃
  lwp_expr_simp
  lwp_bind hl(fork(v(&Flag.set) #x)) HT
  have hsub : ({k} : Oids) ⊆ ({kr} : Oids).insert k := fun z hz => by
    rw [Iris.Std.LawfulSet.mem_singleton] at hz
    subst hz
    exact Std.ExtTreeSet.mem_insert_self
  iapply lwp_fork (o := 0) (G := ({kr} : Oids).insert k) (R := ∅) {k}
    iprop(oblKids k ∅ ∗ Obl.fuel k 0 μfs ∗ flagTk x k)
    hl(v(&Flag.set) #x) hsub $$ [] [HT HG Hf₃ Hmv Hkk Hfj Htk]
  · -- The forked thread sets the flag and terminates.
    iintro %j %Φ' !> ⟨HTj, HGj, Hkk, Hfj, Htk⟩ HΦ'
    iapply lwp_mupd
    iapply hfs 0 j x {k} k 0 [] $$ [HTj HGj Hkk Htk Hfj]
    · iframe HTj HGj Hkk Htk
      isplitl [Hfj]
      · iapply BigSepS.bigSepS_singleton.mpr
        iexact Hfj
      isplitl
      · ipureintro
        exact Iris.Std.LawfulSet.mem_singleton.mpr rfl
      · iexact Hflag
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
  · iframe HT Hkk Hfj Htk
    isplitl [HG Hf₃]
    · iapply stepPre_nil $$ HG Hf₃
    · unfold oblFuels
      iapply BigSepS.bigSepS_singleton.mpr
      iexists _
      iexact Hmv
  iintro ⟨HT, -, HG, -⟩
  ihave HG := Par.kids_congr (B := {kr}) ?_ $$ HG
  · intro z
    simp at hk ⊢
    grind
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(v(&Flag.wait) #x) HT
  ihave Hfw := BigSepS.bigSepS_subseteq (Y := ({kr} : Oids)) (fun z hz => by simp_all) $$ Hfw
  imod Obl.fuel_layer_mono_set {kr} (ℓ₁ := Ordinals.Ordinal.succ 0) μfw
    (Ordinals.Ordinal.le_of_eq Ordinals.Ordinal.one_eq_succ_zero.symm) $$ Hfw with Hfw
  iapply hfw 0 i x {kr} k 0 _ $$ [HT HG Hfw]
  · iframe
    iexact Hflag
  iintro ⟨HT, -, HG, -⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  unfold v1
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- The return value discharges the commitment to return, and the thread terminates.
  rw [show (hl(#42) : Exp) = .val v42 from rfl]
  iapply lwp_value_mupd'.mpr
  ihave Hc2 := tlc_one_nat.mpr $$ Hc2
  imod threadExpr_terminate_finally i ⊤ v42 kr Nr (fun _ _ => CoPset.mem_full)
    $$ HT Hc2 HG Hkr HFr with ⟨HT, #Hd⟩
  imodintro
  iapply HΦ
  iframe HT
  isplitr
  · ipureintro
    rfl
  unfold liftTerm
  isplitl
  · iexact Hd
  · ipureintro
    trivial

end Spec

end Lantana.Examples.FlagFork
