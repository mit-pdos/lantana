/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Examples.Flag
public import Lantana.Examples.World

/-! # A discharge in the pre-step modality, with nested structures

Rocq `examples/cert_discharge.v`, a test of the adequacy proof: the commitment
`◇ (x ↦ 1 ∗ alwaysI Na (y ↦ 7) ∗ ◇ (x ↦ 2))` (the `finallyI` on `kq` with the right formula
`cdQ x y kf`) is discharged in the pre-step modality of `x ← #2`, which destroys `x ↦ 1`; the
always on `y ↦ 7` is allocated in the same modality, and the nested commitment `◇ (x ↦ 2)` (on
`kf`) is discharged after the store, before the thread terminates. Adequacy records the nested
always and until at the discharge position.

`cert_discharge_adequacy` is the end-to-end statement, from `lwp_adequacy_temporal` in the
closed world `ExGF` (as `FlagFork.main_adequacy`): the initial heap holds `x ↦ 0` and `y ↦ 7`,
whose points-tos come from `heapState_init`; the main thread allocates both obligations in
`main_pre`. At the level of traces (`rMain`): eventually `x` holds `1` while `y` holds `7` from
then on and `x` later holds `2`, and eventually `x` holds `2`. `cert_discharge_safety_adequacy`
is the safety statement.

Statement adaptations: thread ids are list positions, so the main thread is `0`; locations
`x = ⟨0⟩`, `y = ⟨1⟩`. The guarantee of a `finallyI` is inferred as `⌜True⌝ₛ 𝒰ₛ G`, which is
`◇ₛ G` by definition.
-/

@[expose] public noncomputable section

namespace Lantana.Examples.CertDischarge

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.Flag (pointsToSpec pointsToTr)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The program -/

/-- `λ x y, x ← 1; x ← 2; ()`. -/
@[lantana_alias CertDischarge.main]
def main : Val := hl_val(λ x y, x ← #1; x ← #2; #())

/-- The values stored. -/
def v0 : Val := hl_val(#0)
def v1 : Val := hl_val(#1)
def v2 : Val := hl_val(#2)
def v7 : Val := hl_val(#7)

/-- The namespaces of the two commitments and of the always. -/
def Nq : Namespace := nroot.@"cert_discharge_q"
def Nf : Namespace := nroot.@"cert_discharge_f"
def Na : Namespace := nroot.@"cert_discharge_always"

/-! ## The specification -/

section Spec
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]

/-- The right formula of the first commitment: the state at the discharge, a trace-visible
invariant allocated in the same pre-step modality, and the second commitment. -/
@[lantana_alias cd_Q]
def cdQ (x y : Loc) (kf : Oid) : IProp GF :=
  iprop(x ↦ some v1 ∗ alwaysI Na iprop(y ↦ some v7) ∗ finallyI Nf kf 1 iprop(x ↦ some v2))

/-- What `cdQ` guarantees. -/
def cdQSpec (x y : Loc) : TrSpec Exp State GF :=
  pointsToSpec x v1 ∧ₛ □ₛ pointsToSpec y v7 ∧ₛ ◇ₛ pointsToSpec x v2

instance guarOf_cdQ (x y : Loc) (kf : Oid) : GuarOf (cdQ (GF := GF) x y kf) (cdQSpec x y) := by
  unfold cdQ cdQSpec finallyI; exact ⟨GuarOf.guar_of⟩

@[lantana_alias guar_cd_Q]
theorem guar_cdQ (x y : Loc) (kf : Oid) : ⊢@{IProp GF} cdQ x y kf ⊨ₜ cdQSpec x y :=
  GuarOf.guar_of

/-- The main proof: `kq` is discharged in the pre-step modality of the second store, `kf` after
it. -/
@[lantana_alias cert_discharge.main_spec]
theorem main_spec : ∃ μ : Measure, ∀ (i : ThreadId) (kq kf : Oid) (x y : Loc),
    ⊢@{IProp GF} l{{{ threadExpr i [] hl(v(&main) #x #y) ∗ thKids i {kq, kf} ∗
          ([∗set] g ∈ ({kq, kf} : Oids), Obl.fuel g 0 μ) ∗ ⌜kq ≠ kf⌝ ∗ oblKids kq ∅ ∗
          oblKids kf ∅ ∗ x ↦ some v0 ∗ y ↦ some v7 ∗
          finallyI Nq kq 1 (cdQ x y kf) ∗ finallyI Nf kf 1 iprop(x ↦ some v2) }}}
        hl(v(&main) #x #y) @ i
      l{{{ RET hl_val(#()); threadExpr i [] hl(#()) ∗
        liftTerm i (fun _ _ => iprop(True)) hl_val(#()) }}} := by
  refine ⟨10, fun i kq kf x y => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hne, Hkq, Hkf, Hx, Hy, HQ, HFf⟩ HΦ
  ihave HF := oblFuels_init _ 10 0 $$ HF
  unfold main
  lwp_step HT HG HF with Hlc : 1 +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hc1, Hc2⟩
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- `x ← #1`
  lwp_bind hl(#x ← #1) HT
  icases oblFuels_add 1 6 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_store (o := 0) (G := {kq, kf}) (R := ∅) x v0 hl_val(#1)
    $$ [HT HG HF1 Hx]
  · iframe HT Hx
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, Hx⟩
  rw [show (hl_val(#1) : Val) = v1 from rfl]
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- `x ← #2`: the discharge of `kq` happens in the pre-step modality of this store.
  lwp_bind hl(#x ← #2) HT
  imod alwaysI_alloc (E := ⊤) (N := Na) (P := iprop(y ↦ some v7)) $$ [Hy] with #HA
  · inext
    iexact Hy
  ihave Hc1 := tlc_one_nat.mpr $$ Hc1
  imod finallyI_discharge (E := ⊤) (.thread i) {kq, kf} (fun _ _ => CoPset.mem_full) (by simp)
    $$ Hc1 HG Hkq HQ [Hx HFf] with ⟨HQ, HG, -⟩
  · unfold cdQ
    iframe Hx HFf
    iexact HA
  ihave HG := Par.kids_congr (B := {kf}) ?_ $$ HG
  · intro z
    simp
    grind
  ihave HF := oblFuels_subset _ (B := {kf}) (fun z hz => by simp_all) $$ HF
  unfold cdQ
  icases HQ with ⟨Hx, -, HFf⟩
  icases oblFuels_add 1 3 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_store (o := 0) (G := {kf}) (R := ∅) x v1 hl_val(#2) $$ [HT HG HF1 Hx]
  · iframe HT Hx
    iapply stepPre_nil $$ HG HF1
  iintro ⟨HT, ⟨-, HG, -⟩, Hx⟩
  rw [show (hl_val(#2) : Val) = v2 from rfl]
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- The nested commitment, then termination.
  iapply lwp_value_mupd'.mpr
  ihave Hc2 := tlc_one_nat.mpr $$ Hc2
  imod finallyI_discharge (E := ⊤) (.thread i) {kf} (fun _ _ => CoPset.mem_full) (by simp)
    $$ Hc2 HG Hkf HFf Hx with ⟨-, HG, -⟩
  imod Th.terminate ⊤ i $$ [HG] with #Hd
  · iapply Par.kids_congr _ $$ HG
    intro z
    simp
  imodintro
  iapply HΦ
  iframe HT
  unfold liftTerm
  isplitl
  · iexact Hd
  · ipureintro
    trivial

end Spec

end Lantana.Examples.CertDischarge
