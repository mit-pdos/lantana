/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Examples.Flag
public import Lantana.Examples.Handoff
public import Lantana.Examples.World

/-! # A client of the handoff

Rocq `examples/handoff_client.v`.
-/

@[expose] public noncomputable section

namespace Lantana.Examples.HandoffClient

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.Flag (flagTk isFlag isFlagTr flagTrSpec v1)
open Lantana.Examples.Handoff (HandoffG HandoffName isHandoff isTask taskAt handoffInvTrSpec
  handoffTr vNone)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The program -/

/-- `λ _, let b := ref none; fork (receive b); let x := init (); send b set x;
let v := wait x; v`. -/
@[lantana_alias handoff_client.main]
def main : Val :=
  hl_val(λ _,
    let b := ref(none());
    fork(v(&Handoff.receive) b);
    let x := v(&Flag.init) #();
    v(&Handoff.send) b v(&Flag.set) x;
    let r := v(&Flag.wait) x;
    r)

/-- The namespaces of the main thread's commitments: to return, to create a flag and a
handoff. -/
def Nl : Namespace := nroot.@"return"
def Nc : Namespace := nroot.@"handoff_client_flag"

/-! ## The specification -/

section Spec
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [HandoffG GF]

/-- The main proof. Besides returning, the main thread commits to creating a flag and a
handoff cell. The layers: `set` at `0`, the task below `1`, the flag's obligation at `1` (in a
container at `1`), the return obligation and the commitment at `2`. -/
@[lantana_alias handoff_client.main_spec]
theorem main_spec : ∃ μ : Measure, ∀ (i : ThreadId) (kl kc : Oid),
    ⊢@{IProp GF} l{{{ threadExpr i [] hl(v(&main) #()) ∗ thKids i {kl, kc} ∗
          ([∗set] g ∈ ({kl, kc} : Oids), Obl.fuel g 2 μ) ∗ ⌜kl ≠ kc⌝ ∗ oblKids kl ∅ ∗
          oblKids kc ∅ ∗ finallyI Nl kl 1 (exits v1 @ i) ∗
          finallyI Nc kc 1 iprop((∃ (x : Loc) (k : Oid) (ℓ : Layer), isFlag x k ℓ) ∗
            (∃ (b : Loc) (γ : HandoffName) (ℓ : Layer), isHandoff b γ ℓ)) }}}
        hl(v(&main) #()) @ i
      l{{{ (v : Val), RET v; threadExpr i [] hl(&v) ∗
        liftTerm i (fun _ v => iprop(⌜v = v1⌝)) v }}} := by
  obtain ⟨μfi, hfi⟩ := Flag.init_spec (GF := GF)
  obtain ⟨μfs, hfs⟩ := Flag.set_spec (GF := GF)
  obtain ⟨μfw, hfw⟩ := Flag.wait_spec (GF := GF)
  obtain ⟨μhs, hhs⟩ := Handoff.send_spec (GF := GF)
  obtain ⟨μhr, hhr⟩ := Handoff.receive_spec (GF := GF)
  refine ⟨20 + μfi + μhs + μfw, fun i kl kc => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hne, Hkl, Hkc, HFl, HFc⟩ HΦ
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Hfw⟩
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Hhs⟩
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, Hfi⟩
  ihave HF := oblFuels_init _ _ _ $$ HF
  unfold main
  lwp_step HT HG HF with Hlc : 1 +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hc1, Hc2⟩
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_bind hl(allocn(#1, v(none()))) HT
  icases oblFuels_add 1 17 _ $$ HF with ⟨HF1, HF⟩
  iapply lwp_alloc (o := 0) (C := _) (G := {kl, kc}) (R := ∅) $$ [HT HG HF1]
  · iframe HT
    iapply stepPre_nil $$ HG HF1
  iintro %b ⟨HT, ⟨-, HG, -⟩, Hb⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- The receiver's inbox, at layer `0`: an obligation of this thread until the fork moves it to
  -- the receiver. It pays the fork step, its move, and the receiver's steps.
  imod Obl.new ⊤ (.thread i) {kl, kc} 0 (((1 : Nat) : Measure) + (1 + μhr)) $$ [] HG with
    ⟨%gj, %hgj, HG, Kgj, Agj, Fgj, #Wgj⟩
  · iapply parLe_thread
  rw [show (hl_val(none()) : Val) = vNone from rfl]
  icases (pointsTo_halves b _).mp $$ Hb with ⟨Hb, Hb0⟩
  imod Handoff.isHandoff_initialize ⊤ b 1 gj $$ Hb0 Kgj Wgj with ⟨%γ, #Hh, Gv⟩
  icases (Obl.fuel_add gj _ _ _).mp $$ Fgj with ⟨F1, Fgj⟩
  icases (Obl.fuel_add gj _ _ _).mp $$ Fgj with ⟨Fmv, Fhr⟩
  icases oblFuels_add 1 14 _ $$ HF with ⟨HF1, HF⟩
  ihave HF1 := oblFuels_add_obl _ gj 0 _ $$ F1 HF1
  lwp_bind hl(fork(v(&Handoff.receive) #b)) HT
  have hsub : ({gj} : Oids) ⊆ ({kl, kc} : Oids).insert gj := fun z hz => by
    rw [Iris.Std.LawfulSet.mem_singleton] at hz
    subst hz
    exact Std.ExtTreeSet.mem_insert_self
  iapply lwp_fork (o := 0) (G := ({kl, kc} : Oids).insert gj) (R := ∅) {gj}
    iprop(Obl.assigned gj 1 ∗ Obl.fuel gj 0 μhr ∗ (γ.γd ↪VAR{.own (1 : Qp).half} gj))
    hl(v(&Handoff.receive) #b) hsub $$ [] [HT HG HF1 Fmv Agj Fhr Gv]
  · -- The forked thread receives, and terminates when it has run a task.
    iintro %j %Φ' !> ⟨HTj, HGj, Agj, Fhr, Gv⟩ HΦ'
    iapply lwp_mupd
    iapply hhr 0 j b gj γ 1 [] $$ [HTj HGj Fhr Agj Gv]
    · iframe HTj HGj Agj Gv
      isplitl [Fhr]
      · iapply BigSepS.bigSepS_singleton.mpr
        iexact Fhr
      · iexact Hh
    iintro %v ⟨-, -, HGj⟩
    imod Th.terminate ⊤ j $$ HGj with #Hd
    imodintro
    iapply HΦ'
    unfold liftTerm
    isplitl
    · iexact Hd
    · ipureintro
      trivial
  · iframe HT Agj Fhr Gv
    isplitl [HG HF1]
    · iapply stepPre_nil $$ HG HF1
    · unfold oblFuels
      iapply BigSepS.bigSepS_singleton.mpr
      iexists _
      iexact Fmv
  iintro ⟨HT, -, HG, -⟩
  ihave HG := Par.kids_congr (B := {kl, kc}) ?_ $$ HG
  · intro z
    simp at hgj ⊢
    grind
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_bind hl(v(&Flag.init) #()) HT
  -- A container for the flag's obligation, at the flag's layer `1`: the obligation is handed
  -- off from it.
  imod Obl.new ⊤ (.thread i) {kl, kc} 1 (((2 : Nat) : Measure) + (μfi + μhs)) $$ [] HG with
    ⟨%g0, %hg0, HG, Kg0, Ag0, Fg0, #Wg0⟩
  · iapply parLe_thread
  icases (Obl.fuel_add g0 _ _ _).mp $$ Fg0 with ⟨F0, Fg0⟩
  icases (Obl.fuel_add g0 _ _ _).mp $$ Fg0 with ⟨F0fi, F0hs⟩
  imod Obl.fuel_layer_mono_set _ (ℓ₁ := 0) μfi (Ordinals.Ordinal.zero_le _) $$ Hfi with Hfi
  imod Obl.fuel_layer_mono g0 (ℓ₁ := 0) μfi (Ordinals.Ordinal.zero_le _) $$ F0fi with F0fi
  iapply hfi 0 i (({kl, kc} : Oids).insert g0) (.obl g0) ∅ 1 1 _ $$ [HT HG Hfi F0fi Kg0]
  · iframe HT HG Kg0
    isplitl [Hfi F0fi]
    · iapply (bigSepS_insert_oids hg0).mpr
      iframe
    · iapply parLe_obl (ℓq := 1) g0 (Ordinals.Ordinal.le_refl _) $$ Wg0
  iintro %x %k ⟨HT, -, HG, -, Kg0, Hkk, Fk, Htk, #Hflag⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  -- Keep the commitment: the flag and the handoff exist.
  ihave Hc1 := tlc_one_nat.mpr $$ Hc1
  imod finallyI_discharge (E := ⊤) (.thread i) (({kl, kc} : Oids).insert g0)
    (fun _ _ => CoPset.mem_full) (by simp) $$ Hc1 HG Hkc HFc [] with ⟨-, HG, -⟩
  · isplitl
    · iexists x, k, 1
      iexact Hflag
    · iexists b, γ, 1
      iexact Hh
  ihave HG := Par.kids_congr (B := ({kl} : Oids).insert g0) ?_ $$ HG
  · intro z
    simp at hg0 ⊢
    grind
  ihave HF := oblFuels_subset _ (B := {kl}) (fun z hz => by simp_all) $$ HF
  icases oblFuels_add 2 10 _ $$ HF with ⟨HF2, HF⟩
  ihave HF2 := oblFuels_add_obl _ g0 1 _ $$ F0 HF2
  lwp_step HT HG HF2
  lwp_step HT HG HF2
  lwp_expr_simp
  -- Send the task `set x`, with the flag's obligation `k`, from the container `g0`.
  lwp_bind hl(v(&Handoff.send) #b v(&Flag.set) #x) HT
  ihave Hhs := BigSepS.bigSepS_subseteq (Y := ({kl} : Oids)) (fun z hz => by simp_all) $$ Hhs
  imod Obl.fuel_layer_mono_set {kl} (ℓ₁ := 0) μhs (Ordinals.Ordinal.zero_le _) $$ Hhs with Hhs
  imod Obl.fuel_layer_mono g0 (ℓ₁ := 0) μhs (Ordinals.Ordinal.zero_le _) $$ F0hs with F0hs
  have hg0' : g0 ∉ ({kl} : Oids) := fun h => hg0 (by simp_all)
  iapply hhs 0 i b Flag.set hl_val(#x) (({kl} : Oids).insert g0) (.obl g0) {k} {k} γ 1 _
    $$ [HT HG Hhs F0hs Kg0 Fk Hb Htk Hkk]
  · iframe HT HG Hb
    isplitl [Hhs F0hs]
    · iapply (bigSepS_insert_oids hg0').mpr
      iframe
    isplitl [Kg0]
    · iapply Par.kids_congr _ $$ Kg0
      intro z
      simp
    isplitr
    · ipureintro
      exact fun _ h => h
    isplitl [Fk]
    · iapply BigSepS.bigSepS_singleton.mpr
      iexact Fk
    isplitl
    · -- The task: `set x` at layer `0`, with the flag's token and the obligation's children.
      unfold isTask
      iexists 0, iprop(flagTk x k ∗ oblKids k ∅)
      isplit
      · ipureintro
        exact Ordinals.Ordinal.zero_lt_one
      iframe Htk Hkk
      iexists μfs
      unfold taskAt
      iintro %lc' %i' %G' %p' %K'' %C' %Φ'' !> ⟨HT', HG', HF', HK', %hK', Htk', Hkk'⟩ HΦ''
      iapply hfs lc' i' x G' p' K'' k 1 C' $$ [HT' HG' HF' HK' Hkk' Htk']
      · iframe
        isplitl
        · ipureintro
          exact hK' _ (Iris.Std.LawfulSet.mem_singleton.mpr rfl)
        · iexact Hflag
      iintro ⟨HT', Hlc', HG', HK', -⟩
      iapply HΦ''
      iframe
      iapply Par.kids_congr _ $$ HK'
      intro z
      simp only [Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.mem_diff_iff,
        Iris.Std.LawfulSet.mem_singleton]
      grind
    · iexact Hh
  iintro ⟨HT, -, HG, Kg0⟩
  -- The container is empty: discharge it.
  imod Obl.discharge_leaf ⊤ (.thread i) _ g0 Std.ExtTreeSet.mem_insert_self $$ HG [Kg0] Ag0
    with ⟨HG, -⟩
  · iapply Par.kids_congr _ $$ Kg0
    intro z
    simp
  ihave HG := Par.kids_congr (B := {kl}) ?_ $$ HG
  · intro z
    simp at hg0' ⊢
    grind
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  unfold Handoff.vUnit
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- Wait for the flag, at layer `2` above the flag's layer `1`.
  lwp_bind hl(v(&Flag.wait) #x) HT
  ihave Hfw := BigSepS.bigSepS_subseteq (Y := ({kl} : Oids)) (fun z hz => by simp_all) $$ Hfw
  imod Obl.fuel_layer_mono_set {kl} (ℓ₁ := Ordinals.Ordinal.succ 1) (ℓ₂ := 2) μfw
    (Ordinals.Ordinal.le_of_eq rfl) $$ Hfw with Hfw
  iapply hfw 0 i x {kl} k 1 _ $$ [HT HG Hfw]
  · iframe HT HG Hfw
    iexact Hflag
  iintro ⟨HT, -, HG, -⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  unfold v1
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  rw [show (hl(#1) : Exp) = .val hl_val(#1) from rfl]
  iapply lwp_value_mupd'.mpr
  ihave Hc2 := tlc_one_nat.mpr $$ Hc2
  imod threadExpr_terminate_finally i ⊤ hl_val(#1) kl Nl (fun _ _ => CoPset.mem_full)
    $$ HT Hc2 HG Hkl HFl with ⟨HT, #Hd⟩
  imodintro
  iapply HΦ
  iframe HT
  unfold liftTerm
  isplitl
  · iexact Hd
  · ipureintro
    rfl

end Spec

end Lantana.Examples.HandoffClient
