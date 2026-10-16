/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.HeapLang.ProofMode
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

**Skeleton:** the trace-level lemmas are proved; `isFlag_init` and the specifications are
`sorry` until the HeapLang laws (M7).
-/

@[expose] public noncomputable section

namespace Lantana.Examples.Flag

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

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

/-- The until's namespace is outside the invariant's. -/
theorem Np_subseteq : (↑Np : CoPset) ⊆ ⊤ \ ↑Na := by
  intro x hx
  refine Iris.Std.LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun h => ?_⟩
  exact ndot_ne_disjoint N (by decide : "pointsto" ≠ "always") x ⟨hx, h⟩

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
  TrSpec.true ∧ₛ
    □ₛ ((pointsToSpec l v0 𝒰ₛ pointsToSpec l v1) ∨ₛ
      (TrSpec.true ∧ₛ pointsToSpec l v1))

instance guarOf_flagInv (l : Loc) (k : Oid) :
    GuarOf (flagInv (GF := GF) l k)
      ((pointsToSpec l v0 𝒰ₛ pointsToSpec l v1) ∨ₛ
        (TrSpec.true ∧ₛ pointsToSpec l v1)) := by
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

/-- The flag's two values differ. -/
theorem v0_ne_v1 : v0 ≠ v1 := by
  simp [v0, v1]

/-- A location holds one value at a time (Rocq `tr_pointsto_agree`, `temporal_laws.v`). -/
theorem pointsToTr_agree (l : Loc) (dq₁ dq₂ : DFrac) (v₁ v₂ : Val) :
    (TrProp.state (pointstoSat l dq₁ v₁) ∧ₜ TrProp.state (pointstoSat l dq₂ v₂) :
      TrProp Exp State) ⊆ ⌜v₁ = v₂⌝ₜ := by
  intro τ ⟨h₁, h₂⟩
  simp only [TrProp.state, pointstoSat] at h₁ h₂
  exact (by simpa using h₁.symm.trans h₂ : v₁ = v₂)

omit [ModelGS GF] [HeapGS GF] in
/-- The until gives the eventually; in the other branch the flag is `1`, not `0`. -/
@[lantana_alias flag_response_ext]
theorem flagResponse_ext (l : Loc) : (flagTrSpec (GF := GF) l).external ⊆ flagResponse l := by
  intro τ ⟨_, h⟩ m hm h₀
  rcases h m hm with hU | ⟨_, h₁⟩
  · exact TrProp.until_eventually _ hU
  · exact absurd (pointsToTr_agree l (.own 1) (.own 1) v0 v1 _ ⟨h₀, h₁⟩) v0_ne_v1

@[lantana_alias is_flag_response]
theorem isFlag_response (l : Loc) (k : Oid) (ℓ : Layer) :
    ⊢@{IProp GF} isFlag l k ℓ ⊨ₜ
      (flagTrSpec l).cast (flagResponse l) (flagResponse_ext l) :=
  (guar_isFlag l k ℓ).trans (guar_cast _ _)

/-- Initialization: a new obligation below `p` carrying the flag. -/
@[lantana_alias is_flag_init]
theorem isFlag_init (E : CoPset) (l : Loc) (p : Parent) (K : Oids) (ℓ : Layer) (μ : Measure) :
    parLe (GF := GF) p ℓ ⊢ l ↦ some v0 -∗ Par.kids p K -∗
      |={E}=>m ∃ k : Oid, ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ oblKids k ∅ ∗
        Obl.fuel k ℓ μ ∗ flagTk l k ∗ isFlag l k ℓ := by
  iintro #B Ptr Kp
  imod untilI_alloc (E := E) p K ℓ μ $$ B Kp with ⟨%k, %hk, Kp, Kk, Fk, #Wk, H⟩
  imod H $$ %E %Np %iprop(l ↦ some v0) %iprop(l ↦ some v1) [Ptr] with H
  · inext
    iexact Ptr
  icases untilI_frac_split (q₁ := (1 : Qp).half) (q₂ := (1 : Qp).half)
    (Qp.half_add_half 1).symm $$ H with ⟨H1, H2⟩
  imod alwaysI_alloc (E := E) (N := Na) (P := flagInv l k) $$ [H1] with #HA
  · inext
    unfold flagInv
    ileft
    iexact H1
  imodintro
  iexists k
  isplitr
  · ipureintro
    exact hk
  unfold flagTk isFlag
  iframe Kp Kk Fk H2
  isplitl
  · iexact Wk
  · iexact HA

end Invariant

/-! ## Specifications -/

section Helpers
variable {GF : BundledGFunctors}

/-- The precondition of a step without witnesses. -/
theorem stepPre_nil [ModelGS GF] (i : ThreadId) (G : Oids) :
    thKids i G ⊢ oblFuels G ((1 : Nat) : Measure) -∗ stepPre (GF := GF) i G ∅ := by
  iintro HG HF
  simp only [stepPre]
  iframe HG HF
  unfold witLayers
  iapply BigSepS.bigSepS_empty.mpr
  iempintro

instance instPureExecNegBool {b : Bool} :
    PureExec True 1 (Exp.unop .neg (.ofVal (.lit (.bool b)))) (.ofVal (.lit (.bool !b))) :=
  ⟨fun _ => (instPureExecUnOp (op := .neg) (v := .lit (.bool b))
    (v' := .lit (.bool !b))).pureExec rfl⟩

/-- No witnesses. -/
theorem witLayers_empty [ModelGS GF] : ⊢ witLayers (GF := GF) ∅ := by
  unfold witLayers
  iapply BigSepS.bigSepS_empty.mpr
  iempintro

/-- The precondition of a step that observes the witness `k`. -/
theorem stepPre_wit [ModelGS GF] (i : ThreadId) (G : Oids) (k : Oid) (ℓ : Layer) :
    thKids i G ⊢ oblFuels G ((1 : Nat) : Measure) -∗ Wit.layer k ℓ -∗
      stepPre (GF := GF) i G {k} := by
  iintro HG HF Hk
  simp only [stepPre]
  iframe HG HF
  unfold witLayers
  iapply BigSepS.bigSepS_singleton.mpr
  iexists ℓ
  iexact Hk

/-- What a step that observes the witness `k` gives back. -/
theorem witCreds_singleton [ModelGS GF] (k : Oid) :
    witCreds (GF := GF) {k} ⊢ Wit.cred k 1 ∨ Obl.discharged k := by
  unfold witCreds
  exact BigSepS.bigSepS_singleton.mp

end Helpers

section Specs
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]

@[lantana_alias Flag_init_spec]
theorem init_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids) (p : Parent)
    (K : Oids) (ℓ : Layer) (m : Measure) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&init) #()) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ parLe p ℓ ∗ Par.kids p K }}}
        hl(v(&init) #()) @ i
      l{{{ (x : Loc) (k : Oid), RET hl_val(#x); threadExpr i C hl(#x) ∗ £ₒ lc ∗
        thKids i G ∗ ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ oblKids k ∅ ∗
        Obl.fuel k ℓ m ∗
        flagTk x k ∗ isFlag x k ℓ }}} := by
  refine ⟨10, fun lc i G p K ℓ m C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, #HB, HK⟩ HΦ
  ihave HF := oblFuels_init G 10 0 $$ HF
  unfold init
  lwp_pure HT
  iexists G, 9, ∅, lc
  isplitl [HG HF]
  · iframe HG
    isplitl [HF]
    · iexact HF
    · unfold witLayers
      iapply BigSepS.bigSepS_empty.mpr
      iempintro
  iintro HG HF - Hlc HT
  lwp_expr_simp
  imodintro
  iapply lwp_mupd
  icases oblFuels_add 1 8 G $$ HF with ⟨HF, -⟩
  iapply lwp_alloc (o := 0) (C := C) (G := G) (R := ∅) $$ [HT HG HF]
  · iframe HT
    iapply stepPre_nil $$ HG HF
  iintro %x ⟨HT, ⟨-, HG, -⟩, Hx⟩
  rw [show (hl_val(#0) : Val) = v0 from rfl]
  imod isFlag_init ⊤ x p K ℓ m $$ HB Hx HK with ⟨%k, %hk, HK, Hkk, Hf, Htk, #Hflag⟩
  imodintro
  iapply HΦ $$ %x %k
  iframe
  isplitl
  · ipureintro
    exact hk
  · iexact Hflag

@[lantana_alias Flag_set_spec]
theorem set_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (l : Loc) (G : Oids)
    (p : Parent) (K : Oids) (k : Oid) (ℓ : Layer) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&set) #l) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ Par.kids p K ∗ ⌜k ∈ K⌝ ∗
          oblKids k ∅ ∗ flagTk l k ∗ isFlag l k ℓ }}}
        hl(v(&set) #l) @ i
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i G ∗
        Par.kids p (K.erase k) ∗ Obl.discharged k }}} := by
  refine ⟨10, fun lc i l G p K k ℓ C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, HK, %hk, Hkk, HU, #Hflag⟩ HΦ
  ihave HF := oblFuels_init G 10 0 $$ HF
  unfold isFlag set
  icases Hflag with ⟨#Wk, #HA⟩
  lwp_pure HT
  iexists G, 9, ∅, lc +ₕ 1 +ₕ 1
  isplitl [HG HF]
  · iframe HG
    isplitl [HF]
    · iexact HF
    · unfold witLayers
      iapply BigSepS.bigSepS_empty.mpr
      iempintro
  iintro HG HF - Hlc HT
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc2⟩
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc1⟩
  lwp_expr_simp
  imodintro
  icases oblFuels_add 1 8 G $$ HF with ⟨HF, -⟩
  ihave Hacc := alwaysI_acc (E := ⊤) (N := Na) (P := flagInv l k)
    (fun _ _ => CoPset.mem_full) $$ HA
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  rw [val_to_ofVal]
  imod Hacc with ⟨Hinv, Hclose⟩
  iapply lwp_credit_later $$ Hc1
  inext
  unfold flagInv flagTk
  icases Hinv with (Hinv | ⟨#Hd, -⟩)
  rotate_left
  · iexfalso
    iapply untilI_discharged_false $$ HU Hd
  ihave HU := untilI_frac_add (q := 1) (Qp.half_add_half 1).symm $$ HU Hinv
  ihave HU := untilI_discharge (E := ⊤ \ ↑Na) Np_subseteq $$ HU
  ihave HU := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ HU
  imod HU
  iapply lwp_credit_later $$ Hc2
  inext
  icases HU with ⟨Hl, Hdis⟩
  rw [← val_to_ofVal]
  iapply lwp_store (o := 0) (C := C) (G := G) (R := ∅) $$ [HT HG HF Hl]
  · iframe HT Hl
    iapply stepPre_nil $$ HG HF
  iintro ⟨HT, ⟨-, HG, -⟩, Hl⟩
  rw [show (hl_val(#1) : Val) = v1 from rfl]
  imod Hdis $$ %p %K %hk HK Hkk Hl %_ with H
  imod H with ⟨Hl, HK, #Hd⟩
  imodintro
  imod Hclose $$ [Hl]
  · inext
    iright
    iframe Hl
    iexact Hd
  imodintro
  iapply HΦ
  iframe
  iexact Hd

/-- The same operations when the flag's obligation is a child of the calling thread itself. -/
@[lantana_alias Flag_init_thread_spec]
theorem init_thread_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (G : Oids) (ℓ : Layer)
    (m : Measure) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&init) #()) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) }}}
        hl(v(&init) #()) @ i
      l{{{ (x : Loc) (k : Oid), RET hl_val(#x); threadExpr i C hl(#x) ∗ £ₒ lc ∗
        ⌜k ∉ G⌝ ∗ thKids i (G.insert k) ∗ oblKids k ∅ ∗ Obl.fuel k ℓ m ∗
        flagTk x k ∗ isFlag x k ℓ }}} := by
  refine ⟨10, fun lc i G ℓ m C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF⟩ HΦ
  ihave HF := oblFuels_init G 10 0 $$ HF
  unfold init
  lwp_pure HT
  iexists G, 9, ∅, lc
  isplitl [HG HF]
  · iframe HG
    isplitl [HF]
    · iexact HF
    · unfold witLayers
      iapply BigSepS.bigSepS_empty.mpr
      iempintro
  iintro HG HF - Hlc HT
  lwp_expr_simp
  imodintro
  iapply lwp_mupd
  icases oblFuels_add 1 8 G $$ HF with ⟨HF, -⟩
  iapply lwp_alloc (o := 0) (C := C) (G := G) (R := ∅) $$ [HT HG HF]
  · iframe HT
    iapply stepPre_nil $$ HG HF
  iintro %x ⟨HT, ⟨-, HG, -⟩, Hx⟩
  rw [show (hl_val(#0) : Val) = v0 from rfl]
  imod isFlag_init ⊤ x (.thread i) G ℓ m $$ [] Hx HG with
    ⟨%k, %hk, HG, Hkk, Hf, Htk, #Hflag⟩
  · iapply parLe_thread
  imodintro
  iapply HΦ $$ %x %k
  iframe
  isplitl
  · ipureintro
    exact hk
  · iexact Hflag

@[lantana_alias Flag_set_thread_spec]
theorem set_thread_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (l : Loc) (G : Oids)
    (k : Oid) (ℓ : Layer) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&set) #l) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ ⌜k ∈ G⌝ ∗ oblKids k ∅ ∗
          flagTk l k ∗ isFlag l k ℓ }}}
        hl(v(&set) #l) @ i
      l{{{ RET hl_val(#()); threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i (G.erase k) ∗
        Obl.discharged k }}} := by
  refine ⟨10, fun lc i l G k ℓ C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hk, Hkk, HU, #Hflag⟩ HΦ
  ihave HF := oblFuels_init G 10 0 $$ HF
  unfold isFlag set
  icases Hflag with ⟨#Wk, #HA⟩
  lwp_pure HT
  iexists G, 9, ∅, lc +ₕ 1 +ₕ 1
  isplitl [HG HF]
  · iframe HG
    isplitl [HF]
    · iexact HF
    · unfold witLayers
      iapply BigSepS.bigSepS_empty.mpr
      iempintro
  iintro HG HF - Hlc HT
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc2⟩
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc1⟩
  lwp_expr_simp
  imodintro
  icases oblFuels_add 1 8 G $$ HF with ⟨HF, -⟩
  ihave Hacc := alwaysI_acc (E := ⊤) (N := Na) (P := flagInv l k)
    (fun _ _ => CoPset.mem_full) $$ HA
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  rw [val_to_ofVal]
  imod Hacc with ⟨Hinv, Hclose⟩
  iapply lwp_credit_later $$ Hc1
  inext
  unfold flagInv flagTk
  icases Hinv with (Hinv | ⟨#Hd, -⟩)
  rotate_left
  · iexfalso
    iapply untilI_discharged_false $$ HU Hd
  ihave HU := untilI_frac_add (q := 1) (Qp.half_add_half 1).symm $$ HU Hinv
  ihave HU := untilI_discharge (E := ⊤ \ ↑Na) Np_subseteq $$ HU
  ihave HU := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ HU
  imod HU
  iapply lwp_credit_later $$ Hc2
  inext
  icases HU with ⟨Hl, Hdis⟩
  rw [← val_to_ofVal]
  iapply lwp_store (o := 0) (C := C) (G := G) (R := ∅) $$ [HT HG HF Hl]
  · iframe HT Hl
    iapply stepPre_nil $$ HG HF
  iintro ⟨HT, ⟨-, HG, -⟩, Hl⟩
  rw [show (hl_val(#1) : Val) = v1 from rfl]
  imod Hdis $$ %(.thread i) %G %hk HG Hkk Hl %_ with H
  imod H with ⟨Hl, HG, #Hd⟩
  imodintro
  imod Hclose $$ [Hl]
  · inext
    iright
    iframe Hl
    iexact Hd
  imodintro
  iapply HΦ
  iframe
  iexact Hd

/-- Waiting is fair: the caller's fuel is at the layer above the flag's witness layer. -/
@[lantana_alias Flag_wait_spec]
theorem wait_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (l : Loc) (G : Oids) (k : Oid)
    (ℓ : Layer) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&wait) #l) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g ℓ.succ μ) ∗ isFlag l k ℓ }}}
        hl(v(&wait) #l) @ i
      l{{{ RET v1; threadExpr i C hl(#1) ∗ £ₒ lc ∗ thKids i G ∗ Obl.discharged k }}} := by
  refine ⟨5 * ▽ + 5, fun lc i l G k ℓ C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, #Hflag⟩ HΦ
  unfold isFlag
  icases Hflag with ⟨#Wk, #HA⟩
  icases (Obl.fuel_add_set G ℓ.succ (5 * ▽) 5).mp $$ HF with ⟨HFw, HF⟩
  imod Wit.layer_ind k ℓ G ℓ.succ 5
    iprop(threadExpr i C hl(v(&wait) #l) -∗ thKids i G -∗
      (threadExpr i C hl(#1) ∗ £ₒ lc ∗ thKids i G ∗ Obl.discharged k -∗ Φ v1) -∗
      ([∗set] g ∈ G, Obl.fuel g ℓ.succ 5) -∗ lWP hl(v(&wait) #l) @ i {{ Φ }})
    (Ordinals.Ordinal.lt_succ ℓ) $$ [HFw] with HP
  · isplitl []
    · imodintro
      iintro IH
      imodintro
      iintro HT HG HΦ HF
      ihave HF := oblFuels_init G 5 ℓ.succ $$ HF
      unfold wait
      lwp_pure HT
      iexists G, 4, ∅, 1 +ₕ 1
      isplitl [HG HF]
      · iframe HG HF
        iapply witLayers_empty
      iintro HG HF - Hc HT
      icases tlc_split.mp $$ Hc with ⟨Hc1, Hc2⟩
      lwp_expr_simp
      simp only [val_to_ofVal]
      imodintro
      lwp_bind hl(!#l) HT
      ihave Hacc := alwaysI_acc (E := ⊤) (N := Na) (P := flagInv l k)
        (fun _ _ => CoPset.mem_full) $$ HA
      ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
      imod Hacc with ⟨Hinv, Hclose⟩
      iapply lwp_credit_later $$ Hc1
      inext
      unfold flagInv
      icases Hinv with (Hinv | ⟨#Hd, Hl⟩)
      · ihave Hu := untilI_acc (E := ⊤ \ ↑Na) Np_subseteq $$ Hinv
        ihave Hu := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hu
        imod Hu
        iapply lwp_credit_later $$ Hc2
        inext
        icases Hu with ⟨Hl, Hucl⟩
        icases oblFuels_add 1 3 G $$ HF with ⟨HF1, HF⟩
        rw [← val_to_ofVal]
        iapply lwp_load (o := 0) (C := _ ++ C) (G := G) (R := {k}) $$ [HT HG HF1 Hl]
        · iframe HT Hl
          iapply stepPre_wit $$ HG HF1 Wk
        iintro ⟨HT, ⟨-, HG, HW⟩, Hl⟩
        icases witCreds_singleton k $$ HW with (Hwc | #Hd)
        rotate_left
        · imod Hucl $$ [Hl] with Hu
          · inext
            iexact Hl
          iexfalso
          iapply untilI_discharged_false $$ Hu Hd
        imod Hucl $$ [Hl] with Hu
        · inext
          iexact Hl
        imodintro
        imod Hclose $$ [Hu]
        · inext
          ileft
          iexact Hu
        imodintro
        ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
        lwp_expr_simp
        simp only [val_to_ofVal]
        lwp_pure HT
        iexists G, 2, ∅, 0
        isplitl [HG HF]
        · iframe HG HF
          iapply witLayers_empty
        iintro HG HF - - HT
        rw [show (v0 == hl_val(#1)) = false from rfl]
        imodintro
        lwp_pure HT
        iexists G, 1, ∅, 0
        isplitl [HG HF]
        · iframe HG HF
          iapply witLayers_empty
        iintro HG HF - - HT
        simp only [Bool.not_false]
        imodintro
        lwp_pure HT
        iexists G, 0, ∅, 0
        isplitl [HG HF]
        · iframe HG HF
          iapply witLayers_empty
        iintro HG HF - - HT
        imod IH $$ Hwc with ⟨HF, HP⟩
        imodintro
        iapply HP $$ HT HG HΦ HF
      · icases oblFuels_add 1 3 G $$ HF with ⟨HF1, HF⟩
        rw [← val_to_ofVal]
        iapply lwp_load (o := 0) (C := _ ++ C) (G := G) (R := ∅) $$ [HT HG HF1 Hl]
        · iframe HT Hl
          iapply stepPre_nil $$ HG HF1
        iintro ⟨HT, ⟨-, HG, -⟩, Hl⟩
        imod Hclose $$ [Hl]
        · inext
          iright
          iframe Hl
          iexact Hd
        imodintro
        ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
        lwp_expr_simp
        simp only [val_to_ofVal]
        lwp_pure HT
        iexists G, 2, ∅, 0
        isplitl [HG HF]
        · iframe HG HF
          iapply witLayers_empty
        iintro HG HF - - HT
        rw [show (v1 == hl_val(#1)) = true from rfl]
        imodintro
        lwp_pure HT
        iexists G, 1, ∅, 0
        isplitl [HG HF]
        · iframe HG HF
          iapply witLayers_empty
        iintro HG HF - - HT
        simp only [Bool.not_true]
        imodintro
        lwp_pure HT
        iexists G, 0, ∅, lc
        isplitl [HG HF]
        · iframe HG HF
          iapply witLayers_empty
        iintro HG - - Hlc HT
        imodintro
        iapply lwp_value'
        rw [show Φ hl_val(#1) = Φ v1 from rfl]
        iapply HΦ
        iframe
        iexact Hd
    isplitl []
    · iexact Wk
    · iexact HFw
  iapply HP $$ HT HG HΦ HF

end Specs

/-! ## Traces -/

section Traces
variable {GF : BundledGFunctors}

/-- The flag at the level of traces: `0` until `1`, and `1` from then on. -/
@[lantana_alias is_flag_tr]
def isFlagTr (l : Loc) : TrProp Exp State :=
  □ₜ ((pointsToTr l v0 𝒰ₜ pointsToTr l v1) ∨ₜ pointsToTr l v1)

@[lantana_alias flag_trSpec_impl]
theorem flagTrSpec_impl (l : Loc) : (flagTrSpec (GF := GF) l).external ⊆ isFlagTr l :=
  fun _ ⟨_, h⟩ m hm => (h m hm).imp id And.right

/-- The run `0, 1, 0, 1, 1, …` of a single idle thread. -/
@[lantana_alias flag_run]
def flagRun (l : Loc) (n : Nat) : TraceState Exp State :=
  { cfg := ([], ⟨(∅ : Std.ExtTreeMap Loc (Option Val) compare).insert l
      (some (if n = 0 ∨ n = 2 then v0 else v1))⟩),
    thread := 0 }

@[lantana_alias flag_run_at]
theorem flagRun_at (l : Loc) (m : Nat) (v : Val) :
    pointsToTr l v ⟨m, flagRun l⟩ ↔ v = if m = 0 ∨ m = 2 then v0 else v1 := by
  simp only [TrProp.state, Trace.cfg, Trace.now, flagRun, pointstoSat]
  rw [Std.ExtTreeMap.getElem?_insert_self]
  simp [eq_comm]

/-- The run satisfies the flag's guarantee … -/
@[lantana_alias flag_run_satisfies_guarantee]
theorem flagRun_satisfies_guarantee (l : Loc) :
    (flagTrSpec (GF := GF) l).external ⟨0, flagRun l⟩ := by
  refine ⟨trivial, fun m _ => ?_⟩
  by_cases hm : m = 0 ∨ m = 2
  · refine .inl ⟨m + 1, Nat.le_succ m, (flagRun_at l _ _).mpr (ite_eq_right (by omega)).symm,
      fun n (hn : m ≤ n) (hn' : n < m + 1) =>
        (flagRun_at l _ _).mpr (ite_eq_left (by omega)).symm⟩
  · exact .inr ⟨trivial, (flagRun_at l _ _).mpr (ite_eq_right hm).symm⟩

/-- … although the flag goes back to `0`: the guarantee describes each state, not the history
(see `flag_stable.v`). -/
@[lantana_alias flag_run_goes_back]
theorem flagRun_goes_back (l : Loc) :
    ¬ (□ₜ (pointsToTr l v1 →ₜ □ₜ pointsToTr l v1)) ⟨0, flagRun l⟩ := fun h =>
  v0_ne_v1 <| ((flagRun_at l 2 v1).mp <|
    h 1 (Nat.zero_le _) ((flagRun_at l 1 v1).mpr (ite_eq_right (by omega)).symm) 2
      (Nat.le_succ 1)).symm

end Traces

end Lantana.Examples.Flag
