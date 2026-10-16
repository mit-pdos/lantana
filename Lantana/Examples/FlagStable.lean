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

The specifications are proved as `Flag`'s, with the same measures; `set` allocates the
invariant of the set flag after its store, and `wait` reads the set flag from it. Everything
here is proved, from the obligation-forest interface and the rules of temporal formulas (whose
own proofs are M4–M6).
-/

@[expose] public noncomputable section

namespace Lantana.Examples.FlagStable

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.Flag (init set wait v0 v1 N Na Np pointsToSpec pointsToTr flagRun)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

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

/-- The flag's guarantee as an instance, for the inference (and checking) of the guarantees of
formulas containing `isFlag`. -/
instance guarOf_isFlag (l : Loc) (k : Oid) (ℓ : Layer) :
    GuarOf (isFlag (GF := GF) l k ℓ) (flagTrSpec l) :=
  ⟨guar_isFlag l k ℓ⟩

/-- The setter's token's guarantee as an instance. -/
instance guarOf_flagTk (l : Loc) (k : Oid) :
    GuarOf (flagTk (GF := GF) l k) (pointsToSpec l v0 𝒰ₛ □ₛ pointsToSpec l v1) :=
  ⟨guar_flagTk l k⟩

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
        Obl.fuel k ℓ μ ∗ flagTk l k ∗ isFlag l k ℓ := by
  iintro #B Ptr Kp
  imod untilI_alloc (E := E) p K ℓ μ $$ B Kp with ⟨%k, %hk, Kp, Kk, Fk, #Wk, H⟩
  imod H $$ %E %Np %iprop(l ↦ some v0) %(alwaysI Nv iprop(l ↦ some v1)) [Ptr] with H
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
        flagTk x k ∗ isFlag x k ℓ }}} := by
  refine ⟨10, fun lc i G p K ℓ m C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, #HB, HK⟩ HΦ
  ihave HF := oblFuels_init G 10 0 $$ HF
  unfold init
  lwp_step HT HG HF with Hlc : lc
  lwp_expr_simp
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

/-- `set` allocates the invariant of the set flag after its store. -/
@[lantana_alias flag_stable.Flag_set_spec]
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
  unfold isFlag Flag.set
  icases Hflag with ⟨#Wk, #HA⟩
  lwp_step HT HG HF with Hlc : lc +ₕ 1 +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc2⟩
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc1⟩
  lwp_expr_simp
  icases oblFuels_add 1 8 G $$ HF with ⟨HF, -⟩
  ihave Hacc := alwaysI_acc (E := ⊤) (N := Na) (P := flagInv l k)
    (fun _ _ => CoPset.mem_full) $$ HA
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨Hinv, Hclose⟩
  iapply lwp_credit_later $$ Hc1
  inext
  unfold flagInv flagTk
  icases Hinv with (Hinv | ⟨#Hd, -⟩)
  rotate_left
  · iexfalso
    iapply untilI_discharged_false $$ HU Hd
  ihave HU := untilI_frac_add (q := 1) (Qp.half_add_half 1).symm $$ HU Hinv
  ihave HU := untilI_discharge (E := ⊤ \ ↑Na) Flag.Np_subseteq $$ HU
  ihave HU := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ HU
  imod HU
  iapply lwp_credit_later $$ Hc2
  inext
  icases HU with ⟨Hl, Hdis⟩
  iapply lwp_store (o := 0) (C := C) (G := G) (R := ∅) $$ [HT HG HF Hl]
  · iframe HT Hl
    iapply stepPre_nil $$ HG HF
  iintro ⟨HT, ⟨-, HG, -⟩, Hl⟩
  rw [show (hl_val(#1) : Val) = v1 from rfl]
  -- The set flag becomes an invariant: the right formula of the until.
  imod alwaysI_alloc (N := Nv) (P := iprop(l ↦ some v1)) $$ [Hl] with #Av
  · inext
    iexact Hl
  imod Hdis $$ %p %K %hk HK Hkk Av %_ with H
  imod H with ⟨-, HK, #Hd⟩
  imodintro
  imod Hclose $$ []
  · inext
    iright
    isplitl
    · iexact Hd
    · iexact Av
  imodintro
  iapply HΦ
  iframe
  iexact Hd

/-- The same operations when the flag's obligation is a child of the calling thread itself. -/
@[lantana_alias flag_stable.Flag_init_thread_spec]
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
  lwp_step HT HG HF with Hlc : lc
  lwp_expr_simp
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

@[lantana_alias flag_stable.Flag_set_thread_spec]
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
  unfold isFlag Flag.set
  icases Hflag with ⟨#Wk, #HA⟩
  lwp_step HT HG HF with Hlc : lc +ₕ 1 +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc2⟩
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc1⟩
  lwp_expr_simp
  icases oblFuels_add 1 8 G $$ HF with ⟨HF, -⟩
  ihave Hacc := alwaysI_acc (E := ⊤) (N := Na) (P := flagInv l k)
    (fun _ _ => CoPset.mem_full) $$ HA
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨Hinv, Hclose⟩
  iapply lwp_credit_later $$ Hc1
  inext
  unfold flagInv flagTk
  icases Hinv with (Hinv | ⟨#Hd, -⟩)
  rotate_left
  · iexfalso
    iapply untilI_discharged_false $$ HU Hd
  ihave HU := untilI_frac_add (q := 1) (Qp.half_add_half 1).symm $$ HU Hinv
  ihave HU := untilI_discharge (E := ⊤ \ ↑Na) Flag.Np_subseteq $$ HU
  ihave HU := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ HU
  imod HU
  iapply lwp_credit_later $$ Hc2
  inext
  icases HU with ⟨Hl, Hdis⟩
  iapply lwp_store (o := 0) (C := C) (G := G) (R := ∅) $$ [HT HG HF Hl]
  · iframe HT Hl
    iapply stepPre_nil $$ HG HF
  iintro ⟨HT, ⟨-, HG, -⟩, Hl⟩
  rw [show (hl_val(#1) : Val) = v1 from rfl]
  -- The set flag becomes an invariant: the right formula of the until.
  imod alwaysI_alloc (N := Nv) (P := iprop(l ↦ some v1)) $$ [Hl] with #Av
  · inext
    iexact Hl
  imod Hdis $$ %(.thread i) %G %hk HG Hkk Av %_ with H
  imod H with ⟨-, HG, #Hd⟩
  imodintro
  imod Hclose $$ []
  · inext
    iright
    isplitl
    · iexact Hd
    · iexact Av
  imodintro
  iapply HΦ
  iframe
  iexact Hd

/-- Waiting is fair: the caller's fuel is at the layer above the flag's witness layer. -/
@[lantana_alias flag_stable.Flag_wait_spec]
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
      lwp_step HT HG HF with Hc : 1 +ₕ 1
      icases tlc_split.mp $$ Hc with ⟨Hc1, Hc2⟩
      lwp_expr_simp
      lwp_bind hl(!#l) HT
      ihave Hacc := alwaysI_acc (E := ⊤) (N := Na) (P := flagInv l k)
        (fun _ _ => CoPset.mem_full) $$ HA
      ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
      imod Hacc with ⟨Hinv, Hclose⟩
      iapply lwp_credit_later $$ Hc1
      inext
      unfold flagInv
      icases Hinv with (Hinv | ⟨#Hd, #Av⟩)
      · ihave Hu := untilI_acc (E := ⊤ \ ↑Na) Flag.Np_subseteq $$ Hinv
        ihave Hu := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hu
        imod Hu
        iapply lwp_credit_later $$ Hc2
        inext
        icases Hu with ⟨Hl, Hucl⟩
        icases oblFuels_add 1 3 G $$ HF with ⟨HF1, HF⟩
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
        lwp_step HT HG HF
        rw [show (v0 == hl_val(#1)) = false from rfl]
        lwp_step HT HG HF
        simp only [Bool.not_false]
        lwp_step HT HG HF
        imod IH $$ Hwc with ⟨HF, HP⟩
        iapply HP $$ HT HG HΦ HF
      · -- The set flag is read from its own invariant.
        ihave Hvacc := alwaysI_acc (E := ⊤ \ ↑Na) (N := Nv) (P := iprop(l ↦ some v1))
          (Flag.ndot_subseteq_diff N (by decide)) $$ Av
        ihave Hvacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hvacc
        imod Hvacc with ⟨Hl, Hvclose⟩
        iapply lwp_credit_later $$ Hc2
        inext
        icases oblFuels_add 1 3 G $$ HF with ⟨HF1, HF⟩
        iapply lwp_load (o := 0) (C := _ ++ C) (G := G) (R := ∅) $$ [HT HG HF1 Hl]
        · iframe HT Hl
          iapply stepPre_nil $$ HG HF1
        iintro ⟨HT, ⟨-, HG, -⟩, Hl⟩
        imod Hvclose $$ [Hl]
        · inext
          iexact Hl
        imodintro
        imod Hclose $$ []
        · inext
          iright
          isplitl
          · iexact Hd
          · iexact Av
        imodintro
        ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
        lwp_expr_simp
        lwp_step HT HG HF
        rw [show (v1 == hl_val(#1)) = true from rfl]
        lwp_step HT HG HF
        simp only [Bool.not_true]
        lwp_step HT HG HF with Hlc : lc
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
