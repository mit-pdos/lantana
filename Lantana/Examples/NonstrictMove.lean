/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Examples.World

/-! # A move below an obligation of the same layer is unsound

Rocq `examples/nonstrict_move.v`. The interface's `Obl.move` needs the new parent's witness
layer strictly below the layer of the moved obligation's fuel (`parBelow`). With a non-strict
move (`OblMoveNonstrict`: the layers may be equal), each iteration of the loop
`rec loop _ := loop ()` creates a fresh obligation `r'` at layer `0` below the thread, moves the
thread's old obligation `r` below `r'`, paying the last unit of `r`'s fuel at layer `0`, and pays
the step with one of the two units of `r'`, keeping the other for the next iteration
(`loop_spec`, by Löb induction). The main thread can then commit to `True U False` on an
obligation it never discharges, and adequacy gives "eventually `False`"
(`nonstrictMove_unsound`). The run of the loop, thread `0` stepping from `loop ()` to
`loop ()` forever, is a fair behavior, so the assumed rule is absurd (`nonstrictMove_absurd`).

The assumed rule is a hypothesis of the theorems (the class `OblMoveNonstrict`, assumed for
every instance of the ghost state of the closed world `ExGF`), never an axiom. Statement
adaptations: thread ids are list positions, so the looping thread is `0`; the hypothesis is
over `ExGF` only (Rocq: over every `Σ` with `heapGS Σ`), which makes the theorems stronger.
-/

@[expose] public noncomputable section

namespace Lantana.Examples.NonstrictMove

open Iris Iris.BI Lantana Lantana.HeapLang
open Iris.ProgramLogic (EctxLanguage)
open Iris.ProgramLogic.PrimStep (primStep)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The assumed rule -/

/-- The non-strict move (Rocq `obl_move_nonstrict`): `k` may move below `q` when a witness
layer `ℓq` of `q` is at most (not strictly below) the layer `ℓ` of the unit of fuel paid. -/
@[lantana_alias obl_move_nonstrict]
class OblMoveNonstrict (GF : BundledGFunctors) [ModelGS GF] [HeapGS GF] : Prop where
  move_le (E : CoPset) (p₁ : Parent) (q : Oid) (K₁ K₂ : Oids) (k : Oid) (ℓ ℓq : Layer) :
    k ∈ K₁ → ℓq ≤ ℓ →
    Wit.layer (GF := GF) q ℓq ⊢ Par.kids p₁ K₁ -∗ oblKids q K₂ -∗ Obl.fuel k ℓ 1 -∗
      |={E}=>m ⌜k ∉ K₂⌝ ∗ Par.kids p₁ (K₁.erase k) ∗ oblKids q (K₂.insert k)

attribute [lantana_alias obl_move_le] OblMoveNonstrict.move_le

/-! ## The program -/

/-- `rec loop _ := loop ()`. -/
@[lantana_alias nonstrict_move.loop]
def loop : Val := hl_val(rec loop _ := loop #())

/-! ## The loop runs forever on one unit of fuel -/

section Spec
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [OblMoveNonstrict GF]

/-- Each iteration moves the thread's obligation below a fresh one of the same layer, paying
its last unit of fuel, and pays the step with the fresh one (the bill of the thread follows its
children). -/
@[lantana_alias nonstrict_move.loop_spec]
theorem loop_spec (i : ThreadId) (r : Oid) (C : List ECtxItem) (Φ : Val → IProp GF) :
    threadExpr i C hl(v(&loop) #()) ⊢ thKids i {r} -∗ thCarriers i {r} -∗ Obl.fuel r 0 1 -∗
      lWP hl(v(&loop) #()) @ i {{ Φ }} := by
  iintro HT HK HG Hr
  iloeb as IH generalizing %r
  imod Obl.new ⊤ (.thread i) {r} {r} 0 (1 + 1) $$ [] HK HG with
    ⟨%r', %hr', HK, HG, Kr', -, Fr', #Wr'⟩
  · iapply parLe_thread
  imod OblMoveNonstrict.move_le ⊤ (.thread i) r' (({r} : Oids).insert r') ∅ r 0 0
    (by simp) (Ordinals.Ordinal.le_refl _) $$ Wr' HK Kr' Hr with ⟨-, HK, -⟩
  imod Th.carriers_resync ⊤ i _ _ $$ HG HK with ⟨HG, HK⟩
  have hr : ∀ z, z ∈ (({r} : Oids).insert r').erase r ↔ z ∈ ({r'} : Oids) := by
    intro z
    simp at hr' ⊢
    grind
  ihave HG := Th.carriers_congr hr $$ HG
  ihave HK := Par.kids_congr hr $$ HK
  icases (Obl.fuel_add r' 0 1 1).mp $$ Fr' with ⟨HF, Fr'⟩
  ihave HF := oblFuels_init {r'} 1 0 $$ [HF]
  · iapply BigSepS.bigSepS_singleton.mpr
    iexact HF
  unfold loop
  lwp_step HT HG HF with Hc : 1
  lwp_expr_simp
  iapply lwp_credit_later $$ Hc
  inext
  iapply IH $$ HT HK HG Fr'

end Spec

/-! ## Adequacy: "eventually `False`" -/

section Adequacy

/-- The initial pool: the loop, thread `0`. -/
abbrev tp0 : ThreadPool Exp := [hl(v(&loop) #())]

/-- The initial state: the empty heap. -/
abbrev σ0 : State := ⟨∅⟩

/-- The namespace of the commitment. -/
def N : Namespace := nroot.@"nonstrict"

/-- The commitment of thread `0` to `True U False`, and its obligation with one unit of fuel
(Rocq `Φ_P`). -/
def mainRes {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] : IProp GF :=
  iprop(∃ x : Oid, untilI N x 1 iprop(True) iprop(False) ∗
    (thKids 0 {x} ∗ thCarriers 0 {x} ∗ Obl.fuel x 0 1))

/-- What it guarantees (Rocq `G_main`, inferred): `True U False`. -/
def gMain {GF : BundledGFunctors} : TrSpec Exp State GF := (⌜True⌝ₛ Uₛ ⌜False⌝ₛ) ∧ₛ TrSpec.true

/-- `True U False` is false on every trace. -/
@[lantana_alias nonstrict_move.G_main_false]
theorem gMain_false {GF : BundledGFunctors} : (gMain (GF := GF)).external ⊆ ⌜False⌝ₜ :=
  fun _ ⟨⟨_, _, h, _⟩, _⟩ => h

@[lantana_alias nonstrict_move.guar_Φ_P]
theorem guar_mainRes {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] :
    ⊢@{IProp GF} mainRes ⊨ₜ gMain := by
  unfold mainRes gMain
  exact IntoGuar.into_guar

/-- With the non-strict move, the loop is verified with a commitment that is never kept: in
every fair behavior from the initial configuration, eventually `False`. -/
@[lantana_alias nonstrict_move_unsound]
theorem nonstrictMove_unsound (hns : ∀ [ModelGS ExGF] [HeapGS ExGF], OblMoveNonstrict ExGF)
    (τ : Trace (Cfg Exp State)) (hbeh : IsBehavior τ) (hfair : fairScheduling τ) (hpos : τ.pos = 0)
    (hinit : τ.seq 0 = (tp0, σ0)) : False := by
  refine lwp_adequacy_temporal (GF := ExGF) σ0 tp0 gMain ⌜False⌝ₜ gMain_false τ hbeh hfair
    hpos hinit ?_
  intro _ _
  refine ⟨2, ?_⟩
  imod heapState_init σ0 tp0 with ⟨%hs, Hσ, -, HT⟩
  letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
  haveI : OblMoveNonstrict ExGF := hns
  imodintro
  iexists instStateInterp, (fun _ _ => iprop(True)), (fun _ _ => iprop(True))
  isplitl [Hσ]
  · iexact Hσ
  iintro Hc HG
  ihave HG := initThreads σ0 tp0 $$ HG
  rw [show List.range (List.length tp0) = [0] from rfl]
  icases BigSepL.bigSepL_singleton.mp $$ HG with ⟨-, HG, HB⟩
  ihave HT := BigSepL.bigSepL_singleton.mp $$ HT
  imod untilI_alloc (E := ⊤) (.thread 0) ∅ ∅ 0 1 $$ [] HG HB with
    ⟨%x, -, HG, HB, -, Fx, -, Ax⟩
  · iapply parLe_thread
  imod Ax $$ %⊤ %N %iprop(True) %iprop(False) [] with Ux
  · inext
    ipureintro
    trivial
  imodintro
  iexists mainRes
  isplitr
  · iapply guar_mainRes
  have hx : ∀ z, z ∈ (∅ : Oids).insert x ↔ z ∈ ({x} : Oids) := by
    intro z
    simp
  isplitl [Ux HG HB Fx]
  · unfold mainRes
    iexists x
    iframe Ux Fx
    isplitl [HG]
    · iapply Par.kids_congr hx $$ HG
    · iapply Th.carriers_congr hx $$ HB
  iintro HP
  unfold mainRes
  icases HP with ⟨%x, -, HG, HB, Fx⟩
  imodintro
  iapply BigSepL.bigSepL_singleton.mpr
  iapply loop_spec 0 x [] $$ HT HG HB Fx

/-! ## The run of the loop -/

/-- `loop ()` steps to itself. -/
@[lantana_alias nonstrict_move.loop_prim_step]
theorem loop_primStep (σ : State) :
    primStep ((hl(v(&loop) #()) : Exp), σ) [] (hl(v(&loop) #()), σ, []) :=
  EctxLanguage.primStep_of_baseStep (.betaS _ _ _ _ _ σ rfl)

/-- The run of the loop: thread `0` steps from `loop ()` to `loop ()` forever. -/
@[lantana_alias nonstrict_move.loop_run]
def loopRun : Trace (Cfg Exp State) := ⟨0, fun _ => (tp0, σ0)⟩

/-- Thread `0` takes a trace step at every position: `loop ()` steps to itself. -/
theorem loopRun_traceStep (m : Nat) : TraceStep 0 (loopRun.seq m) (loopRun.seq (m + 1)) := by
  left
  have h := ThreadStep.step (i := 0) (tp := tp0) (σ := σ0) rfl (loop_primStep σ0)
  simp only [List.set_cons_zero, List.append_nil] at h
  exact h

@[lantana_alias nonstrict_move.loop_run_behavior]
theorem loopRun_behavior : IsBehavior loopRun :=
  isBehavior_iff.mpr fun m _ => ⟨0, loopRun_traceStep m⟩

/-- Thread `0` is active and steps at every position; no other thread is ever active. -/
@[lantana_alias nonstrict_move.loop_run_fair]
theorem loopRun_fair : fairScheduling loopRun := by
  intro i hinf
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact TrProp.always_eventually_iff.mpr fun n _ =>
      ⟨n, Nat.le_refl n, active_iff.mpr ⟨_, rfl, rfl, not_crashed _ _⟩,
        stepOf_iff.mpr (loopRun_traceStep n)⟩
  · obtain ⟨m, -, hm⟩ := TrProp.always_eventually_iff.mp hinf 0 (Nat.le_refl _)
    obtain ⟨e, he, -⟩ := active_iff.mp hm
    simp only [loopRun] at he
    rw [List.getElem?_eq_none (by simp [Trace.now]; omega)] at he
    cases he

/-- **The non-strict move is unsound**: assuming it, the fair run of the loop satisfies
"eventually `False`". -/
@[lantana_alias nonstrict_move_absurd]
theorem nonstrictMove_absurd (hns : ∀ [ModelGS ExGF] [HeapGS ExGF], OblMoveNonstrict ExGF) :
    False :=
  nonstrictMove_unsound hns loopRun loopRun_behavior loopRun_fair rfl rfl

end Adequacy

end Lantana.Examples.NonstrictMove
