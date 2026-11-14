/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LantanaTest.Crash.Worker
public import LantanaTest.Crash.Reviver

/-! # A language whose threads crash: the closed systems and their liveness

The pools `[work N, kill]` and `[work N, kill, revive]`, started alive, in the world `CrashGF`.
The worker's obligations are allocated from the initial pieces of thread `0`: `k` at layer `0`
with the fuel of `N + 1` steps and, below it, a chain of `m` obligations allocated by induction on
`m` (`chain_alloc`; the closed systems take `m = N`), all finallies of `doneOrCrashed` in the
namespaces of their obligations; the finally on `k` is the resource whose guarantee adequacy reads
(`◇ₛ` of the state fact of `doneOrCrashed`), then goes with the rest into the shared invariant.
By `lwp_adequacy_temporal`: on every behavior from the initial configuration on which the active
threads are fairly scheduled, eventually the worker has finished or is crashed. The killer may
give up, so the worker's obligation is needed; with the reviver, a crashed worker may recover and
finish later.
-/

@[expose] public noncomputable section

namespace LantanaTest.Crash

open Iris Iris.BI Iris.ProofMode Iris.Std
open Ordinals Ordinal Lantana
open scoped Lantana.TrSpec Lantana.TrProp
open Iris.ProgramLogic (toVal Language PrimStep EvContext EvContextOps)

theorem insert_empty (k : Oid) : (∅ : Oids).insert k = {k} :=
  Std.ExtTreeSet.ext_mem fun _ => by simp

/-- Eventually the worker (thread `0`) has finished, or it is crashed. -/
def finishedOrCrashed : TrProp (Cfg Exp St) :=
  ◇ₜ TrProp.state fun σ tp => tp[0]? = some .ret ∨ σ = false

/-- What the finally on `k` guarantees: eventually the state fact of `doneOrCrashed`. -/
def gCrash {GF : BundledGFunctors} : TrSpec Exp St GF :=
  ◇ₛ TrSpec.state fun σ tp => σ = false ∨ fin tp = true

theorem gCrash_impl {GF : BundledGFunctors} : (gCrash (GF := GF)).external ⊆ finishedOrCrashed :=
  fun τ h => TrProp.eventually_mono (S := TrProp.state fun σ tp => σ = false ∨ fin tp = true)
    (TrProp.state_mono fun σ tp h => by
      rcases h with h | h
      · exact .inr h
      · refine .inl ?_
        unfold fin at h
        simpa using h) τ h

section Init
variable {GF : BundledGFunctors} [ModelGS GF] [CrashGS GF]

theorem guar_finallyI (k : Oid) :
    ⊢@{IProp GF} finallyI (Nobl.@k) k 1 doneOrCrashed ⊨ₜ gCrash := by
  unfold gCrash finallyI
  exact IntoGuar.into_guar

omit [CrashGS GF] in
/-- An obligation whose children predicate is at hand is not one of a set whose children
predicates are at hand. -/
theorem kids_fresh (k : Oid) (c T : Oids) (kids : Oid → Oids) (Φ : Oid → IProp GF) :
    oblKids k c ∗ ([∗set] j ∈ T, Φ j ∗ oblKids j (kids j)) ⊢
      ⌜k ∉ T⌝ ∗ oblKids k c ∗ [∗set] j ∈ T, Φ j ∗ oblKids j (kids j) := by
  iintro ⟨Hk, HT⟩
  by_cases hk : k ∈ T
  · iexfalso
    icases BigSepS.bigSepS_elem_of_acc hk $$ HT with ⟨⟨-, Hk'⟩, -⟩
    iapply Par.kids_excl (.obl k) c (kids k) $$ Hk Hk'
  · iframe Hk HT
    ipureintro
    exact hk

/-- The finally and the children of a new obligation `k`, with those of `T`, make those of
`{k} ∪ T`. -/
theorem obls_insert {k : Oid} {c T : Oids} {kids : Oid → Oids} (hk : k ∉ T) :
    finallyI (Nobl.@k) k 1 doneOrCrashed ∗ oblKids k c ∗
      ([∗set] j ∈ T, finallyI (Nobl.@j) j 1 doneOrCrashed ∗ oblKids j (kids j)) ⊢@{IProp GF}
      [∗set] j ∈ {k} ∪ T, finallyI (Nobl.@j) j 1 doneOrCrashed ∗
        oblKids j (if j = k then c else kids j) :=
  sep_assoc.2.trans (BigSepS.bigSepS_fn_insert (Ψ := fun j K =>
    iprop(finallyI (Nobl.@j) j 1 doneOrCrashed ∗ oblKids j K)) hk).2

/-- A chain of `m` obligations below the obligation `q`, each a finally of `doneOrCrashed` in the
namespace of its obligation: the new children `c` of `q` (none, or the head of the chain), and the
chain `T` with its children `kids`, hanging below `c`. -/
theorem chain_alloc (m : Nat) (q : Oid) :
    Wit.layer q 0 ⊢@{IProp GF} oblKids q ∅ -∗ |={⊤}=>m ∃ (c T : Oids) (kids : Oid → Oids),
      ⌜HangsBelow c T kids⌝ ∗ oblKids q c ∗
      [∗set] j ∈ T, finallyI (Nobl.@j) j 1 doneOrCrashed ∗ oblKids j (kids j) := by
  induction m generalizing q with
  | zero =>
    iintro - Hq
    imodintro
    iexists ∅, ∅, fun _ => ∅
    iframe Hq
    isplitr
    · ipureintro
      exact ⟨fun _ h => h, fun _ _ _ h => h, fun _ h => .inl h⟩
    iapply BigSepS.bigSepS_empty.2
    iempintro
  | succ m ih =>
    iintro #W Hq
    imod untilI_alloc (E := ⊤) (.obl q) ∅ ∅ 0 1 $$ [] Hq [] with
      ⟨%k, -, Hq, -, Hkk, -, #Wk, Ak⟩
    · iapply parLe_obl q (Std.IsPreorder.le_refl _) $$ W
    · iempintro
    imod Ak $$ %⊤ %(Nobl.@k) %iprop(True) %doneOrCrashed [] with Uk
    · inext
      ipureintro
      trivial
    imod ih k $$ Wk Hkk with ⟨%c, %T, %kids, %hT, Hkk, HT⟩
    icases kids_fresh k c T kids (fun j => finallyI (Nobl.@j) j 1 doneOrCrashed)
      $$ [$Hkk $HT] with ⟨%hk, Hkk, HT⟩
    imodintro
    iexists {k}, {k} ∪ T, fun j => if j = k then c else kids j
    rw [insert_empty]
    iframe Hq
    isplitr
    · ipureintro
      exact hT.insert hk
    iapply obls_insert hk
    iframe HT Hkk
    unfold finallyI
    iexact Uk

/-- The worker's obligations, from its initial pieces: `k` under thread `0` with the fuel of
`N + 1` steps, and a chain of `m` obligations below it, all finallies of `doneOrCrashed`. -/
theorem worker_obls_alloc (N m : Nat) :
    thKids 0 ∅ ⊢@{IProp GF} thCarriers 0 ∅ -∗
      |={⊤}=>m ∃ (k : Oid) (c T : Oids) (kids : Oid → Oids), ⌜k ∉ T ∧ HangsBelow c T kids⌝ ∗
        thKids 0 {k} ∗ thCarriers 0 {k} ∗ oblFuels {k} ((N + 1 : Nat) : Measure) ∗
        finallyI (Nobl.@k) k 1 doneOrCrashed ∗ oblKids k c ∗
        [∗set] j ∈ T, finallyI (Nobl.@j) j 1 doneOrCrashed ∗ oblKids j (kids j) := by
  iintro Hk0 HB0
  imod untilI_alloc (E := ⊤) (.thread 0) ∅ ∅ 0 ((N + 1 : Nat) : Measure) $$ [] Hk0 HB0 with
    ⟨%k, -, Hk0, HB0, Hkk, Fk, #Wk, Ak⟩
  · iapply parLe_thread
  imod Ak $$ %⊤ %(Nobl.@k) %iprop(True) %doneOrCrashed [] with Uk
  · inext
    ipureintro
    trivial
  imod chain_alloc m k $$ Wk Hkk with ⟨%c, %T, %kids, %hT, Hkk, HT⟩
  icases kids_fresh k c T kids (fun j => finallyI (Nobl.@j) j 1 doneOrCrashed)
    $$ [$Hkk $HT] with ⟨%hk, Hkk, HT⟩
  imodintro
  iexists k, c, T, kids
  rw [insert_empty]
  isplitr
  · ipureintro
    exact ⟨hk, hT⟩
  iframe Hk0 HB0 Hkk HT
  unfold finallyI
  iframe Uk
  iapply oblFuels_init {k} _ 0
  iapply BigSepS.bigSepS_singleton.mpr
  iexact Fk

omit [ModelGS GF] in
/-- The ghost variable of the state splits in two halves. -/
theorem stVar_halves (b f : Bool) :
    stVar (GF := GF) 1 b f ⊢ stVar (Qp.half 1) b f ∗ stVar (Qp.half 1) b f := by
  have h := ghost_var_split (GF := GF) (CrashGS.varName GF) (b, f) (Qp.half 1) (Qp.half 1)
  rw [Qp.half_add_half] at h
  exact wand_entails h

omit [CrashGS GF] in
/-- A terminated thread with the postcondition `True`. -/
theorem liftTerm_of_done (j : ThreadId) (v : Unit) :
    Th.done j ⊢@{IProp GF} liftTerm j (fun _ _ => iprop(True)) v := by
  iintro Hd
  unfold liftTerm
  iframe Hd

/-- The pool without the reviver: the worker and the killer. -/
abbrev tpKill (N : Nat) : ThreadPool Exp := [.work N, .kill]

omit [ModelGS GF] in
/-- The state interpretation of an initial configuration: the worker, then threads that are not
workers. -/
theorem crashInterp_init (N : Nat) (rest : List Exp)
    (hrest : ∀ (j n : Nat), rest[j]? ≠ some (Exp.work n)) :
    stVar (GF := GF) (Qp.half 1) true false ⊢ crashInterp true (.work N :: rest) := by
  have hf : fin (.work N :: rest) = false := by simp [fin]
  iintro Hs
  iunfold crashInterp
  rw [hf]
  iframe Hs
  ipureintro
  refine ⟨fun j n hj => ?_, .inl ⟨N, rfl⟩⟩
  rcases j with _ | j
  · rfl
  · rw [List.getElem?_cons_succ] at hj
    exact (hrest j n hj).elim

/-- The worker's side of the initial resources: from half of the ghost variable of the state, a
later credit and thread `0`'s pieces, the worker's obligations (`k` and a chain of `m` below it)
and the finally on `k` for adequacy, then the shared invariant and the worker's `lWP`. -/
theorem worker_init (N m : Nat) :
    stVar (GF := GF) (Qp.half 1) true false ⊢ £ₙ 1 -∗ thActive 0 -∗ thKids 0 ∅ -∗
      thCarriers 0 ∅ -∗ |={⊤}=>m ∃ P : IProp GF, (P ⊨ₜ gCrash) ∗ P ∗
        (P -∗ |={⊤}=>m ∃ (k : Oid) (S : Oids) (kids : Oid → Oids), ⌜HangsBelow {k} S kids⌝ ∗
          inv Ninv (crashInv k S kids) ∗
          lWP (Exp.work N) @ 0; ⊤ {{ liftTerm 0 (fun _ _ => iprop(True)) }}) := by
  iintro Hv Hc0 Ha0 Hk0 HB0
  imod worker_obls_alloc N m $$ Hk0 HB0 with
    ⟨%k, %c, %T, %kids, %⟨hk, hT⟩, Hk0, HB0, HF, Uk, Hkk, HT⟩
  imodintro
  iexists finallyI (Nobl.@k) k 1 doneOrCrashed
  isplitr
  · iapply guar_finallyI
  iframe Uk
  iintro Uk
  imod inv_alloc Ninv ⊤ (crashInv k ({k} ∪ T) fun j => if j = k then c else kids j)
    $$ [Hv Ha0 Hk0 Uk Hkk HT] with #HI
  · inext
    iunfold crashInv
    iexists true, false
    iframe Hv
    simp only [crashProto]
    ileft
    iunfold workerObls
    iframe Ha0 Hk0
    iapply obls_insert hk
    iframe Uk Hkk HT
  imodintro
  iexists k, {k} ∪ T, fun j => if j = k then c else kids j
  iframe HI
  isplitr
  · ipureintro
    exact hT.insert hk
  iapply lwp_mono (liftTerm_of_done 0)
  iapply worker_spec k _ _ (hT.insert hk) $$ HI %N %{k} Hc0 HB0 %(.inr rfl) HF

/-- The initial resources of `[work N, kill]`, the worker owing `m + 1` obligations: the worker's,
then the killer's `lWP`. -/
theorem crash_init (N m : Nat) :
    stVar (GF := GF) (Qp.half 1) true false ⊢ £ₙ 1 -∗ £ₙ 1 -∗
      ([∗list] j ∈ List.range (tpKill N).length, thActive j ∗ thKids j ∅ ∗ thCarriers j ∅) -∗
      |={⊤}=>m ∃ P : IProp GF, (P ⊨ₜ gCrash) ∗ P ∗
        (P -∗ |={⊤}=>m [∗list] j ↦ e ∈ tpKill N,
          lWP e @ j; ⊤ {{ liftTerm j (fun _ _ => iprop(True)) }}) := by
  have hr : List.range (tpKill N).length = [0, 1] := rfl
  rw [hr]
  iintro Hv Hc0 Hc1 HT
  icases BigSepL.bigSepL_cons.mp $$ HT with ⟨⟨Ha0, Hk0, HB0⟩, HT⟩
  icases BigSepL.bigSepL_singleton.mp $$ HT with ⟨Ha1, Hk1, HB1⟩
  imod worker_init N m $$ Hv Hc0 Ha0 Hk0 HB0 with ⟨%P, #HG, HP, Hwp⟩
  imodintro
  iexists P
  iframe HG HP
  iintro HP
  imod Hwp $$ HP with ⟨%k, %S, %kids, %hF, #HI, Hw⟩
  imodintro
  iapply BigSepL.bigSepL_cons.mpr
  iframe Hw
  iapply BigSepL.bigSepL_singleton.mpr
  iapply lwp_mono (liftTerm_of_done 1)
  iapply killer_spec k S kids hF $$ HI Hc1 Ha1 Hk1 HB1

/-- The pool with the reviver: the worker, the killer and the reviver. -/
abbrev tpRevive (N : Nat) : ThreadPool Exp := [.work N, .kill, .revive]

/-- The initial resources of `[work N, kill, revive]`, the worker owing `m + 1` obligations: the
worker's, then the killer's and the reviver's `lWP`s. -/
theorem crash_init_revive (N m : Nat) :
    stVar (GF := GF) (Qp.half 1) true false ⊢ £ₙ 1 -∗ £ₙ 1 -∗ £ₙ 1 -∗
      ([∗list] j ∈ List.range (tpRevive N).length, thActive j ∗ thKids j ∅ ∗ thCarriers j ∅) -∗
      |={⊤}=>m ∃ P : IProp GF, (P ⊨ₜ gCrash) ∗ P ∗
        (P -∗ |={⊤}=>m [∗list] j ↦ e ∈ tpRevive N,
          lWP e @ j; ⊤ {{ liftTerm j (fun _ _ => iprop(True)) }}) := by
  have hr : List.range (tpRevive N).length = [0, 1, 2] := rfl
  rw [hr]
  iintro Hv Hc0 Hc1 Hc2 HT
  icases BigSepL.bigSepL_cons.mp $$ HT with ⟨⟨Ha0, Hk0, HB0⟩, HT⟩
  icases BigSepL.bigSepL_cons.mp $$ HT with ⟨⟨Ha1, Hk1, HB1⟩, HT⟩
  icases BigSepL.bigSepL_singleton.mp $$ HT with ⟨Ha2, Hk2, HB2⟩
  imod worker_init N m $$ Hv Hc0 Ha0 Hk0 HB0 with ⟨%P, #HG, HP, Hwp⟩
  imodintro
  iexists P
  iframe HG HP
  iintro HP
  imod Hwp $$ HP with ⟨%k, %S, %kids, %hF, #HI, Hw⟩
  imodintro
  iapply BigSepL.bigSepL_cons.mpr
  iframe Hw
  iapply BigSepL.bigSepL_cons.mpr
  isplitl [Hc1 Ha1 Hk1 HB1]
  · iapply lwp_mono (liftTerm_of_done 1)
    iapply killer_spec k S kids hF $$ HI Hc1 Ha1 Hk1 HB1
  · iapply BigSepL.bigSepL_singleton.mpr
    iapply lwp_mono (liftTerm_of_done 2)
    iapply reviver_spec k S kids $$ HI Hc2 Ha2 Hk2 HB2

end Init

/-- **Liveness of `[work N, kill]`.** On every behavior from the initial configuration, started
alive, on which the active threads are fairly scheduled, eventually the worker has finished or is
crashed. -/
theorem crash_adequacy (N : Nat) (τ : Trace (Cfg Exp St)) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = (tpKill N, true)) :
    finishedOrCrashed τ := by
  refine lwp_adequacy_temporal (GF := CrashGF) true (tpKill N) gCrash finishedOrCrashed
    gCrash_impl τ hbeh hfair hpos hinit ?_
  intro _ _
  refine ⟨Ordinal.ofNat (1 + 1), ?_⟩
  imod ghost_var_alloc (GF := CrashGF) (true, false) with ⟨%γ, Hγ⟩
  letI : CrashGS CrashGF := { toTemporalGS := ‹_›, varName := γ }
  imodintro
  iexists instStateInterp, (fun _ _ => iprop(True)), (fun _ _ => iprop(True))
  icases stVar_halves true false $$ Hγ with ⟨Hs, Hv⟩
  isplitl [Hs]
  · iapply crashInterp_init N [.kill] (fun j n h => by rcases j with _ | j <;> simp at h) $$ Hs
  iintro Hc HT
  icases (tlc_split_nat 1 1).mp $$ Hc with ⟨Hc0, Hc1⟩
  ihave HT := initThreads_of_not_crashed (fun j => not_crashed_true _ j) $$ HT
  iapply crash_init N N $$ Hv Hc0 Hc1 HT

/-- **Liveness of `[work N, kill, revive]`.** On every behavior from the initial configuration,
started alive, on which the active threads are fairly scheduled, eventually the worker has
finished or is crashed. -/
theorem crash_revive_adequacy (N : Nat) (τ : Trace (Cfg Exp St)) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = (tpRevive N, true)) :
    finishedOrCrashed τ := by
  refine lwp_adequacy_temporal (GF := CrashGF) true (tpRevive N) gCrash finishedOrCrashed
    gCrash_impl τ hbeh hfair hpos hinit ?_
  intro _ _
  refine ⟨Ordinal.ofNat (1 + 1 + 1), ?_⟩
  imod ghost_var_alloc (GF := CrashGF) (true, false) with ⟨%γ, Hγ⟩
  letI : CrashGS CrashGF := { toTemporalGS := ‹_›, varName := γ }
  imodintro
  iexists instStateInterp, (fun _ _ => iprop(True)), (fun _ _ => iprop(True))
  icases stVar_halves true false $$ Hγ with ⟨Hs, Hv⟩
  isplitl [Hs]
  · iapply crashInterp_init N [.kill, .revive]
      (fun j n h => by rcases j with _ | _ | j <;> simp at h) $$ Hs
  iintro Hc HT
  icases (tlc_split_nat (1 + 1) 1).mp $$ Hc with ⟨Hc, Hc2⟩
  icases (tlc_split_nat 1 1).mp $$ Hc with ⟨Hc0, Hc1⟩
  ihave HT := initThreads_of_not_crashed (fun j => not_crashed_true _ j) $$ HT
  iapply crash_init_revive N N $$ Hv Hc0 Hc1 Hc2 HT

/-! The theorems depend only on the standard axioms. -/

/--
info: 'LantanaTest.Crash.crash_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms crash_adequacy

/--
info: 'LantanaTest.Crash.crash_revive_adequacy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms crash_revive_adequacy

end LantanaTest.Crash
