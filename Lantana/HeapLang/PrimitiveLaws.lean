/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.BI.Lib.GenHeap
public import Iris.Instances.Lib.GhostMap
public import Lantana.HeapLang.Instances
public import Lantana.ProgramLogic.EctxLifting

/-! # The program logic of HeapLang: ghost state, assertions, primitive laws

Rocq `lantana_heap_lang/primitive_laws.v`. The ghost state `HeapGS` is the temporal layer plus
the heap (Iris-Lean's `genHeap`, locations to `Option Val`) and the *thread-expression map*
(a ghost map from thread ids to their expressions, D17): `threadExpr i C e` is exact
ownership of thread `i`'s whole expression `fill C e`, split into the caller context `C` and
the current subexpression `e`. Every step law takes and returns the token, the children
`thKids i G` of the thread with one unit of fuel each, and a witness set `R`; it returns `£ₒ o`
later credits and the witnesses' credits (the paper's STEP rules).

Points-to is Iris-Lean's `l ↦{dq} v` at value type `Option Val`: `l ↦ v` with `v : Val` means
`l ↦ some v` by coercion, and a freed location is `l ↦{q} none` (Rocq `freed l q`).

**Contexts.** As in Rocq, the contexts of HeapLang are lists of items (D31): `lWP` quantifies
over the contexts `K` that put the thread's expression into the pool, `fill K e`. The token knows
`fill C e`; as `e` can step, `K = C` (`threadExpr_ctx`, by `fill_ctx_step_inj`), so the pool
after the step is `tp.set i (fill C e')`.
-/

@[expose] public noncomputable section

namespace Lantana.HeapLang

open Iris Iris.BI Iris.ProofMode Lantana Lantana.Language
open Iris.ProgramLogic (toVal)

/-! ## Ghost state -/

/-- Finite maps from thread ids. -/
abbrev ThreadMapF := fun V => Std.ExtTreeMap ThreadId V compare

/-- The heap-specific ghost state: the heap and the thread-expression map. -/
@[lantana_alias heap_stateGS]
class HeapStateGS (GF : BundledGFunctors) where
  [genHeap : genHeapGS Loc (Option Val) GF HeapF]
  [threadMap : GhostMapG GF ThreadId Exp ThreadMapF]
  /-- The ghost name of the thread-expression map. -/
  threadMapName : GName

attribute [reducible, instance] HeapStateGS.genHeap HeapStateGS.threadMap

/-- The ghost state of HeapLang: the temporal layer and the heap state. -/
@[lantana_alias heapGS]
class HeapGS (GF : BundledGFunctors) extends TemporalGS Exp State GF, HeapStateGS GF

/-- The thread pool as a finite map from thread ids: thread `j` is the `j`-th expression. -/
def ThreadPool.toMap (tp : ThreadPool Exp) : ThreadMapF Exp :=
  Iris.Std.FiniteMap.map_seq 0 tp

namespace ThreadPool

theorem get?_toMap (tp : ThreadPool Exp) (j : ThreadId) :
    Iris.Std.get? (toMap tp) j = tp[j]? := by
  rw [toMap, Iris.Std.LawfulFiniteMap.get?_map_seq]
  simp

theorem toMap_ext {m : ThreadMapF Exp} {tp : ThreadPool Exp}
    (h : ∀ j, Iris.Std.get? m j = tp[j]?) : m = toMap tp :=
  Iris.Std.LawfulPartialMap.equiv_iff_eq.mp fun j => by rw [h, get?_toMap]

theorem toMap_set {tp : ThreadPool Exp} {j : ThreadId} (hj : j < tp.length) (e : Exp) :
    toMap (tp.set j e) = Iris.Std.insert (toMap tp) j e := by
  refine (toMap_ext fun k => ?_).symm
  rw [Iris.Std.LawfulPartialMap.get?_insert, get?_toMap, List.getElem?_set]
  by_cases hk : j = k
  · subst hk; simp [hj]
  · simp [hk]

theorem toMap_append_singleton (tp : ThreadPool Exp) (e : Exp) :
    toMap (tp ++ [e]) = Iris.Std.insert (toMap tp) tp.length e := by
  refine (toMap_ext fun k => ?_).symm
  rw [Iris.Std.LawfulPartialMap.get?_insert, get?_toMap]
  rcases Nat.lt_trichotomy k tp.length with hk | rfl | hk
  · rw [ite_eq_right (show tp.length ≠ k by omega), List.getElem?_append_left hk]
  · simp
  · rw [ite_eq_right (show tp.length ≠ k by omega), List.getElem?_eq_none (by omega),
      List.getElem?_eq_none (by simp; omega)]

theorem get?_toMap_length (tp : ThreadPool Exp) :
    Iris.Std.get? (toMap tp) tp.length = none := by
  simp [get?_toMap]

end ThreadPool

section
variable {GF : BundledGFunctors} [HeapStateGS GF]

/-- Exact ownership of thread `i`'s expression: `e` in the context `C`. -/
@[lantana_alias thread_expr]
def threadExpr (i : ThreadId) (C : List ECtxItem) (e : Exp) : IProp GF :=
  HeapStateGS.threadMapName (GF := GF) ↪◯MAP[i]{DFrac.own 1} fill C e

/-- Thread `i` has exited with the value `v`. -/
scoped notation:20 "exits " v:max " @ " i:max => threadExpr i [] (Exp.val v)

/-- The authoritative thread-expression map of the pool `tp`. -/
abbrev threadMapAuth (tp : ThreadPool Exp) : IProp GF :=
  HeapStateGS.threadMapName (GF := GF) ↪●MAP{DFrac.own 1} ThreadPool.toMap tp

/-- The state interpretation: the heap and the thread-expression map hold the state and the
pool. -/
@[lantana_alias state_interp]
def stateInterp (σ : State) (tp : ThreadPool Exp) : IProp GF :=
  iprop(genHeapInterp σ.heap ∗ threadMapAuth tp)

instance threadExpr_timeless (i : ThreadId) (C : List ECtxItem) (e : Exp) :
    Timeless (threadExpr (GF := GF) i C e) := by
  unfold threadExpr; infer_instance

@[lantana_alias thread_expr_fill]
theorem threadExpr_fill (i : ThreadId) (C D : List ECtxItem) (e : Exp) :
    threadExpr (GF := GF) i C (fill D e) ⊣⊢ threadExpr i (D ++ C) e := by
  unfold threadExpr
  rw [EctxItemLanguage.fill_append]
  exact .rfl

/-- The token agrees with the pool. -/
theorem threadMapAuth_lookup (tp : ThreadPool Exp) (i : ThreadId) (C : List ECtxItem)
    (e : Exp) :
    threadMapAuth (GF := GF) tp ∗ threadExpr i C e ⊢ ⌜tp[i]? = some (fill C e)⌝ := by
  unfold threadExpr
  iintro ⟨Ha, Hf⟩
  ihave %h := ghost_map_lookup $$ Ha Hf
  ipureintro
  rwa [ThreadPool.get?_toMap] at h

/-- The context of a thread is determined by its expression when that expression can step: the
context `K` of the pool is the context `C` of the token (`fill_ctx_step_inj`). -/
theorem ctx_eq_of_primStep {tp : ThreadPool Exp} {i : ThreadId} {C K : List ECtxItem} {e : Exp}
    {σ : State} {e' : Exp} {σ' : State} {efs : List Exp} (hs : primStep e σ e' σ' efs)
    (hC : tp[i]? = some (fill C e)) (hK : tp[i]? = some (fill K e)) : C = K :=
  EctxItemLanguage.fill_ctx_step_inj hs (Option.some.inj (hC.symm.trans hK))

/-- The token determines the context of a thread that can step. -/
@[lantana_alias thread_expr_ctx]
theorem threadExpr_ctx (tp : ThreadPool Exp) (i : ThreadId) (C K : List ECtxItem) (e : Exp)
    {σ : State} {e' : Exp} {σ' : State} {efs : List Exp} (hK : tp[i]? = some (fill K e))
    (hs : primStep e σ e' σ' efs) :
    threadMapAuth (GF := GF) tp ∗ threadExpr i C e ⊢ ⌜C = K⌝ := by
  iintro H
  ihave %hC := threadMapAuth_lookup tp i C e $$ H
  ipureintro
  exact ctx_eq_of_primStep hs hC hK

/-- The token and the pool change together. -/
theorem threadMapAuth_update (tp : ThreadPool Exp) (i : ThreadId) (C : List ECtxItem)
    (e e' : Exp) :
    threadMapAuth (GF := GF) tp ∗ threadExpr i C e ⊢
      |==> (threadMapAuth (tp.set i (fill C e')) ∗ threadExpr i C e') := by
  iintro ⟨Ha, Hf⟩
  ihave %h : ⌜tp[i]? = some (fill C e)⌝ $$ [Ha Hf]
  · iapply threadMapAuth_lookup
    iframe
  unfold threadExpr
  imod ghost_map_update (fill C e') $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe Hf
  simp only [threadMapAuth, ThreadPool.toMap_set (List.getElem?_eq_some_iff.mp h).1]
  iexact Ha

/-- A forked thread gets a token for its expression. -/
theorem threadMapAuth_fork (tp : ThreadPool Exp) (e : Exp) :
    threadMapAuth (GF := GF) tp ⊢ |==> (threadMapAuth (tp ++ [e]) ∗ threadExpr tp.length [] e) := by
  iintro Ha
  unfold threadExpr
  imod ghost_map_insert tp.length e (ThreadPool.get?_toMap_length tp) $$ Ha with ⟨Ha, Hf⟩
  imodintro
  simp only [threadMapAuth, ThreadPool.toMap_append_singleton, EctxItemLanguage.fill_nil]
  iframe

@[lantana_alias thread_expr_read]
theorem threadExpr_read (σ : State) (tp : ThreadPool Exp) (i : ThreadId) (C : List ECtxItem)
    (e : Exp) :
    stateInterp (GF := GF) σ tp ⊢ threadExpr i C e -∗ ⌜tp[i]? = some (fill C e)⌝ := by
  unfold stateInterp
  iintro ⟨-, Ha⟩ Hf
  iapply threadMapAuth_lookup
  iframe

@[lantana_alias pointsto_state_interp]
theorem pointsTo_stateInterp (σ : State) (tp : ThreadPool Exp) (l : Loc) (dq : DFrac) (v : Val) :
    stateInterp (GF := GF) σ tp ∗ l ↦{dq} some v ⊢ ⌜pointstoSat l dq v σ tp⌝ := by
  unfold stateInterp genHeapInterp pointsTo
  iintro ⟨⟨⟨%m, -, Hh, -⟩, -⟩, Hl⟩
  ihave %h := ghost_map_lookup $$ Hh Hl
  ipureintro
  exact h

@[lantana_alias thread_expr_state_interp]
theorem threadExpr_stateInterp (σ : State) (tp : ThreadPool Exp) (i : ThreadId)
    (C : List ECtxItem) (e : Exp) :
    stateInterp (GF := GF) σ tp ∗ threadExpr i C e ⊢ ⌜threadExprSat i C e σ tp⌝ := by
  iintro ⟨Hσ, Hf⟩
  ihave %h := threadExpr_read σ tp i C e $$ Hσ Hf
  ipureintro
  exact threadExprSat_iff.mpr h

/-- The heap agrees with a points-to. -/
theorem genHeapInterp_lookup (σ : State) (l : Loc) (dq : DFrac) (v : Option Val) :
    genHeapInterp (GF := GF) σ.heap ∗ l ↦{dq} v ⊢ ⌜σ.get? l = some v⌝ := by
  unfold genHeapInterp pointsTo
  iintro ⟨⟨%m, -, Hh, -⟩, Hl⟩
  iapply ghost_map_lookup $$ Hh Hl

end

/-- The state interpretation class of HeapLang. -/
instance instStateInterp {GF : BundledGFunctors} [HeapStateGS GF] : StateInterp Exp State GF :=
  ⟨stateInterp⟩

/-- HeapLang's instance of the program logic: forked threads have the postcondition `True`. -/
@[lantana_alias heapGS_lantanaGS]
instance instLantanaGS {GF : BundledGFunctors} [HeapGS GF] : LantanaGS Exp State Val GF where
  toTemporalGS := inferInstance
  toStateInterp := instStateInterp
  forkPost _ _ := iprop(True)

section
variable {GF : BundledGFunctors} [HeapStateGS GF]

/-- The state interpretation of the program logic is HeapLang's. -/
theorem stateInterp_unfold (σ : State) (tp : ThreadPool Exp) :
    StateInterp.stateInterp (Expr := Exp) (GF := GF) σ tp ⊣⊢
      genHeapInterp σ.heap ∗ threadMapAuth tp :=
  .rfl

end

/-- A pure step of thread `i` updates its token and the pool together. -/
@[lantana_alias thread_expr_pure_exec_si]
instance threadExpr_pureExecSI {GF : BundledGFunctors} [HeapGS GF] (C : List ECtxItem)
    (i : ThreadId) : PureExecSI (GF := GF) (fun i e => threadExpr i C e) i where
  pureExecSI {K e₁ e₂ σ tp} _ hi hstep := by
    iintro ⟨Hf, Hσ⟩
    icases (stateInterp_unfold σ tp).mp $$ Hσ with ⟨Hh, Ha⟩
    ihave %hC := threadExpr_ctx tp i C K e₁ hi hstep $$ [Ha Hf]
    · iframe
    subst hC
    imod threadMapAuth_update tp i C e₁ e₂ $$ [Ha Hf] with ⟨Ha, Hf⟩
    · iframe
    imodintro
    iframe Hf
    iapply (stateInterp_unfold σ _).mpr
    iframe

/-! ## The primitive laws -/

section Laws

open Ordinals Ordinal

variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF]
  [TemporalInterp Exp State GF]
variable {s : Stuckness} {i : ThreadId} {E : CoPset} {C : List ECtxItem} {G R : Oids} {o : Fuel}

/-- What a step takes: the children of the thread with one unit of fuel each, and witnesses. -/
abbrev stepPre (i : ThreadId) (G R : Oids) : IProp GF :=
  iprop(thKids i G ∗ oblFuels G 1 ∗ witLayers R)

/-- What a step gives back: later credits, the children, the witnesses' credits. -/
abbrev stepPost (i : ThreadId) (G R : Oids) (o : Fuel) : IProp GF :=
  iprop(£ₒ o ∗ thKids i G ∗ witCreds R)

/-- A step of the redex `e₁` that forks no thread and ends in a value: the token, the children
and the witnesses are handled here, the heap by `hstep` (from the heap's interpretation and the
resources `H`). -/
theorem lwp_heap_step {e₁ : Exp} (he : toVal e₁ = none) (H : IProp GF) (Ψ : Val → IProp GF)
    (Φ : Val → IProp GF)
    (hstep : ∀ σ₁ : State, genHeapInterp σ₁.heap ∗ H ⊢ ⌜EctxLanguage.BaseReducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂ efs, ⌜BaseStep e₁ σ₁ e₂ σ₂ efs⌝ ==∗
        ⌜efs = []⌝ ∗ ∃ v : Val, ⌜e₂ = Exp.val v⌝ ∗ genHeapInterp σ₂.heap ∗ Ψ v) :
    threadExpr i C e₁ ∗ stepPre i G R ∗ H ∗
      (∀ v, threadExpr i C (.val v) ∗ stepPost i G R o ∗ Ψ v -∗ Φ v)
      ⊢ lWP e₁ @ s; i; E {{ Φ }} := by
  iintro ⟨HT, ⟨HG, HF, HR⟩, HH, HΦ⟩
  iapply lwp_lift_atomic_base_step_no_fork he
  iintro %K %σ₁ %tp %hi Hσ
  icases (stateInterp_unfold σ₁ tp).mp $$ Hσ with ⟨Hh, Ha⟩
  icases hstep σ₁ $$ [Hh HH] with ⟨%hred, Hstep⟩
  · iframe
  have ⟨_, _, _, hb⟩ := hred
  ihave %hC := threadExpr_ctx tp i C K e₁ hi (EctxLanguage.primStep_of_baseStep hb) $$ [Ha HT]
  · iframe
  subst hC
  imodintro
  isplitr
  · ipureintro
    exact hred
  iexists G
  iframe HG HF
  iexists R
  iframe HR
  iintro %e₂ %σ₂ %efs %hs
  imod Hstep $$ %e₂ %σ₂ %efs %hs with ⟨%hefs, %v, %hv, Hh, HΨ⟩
  imod threadMapAuth_update tp i C e₁ e₂ $$ [Ha HT] with ⟨Ha, HT⟩
  · iframe
  imodintro
  iintro HG HW
  iapply (ALC_credits o).mpr
  iapply ALC_intro
  iintro Ho
  imodintro
  isplitr
  · ipureintro
    exact hefs
  isplitl [Hh Ha]
  · iapply (stateInterp_unfold σ₂ _).mpr
    iframe
  subst hv
  iexists v
  isplitr
  · ipureintro
    rfl
  iapply mupd_intro
  iapply HΦ
  isplitl [HT]
  · iexact HT
  isplitl [Ho HG HW]
  · isplitl [Ho]
    · iexact Ho
    isplitl [HG]
    · iexact HG
    · iexact HW
  · iexact HΨ

omit [HeapGS GF] [TemporalInterp Exp State GF] in
/-- The credits of `m + 1` steps give those of one step. -/
theorem witCreds_of_nat (R : Oids) (m : Nat) :
    ([∗set] r ∈ R, Wit.cred (GF := GF) r ((m + 1 : Nat) : Fuel) ∨ Obl.discharged r) ⊢
      witCreds R := by
  unfold witCreds
  refine BigSepS.bigSepS_mono fun _ => ?_
  iintro (H | #H)
  · ileft
    rw [show ((m + 1 : Nat) : Fuel) = (m : Fuel) +ₕ 1 from (Ordinals.Ordinal.nadd_ofNat m 1).symm]
    icases (Wit.cred_split _ _ _).mp $$ H with ⟨-, H⟩
    iexact H
  · iright
    iexact H

@[lantana_alias heap_lang.lwp_pure_step]
theorem lwp_pure_step (n : Nat) (e₁ e₂ : Exp) (φ : Prop) (Φ : Val → IProp GF)
    [PureExec φ n e₁ e₂] (hφ : φ) (hn : 0 < n) :
    threadExpr i C e₁ ∗ thKids i G ∗ oblFuels G n ∗ witLayers R ∗
      (threadExpr i C e₂ -∗ thKids i G -∗ witCreds R -∗ £ₒ o -∗
        |={E}=>m lWP e₂ @ s; i; E {{ Φ }})
      ⊢ lWP e₁ @ s; i; E {{ Φ }} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  iintro ⟨HT, HG, HF, HR, H⟩
  iapply Lantana.lwp_pure_step_simple (ς := fun i e => threadExpr i C e) (m + 1) hn G R o hφ
  iframe HT HG HF HR
  iintro HT HG HW Ho
  iapply H $$ HT HG [HW] [Ho]
  · iapply witCreds_of_nat
    iexact HW
  · rw [show ((m + 1 : Nat) : Fuel) = Ordinals.Ordinal.succ (m : Fuel) from rfl,
      Ordinals.Ordinal.jmul_succ]
    icases tlc_split.mp $$ Ho with ⟨Ho, -⟩
    iexact Ho

/-! ### Moving children to a forked thread

Rocq `obl_move_thread_set` (`obl_forest_rules.v`), which `lwp_fork` needs: the children `X ⊆ K₁`
of `p` move below the thread `j`, each paying one unit of fuel. Derived here from `Obl.move` by
induction on `X`; a set version in the obligation interface can replace it. -/

omit [HeapGS GF] [TemporalInterp Exp State GF] in
theorem Par.kids_congr {p : Parent} {A B : Oids} (h : ∀ k, k ∈ A ↔ k ∈ B) :
    Par.kids (GF := GF) p A ⊢ Par.kids p B := by
  rw [Std.ExtTreeSet.ext_mem h]

theorem obl_move_thread_set (E : CoPset) (p : Parent) (j : ThreadId) (X : Oids) :
    ∀ K₁ K₂ : Oids, X ⊆ K₁ →
      Par.kids (GF := GF) p K₁ ∗ thKids j K₂ ∗ oblFuels X 1 ⊢
        |={E}=>m (Par.kids p (K₁ \ X) ∗ thKids j (X ∪ K₂)) := by
  induction X using Iris.Std.FiniteSet.set_ind with
  | hemp =>
    intro K₁ K₂ _
    iintro ⟨H1, H2, -⟩
    imodintro
    isplitl [H1]
    · iapply Par.kids_congr _ $$ H1
      intro k
      simp
    · iapply Par.kids_congr _ $$ H2
      intro k
      simp
  | hadd x X hx IH =>
    intro K₁ K₂ hsub
    have hxK₁ : x ∈ K₁ := hsub x (Iris.Std.LawfulSet.mem_insert.mpr (.inl rfl))
    have hXK₁ : X ⊆ K₁.erase x := fun k hk => by
      simp only [Std.ExtTreeSet.mem_erase, ne_eq, Nat.compare_eq_eq]
      exact ⟨by rintro rfl; exact hx hk, hsub k (Iris.Std.LawfulSet.mem_insert.mpr (.inr hk))⟩
    iintro ⟨H1, H2, HF⟩
    unfold oblFuels
    icases (BigSepS.bigSepS_insert hx).mp $$ HF with ⟨⟨%ℓ, Hx⟩, HF⟩
    imod Obl.move E p (.thread j) K₁ K₂ x ℓ hxK₁ $$ [] H1 H2 Hx with ⟨-, H1, H2⟩
    · unfold parBelow
      itrivial
    imod IH (K₁.erase x) (K₂.insert x) hXK₁ $$ [H1 H2 HF] with ⟨H1, H2⟩
    · iframe H1 H2
      unfold oblFuels
      iexact HF
    imodintro
    isplitl [H1]
    · iapply Par.kids_congr _ $$ H1
      intro k
      simp only [Std.ExtTreeSet.mem_diff_iff, Std.ExtTreeSet.mem_erase,
        Iris.Std.LawfulSet.mem_insert]
      grind
    · iapply Par.kids_congr _ $$ H2
      intro k
      simp only [Std.ExtTreeSet.mem_union_iff, Std.ExtTreeSet.mem_insert, Nat.compare_eq_eq,
        Iris.Std.LawfulSet.mem_insert]
      grind

/-- Fork: the children `K ⊆ G` move to the new thread, each paying one unit of fuel. -/
@[lantana_alias heap_lang.lwp_fork]
theorem lwp_fork (K : Oids) (P : IProp GF) (e : Exp) (hK : K ⊆ G) :
    (∀ j : ThreadId, l{{{ threadExpr j [] e ∗ thKids j K ∗ P }}} e @ s; j; ⊤
        l{{{ v, RET v; liftTerm j (fun _ _ => iprop(True)) v }}})
      ⊢@{IProp GF} l{{{ threadExpr i C (.fork e) ∗ stepPre i G R ∗ oblFuels K 1 ∗ P }}}
          (Exp.fork e) @ s; i; E
        l{{{ RET Val.lit .unit; threadExpr i C (.val (.lit .unit)) ∗
          (£ₒ o ∗ thKids i (G \ K) ∗ witCreds R) }}} := by
  iintro #Hfork %Φ !> ⟨HT, ⟨HG, HF, HR⟩, HK, HP⟩ HΦ
  iapply lwp_lift_atomic_base_step rfl
  iintro %K' %σ₁ %tp %hi Hσ
  icases (stateInterp_unfold σ₁ tp).mp $$ Hσ with ⟨Hh, Ha⟩
  ihave %hC := threadExpr_ctx tp i C K' (.fork e) hi
    (EctxLanguage.primStep_of_baseStep (.forkS e σ₁)) $$ [Ha HT]
  · iframe
  subst hC
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, _, _, .forkS e σ₁⟩
  iexists G
  iframe HG HF
  iexists R
  iframe HR
  iintro %e₂ %σ₂ %efs %hs
  cases hs
  imod threadMapAuth_update tp i C (.fork e) (.val (.lit .unit)) $$ [Ha HT] with ⟨Ha, HT⟩
  · iframe
  imod threadMapAuth_fork _ e $$ Ha with ⟨Ha, Hj⟩
  imodintro
  iintro HG HW Hforks
  iapply (ALC_credits o).mpr
  iapply ALC_intro
  iintro Ho
  imodintro
  isplitl [Hh Ha]
  · iapply (stateInterp_unfold σ₁ _).mpr
    iframe
  simp only [List.length_set, List.length_singleton, List.range_one]
  icases BigSepL.bigSepL_singleton.mp $$ Hforks with Hkj
  imod obl_move_thread_set E (.thread i) tp.length K G ∅ hK $$ [HG Hkj HK] with ⟨HG, Hkj⟩
  · iframe
  imodintro
  isplitl [HT Ho HG HW HΦ]
  · iexists .lit .unit
    isplitr
    · ipureintro
      rfl
    iapply HΦ
    iframe
  iapply BigSepL.bigSepL_singleton.mpr
  iapply Hfork $$ %tp.length %_ [Hj Hkj HP]
  · iframe Hj HP
    iapply Par.kids_congr _ $$ Hkj
    intro k
    simp
  · iintro %v Hv
    iexact Hv

@[lantana_alias heap_lang.lwp_choosenat]
theorem lwp_chooseNat :
    ⊢@{IProp GF} l{{{ threadExpr i C .chooseNat ∗ stepPre i G R }}} Exp.chooseNat @ s; i; E
      l{{{ (n : Nat), RET Val.lit (.int n); threadExpr i C (.val (.lit (.int n))) ∗
        stepPost i G R o }}} := by
  iintro %Φ !> ⟨HT, Hpre⟩ HΦ
  iapply lwp_heap_step (o := o) rfl iprop(emp) (fun w => iprop(⌜∃ n : Nat, w = .lit (.int n)⌝))
  · intro σ₁
    iintro ⟨Hh, -⟩
    isplitr
    · ipureintro
      exact ⟨_, _, _, .chooseNatS 0 σ₁⟩
    iintro %e₂ %σ₂ %efs %hs
    cases hs
    next n =>
    imodintro
    isplitr
    · ipureintro; trivial
    iexists .lit (.int n)
    isplitr
    · ipureintro; trivial
    iframe Hh
    ipureintro
    exact ⟨n, rfl⟩
  iframe HT Hpre
  isplitr
  · iempintro
  iintro %w ⟨HT, Hpost, %hw⟩
  obtain ⟨n, rfl⟩ := hw
  iapply HΦ $$ %n
  iframe

@[lantana_alias heap_lang.lwp_alloc]
theorem lwp_alloc (v : Val) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.allocN (.val (.lit (.int 1))) (.val v)) ∗
          stepPre i G R }}}
        (Exp.allocN (.val (.lit (.int 1))) (.val v)) @ s; i; E
      l{{{ (l : Loc), RET Val.lit (.loc l); threadExpr i C (.val (.lit (.loc l))) ∗
        stepPost i G R o ∗ l ↦ some v }}} := by
  iintro %Φ !> ⟨HT, Hpre⟩ HΦ
  iapply lwp_heap_step (o := o) rfl iprop(emp)
    (fun w => iprop(∃ l : Loc, ⌜w = .lit (.loc l)⌝ ∗ l ↦ some v))
  · intro σ₁
    iintro ⟨Hh, -⟩
    isplitr
    · ipureintro
      exact ⟨_, _, _, alloc_fresh v 1 σ₁ (by omega)⟩
    iintro %e₂ %σ₂ %efs %hs
    cases hs
    next l _ hfresh =>
    have hl : σ₁.get? l = none := by
      have := hfresh 0 (by omega) (by omega)
      rwa [loc_add_zero] at this
    imod genHeap_alloc (v := some v) hl $$ Hh with ⟨Hh, Hl, -⟩
    imodintro
    isplitr
    · ipureintro; trivial
    iexists .lit (.loc l)
    isplitr
    · ipureintro; trivial
    rw [State.initHeap_singleton]
    iframe Hh
    iexists l
    isplitr
    · ipureintro; trivial
    iexact Hl
  iframe HT Hpre
  isplitr
  · iempintro
  iintro %w ⟨HT, Hpost, %l, %hw, Hl⟩
  subst hw
  iapply HΦ $$ %l
  iframe

@[lantana_alias heap_lang.lwp_free]
theorem lwp_free (l : Loc) (v : Val) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.free (.val (.lit (.loc l)))) ∗ stepPre i G R ∗
          l ↦ some v }}}
        (Exp.free (.val (.lit (.loc l)))) @ s; i; E
      l{{{ RET Val.lit .unit; threadExpr i C (.val (.lit .unit)) ∗ stepPost i G R o ∗
        l ↦ (none : Option Val) }}} := by
  iintro %Φ !> ⟨HT, Hpre, Hl⟩ HΦ
  iapply lwp_heap_step (o := o) rfl iprop(l ↦ some v)
    (fun w => iprop(⌜w = .lit .unit⌝ ∗ l ↦ (none : Option Val)))
  · intro σ₁
    iintro ⟨Hh, Hl⟩
    ihave %hl : ⌜σ₁.get? l = some (some v)⌝ $$ [Hh Hl]
    · iapply genHeapInterp_lookup
      iframe
    isplitr
    · ipureintro
      exact ⟨_, _, _, .freeS l v σ₁ hl⟩
    iintro %e₂ %σ₂ %efs %hs
    cases hs
    imod genHeap_update (v₂ := none) $$ [$Hh $Hl] with ⟨Hh, Hl⟩
    imodintro
    isplitr
    · ipureintro; trivial
    iexists .lit .unit
    isplitr
    · ipureintro; trivial
    rw [State.initHeap_singleton]
    iframe Hh
    isplitr
    · ipureintro; trivial
    iexact Hl
  iframe HT Hpre Hl
  iintro %w ⟨HT, Hpost, %hw, Hl⟩
  subst hw
  iapply HΦ
  iframe

@[lantana_alias heap_lang.lwp_load]
theorem lwp_load (l : Loc) (dq : DFrac) (v : Val) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.load (.val (.lit (.loc l)))) ∗ stepPre i G R ∗
          l ↦{dq} some v }}}
        (Exp.load (.val (.lit (.loc l)))) @ s; i; E
      l{{{ RET v; threadExpr i C (.val v) ∗ stepPost i G R o ∗ l ↦{dq} some v }}} := by
  iintro %Φ !> ⟨HT, Hpre, Hl⟩ HΦ
  iapply lwp_heap_step (o := o) rfl iprop(l ↦{dq} some v) (fun w => iprop(⌜w = v⌝ ∗ l ↦{dq} some v))
  · intro σ₁
    iintro ⟨Hh, Hl⟩
    ihave %hl : ⌜σ₁.get? l = some (some v)⌝ $$ [Hh Hl]
    · ihave >%h := genHeap_valid $$ [$Hh $Hl]
      itrivial
    isplitr
    · ipureintro
      exact ⟨_, _, _, .loadS l v σ₁ hl⟩
    iintro %e₂ %σ₂ %efs %hs
    cases hs
    next v' hget =>
    obtain rfl : v' = v := by rw [hl] at hget; simpa using hget.symm
    imodintro
    isplitr
    · ipureintro; trivial
    iexists v'
    isplitr
    · ipureintro; trivial
    iframe Hh
    isplitr
    · ipureintro; trivial
    iexact Hl
  iframe HT Hpre Hl
  iintro %w ⟨HT, Hpost, %hw, Hl⟩
  subst hw
  iapply HΦ
  iframe

@[lantana_alias heap_lang.lwp_store]
theorem lwp_store (l : Loc) (v' v : Val) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.store (.val (.lit (.loc l))) (.val v)) ∗
          stepPre i G R ∗ l ↦ some v' }}}
        (Exp.store (.val (.lit (.loc l))) (.val v)) @ s; i; E
      l{{{ RET Val.lit .unit; threadExpr i C (.val (.lit .unit)) ∗ stepPost i G R o ∗
        l ↦ some v }}} := by
  iintro %Φ !> ⟨HT, Hpre, Hl⟩ HΦ
  iapply lwp_heap_step (o := o) rfl iprop(l ↦ some v')
    (fun w => iprop(⌜w = .lit .unit⌝ ∗ l ↦ some v))
  · intro σ₁
    iintro ⟨Hh, Hl⟩
    ihave %hl : ⌜σ₁.get? l = some (some v')⌝ $$ [Hh Hl]
    · iapply genHeapInterp_lookup
      iframe
    isplitr
    · ipureintro
      exact ⟨_, _, _, .storeS l v' v σ₁ hl⟩
    iintro %e₂ %σ₂ %efs %hs
    cases hs
    imod genHeap_update (v₂ := some v) $$ [$Hh $Hl] with ⟨Hh, Hl⟩
    imodintro
    isplitr
    · ipureintro; trivial
    iexists .lit .unit
    isplitr
    · ipureintro; trivial
    rw [State.initHeap_singleton]
    iframe Hh
    isplitr
    · ipureintro; trivial
    iexact Hl
  iframe HT Hpre Hl
  iintro %w ⟨HT, Hpost, %hw, Hl⟩
  subst hw
  iapply HΦ
  iframe

@[lantana_alias heap_lang.lwp_xchg]
theorem lwp_xchg (l : Loc) (v' v : Val) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.xchg (.val (.lit (.loc l))) (.val v)) ∗ stepPre i G R ∗
          l ↦ some v' }}}
        (Exp.xchg (.val (.lit (.loc l))) (.val v)) @ s; i; E
      l{{{ RET v'; threadExpr i C (.val v') ∗ stepPost i G R o ∗ l ↦ some v }}} := by
  iintro %Φ !> ⟨HT, Hpre, Hl⟩ HΦ
  iapply lwp_heap_step (o := o) rfl iprop(l ↦ some v') (fun w => iprop(⌜w = v'⌝ ∗ l ↦ some v))
  · intro σ₁
    iintro ⟨Hh, Hl⟩
    ihave %hl : ⌜σ₁.get? l = some (some v')⌝ $$ [Hh Hl]
    · iapply genHeapInterp_lookup
      iframe
    isplitr
    · ipureintro
      exact ⟨_, _, _, .xchgS l v' v σ₁ hl⟩
    iintro %e₂ %σ₂ %efs %hs
    cases hs
    next v'' hget =>
    obtain rfl : v'' = v' := by rw [hl] at hget; simpa using hget.symm
    imod genHeap_update (v₂ := some v) $$ [$Hh $Hl] with ⟨Hh, Hl⟩
    imodintro
    isplitr
    · ipureintro; trivial
    iexists v''
    isplitr
    · ipureintro; trivial
    rw [State.initHeap_singleton]
    iframe Hh
    isplitr
    · ipureintro; trivial
    iexact Hl
  iframe HT Hpre Hl
  iintro %w ⟨HT, Hpost, %hw, Hl⟩
  subst hw
  iapply HΦ
  iframe

@[lantana_alias heap_lang.lwp_cmpxchg_fail]
theorem lwp_cmpXchg_fail (l : Loc) (dq : DFrac) (v' v₁ v₂ : Val) (hne : v' ≠ v₁)
    (hsafe : Val.compareSafe v' v₁) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.cmpXchg (.val (.lit (.loc l))) (.val v₁) (.val v₂)) ∗
          stepPre i G R ∗ l ↦{dq} some v' }}}
        (Exp.cmpXchg (.val (.lit (.loc l))) (.val v₁) (.val v₂)) @ s; i; E
      l{{{ RET Val.pair v' (.lit (.bool false));
        threadExpr i C (.val (.pair v' (.lit (.bool false)))) ∗ stepPost i G R o ∗
        l ↦{dq} some v' }}} := by
  iintro %Φ !> ⟨HT, Hpre, Hl⟩ HΦ
  iapply lwp_heap_step (o := o) rfl iprop(l ↦{dq} some v')
    (fun w => iprop(⌜w = Val.pair v' (.lit (.bool false))⌝ ∗ l ↦{dq} some v'))
  · intro σ₁
    iintro ⟨Hh, Hl⟩
    ihave %hl : ⌜σ₁.get? l = some (some v')⌝ $$ [Hh Hl]
    · iapply genHeapInterp_lookup
      iframe
    isplitr
    · ipureintro
      exact ⟨_, _, _, .cmpXchgS l v₁ v₂ v' σ₁ false hl hsafe (by simp [hne])⟩
    iintro %e₂ %σ₂ %efs %hs
    cases hs
    next vl b _ _ hget =>
    obtain rfl : vl = v' := by rw [hl] at hget; simpa using hget.symm
    obtain rfl : b = false := by simp_all
    simp only [Bool.false_eq_true, ↓reduceIte]
    imodintro
    isplitr
    · ipureintro; trivial
    iexists .pair vl (.lit (.bool false))
    isplitr
    · ipureintro; trivial
    iframe Hh
    isplitr
    · ipureintro; trivial
    iexact Hl
  iframe HT Hpre Hl
  iintro %w ⟨HT, Hpost, %hw, Hl⟩
  subst hw
  iapply HΦ
  iframe

@[lantana_alias heap_lang.lwp_cmpxchg_suc]
theorem lwp_cmpXchg_suc (l : Loc) (v' v₁ v₂ : Val) (heq : v' = v₁)
    (hsafe : Val.compareSafe v' v₁) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.cmpXchg (.val (.lit (.loc l))) (.val v₁) (.val v₂)) ∗
          stepPre i G R ∗ l ↦ some v' }}}
        (Exp.cmpXchg (.val (.lit (.loc l))) (.val v₁) (.val v₂)) @ s; i; E
      l{{{ RET Val.pair v' (.lit (.bool true));
        threadExpr i C (.val (.pair v' (.lit (.bool true)))) ∗ stepPost i G R o ∗
        l ↦ some v₂ }}} := by
  iintro %Φ !> ⟨HT, Hpre, Hl⟩ HΦ
  iapply lwp_heap_step (o := o) rfl iprop(l ↦ some v')
    (fun w => iprop(⌜w = Val.pair v' (.lit (.bool true))⌝ ∗ l ↦ some v₂))
  · intro σ₁
    iintro ⟨Hh, Hl⟩
    ihave %hl : ⌜σ₁.get? l = some (some v')⌝ $$ [Hh Hl]
    · iapply genHeapInterp_lookup
      iframe
    isplitr
    · ipureintro
      exact ⟨_, _, _, .cmpXchgS l v₁ v₂ v' σ₁ true hl hsafe (by simp [heq])⟩
    iintro %e₂ %σ₂ %efs %hs
    cases hs
    next vl b _ _ hget =>
    obtain rfl : vl = v' := by rw [hl] at hget; simpa using hget.symm
    obtain rfl : b = true := by simp_all
    rw [State.initHeap_singleton]
    simp only [↓reduceIte]
    imod genHeap_update (v₂ := some v₂) $$ [$Hh $Hl] with ⟨Hh, Hl⟩
    imodintro
    isplitr
    · ipureintro; trivial
    iexists .pair vl (.lit (.bool true))
    isplitr
    · ipureintro; trivial
    iframe Hh
    isplitr
    · ipureintro; trivial
    iexact Hl
  iframe HT Hpre Hl
  iintro %w ⟨HT, Hpost, %hw, Hl⟩
  subst hw
  iapply HΦ
  iframe

@[lantana_alias heap_lang.lwp_faa]
theorem lwp_faa (l : Loc) (n₁ n₂ : Int) :
    ⊢@{IProp GF} l{{{ threadExpr i C (.faa (.val (.lit (.loc l))) (.val (.lit (.int n₂)))) ∗
          stepPre i G R ∗ l ↦ some (Val.lit (.int n₁)) }}}
        (Exp.faa (.val (.lit (.loc l))) (.val (.lit (.int n₂)))) @ s; i; E
      l{{{ RET Val.lit (.int n₁); threadExpr i C (.val (.lit (.int n₁))) ∗
        stepPost i G R o ∗ l ↦ some (Val.lit (.int (n₁ + n₂))) }}} := by
  iintro %Φ !> ⟨HT, Hpre, Hl⟩ HΦ
  iapply lwp_heap_step (o := o) rfl iprop(l ↦ some (Val.lit (.int n₁)))
    (fun w => iprop(⌜w = .lit (.int n₁)⌝ ∗ l ↦ some (Val.lit (.int (n₁ + n₂)))))
  · intro σ₁
    iintro ⟨Hh, Hl⟩
    ihave %hl : ⌜σ₁.get? l = some (some (.lit (.int n₁)))⌝ $$ [Hh Hl]
    · iapply genHeapInterp_lookup
      iframe
    isplitr
    · ipureintro
      exact ⟨_, _, _, .faaS l n₁ n₂ σ₁ hl⟩
    iintro %e₂ %σ₂ %efs %hs
    cases hs
    next i₁ hget =>
    obtain rfl : i₁ = n₁ := by rw [hl] at hget; simpa using hget.symm
    imod genHeap_update (v₂ := some (Val.lit (.int (i₁ + n₂)))) $$ [$Hh $Hl] with ⟨Hh, Hl⟩
    imodintro
    isplitr
    · ipureintro; trivial
    iexists .lit (.int i₁)
    isplitr
    · ipureintro; trivial
    rw [State.initHeap_singleton]
    iframe Hh
    isplitr
    · ipureintro; trivial
    iexact Hl
  iframe HT Hpre Hl
  iintro %w ⟨HT, Hpost, %hw, Hl⟩
  subst hw
  iapply HΦ
  iframe

end Laws

end Lantana.HeapLang
