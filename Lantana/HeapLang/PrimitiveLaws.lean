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

**Contexts.** Unlike Rocq, where a context is the list of its items, `lWP` quantifies over
every function `K` with `Language.Context K` that puts the thread's expression into the pool.
The token knows `fill C e`; that `K` agrees with `fill C` after the step is
`Context.eq_fill_of_primStep`. For a deterministic step this follows from the context laws; for
`chooseNat` it needs HeapLang itself (`Context.eq_fill_chooseNat`, by probing `K` with a load).
-/

@[expose] public noncomputable section

namespace Lantana.HeapLang

open Iris Iris.BI Iris.ProofMode Lantana Lantana.Language
open Iris.ProgramLogic (toVal)

/-! ## Contexts are determined by a step -/

section Contexts

open EctxItemLanguage EctxLanguage FromMathlib

theorem ofVal_eq_ofVal_iff {v w : Val} : (Exp.ofVal v : Exp) = Exp.ofVal w ↔ v = w :=
  ⟨fun h => Exp.val.inj h, fun h => h ▸ rfl⟩

attribute [local simp] ofVal_eq_ofVal_iff

theorem ECtxItem.eq_of_fill_eq₂ {Ki Kj : ECtxItem} {u₀ u₁ w₀ w₁ : Exp} (hne : u₀ ≠ u₁)
    (h₀ : Ki.fill u₀ = Kj.fill w₀) (h₁ : Ki.fill u₁ = Kj.fill w₁) : Ki = Kj := by
  cases Ki <;> cases Kj <;> simp_all [ECtxItem.fill]

/-- Two contexts that agree on two different values plugged into them are equal. -/
theorem ctx_eq_of_fill_val_eq₂ {A B : List ECtxItem} {a₀ a₁ b₀ b₁ : Val} (hne : a₀ ≠ a₁)
    (h₀ : fill A (Exp.ofVal a₀ : Exp) = fill B (Exp.ofVal b₀ : Exp))
    (h₁ : fill A (Exp.ofVal a₁ : Exp) = fill B (Exp.ofVal b₁ : Exp)) : A = B := by
  induction A using List.reverseRec generalizing B with
  | nil =>
    cases B using List.reverseCases with
    | nil => rfl
    | append_singleton B Kj =>
      rw [fill_append, fill_singleton, fill_nil] at h₀
      exact absurd (congrArg toVal h₀) (by simp)
  | append_singleton A Ki ih =>
    cases B using List.reverseCases with
    | nil =>
      rw [fill_append, fill_singleton, fill_nil] at h₀
      exact absurd (congrArg toVal h₀) (by simp)
    | append_singleton B Kj =>
      rw [fill_append, fill_append, fill_singleton, fill_singleton] at h₀ h₁
      have hu : fill A (Exp.ofVal a₀ : Exp) ≠ fill A (Exp.ofVal a₁ : Exp) := fun h =>
        hne (ofVal_eq_ofVal_iff.mp (EvContext.fill_inj h))
      obtain rfl : Ki = Kj := ECtxItem.eq_of_fill_eq₂ hu h₀ h₁
      rw [ih (fillItem_inj h₀) (fillItem_inj h₁)]

/-! ### Base steps -/

theorem State.get?_initHeap_self {σ : State} {l : Loc} {n : Int} (hn : 0 < n) {v : Option Val} :
    (σ.initHeap l n v).get? l = some v := by
  simp only [State.get?]
  rw [get?_foldl_insert, ite_eq_left ⟨0, by omega, by simp [loc_add_zero]⟩]

theorem State.get?_initHeap (σ : State) (l k : Loc) (n : Int) (v : Option Val) :
    (σ.initHeap l n v).get? k =
      if (∃ i, i < n.toNat ∧ k = l + (i : Int)) then some v else σ.get? k := by
  simp only [State.get?]
  rw [get?_foldl_insert]

/-- Allocation at two fresh blocks gives the same state only at the same location. -/
theorem State.eq_of_initHeap_eq {σ : State} {l l' : Loc} {n : Int} {v : Option Val} (hn : 0 < n)
    (hf : ∀ i : Int, 0 ≤ i → i < n → σ.get? (l + i) = none)
    (hf' : ∀ i : Int, 0 ≤ i → i < n → σ.get? (l' + i) = none)
    (h : σ.initHeap l n v = σ.initHeap l' n v) : l = l' := by
  have key : ∀ {l l' : Loc}, (∀ i : Int, 0 ≤ i → i < n → σ.get? (l + i) = none) →
      σ.initHeap l n v = σ.initHeap l' n v → ∃ i : Nat, l = l' + (i : Int) := by
    intro l l' hf h
    have h1 := State.get?_initHeap_self (σ := σ) (l := l) hn (v := v)
    rw [h, State.get?_initHeap] at h1
    split at h1
    · next hex => obtain ⟨i, -, hi⟩ := hex; exact ⟨i, hi⟩
    · have := hf 0 (by omega) hn
      rw [loc_add_zero] at this
      simp [this] at h1
  obtain ⟨i, hi⟩ := key hf h
  obtain ⟨j, hj⟩ := key hf' h.symm
  have h1 := congrArg Loc.n hi
  have h2 := congrArg Loc.n hj
  simp only [loc_add_n] at h1 h2
  ext
  omega

/-- A base step other than `chooseNat` is deterministic, given the final state. -/
theorem BaseStep.det_of_ne_chooseNat {r a b : Exp} {σ σ₁ σ₂ : State} {efs efs' : List Exp}
    (ha : BaseStep r σ a σ₁ efs) (hb : BaseStep r σ b σ₂ efs') (hσ : σ₁ = σ₂)
    (hr : r ≠ .chooseNat) : a = b := by
  cases ha with
  | allocNS n v σ l hn hf =>
    cases hb with
    | allocNS _ _ _ l' _ hf' => rw [State.eq_of_initHeap_eq hn hf hf' hσ]
  | _ => cases hb; simp_all

/-! ### Contexts are determined by a step

`Language.Context K` is a property of a function `K`, so `K e₁ = fill C e₁` alone does not say
that `K` is `fill C`. Along a step of `e₁` it does: for a deterministic step this follows from
the context laws, and for `chooseNat` from probing `K` with a load (`eq_fill_chooseNat`). -/

/-- The location the probe reads. -/
def probeLoc : Loc := ⟨0⟩

/-- The state whose heap holds `#m` at `probeLoc` and nothing else. -/
def probeState (m : Nat) : State :=
  ⟨Iris.Std.insert (∅ : HeapF (Option Val)) probeLoc (some (.lit (.int m)))⟩

theorem probeState_get? (m : Nat) (l : Loc) :
    (probeState m).get? l = if probeLoc = l then some (some (.lit (.int m))) else none := by
  simp only [State.get?, probeState]
  rw [Iris.Std.LawfulPartialMap.get?_insert, Iris.Std.get?_empty]

theorem probeState_get?_eq_some {m : Nat} {l : Loc} {v : Option Val}
    (h : (probeState m).get? l = some v) : l = probeLoc ∧ v = some (.lit (.int m)) := by
  rw [probeState_get?] at h
  split at h <;> simp_all

/-- The base steps of a redex `q` in the probe states: they read the probe (`load`, `faa`),
read it into a pair (`cmpXchg`), or do not depend on it. -/
theorem probe_classify {q a₀ : Exp} {σ₀' : State} {efs₀ : List Exp}
    (h₀ : BaseStep q (probeState 0) a₀ σ₀' efs₀) (hσ₀ : σ₀' = probeState 0) (hefs₀ : efs₀ = [])
    (huniq : ∀ a σ' efs, BaseStep q (probeState 0) a σ' efs → a = a₀)
    (h₁ : ∃ a σ' efs, BaseStep q (probeState 1) a σ' efs ∧ σ' = probeState 1 ∧ efs = []) :
    (∀ m a σ' efs, BaseStep q (probeState m) a σ' efs → a = .val (.lit (.int m))) ∨
    (∀ m a σ' efs, BaseStep q (probeState m) a σ' efs →
      ∃ b, a = .val (.pair (.lit (.int m)) (.lit (.bool b)))) ∨
    (∀ m a σ' efs, BaseStep q (probeState m) a σ' efs → a = a₀) := by
  cases h₀
  case loadS l v hget =>
    left
    intro m a σ' efs h
    cases h
    next v' hget' => obtain ⟨-, h⟩ := probeState_get?_eq_some hget'; simp_all
  case faaS l i1 i2 hget =>
    left
    intro m a σ' efs h
    cases h
    next i1' hget' => obtain ⟨-, h⟩ := probeState_get?_eq_some hget'; simp_all
  case cmpXchgS l v1 v2 vl b hget _ _ =>
    right; left
    intro m a σ' efs h
    cases h
    next vl' b' _ _ hget' => obtain ⟨-, h⟩ := probeState_get?_eq_some hget'; simp_all
  case allocNS n v l hn hf =>
    exfalso
    have h1 := State.get?_initHeap_self (σ := probeState 0) (l := l) hn (v := some v)
    rw [hσ₀] at h1
    have h2 := hf 0 (by omega) hn
    rw [loc_add_zero] at h2
    simp [h1] at h2
  case freeS l v hget =>
    exfalso
    have h1 := State.get?_initHeap_self (σ := probeState 0) (l := l) (n := 1) (by omega)
      (v := none)
    rw [hσ₀, hget] at h1
    simp at h1
  case storeS l v w hget =>
    exfalso
    obtain ⟨hl, -⟩ := probeState_get?_eq_some hget
    have h0 := State.get?_initHeap_self (σ := probeState 0) (l := l) (n := 1) (by omega)
      (v := some w)
    rw [hσ₀] at h0
    obtain ⟨a, σ', efs, h, hσ', -⟩ := h₁
    cases h
    have h1 := State.get?_initHeap_self (σ := probeState 1) (l := l) (n := 1) (by omega)
      (v := some w)
    rw [hσ'] at h1
    obtain ⟨-, h0⟩ := probeState_get?_eq_some h0
    obtain ⟨-, h1⟩ := probeState_get?_eq_some h1
    simp_all
  case xchgS l v1 v2 hget =>
    exfalso
    obtain ⟨hl, -⟩ := probeState_get?_eq_some hget
    have h0 := State.get?_initHeap_self (σ := probeState 0) (l := l) (n := 1) (by omega)
      (v := some v2)
    rw [hσ₀] at h0
    obtain ⟨a, σ', efs, h, hσ', -⟩ := h₁
    cases h
    have h1 := State.get?_initHeap_self (σ := probeState 1) (l := l) (n := 1) (by omega)
      (v := some v2)
    rw [hσ'] at h1
    obtain ⟨-, h0⟩ := probeState_get?_eq_some h0
    obtain ⟨-, h1⟩ := probeState_get?_eq_some h1
    simp_all
  case forkS => simp at hefs₀
  case chooseNatS k =>
    exfalso
    have := huniq _ _ _ (.chooseNatS (k + 1) _)
    simp at this
    omega
  all_goals
    right; right
    intro m a σ' efs h
    cases h
    simp_all

/-- A context that agrees with `fill C` on `fill D chooseNat` agrees with it on every result of
the step. The bijection between the results that the context laws give is the identity: the
context maps the load of a location to a redex whose results follow the location's contents. -/
theorem Context.eq_fill_chooseNat {K : Exp → Exp} [Context K] {C D : List ECtxItem}
    (hK : K (fill D .chooseNat) = fill C (fill D .chooseNat)) (n : Nat) :
    K (fill D (.val (.lit (.int n)))) = fill C (fill D (.val (.lit (.int n)))) := by
  have hnv : toVal (fill D Exp.chooseNat) = none := EctxItemLanguage.fill_not_val D rfl
  have hred : ∀ σ : State, BaseReducible Exp.chooseNat σ := fun σ => ⟨_, _, _, .chooseNatS 0 σ⟩
  -- The results of `chooseNat` under `K` are those under `fill (D ++ C)`.
  have hF1 (m : Nat) : ∃ m' : Nat,
      K (fill D (.val (.lit (.int m)))) = fill (D ++ C) (.val (.lit (.int m'))) := by
    have hs := Context.primStep_fill (K := K)
      (primStep_fill_of_baseStep D (BaseStep.chooseNatS m default))
    rw [hK, ← fill_append] at hs
    obtain ⟨y, hy, hb⟩ := exists_baseStep_of_primStep_fill (hred default) hs
    cases hb
    exact ⟨_, hy⟩
  have hF2 (m' : Nat) : ∃ m : Nat,
      fill (D ++ C) (.val (.lit (.int m'))) = K (fill D (.val (.lit (.int m)))) := by
    have hs := primStep_fill_of_baseStep (Expr := Exp) (D ++ C) (BaseStep.chooseNatS m' default)
    rw [fill_append, ← hK] at hs
    obtain ⟨x, hx, hs'⟩ := Context.primStep_fill_inv (K := K) hnv hs
    obtain ⟨y, rfl, hb⟩ := exists_baseStep_of_primStep_fill (hred default) hs'
    cases hb
    exact ⟨_, hx⟩
  -- The probe: a load of `probeLoc` in the context `D`.
  have hload (m : Nat) : BaseStep (.load (.val (.lit (.loc probeLoc)))) (probeState m)
      (.val (.lit (.int m))) (probeState m) [] :=
    .loadS _ _ _ (by simp [probeState_get?])
  have hPuniq (m : Nat) (x : Exp) (σ' : State) (efs : List Exp)
      (h : primStep (fill D (.load (.val (.lit (.loc probeLoc))))) (probeState m) x σ' efs) :
      x = fill D (.val (.lit (.int m))) := by
    obtain ⟨y, rfl, hb⟩ := exists_baseStep_of_primStep_fill ⟨_, _, _, hload m⟩ h
    cases hb
    next v hget => obtain ⟨-, h⟩ := probeState_get?_eq_some hget; simp_all
  -- Its image under `K` reads the probe.
  have hY (m : Nat) : primStep (K (fill D (.load (.val (.lit (.loc probeLoc)))))) (probeState m)
      (K (fill D (.val (.lit (.int m))))) (probeState m) [] :=
    Context.primStep_fill (primStep_fill_of_baseStep D (hload m))
  have hYuniq (m : Nat) (Z : Exp) (σ' : State) (efs : List Exp)
      (h : primStep (K (fill D (.load (.val (.lit (.loc probeLoc)))))) (probeState m) Z σ' efs) :
      Z = K (fill D (.val (.lit (.int m)))) := by
    obtain ⟨x, rfl, hx⟩ := Context.primStep_fill_inv (K := K)
      (EctxItemLanguage.fill_not_val D rfl) h
    rw [hPuniq m x σ' efs hx]
  obtain ⟨D', q, a₀, hYeq, hX₀, hb₀⟩ := hY 0
  have hall (m : Nat) : ∃ a, K (fill D (.val (.lit (.int m)))) = fill D' a ∧
      BaseStep q (probeState m) a (probeState m) [] := by
    obtain ⟨D'', q', a', heq, ha', hb'⟩ := hY m
    obtain ⟨rfl, rfl⟩ := base_redex_unique (hYeq.symm.trans heq) ⟨_, _, _, hb₀⟩ ⟨_, _, _, hb'⟩
    exact ⟨a', ha', hb'⟩
  have huniq (a : Exp) (σ' : State) (efs : List Exp) (h : BaseStep q (probeState 0) a σ' efs) :
      a = a₀ := by
    have h' : primStep (K (fill D (.load (.val (.lit (.loc probeLoc)))))) (probeState 0)
        (fill D' a) σ' efs := by
      rw [hYeq]; exact primStep_fill_of_baseStep (Expr := Exp) D' h
    have := hYuniq 0 _ _ _ h'
    exact EvContext.fill_inj (this.trans hX₀)
  obtain ⟨a₁, -, hb₁⟩ := hall 1
  obtain ⟨m₀, h₀⟩ := hF1 0
  obtain ⟨m₁, h₁⟩ := hF1 1
  obtain ⟨c₀, hk₀, hs₀⟩ := hall 0
  obtain ⟨c₁, hk₁, hs₁⟩ := hall 1
  rcases probe_classify hb₀ rfl rfl huniq ⟨a₁, _, _, hb₁, rfl, rfl⟩ with hA | hB | hC
  · -- The redex reads the probe: `K` is `fill (D ++ C)` on the results.
    rw [hA _ _ _ _ hs₀] at hk₀
    rw [hA _ _ _ _ hs₁] at hk₁
    have hDC : D' = D ++ C :=
      ctx_eq_of_fill_val_eq₂ (a₀ := .lit (.int 0)) (a₁ := .lit (.int 1)) (by simp)
        (hk₀.symm.trans h₀) (hk₁.symm.trans h₁)
    obtain ⟨cn, hkn, hsn⟩ := hall n
    rw [hkn, hA _ _ _ _ hsn, hDC, fill_append]
  · -- The redex reads the probe into a pair: impossible.
    obtain ⟨d₀, hd₀⟩ := hB _ _ _ _ hs₀
    obtain ⟨d₁, hd₁⟩ := hB _ _ _ _ hs₁
    rw [hd₀] at hk₀
    rw [hd₁] at hk₁
    have hDC : D' = D ++ C :=
      ctx_eq_of_fill_val_eq₂ (a₀ := .pair (.lit (.int 0)) (.lit (.bool d₀)))
        (a₁ := .pair (.lit (.int 1)) (.lit (.bool d₁))) (by simp)
        (hk₀.symm.trans h₀) (hk₁.symm.trans h₁)
    subst hDC
    have := EvContext.fill_inj (hk₀.symm.trans h₀)
    simp at this
  · -- The redex ignores the probe: then `K` is constant on the results, but they are not.
    obtain ⟨x₀, hx₀⟩ := hF2 0
    obtain ⟨x₁, hx₁⟩ := hF2 1
    obtain ⟨e₀, he₀, hse₀⟩ := hall x₀
    obtain ⟨e₁, he₁, hse₁⟩ := hall x₁
    rw [hC _ _ _ _ hse₀] at he₀
    rw [hC _ _ _ _ hse₁] at he₁
    have := EvContext.fill_inj ((hx₀.trans he₀).trans (hx₁.trans he₁).symm)
    simp at this

/-- A context that agrees with `fill C` on an expression agrees with it on the results of the
steps of that expression. -/
theorem Context.eq_fill_of_primStep {K : Exp → Exp} [Context K] {C : List ECtxItem}
    {e₁ e₂ : Exp} {σ σ' : State} {efs : List Exp}
    (hK : K e₁ = fill C e₁) (h : primStep e₁ σ e₂ σ' efs) : K e₂ = fill C e₂ := by
  obtain ⟨D, r, r', rfl, rfl, hb⟩ := h
  by_cases hr : r = .chooseNat
  · subst hr
    cases hb
    exact Context.eq_fill_chooseNat hK _
  · have hs : primStep (K (fill D r)) σ (fill C (fill D r')) σ' efs := by
      rw [hK]
      exact Context.primStep_fill (primStep_fill_of_baseStep D hb)
    obtain ⟨x, hx, hxs⟩ := Context.primStep_fill_inv (K := K)
      (EctxItemLanguage.fill_not_val D (EctxLanguage.val_base_stuck hb)) hs
    obtain ⟨y, rfl, hy⟩ := exists_baseStep_of_primStep_fill ⟨_, _, _, hb⟩ hxs
    rw [BaseStep.det_of_ne_chooseNat hy hb rfl hr] at hx
    exact hx.symm

end Contexts

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
scoped notation:20 "exits " v " @ " i => threadExpr i [] (Exp.val v)

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
  pureExecSI {K e₁ e₂ σ tp} hK hi hstep := by
    iintro ⟨Hf, Hσ⟩
    icases (stateInterp_unfold σ tp).mp $$ Hσ with ⟨Hh, Ha⟩
    ihave %h : ⌜tp[i]? = some (fill C e₁)⌝ $$ [Ha Hf]
    · iapply threadMapAuth_lookup
      iframe
    have hKe₂ := Context.eq_fill_of_primStep (Option.some.inj (hi.symm.trans h)) hstep
    imod threadMapAuth_update tp i C e₁ e₂ $$ [Ha Hf] with ⟨Ha, Hf⟩
    · iframe
    imodintro
    iframe Hf
    iapply (stateInterp_unfold σ _).mpr
    rw [hKe₂]
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
  iintro %K %σ₁ %tp %hK %hi Hσ
  icases (stateInterp_unfold σ₁ tp).mp $$ Hσ with ⟨Hh, Ha⟩
  ihave %hT : ⌜tp[i]? = some (fill C e₁)⌝ $$ [Ha HT]
  · iapply threadMapAuth_lookup
    iframe
  have hKe : K e₁ = fill C e₁ := Option.some.inj (hi.symm.trans hT)
  icases hstep σ₁ $$ [Hh HH] with ⟨%hred, Hstep⟩
  · iframe
  imodintro
  isplitr
  · ipureintro
    exact hred
  iexists G
  iframe HG HF
  iexists R
  iframe HR
  iintro %e₂ %σ₂ %efs %hs
  have hKe₂ := Context.eq_fill_of_primStep hKe (EctxLanguage.primStep_of_baseStep hs)
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
    rw [hKe₂]
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

/-- Fork: the children `K ⊆ G` move to the new thread, each paying one unit of fuel. -/
@[lantana_alias heap_lang.lwp_fork]
theorem lwp_fork (K : Oids) (P : IProp GF) (e : Exp) (hK : K ⊆ G) :
    (∀ j : ThreadId, l{{{ threadExpr j [] e ∗ thKids j K ∗ P }}} e @ s; j; ⊤
        l{{{ v, RET v; liftTerm j (fun _ _ => iprop(True)) v }}})
      ⊢@{IProp GF} l{{{ threadExpr i C (.fork e) ∗ stepPre i G R ∗ oblFuels K 1 ∗ P }}}
          (Exp.fork e) @ s; i; E
        l{{{ RET Val.lit .unit; threadExpr i C (.val (.lit .unit)) ∗
          (£ₒ o ∗ thKids i (G \ K) ∗ witCreds R) }}} := sorry

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
  iapply lwp_heap_step (o := o) rfl iprop(l ↦ some v') (fun w => iprop(⌜w = .lit .unit⌝ ∗ l ↦ some v))
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
