/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.Instances.IProp
public import Iris.BI
public import Iris.BI.Lib.Fractional
public import Iris.Std.CoPset
public import Iris.Std.Namespaces
public import Iris.Std.GenSetsInstances
public import Iris.Std.HeapInstances
public import Lantana.Algebra.Measure
public import Lantana.ProgramLogic.TemporalClass

/-! # The obligation-forest interface

The core of the logic (Rocq `lantana/program_logic/obl_forest.v`): the obligation predicates,
the model update `|={E₁,E₂}=>m P`, the physical-step modalities, and their rules. Every live
obligation is a child of one parent, a thread or an obligation (`Par.kids p K`: the children of
`p` are exactly `K`).

Design (D13): this is a *sealed API module*, not a class. The predicates are defined by the
model (`Lantana.BaseLogic`) and re-exported here as irreducible definitions; the rules are
theorems; nothing outside the model and this module unfolds the predicates.

**Skeleton (M1):** the predicates are `opaque` constants over a placeholder ghost-state class
and the rules are stated with `sorry`, so that the statements and universes are validated
before the model exists. The model (M4) replaces the constants by definitions and the sorries
by proofs; the statements do not change.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open Iris.ProgramLogic (toVal)
open scoped Lantana.Measure Ordinals.Ordinal


/-- Obligation ids. -/
@[lantana_alias oid]
abbrev Oid := Nat

/-- Finite sets of obligation ids. -/
@[lantana_alias oids]
abbrev Oids := Std.ExtTreeSet Oid compare

/-- Finite maps from obligation ids. -/
abbrev OidMap (V : Type _) := Std.ExtTreeMap Oid V compare

/-- A parent in the obligation forest: a thread or an obligation. -/
@[lantana_alias parent]
inductive Parent where
  | thread (i : ThreadId)
  | obl (k : Oid)
  deriving DecidableEq

attribute [lantana_alias PThread] Parent.thread
attribute [lantana_alias PObl] Parent.obl

section Predicates

variable {GF : BundledGFunctors} [ModelGS GF]

/-! ## The predicates -/

/-- `Par.kids p K`: the children of `p` are exactly `K`. For a thread, it is also running;
for an obligation, it exists exactly while the obligation is live and in the forest. -/
@[lantana_alias oblf.parP_kids]
opaque Par.kids (p : Parent) (K : Oids) : IProp GF

/-- Thread `i` has terminated. -/
@[lantana_alias oblf.thP_done]
opaque Th.done (i : ThreadId) : IProp GF

/-- Obligation `k` is live (`q` a fraction). -/
@[lantana_alias oblf.oblP_assigned]
opaque Obl.assigned (k : Oid) (q : Qp) : IProp GF

/-- Obligation `k` is discharged. -/
@[lantana_alias oblf.oblP_discharged]
opaque Obl.discharged (k : Oid) : IProp GF

/-- Fuel `μ` of obligation `k` at layer `ℓ`. -/
@[lantana_alias oblf.oblP_fuel]
opaque Obl.fuel (k : Oid) (ℓ : Layer) (μ : Measure) : IProp GF

/-- An invariant over the status of `k`: `P` while live, `R` once discharged. -/
@[lantana_alias oblf.oblP_inv]
opaque Obl.inv (N : Namespace) (k : Oid) (P R : IProp GF) : IProp GF

/-- A witness of `k` at layer `ℓ`. -/
@[lantana_alias oblf.witP_layer]
opaque Wit.layer (k : Oid) (ℓ : Layer) : IProp GF

/-- Witness credits `a` of `k`. -/
@[lantana_alias oblf.witP_cred]
opaque Wit.cred (k : Oid) (a : Fuel) : IProp GF

/-- The witness induction of `k` at layer `ℓ` with budget `α`, carrying the fuels `F`. -/
@[lantana_alias oblf.wit_fuels]
opaque Wit.fuels (k : Oid) (ℓ : Layer) (α : Fuel) (F : OidMap (Layer × Measure)) : IProp GF

/-- The base model update `|=[n,tc]=>m P` at step index `n` with `tc` threads: a least fixpoint
of rounds that may change obligations and witnesses while keeping the model interpretation
(Rocq `mupd`). -/
@[lantana_alias mupd]
opaque mupdBase (n tc : Nat) (P : IProp GF) : IProp GF

/-- The progress round of a physical step of thread `i`, at step index `n` with `tc` threads:
`i`'s obligations progress and the witnesses get credits (Rocq `mprog`, `@={n,Θ,i}=↓ P`). -/
@[lantana_alias mprog]
opaque mprog (n tc : Nat) (i : ThreadId) (P : IProp GF) : IProp GF

/-- The physical round of a step from index `n₁` with `tc₁` threads to `n₂` with `tc₂`
threads (Rocq `mphys`, `@={n1,n2,Θ1,Θ2}=> P`). -/
@[lantana_alias mphys]
opaque mphys (n₁ n₂ tc₁ tc₂ : Nat) (P : IProp GF) : IProp GF

end Predicates

/-! ## Notations -/

/-- `|=[n,tc]=>m P`: the base model update. -/
scoped syntax:max "|=[" term "," term "]=>m " term:40 : term
scoped macro_rules
  | `(|=[$n,$tc]=>m $P) => `(mupdBase $n $tc iprop($P))

section
variable {Expr : Type} {State : Type} {GF : BundledGFunctors} [ModelGS GF]
  [BIFUpdate (IProp GF)]

/-- The fancy model update `|={E₁,E₂:n,tc}=>m P` (Rocq `fmupd`). -/
@[lantana_alias fmupd]
def mupdFancy (E₁ E₂ : CoPset) (n tc : Nat) (P : IProp GF) : IProp GF :=
  iprop(|={E₁,∅}=> |=[n,tc]=>m |={∅,E₂}=> P)

variable [TemporalGS Expr State GF] [StateInterp Expr State GF] [TemporalInterp Expr State GF]

/-- The model update `|={E₁,E₂}=>m P` of the interface: a fancy update that may also change
the model, keeping the history and temporal interpretations (Rocq `sfmupd`). -/
@[lantana_alias oblf.sfmupd]
def mupd (E₁ E₂ : CoPset) (P : IProp GF) : IProp GF :=
  iprop(∀ (h : List (HistEntry Expr State)) (n : Nat) (σ : State) (tp : ThreadPool Expr),
    historyTInterp h n σ tp -∗ mupdFancy E₁ E₂ n tp.length iprop(historyTInterp h n σ tp ∗ P))

end

/-- `|={E₁,E₂}=>m P`: the model update. -/
scoped syntax:max "|={" term "," term "}=>m " term:40 : term
/-- `|={E}=>m P`: the model update at one mask. -/
scoped syntax:max "|={" term "}=>m " term:40 : term
/-- `P ={E₁,E₂}=∗m Q`: the wand form of the model update. -/
scoped syntax:25 term:26 " ={" term "," term "}=∗m " term:25 : term
/-- `P ={E}=∗m Q`. -/
scoped syntax:25 term:26 " ={" term "}=∗m " term:25 : term

scoped macro_rules
  | `(|={$E₁,$E₂}=>m $P) => `(mupd $E₁ $E₂ iprop($P))
  | `(|={$E}=>m $P) => `(mupd $E $E iprop($P))
  | `($P ={$E₁,$E₂}=∗m $Q) => `(iprop($P -∗ |={$E₁,$E₂}=>m $Q))
  | `($P ={$E}=∗m $Q) => `(iprop($P -∗ |={$E}=>m $Q))

/-- `thKids i K`: the children of thread `i` are `K`. -/
scoped notation:max "thKids " i:max K:max => Par.kids (Parent.thread i) K
/-- `oblKids k K`: the children of obligation `k` are `K`. -/
scoped notation:max "oblKids " k:max K:max => Par.kids (Parent.obl k) K

section Rules

variable {Expr : Type} {State : Type} {GF : BundledGFunctors} [ModelGS GF]

/-- One unit of fuel at layer `ℓ` is enough to hang below `p`: always below a thread; below
an obligation `q`, `ℓ` must be above a witness layer of `q`. -/
@[lantana_alias parent_below]
def parBelow (p : Parent) (ℓ : Layer) : IProp GF :=
  match p with
  | .thread _ => iprop(True)
  | .obl q => iprop(∃ ℓq : Layer, ⌜ℓq < ℓ⌝ ∗ Wit.layer q ℓq)

/-- A new obligation at layer `ℓ` may be created below `p`: below an obligation `q`, `ℓ` must be
at least a witness layer of `q`. A move needs a strictly larger layer (`parBelow`). -/
@[lantana_alias parent_le]
def parLe (p : Parent) (ℓ : Layer) : IProp GF :=
  match p with
  | .thread _ => iprop(True)
  | .obl q => iprop(∃ ℓq : Layer, ⌜ℓq ≤ ℓ⌝ ∗ Wit.layer q ℓq)

/-- `n` units of fuel of each obligation of `K`, at any layers. -/
@[lantana_alias oblf.oblP_fuels]
def oblFuels (K : Oids) (n : Measure) : IProp GF :=
  iprop([∗set] k ∈ K, ∃ ℓ : Layer, Obl.fuel k ℓ n)

/-- The witnesses `R` with their layers. -/
def witLayers (R : Oids) : IProp GF := iprop([∗set] r ∈ R, ∃ ℓ : Layer, Wit.layer r ℓ)

/-- One credit for each witness of `R`, or its discharge (what a step gives back). -/
def witCreds (R : Oids) : IProp GF := iprop([∗set] r ∈ R, Wit.cred r 1 ∨ Obl.discharged r)

/-! ## Structural properties -/

instance Par.kids_timeless (p : Parent) (K : Oids) : Timeless (Par.kids (GF := GF) p K) := sorry
instance Th.done_timeless (i : ThreadId) : Timeless (Th.done (GF := GF) i) := sorry
instance Th.done_persistent (i : ThreadId) : Persistent (Th.done (GF := GF) i) := sorry
instance Obl.assigned_timeless (k : Oid) (q : Qp) : Timeless (Obl.assigned (GF := GF) k q) := sorry
instance Obl.assigned_fractional (k : Oid) : Fractional (Obl.assigned (GF := GF) k) := sorry
instance Obl.discharged_timeless (k : Oid) : Timeless (Obl.discharged (GF := GF) k) := sorry
instance Obl.discharged_persistent (k : Oid) : Persistent (Obl.discharged (GF := GF) k) := sorry
instance Obl.fuel_timeless (k : Oid) (ℓ : Layer) (μ : Measure) :
    Timeless (Obl.fuel (GF := GF) k ℓ μ) := sorry
instance Obl.inv_persistent (N : Namespace) (k : Oid) (P R : IProp GF) :
    Persistent (Obl.inv N k P R) := sorry
instance Obl.inv_contractive_left (N : Namespace) (k : Oid) (R : IProp GF) :
    OFE.Contractive (fun P => Obl.inv N k P R) := sorry
instance Obl.inv_contractive_right (N : Namespace) (k : Oid) (P : IProp GF) :
    OFE.Contractive (fun R => Obl.inv N k P R) := sorry
instance Wit.layer_timeless (k : Oid) (ℓ : Layer) : Timeless (Wit.layer (GF := GF) k ℓ) := sorry
instance Wit.layer_persistent (k : Oid) (ℓ : Layer) : Persistent (Wit.layer (GF := GF) k ℓ) :=
  sorry
instance Wit.cred_timeless (k : Oid) (a : Fuel) : Timeless (Wit.cred (GF := GF) k a) := sorry
instance Wit.fuels_timeless (k : Oid) (ℓ : Layer) (α : Fuel) (F : OidMap (Layer × Measure)) :
    Timeless (Wit.fuels (GF := GF) k ℓ α F) := sorry
instance Wit.fuels_empty_persistent (k : Oid) (ℓ : Layer) (α : Fuel) :
    Persistent (Wit.fuels (GF := GF) k ℓ α ∅) := sorry

/-! ## The model update: the three core rules (the rest is derived) -/

section ModelUpdate
variable [BIFUpdate (IProp GF)] [TemporalGS Expr State GF] [StateInterp Expr State GF]
  [TemporalInterp Expr State GF]

instance mupd_ne (E₁ E₂ : CoPset) :
    OFE.NonExpansive (mupd (Expr := Expr) (State := State) (GF := GF) E₁ E₂) := sorry

@[lantana_alias oblf.fupd_sfmupd]
theorem fupd_mupd (E₁ E₂ : CoPset) (P : IProp GF) :
    (|={E₁,E₂}=> P) ⊢ mupd (Expr := Expr) (State := State) E₁ E₂ P := sorry

@[lantana_alias oblf.sfmupd_bind]
theorem mupd_bind (E₁ E₂ E₃ : CoPset) (P Q : IProp GF) :
    (P -∗ mupd (Expr := Expr) (State := State) E₂ E₃ Q) ⊢
      mupd (Expr := Expr) (State := State) E₁ E₂ P -∗ mupd (Expr := Expr) (State := State) E₁ E₃ Q :=
  sorry

end ModelUpdate

/-! ## Logical rules -/

@[lantana_alias oblf.oblP_assigned_discharged_false]
theorem Obl.assigned_discharged_false (k : Oid) (q : Qp) :
    Obl.assigned (GF := GF) k q ⊢ Obl.discharged k -∗ False := sorry

@[lantana_alias oblf.oblP_kids_discharged_false]
theorem Obl.kids_discharged_false (k : Oid) (K : Oids) :
    oblKids k K ⊢ Obl.discharged (GF := GF) k -∗ False := sorry

@[lantana_alias oblf.parP_kids_discharged]
theorem Par.kids_discharged (k : Oid) (p : Parent) (K : Oids) :
    Par.kids (GF := GF) p K ⊢ Obl.discharged k -∗ ⌜k ∉ K⌝ := sorry

@[lantana_alias oblf.oblP_fuel_proper]
theorem Obl.fuel_eq (k : Oid) {ℓ₁ ℓ₂ : Layer} {μ₁ μ₂ : Measure}
    (h : Measure.rep ℓ₁ μ₁ = Measure.rep ℓ₂ μ₂) :
    Obl.fuel (GF := GF) k ℓ₁ μ₁ ⊣⊢ Obl.fuel k ℓ₂ μ₂ := sorry

section BUpd
variable [BIUpdate (IProp GF)]

@[lantana_alias oblf.oblP_fuel_mon_gen]
theorem Obl.fuel_mono_gen (k : Oid) {ℓ₁ ℓ₂ : Layer} {μ₁ μ₂ : Measure} (hℓ : ℓ₁ ≤ ℓ₂)
    (h : Measure.rep ℓ₁ μ₁ ≤ Measure.rep ℓ₂ μ₂) :
    Obl.fuel (GF := GF) k ℓ₂ μ₂ ⊢ |==> Obl.fuel k ℓ₁ μ₁ := sorry

@[lantana_alias oblf.oblP_fuel_extend]
theorem Obl.fuel_extend (k : Oid) {ℓ₁ ℓ₂ : Layer} (h : ℓ₁ < ℓ₂) (μ : Measure) :
    Obl.fuel (GF := GF) k ℓ₂ 1 ⊢ |==> Obl.fuel k ℓ₁ μ := sorry

@[lantana_alias oblf.witP_cred_mon]
theorem Wit.cred_mono (k : Oid) {a₀ a₁ : Fuel} (h : a₀ ≤ a₁) :
    Wit.cred (GF := GF) k a₁ ⊢ |==> Wit.cred k a₀ := sorry

end BUpd

@[lantana_alias oblf.oblP_fuel_add]
theorem Obl.fuel_add (k : Oid) (ℓ : Layer) (μ₁ μ₂ : Measure) :
    Obl.fuel (GF := GF) k ℓ (μ₁ + μ₂) ⊣⊢ Obl.fuel k ℓ μ₁ ∗ Obl.fuel k ℓ μ₂ := sorry

@[lantana_alias oblf.witP_cred_split]
theorem Wit.cred_split (k : Oid) (a₀ a₁ : Fuel) :
    Wit.cred (GF := GF) k (a₀ +ₕ a₁) ⊣⊢ Wit.cred k a₀ ∗ Wit.cred k a₁ := sorry

#lantana_ignore oblf.witP_cred_proper "ordinal equality is Leibniz: rewrite"

/-! ## Invariants over obligations -/

section FUpd
variable [BIFUpdate (IProp GF)]

@[lantana_alias oblf.oblP_inv_alloc_assigned]
theorem Obl.inv_alloc_assigned (E : CoPset) (N : Namespace) (k : Oid) (P R : IProp GF) :
    ⊢@{IProp GF} Obl.assigned k (Qp.half 1) -∗ ▷ P ={E}=∗ Obl.inv N k P R := sorry

@[lantana_alias oblf.oblP_inv_alloc_discharged]
theorem Obl.inv_alloc_discharged (E : CoPset) (N : Namespace) (k : Oid) (P R : IProp GF) :
    ⊢@{IProp GF} Obl.discharged k -∗ ▷ R ={E}=∗ Obl.inv N k P R := sorry

/-- The content of an obligation invariant: `P` with half of the assignment while live, `R`
with the discharge once discharged. -/
@[lantana_alias oblP_variant]
def Obl.variant (k : Oid) (P R : IProp GF) : IProp GF :=
  iprop((Obl.assigned k (Qp.half 1) ∗ P) ∨ (Obl.discharged k ∗ R))

@[lantana_alias oblf.oblP_inv_acc]
theorem Obl.inv_acc (E : CoPset) (N : Namespace) (k : Oid) (P R : IProp GF) (hN : ↑N ⊆ E) :
    Obl.inv N k P R ⊢ |={E, E \ ↑N}=> ▷ Obl.variant k P R ∗
      (▷ Obl.variant k P R ={E \ ↑N, E}=∗ True) := sorry

end FUpd

/-! ## Witness induction -/

section BUpd
variable [BIUpdate (IProp GF)]

@[lantana_alias oblf.wit_fuels_init]
theorem Wit.fuels_init (k : Oid) (ℓ : Layer) :
    Wit.layer (GF := GF) k ℓ ⊢ ∃ α : Fuel, Wit.fuels k ℓ α ∅ := sorry

@[lantana_alias oblf.wit_fuels_witP_layer]
theorem Wit.fuels_layer (k : Oid) (ℓ : Layer) (α : Fuel) (F : OidMap (Layer × Measure)) :
    Wit.fuels (GF := GF) k ℓ α F ⊢ |==> Wit.layer k ℓ := sorry

@[lantana_alias oblf.wit_fuels_add]
theorem Wit.fuels_add (k : Oid) {ℓ₁ ℓ₂ : Layer} (α : Fuel) (F : OidMap (Layer × Measure))
    (f : Oid) (μ : Measure) (h : ℓ₁ < ℓ₂) :
    Wit.fuels (GF := GF) k ℓ₁ α F ⊢ Obl.fuel f ℓ₂ (μ * ▽) ==∗
      Wit.fuels k ℓ₁ α (F.insert f (ℓ₂, μ)) := sorry

@[lantana_alias oblf.wit_fuels_decr]
theorem Wit.fuels_decr (k : Oid) (ℓ : Layer) (α : Fuel) (F : OidMap (Layer × Measure)) :
    Wit.fuels (GF := GF) k ℓ α F ⊢ Wit.cred k 1 ==∗
      ∃ α₀ : Fuel, ⌜α₀ < α⌝ ∗ Wit.fuels k ℓ α₀ F ∗
        [∗map] f ↦ lm ∈ F, Obl.fuel f lm.1 lm.2 := sorry

end BUpd

/-! ## Model updates that keep every obligation live -/

section ModelUpdate
variable [BIFUpdate (IProp GF)] [TemporalGS Expr State GF] [StateInterp Expr State GF]
  [TemporalInterp Expr State GF]

local notation "|={" E "}=>m " P:40 => mupd (Expr := Expr) (State := State) E E iprop(P)

@[lantana_alias oblf.thread_terminate]
theorem Th.terminate (E : CoPset) (i : ThreadId) :
    thKids i ∅ ⊢ |={E}=>m Th.done (GF := GF) i := sorry

@[lantana_alias oblf.obl_new]
theorem Obl.new (E : CoPset) (p : Parent) (K : Oids) (ℓ : Layer) (μ : Measure) :
    parLe (GF := GF) p ℓ ⊢ Par.kids p K -∗
      |={E}=>m ∃ k : Oid, ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ oblKids k ∅ ∗
        Obl.assigned k 1 ∗ Obl.fuel k ℓ μ ∗ Wit.layer k ℓ := sorry

@[lantana_alias oblf.obl_new_discharged]
theorem Obl.new_discharged (E : CoPset) (ℓ : Layer) :
    ⊢ |={E}=>m ∃ k : Oid, Obl.discharged (GF := GF) k ∗ Wit.layer k ℓ := sorry

@[lantana_alias oblf.obl_move]
theorem Obl.move (E : CoPset) (p₁ p₂ : Parent) (K₁ K₂ : Oids) (k : Oid) (ℓ : Layer)
    (hk : k ∈ K₁) :
    parBelow (GF := GF) p₂ ℓ ⊢ Par.kids p₁ K₁ -∗ Par.kids p₂ K₂ -∗ Obl.fuel k ℓ 1 -∗
      |={E}=>m ⌜k ∉ K₂⌝ ∗ Par.kids p₁ (K₁.erase k) ∗ Par.kids p₂ (K₂.insert k) := sorry

@[lantana_alias oblf.obl_move_up]
theorem Obl.move_up (E : CoPset) (p : Parent) (K : Oids) (k : Oid) (Kk : Oids) (x : Oid)
    (hk : k ∈ K) (hx : x ∈ Kk) :
    Par.kids (GF := GF) p K ⊢ oblKids k Kk -∗
      |={E}=>m ⌜x ∉ K⌝ ∗ Par.kids p (K.insert x) ∗ oblKids k (Kk.erase x) := sorry

@[lantana_alias oblf.obl_check_witness]
theorem Obl.check_witness (E : CoPset) (r : Oid) (ℓ : Layer) :
    Wit.layer (GF := GF) r ℓ ⊢ |={E}=>m (Wit.cred r 0 ∨ Obl.discharged r) := sorry

/-! ## Discharge -/

@[lantana_alias oblf.obl_discharge_leaf]
theorem Obl.discharge_leaf (E : CoPset) (p : Parent) (K : Oids) (k : Oid) (hk : k ∈ K) :
    Par.kids (GF := GF) p K ⊢ oblKids k ∅ -∗ Obl.assigned k 1 -∗
      |={E}=>m Par.kids p (K.erase k) ∗ Obl.discharged k := sorry

end ModelUpdate

/-! ## Physical steps -/

section Physical
variable [BIFUpdate (IProp GF)]

/-- A step of thread `i` burns one unit of fuel of each child of `i` and gives one credit for
each live witness in `R`. -/
@[lantana_alias oblf.step_progress]
theorem step_progress (n tc : Nat) (i : ThreadId) (K R : Oids) (P : IProp GF) :
    thKids i K ⊢ oblFuels K 1 -∗ witLayers R -∗
      (thKids i K -∗ witCreds R ={∅}=∗ P) -∗ mprog n tc i P := sorry

/-- A step that forks the threads `tc₁, …, tc₂ - 1` gives each of them an empty set of
children. -/
@[lantana_alias oblf.step_fork]
theorem step_fork (n₁ n₂ tc₁ tc₂ : Nat) (P : IProp GF) (hn : n₁ ≤ n₂) (htc : tc₁ ≤ tc₂) :
    (([∗list] j ∈ List.range' tc₁ (tc₂ - tc₁), thKids j ∅) ={∅}=∗ P) ⊢
      mphys n₁ n₂ tc₁ tc₂ P := sorry

end Physical

end Rules

end Lantana
