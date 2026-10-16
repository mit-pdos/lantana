/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Instances.IProp
public import Iris.BI
public import Iris.BI.Lib.Fractional
public import Iris.Std.CoPset
public import Iris.Std.Namespaces
public import Iris.Std.GenSetsInstances
public import Iris.Std.HeapInstances
public import Lantana.Prelude.Ids
public import Lantana.Algebra.Measure
public import Lantana.ProgramLogic.TemporalClass
public import Lantana.BaseLogic.Model.OPreds

/-! # The obligation-forest interface

The core of the logic (Rocq `lantana/program_logic/obl_forest.v`): the obligation predicates,
the model update `|={E₁,E₂}=>m P`, the physical-step modalities, and their rules. Every live
obligation is a child of one parent, a thread or an obligation (`Par.kids p K`: the children of
`p` are exactly `K`).

Design (D13): this is a *sealed API module*, not a class. The predicates are defined by the
model (`Lantana.BaseLogic`) and re-exported here as irreducible definitions; the rules are
theorems; nothing outside the model and this module unfolds the predicates.

The predicates are `@[irreducible]` definitions over the model of `Lantana.BaseLogic.Model`
(`Model.OPreds.parKids`, `Model.OPreds.oblAssigned`, …, `Model.mupd`, `Model.mprog`,
`Model.mphys`), each with a private unfolding lemma used only in this file (D25), and every rule
is the corresponding model lemma (`Lantana.BaseLogic.Model.OPreds`, `OPredsBase`, `MUpd`) seen
through these unfoldings; the model updates of the forest operations are lifted from the base
model update `|=[n,tc]=>m` to `|={E}=>m` by `mupd_of_base`. The predicates take the ghost state
of the model, `[ModelGS GF]`. The last section exposes what the adequacy proofs read of the
model: the children predicates of new threads and the runs of `|=[n,tc]=>m`, `mprog`, `mphys`
and `|={E₁,E₂}=>m` against the model interpretation `Model.modelInterp`.

`Obl.fuel_eq` is unprovable as stated (it lacks the hypothesis `ℓ₁ = ℓ₂` of Rocq
`oblP_fuel_proper`) and is left unproved; see its comment.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open Iris.ProgramLogic (toVal)
open scoped Lantana.Measure Ordinals.Ordinal


section Predicates

variable {GF : BundledGFunctors} [ModelGS GF]

/-! ## The predicates

Each predicate is an irreducible definition over the model, unfolded only in this file. -/

/-- `Par.kids p K`: the children of `p` are exactly `K`. For a thread, it is also running;
for an obligation, it exists exactly while the obligation is live and in the forest. -/
@[lantana_alias oblf.parP_kids, irreducible]
def Par.kids (p : Parent) (K : Oids) : IProp GF := Model.OPreds.parKids p K

/-- Thread `i` has terminated. -/
@[lantana_alias oblf.thP_done, irreducible]
def Th.done (i : ThreadId) : IProp GF := Model.OPreds.thDone i

/-- Obligation `k` is live (`q` a fraction). -/
@[lantana_alias oblf.oblP_assigned, irreducible]
def Obl.assigned (k : Oid) (q : Qp) : IProp GF := Model.OPreds.oblAssigned k q

/-- Obligation `k` is discharged. -/
@[lantana_alias oblf.oblP_discharged, irreducible]
def Obl.discharged (k : Oid) : IProp GF := Model.OPreds.oblDischarged k

/-- Fuel `μ` of obligation `k` at layer `ℓ`. -/
@[lantana_alias oblf.oblP_fuel, irreducible]
def Obl.fuel (k : Oid) (ℓ : Layer) (μ : Measure) : IProp GF := Model.OPreds.oblFuel k ℓ μ

/-- An invariant over the status of `k`: `P` while live, `R` once discharged. -/
@[lantana_alias oblf.oblP_inv, irreducible]
def Obl.inv (N : Namespace) (k : Oid) (P R : IProp GF) : IProp GF :=
  Model.OPreds.oblInv N k P R

/-- A witness of `k` at layer `ℓ`. -/
@[lantana_alias oblf.witP_layer, irreducible]
def Wit.layer (k : Oid) (ℓ : Layer) : IProp GF := Model.OPreds.witLayer k ℓ

/-- Witness credits `a` of `k`. -/
@[lantana_alias oblf.witP_cred, irreducible]
def Wit.cred (k : Oid) (a : Fuel) : IProp GF := Model.OPreds.witCred k a

/-- The witness induction of `k` at layer `ℓ` with budget `α`, carrying the fuels `F`. -/
@[lantana_alias oblf.wit_fuels, irreducible]
def Wit.fuels (k : Oid) (ℓ : Layer) (α : Fuel) (F : OidMap (Layer × Measure)) : IProp GF :=
  Model.OPreds.witFuels k ℓ α F

/-- The base model update `|=[n,tc]=>m P` at step index `n` with `tc` threads: a least fixpoint
of rounds that may change obligations and witnesses while keeping the model interpretation
(Rocq `mupd`). -/
@[lantana_alias mupd, irreducible]
def mupdBase (n tc : Nat) (P : IProp GF) : IProp GF := Model.mupd n tc P

/-- The progress round of a physical step of thread `i`, at step index `n` with `tc` threads:
`i`'s obligations progress and the witnesses get credits (Rocq `mprog`, `@={n,Θ,i}=↓ P`). -/
@[lantana_alias mprog, irreducible]
def mprog (n tc : Nat) (i : ThreadId) (P : IProp GF) : IProp GF := Model.mprog n tc i P

/-- The physical round of a step from index `n₁` with `tc₁` threads to `n₂` with `tc₂`
threads (Rocq `mphys`, `@={n1,n2,Θ1,Θ2}=> P`). -/
@[lantana_alias mphys, irreducible]
def mphys (n₁ n₂ tc₁ tc₂ : Nat) (P : IProp GF) : IProp GF := Model.mphys n₁ n₂ tc₁ tc₂ P

/-! ### Unfolding (private: D25) -/

private theorem Par.kids_unfold : Par.kids (GF := GF) = Model.OPreds.parKids := by
  funext p K; exact Par.kids.eq_1 p K
private theorem Th.done_unfold : Th.done (GF := GF) = Model.OPreds.thDone := by
  funext i; exact Th.done.eq_1 i
private theorem Obl.assigned_unfold : Obl.assigned (GF := GF) = Model.OPreds.oblAssigned := by
  funext k q; exact Obl.assigned.eq_1 k q
private theorem Obl.discharged_unfold :
    Obl.discharged (GF := GF) = Model.OPreds.oblDischarged := by
  funext k; exact Obl.discharged.eq_1 k
private theorem Obl.fuel_unfold : Obl.fuel (GF := GF) = Model.OPreds.oblFuel := by
  funext k ℓ μ; exact Obl.fuel.eq_1 k ℓ μ
private theorem Obl.inv_unfold : Obl.inv (GF := GF) = Model.OPreds.oblInv := by
  funext N k P R; exact Obl.inv.eq_1 N k P R
private theorem Wit.layer_unfold : Wit.layer (GF := GF) = Model.OPreds.witLayer := by
  funext k ℓ; exact Wit.layer.eq_1 k ℓ
private theorem Wit.cred_unfold : Wit.cred (GF := GF) = Model.OPreds.witCred := by
  funext k a; exact Wit.cred.eq_1 k a
private theorem Wit.fuels_unfold : Wit.fuels (GF := GF) = Model.OPreds.witFuels := by
  funext k ℓ α F; exact Wit.fuels.eq_1 k ℓ α F
private theorem mupdBase_unfold : mupdBase (GF := GF) = Model.mupd := by
  funext n tc P; exact mupdBase.eq_1 n tc P
private theorem mprog_unfold : mprog (GF := GF) = Model.mprog := by
  funext n tc i P; exact mprog.eq_1 n tc i P
private theorem mphys_unfold : mphys (GF := GF) = Model.mphys := by
  funext n₁ n₂ tc₁ tc₂ P; exact mphys.eq_1 n₁ n₂ tc₁ tc₂ P

end Predicates

/-! ## Notations -/

/-- `|=[n,tc]=>m P`: the base model update. Like Iris-Lean's `|={E}=> P` (and unlike `|==> P`),
the argument extends as far as possible: `|=[n,tc]=>m A ∗ B` is `|=[n,tc]=>m (A ∗ B)`. -/
scoped syntax:max "|=[" term "," term "]=>m " term : term
scoped macro_rules
  | `(|=[$n,$tc]=>m $P) => `(mupdBase $n $tc iprop($P))

section
variable {Expr : Type} {State : Type} {GF : BundledGFunctors} [ModelGS GF]

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
scoped syntax:max "|={" term "," term "}=>m " term : term
/-- `|={E}=>m P`: the model update at one mask. -/
scoped syntax:max "|={" term "}=>m " term : term
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

private theorem parLe_eq (p : Parent) (ℓ : Layer) :
    parLe (GF := GF) p ℓ = Model.OPreds.parLe p ℓ := by
  cases p with
  | thread j => rfl
  | obl q => unfold parLe; rw [Wit.layer_unfold]

private theorem parBelow_eq (p : Parent) (ℓ : Layer) :
    parBelow (GF := GF) p ℓ = Model.OPreds.parBelow p ℓ := by
  cases p with
  | thread j => rfl
  | obl q => unfold parBelow; rw [Wit.layer_unfold]

/-! ## Structural properties -/

instance Par.kids_timeless (p : Parent) (K : Oids) : Timeless (Par.kids (GF := GF) p K) := by
  rw [Par.kids_unfold]; infer_instance
instance Th.done_timeless (i : ThreadId) : Timeless (Th.done (GF := GF) i) := by
  rw [Th.done_unfold]; infer_instance
instance Th.done_persistent (i : ThreadId) : Persistent (Th.done (GF := GF) i) := by
  rw [Th.done_unfold]; infer_instance
instance Obl.assigned_timeless (k : Oid) (q : Qp) : Timeless (Obl.assigned (GF := GF) k q) := by
  rw [Obl.assigned_unfold]; infer_instance
instance Obl.assigned_fractional (k : Oid) : Fractional (Obl.assigned (GF := GF) k) := by
  rw [Obl.assigned_unfold]; exact Model.OPreds.oblAssigned_fractional k
instance Obl.discharged_timeless (k : Oid) : Timeless (Obl.discharged (GF := GF) k) := by
  rw [Obl.discharged_unfold]; infer_instance
instance Obl.discharged_persistent (k : Oid) : Persistent (Obl.discharged (GF := GF) k) := by
  rw [Obl.discharged_unfold]; infer_instance
instance Obl.fuel_timeless (k : Oid) (ℓ : Layer) (μ : Measure) :
    Timeless (Obl.fuel (GF := GF) k ℓ μ) := by
  rw [Obl.fuel_unfold]; infer_instance
instance Obl.inv_persistent (N : Namespace) (k : Oid) (P R : IProp GF) :
    Persistent (Obl.inv N k P R) := by
  rw [Obl.inv_unfold]; infer_instance
instance Obl.inv_contractive_left (N : Namespace) (k : Oid) (R : IProp GF) :
    OFE.Contractive (fun P => Obl.inv N k P R) := by
  rw [Obl.inv_unfold]; exact Model.OPreds.oblInv_contractive_left N k R
instance Obl.inv_contractive_right (N : Namespace) (k : Oid) (P : IProp GF) :
    OFE.Contractive (fun R => Obl.inv N k P R) := by
  rw [Obl.inv_unfold]; exact Model.OPreds.oblInv_contractive_right N k P
instance Wit.layer_timeless (k : Oid) (ℓ : Layer) : Timeless (Wit.layer (GF := GF) k ℓ) := by
  rw [Wit.layer_unfold]; infer_instance
instance Wit.layer_persistent (k : Oid) (ℓ : Layer) : Persistent (Wit.layer (GF := GF) k ℓ) := by
  rw [Wit.layer_unfold]; infer_instance
instance Wit.cred_timeless (k : Oid) (a : Fuel) : Timeless (Wit.cred (GF := GF) k a) := by
  rw [Wit.cred_unfold]; infer_instance
instance Wit.fuels_timeless (k : Oid) (ℓ : Layer) (α : Fuel) (F : OidMap (Layer × Measure)) :
    Timeless (Wit.fuels (GF := GF) k ℓ α F) := by
  rw [Wit.fuels_unfold]; infer_instance
instance Wit.fuels_empty_persistent (k : Oid) (ℓ : Layer) (α : Fuel) :
    Persistent (Wit.fuels (GF := GF) k ℓ α ∅) := by
  rw [Wit.fuels_unfold]; infer_instance

/-! ## The base model update and the rounds of a step

Their structural rules (Rocq `base_logic/mupd.v` and `model_physical_updates.v`), used by the
program logic to prove the rules of `lWP`. -/

@[lantana_alias mupd_ne]
instance mupdBase_ne (n tc : Nat) : OFE.NonExpansive (mupdBase (GF := GF) n tc) := by
  rw [mupdBase_unfold]; exact Model.mupd_ne n tc

@[lantana_alias mupd_intro]
theorem mupdBase_intro (n tc : Nat) (P : IProp GF) : P ⊢ |=[n,tc]=>m P := by
  rw [mupdBase_unfold]; exact Model.mupd_intro n tc P

/-- A fancy update at the empty mask can be absorbed by the base model update. -/
@[lantana_alias fupd_mupd_elim]
theorem fupd_mupdBase_elim (n tc : Nat) (P : IProp GF) :
    (|={∅}=> |=[n,tc]=>m P) ⊢ |=[n,tc]=>m P := by
  rw [mupdBase_unfold]; exact Model.fupd_mupd_elim n tc P

@[lantana_alias mupd_bind]
theorem mupdBase_bind (n tc : Nat) (P Q : IProp GF) :
    (P -∗ |=[n,tc]=>m Q) ⊢ (|=[n,tc]=>m P) -∗ |=[n,tc]=>m Q := by
  rw [mupdBase_unfold]; exact Model.mupd_bind n tc P Q

@[lantana_alias mprog_ne]
instance mprog_ne (n tc : Nat) (i : ThreadId) : OFE.NonExpansive (mprog (GF := GF) n tc i) := by
  rw [mprog_unfold]; exact Model.mprog_ne n tc i

@[lantana_alias mprog_wand_l]
theorem mprog_wand (n tc : Nat) (i : ThreadId) (P Q : IProp GF) :
    (P -∗ Q) ⊢ mprog n tc i P -∗ mprog n tc i Q := by
  rw [mprog_unfold]; exact Model.mprog_wand n tc i P Q

@[lantana_alias mphys_ne]
instance mphys_ne (n₁ n₂ tc₁ tc₂ : Nat) :
    OFE.NonExpansive (mphys (GF := GF) n₁ n₂ tc₁ tc₂) := by
  rw [mphys_unfold]; exact Model.mphys_ne n₁ n₂ tc₁ tc₂

@[lantana_alias mphys_wand_l]
theorem mphys_wand (n₁ n₂ tc₁ tc₂ : Nat) (P Q : IProp GF) :
    (P -∗ Q) ⊢ mphys n₁ n₂ tc₁ tc₂ P -∗ mphys n₁ n₂ tc₁ tc₂ Q := by
  rw [mphys_unfold]; exact Model.mphys_wand n₁ n₂ tc₁ tc₂ P Q

/-- A fancy update at the empty mask before the progress round is absorbed (Rocq
`fupd_mprog`). -/
theorem fupd_mprog (n tc : Nat) (i : ThreadId) (P : IProp GF) :
    (|={∅}=> mprog n tc i P) ⊢ mprog n tc i P := by
  rw [mprog_unfold]; exact Model.fupd_mprog n tc i P

/-- A fancy update at the empty mask before the physical round is absorbed (Rocq
`fupd_mphys`). -/
theorem fupd_mphys (n₁ n₂ tc₁ tc₂ : Nat) (P : IProp GF) :
    (|={∅}=> mphys n₁ n₂ tc₁ tc₂ P) ⊢ mphys n₁ n₂ tc₁ tc₂ P := by
  rw [mphys_unfold]; exact Model.fupd_mphys n₁ n₂ tc₁ tc₂ P

/-! ## The model update: the three core rules (the rest is derived) -/

section ModelUpdate
variable [TemporalGS Expr State GF] [StateInterp Expr State GF]
  [TemporalInterp Expr State GF]

instance mupd_ne (E₁ E₂ : CoPset) :
    OFE.NonExpansive (mupd (Expr := Expr) (State := State) (GF := GF) E₁ E₂) := by
  refine ⟨fun {_} P Q hPQ => ?_⟩
  unfold mupd mupdFancy
  refine forall_ne fun h => forall_ne fun n => forall_ne fun σ => forall_ne fun tp => ?_
  refine wand_ne.ne .rfl (OFE.NonExpansive.ne ?_)
  refine OFE.NonExpansive.ne (f := mupdBase n tp.length) ?_
  exact OFE.NonExpansive.ne (sep_ne.ne .rfl hPQ)

@[lantana_alias oblf.fupd_sfmupd]
theorem fupd_mupd (E₁ E₂ : CoPset) (P : IProp GF) :
    (|={E₁,E₂}=> P) ⊢ mupd (Expr := Expr) (State := State) E₁ E₂ P := by
  unfold mupd mupdFancy
  iintro HP %h %n %σ %tp HT
  imod HP with HP
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  iapply mupdBase_intro
  imod Hclose with -
  imodintro
  iframe HT HP

private theorem mupd_bind_aux (E₁ E₂ E₃ : CoPset) (P Q : IProp GF) :
    (P -∗ mupd (Expr := Expr) (State := State) E₂ E₃ Q) ⊢
      mupd (Expr := Expr) (State := State) E₁ E₂ P -∗
        mupd (Expr := Expr) (State := State) E₁ E₃ Q := by
  unfold mupd mupdFancy
  iintro HPQ HP %h %n %σ %tp HT
  imod HP $$ %h %n %σ %tp HT with HP
  imodintro
  iapply mupdBase_bind n tp.length _ _ $$ [HPQ] HP
  iintro HP
  iapply fupd_mupdBase_elim
  imod HP with ⟨HT, HP⟩
  iapply HPQ $$ HP %h %n %σ %tp HT

@[lantana_alias oblf.sfmupd_bind]
theorem mupd_bind (E₁ E₂ E₃ : CoPset) (P Q : IProp GF) :
    (P -∗ mupd (Expr := Expr) (State := State) E₂ E₃ Q) ⊢
      mupd (Expr := Expr) (State := State) E₁ E₂ P -∗ mupd (Expr := Expr) (State := State) E₁ E₃ Q :=
  mupd_bind_aux E₁ E₂ E₃ P Q

/-- A base model update at every step index and thread count is a model update at one mask:
how the forest operations of the model are lifted. -/
private theorem mupd_of_base (E : CoPset) (P : IProp GF) :
    (∀ n tc, Model.mupd n tc P) ⊢ mupd (Expr := Expr) (State := State) E E P := by
  unfold mupd mupdFancy
  rw [mupdBase_unfold]
  iintro H %h %n %σ %tp HT
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  ihave H := H $$ %n %tp.length
  iapply Model.mupd_bind n tp.length P _ $$ [Hclose HT] H
  iintro HP
  iapply Model.mupd_intro
  imod Hclose with -
  imodintro
  iframe HT HP

end ModelUpdate

/-! ## Logical rules -/

@[lantana_alias oblf.oblP_assigned_discharged_false]
theorem Obl.assigned_discharged_false (k : Oid) (q : Qp) :
    Obl.assigned (GF := GF) k q ⊢ Obl.discharged k -∗ False := by
  rw [Obl.assigned_unfold, Obl.discharged_unfold]
  exact Model.OPreds.oblAssigned_discharged_false k q

@[lantana_alias oblf.oblP_kids_discharged_false]
theorem Obl.kids_discharged_false (k : Oid) (K : Oids) :
    oblKids k K ⊢ Obl.discharged (GF := GF) k -∗ False := by
  rw [Par.kids_unfold, Obl.discharged_unfold]
  exact Model.OPreds.oblKids_discharged_false k K

@[lantana_alias oblf.parP_kids_discharged]
theorem Par.kids_discharged (k : Oid) (p : Parent) (K : Oids) :
    Par.kids (GF := GF) p K ⊢ Obl.discharged k -∗ ⌜k ∉ K⌝ := by
  rw [Par.kids_unfold, Obl.discharged_unfold]
  exact Model.OPreds.parKids_discharged k p K

/-- Fuels at one layer with equal interpretations are equal (Rocq `oblP_fuel_proper`, whose
hypothesis `ℓ1 == ℓ2` is the shared layer here). Across layers the statement would be unsound:
`rep ℓ 1 = rep ℓ' 1`, and `Obl.fuel_extend` with `Obl.fuel_add` would duplicate fuel. -/
@[lantana_alias oblf.oblP_fuel_proper]
theorem Obl.fuel_eq (k : Oid) {ℓ : Layer} {μ₁ μ₂ : Measure}
    (h : Measure.rep ℓ μ₁ = Measure.rep ℓ μ₂) :
    Obl.fuel (GF := GF) k ℓ μ₁ ⊣⊢ Obl.fuel k ℓ μ₂ := by
  rw [Obl.fuel_unfold]; exact Model.OPreds.oblFuel_eq_of_rep k ℓ h

section BUpd

@[lantana_alias oblf.oblP_fuel_mon_gen]
theorem Obl.fuel_mono_gen (k : Oid) {ℓ₁ ℓ₂ : Layer} {μ₁ μ₂ : Measure} (hℓ : ℓ₁ ≤ ℓ₂)
    (h : Measure.rep ℓ₁ μ₁ ≤ Measure.rep ℓ₂ μ₂) :
    Obl.fuel (GF := GF) k ℓ₂ μ₂ ⊢ |==> Obl.fuel k ℓ₁ μ₁ := by
  rw [Obl.fuel_unfold]; exact Model.OPreds.oblFuel_mono_gen k hℓ h

@[lantana_alias oblf.oblP_fuel_extend]
theorem Obl.fuel_extend (k : Oid) {ℓ₁ ℓ₂ : Layer} (h : ℓ₁ < ℓ₂) (μ : Measure) :
    Obl.fuel (GF := GF) k ℓ₂ 1 ⊢ |==> Obl.fuel k ℓ₁ μ := by
  rw [Obl.fuel_unfold]; exact Model.OPreds.oblFuel_extend k h μ

@[lantana_alias oblf.witP_cred_mon]
theorem Wit.cred_mono (k : Oid) {a₀ a₁ : Fuel} (h : a₀ ≤ a₁) :
    Wit.cred (GF := GF) k a₁ ⊢ |==> Wit.cred k a₀ := by
  rw [Wit.cred_unfold]; exact Model.OPreds.witCred_mono k h

end BUpd

@[lantana_alias oblf.oblP_fuel_add]
theorem Obl.fuel_add (k : Oid) (ℓ : Layer) (μ₁ μ₂ : Measure) :
    Obl.fuel (GF := GF) k ℓ (μ₁ + μ₂) ⊣⊢ Obl.fuel k ℓ μ₁ ∗ Obl.fuel k ℓ μ₂ := by
  rw [Obl.fuel_unfold]; exact Model.OPreds.oblFuel_add k ℓ μ₁ μ₂

@[lantana_alias oblf.witP_cred_split]
theorem Wit.cred_split (k : Oid) (a₀ a₁ : Fuel) :
    Wit.cred (GF := GF) k (a₀ +ₕ a₁) ⊣⊢ Wit.cred k a₀ ∗ Wit.cred k a₁ := by
  rw [Wit.cred_unfold]; exact Model.OPreds.witCred_split k a₀ a₁

#lantana_ignore oblf.witP_cred_proper "ordinal equality is Leibniz: rewrite"

/-! ## Invariants over obligations -/

section FUpd

@[lantana_alias oblf.oblP_inv_alloc_assigned]
theorem Obl.inv_alloc_assigned (E : CoPset) (N : Namespace) (k : Oid) (P R : IProp GF) :
    ⊢@{IProp GF} Obl.assigned k (Qp.half 1) -∗ ▷ P ={E}=∗ Obl.inv N k P R := by
  rw [Obl.assigned_unfold, Obl.inv_unfold]
  exact Model.OPreds.oblInv_alloc_assigned E N k P R

@[lantana_alias oblf.oblP_inv_alloc_discharged]
theorem Obl.inv_alloc_discharged (E : CoPset) (N : Namespace) (k : Oid) (P R : IProp GF) :
    ⊢@{IProp GF} Obl.discharged k -∗ ▷ R ={E}=∗ Obl.inv N k P R := by
  rw [Obl.discharged_unfold, Obl.inv_unfold]
  exact Model.OPreds.oblInv_alloc_discharged E N k P R

/-- The content of an obligation invariant: `P` with half of the assignment while live, `R`
with the discharge once discharged. -/
@[lantana_alias oblP_variant]
def Obl.variant (k : Oid) (P R : IProp GF) : IProp GF :=
  iprop((Obl.assigned k (Qp.half 1) ∗ P) ∨ (Obl.discharged k ∗ R))

@[lantana_alias oblf.oblP_inv_acc]
theorem Obl.inv_acc (E : CoPset) (N : Namespace) (k : Oid) (P R : IProp GF) (hN : ↑N ⊆ E) :
    Obl.inv N k P R ⊢ |={E, E \ ↑N}=> ▷ Obl.variant k P R ∗
      (▷ Obl.variant k P R ={E \ ↑N, E}=∗ True) := by
  unfold Obl.variant
  rw [Obl.assigned_unfold, Obl.discharged_unfold, Obl.inv_unfold]
  exact Model.OPreds.oblInv_acc E N k P R hN

end FUpd

/-! ## Witness induction -/

section BUpd

@[lantana_alias oblf.wit_fuels_init]
theorem Wit.fuels_init (k : Oid) (ℓ : Layer) :
    Wit.layer (GF := GF) k ℓ ⊢ ∃ α : Fuel, Wit.fuels k ℓ α ∅ := by
  rw [Wit.layer_unfold, Wit.fuels_unfold]; exact Model.OPreds.witFuels_init k ℓ

@[lantana_alias oblf.wit_fuels_witP_layer]
theorem Wit.fuels_layer (k : Oid) (ℓ : Layer) (α : Fuel) (F : OidMap (Layer × Measure)) :
    Wit.fuels (GF := GF) k ℓ α F ⊢ |==> Wit.layer k ℓ := by
  rw [Wit.fuels_unfold, Wit.layer_unfold]
  exact (Model.OPreds.witFuels_layer k ℓ α F).trans
    (BIUpdate.intro (self := UPred.instBIUpdateUPred))

@[lantana_alias oblf.wit_fuels_add]
theorem Wit.fuels_add (k : Oid) {ℓ₁ ℓ₂ : Layer} (α : Fuel) (F : OidMap (Layer × Measure))
    (f : Oid) (μ : Measure) (h : ℓ₁ < ℓ₂) :
    Wit.fuels (GF := GF) k ℓ₁ α F ⊢ Obl.fuel f ℓ₂ (μ * ▽) ==∗
      Wit.fuels k ℓ₁ α (F.insert f (ℓ₂, μ)) := by
  rw [Wit.fuels_unfold, Obl.fuel_unfold, Model.OPreds.oidMap_insert_eq]
  exact Model.OPreds.witFuels_add k α F f μ h

@[lantana_alias oblf.wit_fuels_decr]
theorem Wit.fuels_decr (k : Oid) (ℓ : Layer) (α : Fuel) (F : OidMap (Layer × Measure)) :
    Wit.fuels (GF := GF) k ℓ α F ⊢ Wit.cred k 1 ==∗
      ∃ α₀ : Fuel, ⌜α₀ < α⌝ ∗ Wit.fuels k ℓ α₀ F ∗
        [∗map] f ↦ lm ∈ F, Obl.fuel f lm.1 lm.2 := by
  rw [Wit.fuels_unfold, Wit.cred_unfold, Obl.fuel_unfold]
  exact Model.OPreds.witFuels_decr k ℓ α F

end BUpd

/-! ## Model updates that keep every obligation live -/

section ModelUpdate
variable [TemporalGS Expr State GF] [StateInterp Expr State GF]
  [TemporalInterp Expr State GF]

@[lantana_alias oblf.thread_terminate]
theorem Th.terminate (E : CoPset) (i : ThreadId) :
    thKids i ∅ ⊢ |={E}=>m Th.done (GF := GF) i := by
  rw [Par.kids_unfold, Th.done_unfold]
  iintro H
  iapply mupd_of_base
  iintro %n %tc
  iapply Model.OPreds.thread_terminate_mupd n tc i $$ H

@[lantana_alias oblf.obl_new]
theorem Obl.new (E : CoPset) (p : Parent) (K : Oids) (ℓ : Layer) (μ : Measure) :
    parLe (GF := GF) p ℓ ⊢ Par.kids p K -∗
      |={E}=>m ∃ k : Oid, ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ oblKids k ∅ ∗
        Obl.assigned k 1 ∗ Obl.fuel k ℓ μ ∗ Wit.layer k ℓ := by
  rw [Par.kids_unfold, Obl.assigned_unfold, Obl.fuel_unfold, Wit.layer_unfold, parLe_eq]
  iintro Hb Hp
  iapply mupd_of_base
  iintro %n %tc
  iapply Model.OPreds.obl_new_mupd n tc p K ℓ μ $$ Hb Hp

@[lantana_alias oblf.obl_new_discharged]
theorem Obl.new_discharged (E : CoPset) (ℓ : Layer) :
    ⊢ |={E}=>m ∃ k : Oid, Obl.discharged (GF := GF) k ∗ Wit.layer k ℓ := by
  rw [Obl.discharged_unfold, Wit.layer_unfold]
  iapply mupd_of_base
  iintro %n %tc
  iapply Model.OPreds.obl_new_discharged_mupd n tc ℓ

@[lantana_alias oblf.obl_move]
theorem Obl.move (E : CoPset) (p₁ p₂ : Parent) (K₁ K₂ : Oids) (k : Oid) (ℓ : Layer)
    (hk : k ∈ K₁) :
    parBelow (GF := GF) p₂ ℓ ⊢ Par.kids p₁ K₁ -∗ Par.kids p₂ K₂ -∗ Obl.fuel k ℓ 1 -∗
      |={E}=>m ⌜k ∉ K₂⌝ ∗ Par.kids p₁ (K₁.erase k) ∗ Par.kids p₂ (K₂.insert k) := by
  rw [Par.kids_unfold, Obl.fuel_unfold, parBelow_eq]
  iintro Hb H₁ H₂ Hf
  iapply mupd_of_base
  iintro %n %tc
  iapply Model.OPreds.obl_move_mupd n tc p₁ p₂ K₁ K₂ k ℓ hk $$ Hb H₁ H₂ Hf

@[lantana_alias oblf.obl_move_up]
theorem Obl.move_up (E : CoPset) (p : Parent) (K : Oids) (k : Oid) (Kk : Oids) (x : Oid)
    (hk : k ∈ K) (hx : x ∈ Kk) :
    Par.kids (GF := GF) p K ⊢ oblKids k Kk -∗
      |={E}=>m ⌜x ∉ K⌝ ∗ Par.kids p (K.insert x) ∗ oblKids k (Kk.erase x) := by
  rw [Par.kids_unfold]
  iintro Hp Hk
  iapply mupd_of_base
  iintro %n %tc
  iapply Model.OPreds.obl_move_up_mupd n tc p K k Kk x hk hx $$ Hp Hk

@[lantana_alias oblf.obl_check_witness]
theorem Obl.check_witness (E : CoPset) (r : Oid) (ℓ : Layer) :
    Wit.layer (GF := GF) r ℓ ⊢ |={E}=>m (Wit.cred r 0 ∨ Obl.discharged r) := by
  rw [Wit.layer_unfold, Wit.cred_unfold, Obl.discharged_unfold]
  iintro H
  iapply mupd_of_base
  iintro %n %tc
  iapply Model.OPreds.obl_check_witness_mupd n tc r ℓ $$ H

/-! ## Discharge -/

@[lantana_alias oblf.obl_discharge_leaf]
theorem Obl.discharge_leaf (E : CoPset) (p : Parent) (K : Oids) (k : Oid) (hk : k ∈ K) :
    Par.kids (GF := GF) p K ⊢ oblKids k ∅ -∗ Obl.assigned k 1 -∗
      |={E}=>m Par.kids p (K.erase k) ∗ Obl.discharged k := by
  rw [Par.kids_unfold, Obl.assigned_unfold, Obl.discharged_unfold]
  iintro Hp Hk Ha
  iapply mupd_of_base
  iintro %n %tc
  iapply Model.OPreds.obl_discharge_mupd n tc p K k hk $$ Hp Hk Ha

end ModelUpdate

/-! ## Physical steps -/

section Physical

/-- A step of thread `i` burns one unit of fuel of each child of `i` and gives one credit for
each live witness in `R`. -/
@[lantana_alias oblf.step_progress]
theorem step_progress (n tc : Nat) (i : ThreadId) (K R : Oids) (P : IProp GF) :
    thKids i K ⊢ oblFuels K 1 -∗ witLayers R -∗
      (thKids i K -∗ witCreds R ={∅}=∗ P) -∗ mprog n tc i P := by
  unfold oblFuels witLayers witCreds
  rw [Par.kids_unfold, Obl.fuel_unfold, Wit.layer_unfold, Wit.cred_unfold,
    Obl.discharged_unfold, mprog_unfold]
  exact Model.OPreds.mprog_step_kids n tc i K R P

/-- A step that forks the threads `tc₁, …, tc₂ - 1` gives each of them an empty set of
children. -/
@[lantana_alias oblf.step_fork]
theorem step_fork (n₁ n₂ tc₁ tc₂ : Nat) (P : IProp GF) (hn : n₁ ≤ n₂) (htc : tc₁ ≤ tc₂) :
    (([∗list] j ∈ List.range' tc₁ (tc₂ - tc₁), thKids j ∅) ={∅}=∗ P) ⊢
      mphys n₁ n₂ tc₁ tc₂ P := by
  rw [Par.kids_unfold, mphys_unfold]
  exact Model.OPreds.mphys_step_kids n₁ n₂ tc₁ tc₂ P hn htc

end Physical

/-! ## Running the model (for adequacy)

What the adequacy proofs read of the model (Rocq `obl_forest_instance.v`, "Facts about the
model at the instance"): the children predicates of new threads, and the base model update and
the two rounds of a step against the model interpretation `Model.modelInterp`. -/

section Adequacy

/-- The children predicates of new threads `tc, …, tc + m - 1` (Rocq
`thP_kids_alloc_threads`). -/
@[lantana_alias thP_kids_alloc_threads]
theorem thKids_alloc_threads (Ω : Model.Obls) (tc m : Nat) :
    Model.oforest Ω tc ⊢@{IProp GF} |==> (Model.oforest Ω (tc + m) ∗
      [∗list] j ∈ List.range' tc m, thKids j ∅) := by
  rw [Par.kids_unfold]
  exact Model.OPreds.thKids_alloc_threads Ω tc m

/-- Running a base model update against the model: the rounds compose into `Obls.le` and keep
a lower bound `γ` of the witnesses (`Model.modelInterp_mupd_steps`). -/
theorem mupdBase_modelInterp_steps (n tc : Nat) (γ : ThreadId → Fuel → Fuel)
    (hγ : Model.owitInvLbMonoFair γ) (P : IProp GF) :
    (|=[n,tc]=>m P) ⊢ ∀ (h : List Model.MEvent) (i : Nat) (Ω : Model.Obls)
      (W : Model.Witnesses), ⌜Model.owitInvLb γ Ω W⌝ → Model.modelInterp h i Ω W n tc ={∅}=∗
        P ∗ ∃ h' i' Ω' W', ⌜Model.Obls.le Ω Ω' ∧ Model.owitInvLb γ Ω' W'⌝ ∗
          Model.modelInterp (h ++ h') (i + i') Ω' W' n tc := by
  rw [mupdBase_unfold]
  exact Model.modelInterp_mupd_steps n tc γ hγ P

/-- A base model update that only reads the model, which it returns unchanged (Rocq
`mupd_read`, `temporal_formula.v`): how the temporal formulas record their contents. -/
@[lantana_alias mupd_read]
theorem mupdBase_read (n tc : Nat) (P : IProp GF) :
    (∀ (h : List Model.MEvent) (i : Nat) (Ω : Model.Obls) (W : Model.Witnesses),
      Model.modelInterp h i Ω W n tc -∗ Model.modelInterp h i Ω W n tc ∗ P) ⊢ |=[n,tc]=>m P := by
  rw [mupdBase_unfold]
  exact Model.mupd_read n tc P

open Iris.Std LawfulPartialMap in
/-- A live obligation is assigned in the model (Rocq `osat_lookup_assigned` read through
the interface). -/
theorem Obl.assigned_modelInterp_lookup (k : Oid) (q : Qp) (h : List Model.MEvent) (i : Nat)
    (Ω : Model.Obls) (W : Model.Witnesses) (n tc : Nat) :
    Obl.assigned (GF := GF) k q ∗ Model.modelInterp h i Ω W n tc ⊢
      ⌜∃ a t, get? Ω k = some (Model.Obl.assigned a t)⌝ := by
  rw [Obl.assigned_unfold]
  unfold Model.OPreds.oblAssigned Model.modelInterp
  iintro ⟨⟨-, Ha⟩, -, Hs, -⟩
  iapply Model.osat_lookup_assigned Ω k _
  iframe Hs Ha

open Iris.Std LawfulPartialMap in
/-- A discharged obligation is discharged in the model (Rocq `osat_lookup_discharged` read
through the interface). -/
theorem Obl.discharged_modelInterp_lookup (k : Oid) (h : List Model.MEvent) (i : Nat)
    (Ω : Model.Obls) (W : Model.Witnesses) (n tc : Nat) :
    Obl.discharged (GF := GF) k ∗ Model.modelInterp h i Ω W n tc ⊢
      ⌜get? Ω k = some Model.Obl.discharged⌝ := by
  rw [Obl.discharged_unfold]
  unfold Model.OPreds.oblDischarged Model.modelInterp
  iintro ⟨⟨-, Hd⟩, -, Hs, -⟩
  iapply Model.osat_lookup_discharged Ω k
  iframe Hs Hd

/-- The progress round of thread `i` against the model (the definition of Rocq `mprog`). -/
theorem mprog_modelInterp (n tc : Nat) (i : ThreadId) (P : IProp GF) :
    mprog n tc i P ⊢ ∀ (h : List Model.MEvent) (a : Nat) (Ω₁ : Model.Obls)
      (W₁ : Model.Witnesses), Model.modelInterp h a Ω₁ W₁ n tc ={∅}=∗
        ∃ Ω₂, ⌜Model.Obls.condProgress (Model.Obl.condOwner i) Ω₁ Ω₂⌝ ∗
        ∀ W₂, ⌜Model.Witnesses.condProgress Model.Witness.condAssigned W₁ W₂ ∧
          Model.owitInvFair Ω₂ W₂⌝ ={∅}=∗
          Model.modelInterp (h ++ [(n, Ω₂)]) (a + 1) Ω₂ W₂ n tc ∗ P := by
  rw [mprog_unfold]
  exact .rfl

/-- The physical round against the model (the definition of Rocq `mphys`). -/
theorem mphys_modelInterp (n₁ n₂ tc₁ tc₂ : Nat) (P : IProp GF) :
    mphys n₁ n₂ tc₁ tc₂ P ⊢ ∀ (h : List Model.MEvent) (a : Nat) (Ω : Model.Obls)
      (W : Model.Witnesses), Model.modelInterp h a Ω W n₁ tc₁ ={∅}=∗
        Model.modelInterp (h ++ [(n₂, Ω)]) (a + 1) Ω W n₂ tc₂ ∗ P := by
  rw [mphys_unfold]
  exact .rfl

variable [TemporalGS Expr State GF] [StateInterp Expr State GF]
  [TemporalInterp Expr State GF]

/-- Running a model update against the model (Rocq `all_interp_sfmupd_steps`). -/
@[lantana_alias all_interp_sfmupd_steps]
theorem mupd_modelInterp_steps (γ : ThreadId → Fuel → Fuel) (hγ : Model.owitInvLbMonoFair γ)
    (E₁ E₂ : CoPset) (h : List (HistEntry Expr State)) (n : Nat) (σ : State)
    (tp : ThreadPool Expr) (g : List Model.MEvent) (v : Nat) (Ω : Model.Obls)
    (W : Model.Witnesses) (P : IProp GF) (hLb : Model.owitInvLb γ Ω W) :
    (|={E₁,E₂}=>m P) ⊢ historyTInterp h n σ tp -∗ Model.modelInterp g v Ω W n tp.length ={E₁,E₂}=∗
      P ∗ historyTInterp h n σ tp ∗ ∃ g' v' Ω' W',
        ⌜Model.Obls.le Ω Ω' ∧ Model.owitInvLb γ Ω' W'⌝ ∗
        Model.modelInterp (g ++ g') (v + v') Ω' W' n tp.length := by
  unfold mupd mupdFancy
  rw [mupdBase_unfold]
  iintro HP HT HM
  imod HP $$ %h %n %σ %tp HT with HP
  imod Model.modelInterp_mupd_steps n tp.length γ hγ _ $$ HP %g %v %Ω %W %hLb HM
    with ⟨HP, %g', %v', %Ω', %W', %hle, HM⟩
  imod HP with ⟨HT, HP⟩
  imodintro
  iframe HP HT
  iexists g', v', Ω', W'
  iframe HM
  ipureintro
  exact hle

end Adequacy


end Rules

/-! ## Adequacy bridges (run step)

What the single-step simulation of adequacy (`Lantana.Trace.Adequacy.RunStep`) reads of the
model through the sealed predicates: a terminated thread owns no obligation. -/

section AdequacyRunStep

open Iris.Std LawfulPartialMap

variable {GF : BundledGFunctors} [ModelGS GF]

/-- A terminated thread owns no obligation of the model (Rocq `othread_assigned_done_false`,
through the model interpretation). -/
theorem Th.done_modelInterp_not_owner (i : ThreadId) (h : List Model.MEvent) (a : Nat)
    (Ω : Model.Obls) (W : Model.Witnesses) (n tc : Nat) :
    Th.done i ∗ Model.modelInterp h a Ω W n tc ⊢@{IProp GF}
      ⌜∀ k fu, get? Ω k ≠ some (.assigned fu i)⌝ := by
  rw [Th.done_unfold]
  unfold Model.modelInterp Model.OPreds.thDone
  iintro ⟨Hd, -, -, Hf, -, -⟩
  icases Model.oforest_done_owned Ω tc i $$ [$Hf $Hd] with %h
  ipureintro
  intro k fu hk
  exact h k (Model.Obls.ownerOf_eq hk)

end AdequacyRunStep

end Lantana
