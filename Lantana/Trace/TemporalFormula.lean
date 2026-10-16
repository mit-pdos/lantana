/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.GuaranteeRules

/-! # Temporal formulas: `alwaysI`, `untilI`, `finallyI`, `untilIDone`

Rocq `lantana/trace/temporal_formula.v`: the interpretation of the temporal layer becomes the
registry state (`regTemporalInterp`), whose entries hold the invariants of the registered
formulas and the guarantees of their contents (`regEntryInterp`). Temporal formulas are
`IProp`s:

* `alwaysI N P` is an invariant `inv N P` registered with the guarantee of its content and the
  record of the content at its registration (`alwaysIGuar N P G`, read as `G`; `alwaysI` reads
  it as `TrSpec.canon P`);
* `untilI N k q P Q` ("`P` until `Q`") is a registered obligation invariant over the obligation
  `k`, which holds `P` while `k` is live and the record of `Q`'s reading at the discharge once
  it is discharged (`untilDischarged`), with the fraction `q` of the user's half of `k`;
* `finallyI N k q Q` is `untilI N k q True Q`;
* `untilIDone k Q` is a fulfilled until: `Q`, the discharge of `k` and the guarantee of `Q`.

Allocation reads the model under a model update (`mupd_read`). The certification of the
registry along a run and the loops that read the formulas off a run are in
`Lantana.Trace.TemporalFormulaRun`; the rules and the guarantees (`guar_alwaysI`,
`guar_untilI`, `guar_untilIDone`) in `Lantana.Trace.TemporalFormulaRules`.

The structures carry their trace readings `G` explicitly (`alwaysIGuar`, `untilIGuar`,
`untilIDoneGuar`), and are contractive in their contents for fixed readings (Rocq
`alwaysI_guar_contractive`, `untilI_guar_contractive_l/r`): the canonical forms are not, as
`TrSpec.canon P` is not a non-expansive function of `P`.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open Lantana.Model
open scoped Lantana.TrSpec Lantana.TrProp

variable {Expr State Val : Type} {GF : BundledGFunctors} [Language Expr State Val]
variable [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF]

/-! ## The registry and the registered structures -/

/-- Once discharged, the obligation invariant of an until keeps the record of its right
reading at the discharge event (Rocq notation `until_discharged`). -/
@[lantana_alias until_discharged]
def untilDischarged (k : Oid) (G₂ : TrSpec Expr State GF) : IProp GF :=
  iprop(∃ (n' i' : Nat) (Ω' : Obls), eventObl i' (n', Ω') k .discharged ∗ record G₂ n')

instance untilDischarged_persistent (k : Oid) (G₂ : TrSpec Expr State GF) :
    Persistent (untilDischarged k G₂) := by
  unfold untilDischarged; infer_instance

/-- The interpretation of a registry entry: its saved readings, its invariant and the
later-guarded guarantee of its content, which the check opens at every position. -/
@[lantana_alias reg_entry_interp]
def regEntryInterp : RegEntry → IProp GF
  | .mark => iprop(True)
  | .always N γ => iprop(∃ (P : IProp GF) (G : TrSpec Expr State GF),
      savedTrI γ G.internal ∗ inv N P ∗ ▷ (P ⊨ₜ G))
  | .until N k γP γQ => iprop(∃ (P : IProp GF) (G₁ G₂ : TrSpec Expr State GF),
      savedTrI γP G₁.internal ∗ savedTrI γQ G₂.internal ∗
      Obl.inv N k P (untilDischarged k G₂) ∗ ▷ (P ⊨ₜ G₁))

/-- The registry state: the interpretation of the temporal layer (Rocq `reg_state`). -/
@[lantana_alias reg_state]
def regState : IProp GF := regStateWith (regEntryInterp (Expr := Expr) (State := State))

/-- The temporal layer is interpreted by the registry state (Rocq `reg_temporal_interp`). -/
@[lantana_alias reg_temporal_interp]
instance regTemporalInterp : TemporalInterp Expr State GF := ⟨regState⟩

@[lantana_alias temporal_interp_reg]
theorem temporalInterp_reg : temporalInterp Expr State (GF := GF) = regState := rfl

@[lantana_alias reg_entry_interp_persistent]
instance regEntryInterp_persistent (e : RegEntry) :
    Persistent (regEntryInterp (Expr := Expr) (State := State) (GF := GF) e) := by
  rcases e with _ | ⟨N, γ⟩ | ⟨N, k, γP, γQ⟩ <;> unfold regEntryInterp <;> infer_instance

instance regEntries_persistent (l : List (Nat × RegEntry)) :
    Persistent (regEntries (regEntryInterp (Expr := Expr) (State := State) (GF := GF)) l) := by
  unfold regEntries; infer_instance

/-! ### `alwaysI` -/

/-- An invariant `P` made trace-visible through the reading `G` of its content: registered
at position `r` (index `j`) with `G` and a later-guarded `P ⊨ₜ G`, and the record of `G` at
`r` (Rocq `alwaysI_guar`; sealed). -/
@[lantana_alias alwaysI_guar, irreducible]
def alwaysIGuar (N : Namespace) (P : IProp GF) (G : TrSpec Expr State GF) : IProp GF :=
  iprop(∃ (j r : Nat) (γ : GName) (st : HistEntry Expr State),
    regIdx j r (.always N γ) ∗ histEvent r st ∗ savedTrI γ G.internal ∗ inv N P ∗
    ▷ (P ⊨ₜ G) ∗ ▷ record G r)

theorem alwaysIGuar_unfold (N : Namespace) (P : IProp GF) (G : TrSpec Expr State GF) :
    alwaysIGuar N P G = iprop(∃ (j r : Nat) (γ : GName) (st : HistEntry Expr State),
      regIdx j r (.always N γ) ∗ histEvent r st ∗ savedTrI γ G.internal ∗ inv N P ∗
      ▷ (P ⊨ₜ G) ∗ ▷ record G r) := by
  unfold alwaysIGuar; rfl

/-- The invariant `P` read as the canonical specification of `V` (Rocq `alwaysI_as`). -/
@[lantana_alias alwaysI_as, irreducible]
def alwaysIAs (N : Namespace) (P V : IProp GF) : IProp GF :=
  alwaysIGuar (Expr := Expr) (State := State) N P (TrSpec.canon V)

/-- `alwaysI N P`: a registered invariant holding `P`, read as `TrSpec.canon P`. -/
@[lantana_alias alwaysI, irreducible]
def alwaysI (N : Namespace) (P : IProp GF) : IProp GF :=
  alwaysIAs (Expr := Expr) (State := State) N P P

theorem alwaysIAs_eq (N : Namespace) (P V : IProp GF) :
    alwaysIAs N P V = alwaysIGuar (Expr := Expr) (State := State) N P (TrSpec.canon V) := by
  unfold alwaysIAs; rfl

theorem alwaysI_eq (N : Namespace) (P : IProp GF) :
    alwaysI N P = alwaysIGuar (Expr := Expr) (State := State) N P (TrSpec.canon P) := by
  unfold alwaysI; rw [alwaysIAs_eq]

/-! ### `untilI` -/

/-- The persistent part of `P` until `Q`, read as `G₁` until `G₂`: its registered obligation
invariant, later-guarded `P ⊨ₜ G₁` and `Q ⊨ₜ G₂`, the state of `k` at the registration, and
the record of `G₁` at the registration (Rocq `untilI_guar_pers`). -/
@[lantana_alias untilI_guar_pers]
def untilIGuarPers (N : Namespace) (k : Oid) (P Q : IProp GF)
    (G₁ G₂ : TrSpec Expr State GF) : IProp GF :=
  iprop(∃ (j r : Nat) (γP γQ : GName) (st : HistEntry Expr State) (v : Nat) (Ω : Obls)
      (fu : Fuel) (o : ThreadId),
    regIdx j r (.until N k γP γQ) ∗ histEvent r st ∗
    savedTrI γP G₁.internal ∗ savedTrI γQ G₂.internal ∗
    Obl.inv N k P (untilDischarged k G₂) ∗ ▷ (P ⊨ₜ G₁) ∗ ▷ (Q ⊨ₜ G₂) ∗
    eventObl v (r, Ω) k (.assigned fu o) ∗ ▷ record G₁ r)

/-- With the canonical readings (Rocq `untilI_pers`). -/
@[lantana_alias untilI_pers]
def untilIPers (N : Namespace) (k : Oid) (P Q : IProp GF) : IProp GF :=
  untilIGuarPers (Expr := Expr) (State := State) N k P Q (TrSpec.canon P) (TrSpec.canon Q)

/-- `P` until `Q` on `k`, read as `G₁` until `G₂`: the fraction `q` of the user's half of `k`
and the persistent part (Rocq `untilI_guar`; sealed). -/
@[lantana_alias untilI_guar, irreducible]
def untilIGuar (N : Namespace) (k : Oid) (q : Qp) (P Q : IProp GF)
    (G₁ G₂ : TrSpec Expr State GF) : IProp GF :=
  iprop(Obl.assigned k q.half ∗ untilIGuarPers N k P Q G₁ G₂)

theorem untilIGuar_unfold (N : Namespace) (k : Oid) (q : Qp) (P Q : IProp GF)
    (G₁ G₂ : TrSpec Expr State GF) :
    untilIGuar N k q P Q G₁ G₂ = iprop(Obl.assigned k q.half ∗ untilIGuarPers N k P Q G₁ G₂) := by
  unfold untilIGuar; rfl

/-- `untilI N k q P Q`: `P` until `Q` on the obligation `k` (fraction `q`), read with the
canonical specifications of its formulas (Rocq `untilI`; sealed). -/
@[lantana_alias untilI, irreducible]
def untilI (N : Namespace) (k : Oid) (q : Qp) (P Q : IProp GF) : IProp GF :=
  untilIGuar (Expr := Expr) (State := State) N k q P Q (TrSpec.canon P) (TrSpec.canon Q)

@[lantana_alias untilI_guar_canonical]
theorem untilI_eq (N : Namespace) (k : Oid) (q : Qp) (P Q : IProp GF) :
    untilI N k q P Q =
      untilIGuar (Expr := Expr) (State := State) N k q P Q (TrSpec.canon P) (TrSpec.canon Q) := by
  unfold untilI; rfl

@[lantana_alias untilI_unfold]
theorem untilI_unfold (N : Namespace) (k : Oid) (q : Qp) (P Q : IProp GF) :
    untilI N k q P Q =
      iprop(Obl.assigned k q.half ∗ untilIPers (Expr := Expr) (State := State) N k P Q) := by
  rw [untilI_eq, untilIGuar_unfold]; rfl

/-- `finallyI N k q Q`: eventually `Q`, on the obligation `k`. -/
@[lantana_alias finallyI]
def finallyI (N : Namespace) (k : Oid) (q : Qp) (Q : IProp GF) : IProp GF :=
  untilI N k q iprop(True) Q

/-! ### `untilIDone` -/

/-- A done until, read with `G₂` on the right: `Q`, the discharged obligation `k` and a
later-guarded `Q ⊨ₜ G₂` (Rocq `untilI_done_guar`; sealed). Nothing is registered. -/
@[lantana_alias untilI_done_guar, irreducible]
def untilIDoneGuar (k : Oid) (Q : IProp GF) (G₂ : TrSpec Expr State GF) : IProp GF :=
  iprop(Q ∗ Obl.discharged k ∗ ▷ (Q ⊨ₜ G₂))

theorem untilIDoneGuar_unfold (k : Oid) (Q : IProp GF) (G₂ : TrSpec Expr State GF) :
    untilIDoneGuar k Q G₂ = iprop(Q ∗ Obl.discharged k ∗ ▷ (Q ⊨ₜ G₂)) := by
  unfold untilIDoneGuar; rfl

/-- A fulfilled until: `Q` holds and `k` is discharged (Rocq `untilI_done`). -/
@[lantana_alias untilI_done, irreducible]
def untilIDone (k : Oid) (Q : IProp GF) : IProp GF :=
  untilIDoneGuar (Expr := Expr) (State := State) k Q (TrSpec.canon Q)

theorem untilIDone_eq (k : Oid) (Q : IProp GF) :
    untilIDone k Q = untilIDoneGuar (Expr := Expr) (State := State) k Q (TrSpec.canon Q) := by
  unfold untilIDone; rfl

/-! ## Reading the model under a model update

Allocation reads the history and the model, to record the content at the current position,
and updates the registry state. -/

section Read
variable {E : CoPset} {P : IProp GF}

/-- A model update with fancy updates before and after reading the model, which it returns
unchanged (Rocq `sfmupd_read_fupd`). -/
@[lantana_alias sfmupd_read_fupd]
theorem mupd_read_fupd :
    (∀ (h : List (HistEntry Expr State)) (n : Nat) (σ : State) (tp : ThreadPool Expr),
      historyInterp h n σ tp -∗ regState -∗ |={E,∅}=> ∀ (g : List MEvent) (i : Nat) (Ω : Obls)
        (W : Witnesses), modelInterp g i Ω W n tp.length -∗ modelInterp g i Ω W n tp.length ∗
          |={∅,E}=> historyInterp h n σ tp ∗ regState ∗ P) ⊢ |={E}=>m P := by
  unfold mupd mupdFancy historyTInterp
  iintro H %h %n %σ %tp ⟨HI, TI⟩
  imod H $$ %h %n %σ %tp HI TI with H
  imodintro
  iapply mupdBase_read
  iintro %g %i %Ω %W MI
  icases H $$ %g %i %Ω %W MI with ⟨MI, H⟩
  iframe MI
  imod H with ⟨HI, TI, HP⟩
  imodintro
  iframe HP
  iframe HI
  iexact TI

/-- A model update that reads the history and the model and updates the registry
(Rocq `sfmupd_read`). -/
@[lantana_alias sfmupd_read]
theorem mupd_read :
    (∀ (h : List (HistEntry Expr State)) (n : Nat) (σ : State) (tp : ThreadPool Expr)
      (g : List MEvent) (i : Nat) (Ω : Obls) (W : Witnesses),
      historyInterp h n σ tp -∗ regState -∗ modelInterp g i Ω W n tp.length -∗
        modelInterp g i Ω W n tp.length ∗ |={E}=> historyInterp h n σ tp ∗ regState ∗ P) ⊢
      |={E}=>m P := by
  iintro H
  iapply mupd_read_fupd
  iintro %h %n %σ %tp HI TI
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose %g %i %Ω %W MI
  icases H $$ %h %n %σ %tp %g %i %Ω %W HI TI MI with ⟨MI, H⟩
  iframe MI
  imod Hclose with -
  iexact H

end Read

/-! ## Structure of `alwaysI` -/

section AlwaysStruct

@[lantana_alias alwaysI_guar_persistent]
instance alwaysIGuar_persistent (N : Namespace) (P : IProp GF) (G : TrSpec Expr State GF) :
    Persistent (alwaysIGuar N P G) := by
  rw [alwaysIGuar_unfold]; infer_instance

@[lantana_alias alwaysI_as_persistent]
instance alwaysIAs_persistent (N : Namespace) (P V : IProp GF) :
    Persistent (alwaysIAs (Expr := Expr) (State := State) N P V) := by
  rw [alwaysIAs_eq]; infer_instance

@[lantana_alias alwaysI_persistent]
instance alwaysI_persistent (N : Namespace) (P : IProp GF) :
    Persistent (alwaysI (Expr := Expr) (State := State) N P) := by
  rw [alwaysI_eq]; infer_instance

/-- Contractive in the content, for a fixed reading: structures can be defined by guarded
recursion (Rocq `alwaysI_guar_contractive`). -/
@[lantana_alias alwaysI_guar_contractive]
instance alwaysIGuar_contractive (N : Namespace) (G : TrSpec Expr State GF) :
    OFE.Contractive (fun P : IProp GF => alwaysIGuar N P G) where
  distLater_dist {_ P₁ P₂} h := by
    simp only [alwaysIGuar_unfold]
    refine exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => ?_
    refine sep_ne.ne .rfl (sep_ne.ne .rfl (sep_ne.ne .rfl (sep_ne.ne ?_ (sep_ne.ne ?_ .rfl))))
    · exact OFE.Contractive.distLater_dist (f := inv N) h
    · exact OFE.Contractive.distLater_dist (f := BIBase.later) fun m hm =>
        OFE.NonExpansive.ne (f := fun P : IProp GF => P ⊨ₜ G) (h m hm)

@[lantana_alias alwaysI_guar_inv]
theorem alwaysIGuar_inv (N : Namespace) (P : IProp GF) (G : TrSpec Expr State GF) :
    alwaysIGuar N P G ⊢ inv N P := by
  rw [alwaysIGuar_unfold]
  iintro ⟨%j, %r, %γ, %st, -, -, -, HI, -, -⟩
  iexact HI

@[lantana_alias alwaysI_guar_guar]
theorem alwaysIGuar_guar (N : Namespace) (P : IProp GF) (G : TrSpec Expr State GF) :
    alwaysIGuar N P G ⊢ ▷ (P ⊨ₜ G) := by
  rw [alwaysIGuar_unfold]
  iintro ⟨%j, %r, %γ, %st, -, -, -, -, HG, -⟩
  iexact HG

@[lantana_alias alwaysI_as_inv]
theorem alwaysIAs_inv (N : Namespace) (P V : IProp GF) :
    alwaysIAs (Expr := Expr) (State := State) N P V ⊢ inv N P := by
  rw [alwaysIAs_eq]; exact alwaysIGuar_inv N P _

@[lantana_alias alwaysI_inv]
theorem alwaysI_inv (N : Namespace) (P : IProp GF) :
    alwaysI (Expr := Expr) (State := State) N P ⊢ inv N P := by
  rw [alwaysI_eq]; exact alwaysIGuar_inv N P _

end AlwaysStruct

/-! ## Structure of `untilI` -/

section UntilStruct

@[lantana_alias untilI_guar_pers_persistent]
instance untilIGuarPers_persistent (N : Namespace) (k : Oid) (P Q : IProp GF)
    (G₁ G₂ : TrSpec Expr State GF) : Persistent (untilIGuarPers N k P Q G₁ G₂) := by
  unfold untilIGuarPers
  set_option synthInstance.maxSize 1024 in infer_instance

@[lantana_alias untilI_pers_persistent]
instance untilIPers_persistent (N : Namespace) (k : Oid) (P Q : IProp GF) :
    Persistent (untilIPers (Expr := Expr) (State := State) N k P Q) := by
  unfold untilIPers; infer_instance

@[lantana_alias untilI_done_guar_persistent]
instance untilIDoneGuar_persistent (k : Oid) (Q : IProp GF) (G₂ : TrSpec Expr State GF)
    [Persistent Q] : Persistent (untilIDoneGuar k Q G₂) := by
  rw [untilIDoneGuar_unfold]; infer_instance

@[lantana_alias untilI_done_persistent]
instance untilIDone_persistent (k : Oid) (Q : IProp GF) [Persistent Q] :
    Persistent (untilIDone (Expr := Expr) (State := State) k Q) := by
  rw [untilIDone_eq]; infer_instance

/-- Contractive in the left formula, for fixed readings (Rocq `untilI_guar_contractive_l`). -/
@[lantana_alias untilI_guar_contractive_l]
instance untilIGuar_contractive_left (N : Namespace) (k : Oid) (q : Qp) (Q : IProp GF)
    (G₁ G₂ : TrSpec Expr State GF) :
    OFE.Contractive (fun P : IProp GF => untilIGuar N k q P Q G₁ G₂) where
  distLater_dist {_ P₁ P₂} h := by
    simp only [untilIGuar_unfold]
    unfold untilIGuarPers
    refine sep_ne.ne .rfl ?_
    iterate 9 refine exists_ne fun _ => ?_
    refine sep_ne.ne .rfl (sep_ne.ne .rfl (sep_ne.ne .rfl (sep_ne.ne .rfl ?_)))
    refine sep_ne.ne ?_ (sep_ne.ne ?_ .rfl)
    · exact OFE.Contractive.distLater_dist (f := fun P => Obl.inv N k P (untilDischarged k G₂)) h
    · exact OFE.Contractive.distLater_dist (f := BIBase.later) fun m hm =>
        OFE.NonExpansive.ne (f := fun P : IProp GF => P ⊨ₜ G₁) (h m hm)

/-- Contractive in the right formula, for fixed readings (Rocq `untilI_guar_contractive_r`). -/
@[lantana_alias untilI_guar_contractive_r]
instance untilIGuar_contractive_right (N : Namespace) (k : Oid) (q : Qp) (P : IProp GF)
    (G₁ G₂ : TrSpec Expr State GF) :
    OFE.Contractive (fun Q : IProp GF => untilIGuar N k q P Q G₁ G₂) where
  distLater_dist {_ Q₁ Q₂} h := by
    simp only [untilIGuar_unfold]
    unfold untilIGuarPers
    refine sep_ne.ne .rfl ?_
    iterate 9 refine exists_ne fun _ => ?_
    refine sep_ne.ne .rfl (sep_ne.ne .rfl (sep_ne.ne .rfl (sep_ne.ne .rfl ?_)))
    refine sep_ne.ne .rfl (sep_ne.ne .rfl (sep_ne.ne ?_ .rfl))
    exact OFE.Contractive.distLater_dist (f := BIBase.later) fun m hm =>
      OFE.NonExpansive.ne (f := fun Q : IProp GF => Q ⊨ₜ G₂) (h m hm)

@[lantana_alias untilI_guar_pers_inv]
theorem untilIGuarPers_inv (N : Namespace) (k : Oid) (P Q : IProp GF)
    (G₁ G₂ : TrSpec Expr State GF) :
    untilIGuarPers N k P Q G₁ G₂ ⊢ Obl.inv N k P (untilDischarged k G₂) := by
  unfold untilIGuarPers
  iintro ⟨%j, %r, %γP, %γQ, %st, %v, %Ω, %fu, %o, -, -, -, -, HI, -⟩
  iexact HI

@[lantana_alias untilI_pers_inv]
theorem untilIPers_inv (N : Namespace) (k : Oid) (P Q : IProp GF) :
    untilIPers (Expr := Expr) (State := State) N k P Q ⊢
      Obl.inv N k P (untilDischarged k (TrSpec.canon Q)) :=
  untilIGuarPers_inv N k P Q _ _

@[lantana_alias untilI_guar_pers_guar]
theorem untilIGuarPers_guar (N : Namespace) (k : Oid) (P Q : IProp GF)
    (G₁ G₂ : TrSpec Expr State GF) :
    untilIGuarPers N k P Q G₁ G₂ ⊢ ▷ (P ⊨ₜ G₁) ∗ ▷ (Q ⊨ₜ G₂) := by
  unfold untilIGuarPers
  iintro ⟨%j, %r, %γP, %γQ, %st, %v, %Ω, %fu, %o, -, -, -, -, -, HG₁, HG₂, -⟩
  iframe HG₁ HG₂

@[lantana_alias untilI_guar_guar]
theorem untilIGuar_guar (N : Namespace) (k : Oid) (q : Qp) (P Q : IProp GF)
    (G₁ G₂ : TrSpec Expr State GF) :
    untilIGuar N k q P Q G₁ G₂ ⊢ ▷ (P ⊨ₜ G₁) ∗ ▷ (Q ⊨ₜ G₂) := by
  rw [untilIGuar_unfold]
  iintro ⟨-, U⟩
  iapply untilIGuarPers_guar $$ U

/-! ### Fractions -/

@[lantana_alias untilI_guar_fractional]
instance untilIGuar_fractional (N : Namespace) (k : Oid) (P Q : IProp GF)
    (G₁ G₂ : TrSpec Expr State GF) : Fractional (fun q => untilIGuar N k q P Q G₁ G₂) where
  fractional p q := by
    simp only [untilIGuar_unfold]
    rw [Model.Qp.half_add, ((Obl.assigned_fractional k).fractional p.half q.half).to_eq]
    constructor
    · iintro ⟨⟨A₁, A₂⟩, #U⟩
      isplitl [A₁]
      · iframe A₁
        iexact U
      · iframe A₂
        iexact U
    · iintro ⟨⟨A₁, #U⟩, ⟨A₂, -⟩⟩
      iframe A₁ A₂
      iexact U

@[lantana_alias untilI_guar_as_fractional]
instance untilIGuar_asFractional (N : Namespace) (k : Oid) (q : Qp) (P Q : IProp GF)
    (G₁ G₂ : TrSpec Expr State GF) {ioΦ ioq} :
    AsFractional (untilIGuar N k q P Q G₁ G₂) ioΦ (fun q => untilIGuar N k q P Q G₁ G₂) ioq q
    where
  as_fractional := .rfl
  as_fractional_fractional := untilIGuar_fractional N k P Q G₁ G₂

@[lantana_alias untilI_fractional]
instance untilI_fractional (N : Namespace) (k : Oid) (P Q : IProp GF) :
    Fractional (fun q => untilI (Expr := Expr) (State := State) N k q P Q) where
  fractional p q := by
    simp only [untilI_eq]
    exact (untilIGuar_fractional N k P Q _ _).fractional p q

@[lantana_alias untilI_as_fractional]
instance untilI_asFractional (N : Namespace) (k : Oid) (q : Qp) (P Q : IProp GF) {ioΦ ioq} :
    AsFractional (untilI (Expr := Expr) (State := State) N k q P Q) ioΦ
      (fun q => untilI (Expr := Expr) (State := State) N k q P Q) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := untilI_fractional N k P Q

end UntilStruct

end Lantana
