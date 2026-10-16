/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TrSpec

/-! # Least and greatest fixpoints of trace specifications

Rocq `lantana/trace/trspec_fixpoint.v`. For a body `F` monotone in both readings (`Mono F`):
`nu F`, the union of the post-fixpoints of `F`, and `mu F`, the union of the ordinal
approximants `μ_α := F (∃ β < α, μ_β)`. Always and until are such fixpoints.

The extra connectives are `trp R` (a trace predicate read as a pure fact), `later G` (`G`
after one step of the logic), `step G` (`G` after the step taken at the current position: the
step's credits and mask change), `shift G` (`G` at the next position, without modality) and
`next G` (`step` and `shift` together).

The ordinal is the measure a least fixpoint needs in a step-indexed logic: without it a
guarded body has a unique fixpoint, and `mu` would be `nu`. Guarded bodies are not continuous
(`Cont`), so `mu` has a fold `F (mu F) ⊑ₛ mu F` only for continuous bodies; on traces `mu F` is
a fixpoint for every monotone body (`mu_ext_unfold_l`, `mu_ext_unfold_r`).
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open scoped Lantana.TrProp

namespace TrSpec

variable {Expr State : Type} {GF : BundledGFunctors}

/-! ## Trace predicates, the in-logic step, and the next position -/

/-- Any trace predicate, read in the logic as a pure fact. -/
@[lantana_alias trSpec_trp]
def trp (R : TrProp Expr State) : TrSpec Expr State GF where
  internal := fun τ => iprop(⌜R τ⌝)
  external := R
  adeq _ _ h := (iPropSatLcAtFrame _ ⊤).elim h

/-- `G` after one step of the logic; at the level of traces, just `G`. -/
@[lantana_alias trSpec_later]
def later (G : TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := fun τ => iprop(|={⊤,∅}=> ▷ |={∅,⊤}=> G.internal τ)
  external := G.external
  adeq F τ h := G.adeq F τ (SatFUpd.fupd (SatPred.sat_later _ (SatFUpd.fupd h)))

/-- `G` at the next position. -/
@[lantana_alias trSpec_next]
def next (G : TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := fun τ => iprop(|={⊤,∅}=> ALC iprop(|={∅,⊤}=> G.internal τ.next))
  external := fun τ => G.external τ.next
  adeq F τ h := G.adeq F τ.next (SatFUpd.fupd (sat_ALC (SatFUpd.fupd h)))

/-- `G` after the step taken at the current position. In the logic this is the step's credits
and mask change; at the level of traces it is just `G`. -/
@[lantana_alias trSpec_step]
def step (G : TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := fun τ => iprop(|={⊤,∅}=> ALC iprop(|={∅,⊤}=> G.internal τ))
  external := G.external
  adeq F τ h := G.adeq F τ (SatFUpd.fupd (sat_ALC (SatFUpd.fupd h)))

/-- `G` read at the next position, with no modality; `next G` is `step (shift G)`. -/
@[lantana_alias trSpec_shift]
def shift (G : TrSpec Expr State GF) : TrSpec Expr State GF where
  internal := fun τ => G.internal τ.next
  external := fun τ => G.external τ.next
  adeq F τ h := G.adeq F τ.next h

scoped notation:max "⊳ₛ " G:40 => TrSpec.later G
scoped notation:max "○ₛ " G:40 => TrSpec.next G
scoped notation:max "⊚ₛ " G:40 => TrSpec.step G

section Connectives
variable {G G' : TrSpec Expr State GF}

@[lantana_alias trSpec_later_mono]
theorem later_mono (h : G ⊑ₛ G') : later G ⊑ₛ later G' :=
  fun τ => fupd_mono <| BI.later_mono <| fupd_mono (h τ)

@[lantana_alias trSpec_next_mono]
theorem next_mono (h : G ⊑ₛ G') : next G ⊑ₛ next G' :=
  fun τ => fupd_mono <| ALC_mono <| fupd_mono (h τ.next)

@[lantana_alias trSpec_step_mono]
theorem step_mono (h : G ⊑ₛ G') : step G ⊑ₛ step G' :=
  fun τ => fupd_mono <| ALC_mono <| fupd_mono (h τ)

@[lantana_alias trSpec_shift_mono]
theorem shift_mono (h : G ⊑ₛ G') : shift G ⊑ₛ shift G' :=
  fun τ => h τ.next

/-- The instance argument comes last: synthesized before the index type is known, it would fix
the universe of the index type. -/
@[lantana_alias trSpec_exist_lub]
theorem ex_lub {X : Type _} {G : X → TrSpec Expr State GF} [SIdxLarge SI X]
    (h : ∀ x, G x ⊑ₛ G') : ex G ⊑ₛ G' :=
  fun τ => exists_elim fun x => h x τ

@[lantana_alias trSpec_exist_ub]
theorem ex_ub {X : Type _} (G : X → TrSpec Expr State GF) (x : X) [SIdxLarge SI X] :
    G x ⊑ₛ ex G :=
  fun τ => exists_intro (Ψ := fun x => (G x).internal τ) x

end Connectives

/-! ## Monotone bodies -/

/-- A body monotone in both readings. -/
@[lantana_alias TrSpecMono]
class Mono (F : TrSpec Expr State GF → TrSpec Expr State GF) : Prop where
  mono_le {X Y : TrSpec Expr State GF} : X ⊑ₛ Y → F X ⊑ₛ F Y
  mono_ext {X Y : TrSpec Expr State GF} : X.external ⊆ Y.external → (F X).external ⊆ (F Y).external

attribute [lantana_alias trSpec_mono_le] Mono.mono_le
attribute [lantana_alias trSpec_mono_ext] Mono.mono_ext

section MonoInstances

@[lantana_alias trSpec_mono_id]
instance mono_id : Mono (Expr := Expr) (State := State) (GF := GF) fun X => X :=
  ⟨id, id⟩

@[lantana_alias trSpec_mono_const]
instance mono_const (G : TrSpec Expr State GF) : Mono fun _ => G :=
  ⟨fun _ => le_refl G, fun _ => TrProp.le_refl _⟩

@[lantana_alias trSpec_mono_and]
instance mono_and (F₁ F₂ : TrSpec Expr State GF → TrSpec Expr State GF) [Mono F₁] [Mono F₂] :
    Mono fun X => F₁ X ∧ₛ F₂ X :=
  ⟨fun h => and_mono (Mono.mono_le h) (Mono.mono_le h),
   fun h => TrProp.and_mono (Mono.mono_ext (F := F₁) h) (Mono.mono_ext (F := F₂) h)⟩

@[lantana_alias trSpec_mono_or]
instance mono_or (F₁ F₂ : TrSpec Expr State GF → TrSpec Expr State GF) [Mono F₁] [Mono F₂] :
    Mono fun X => F₁ X ∨ₛ F₂ X :=
  ⟨fun h => or_mono (Mono.mono_le h) (Mono.mono_le h),
   fun h => TrProp.or_mono (Mono.mono_ext (F := F₁) h) (Mono.mono_ext (F := F₂) h)⟩

@[lantana_alias trSpec_mono_impl]
instance mono_imp (A : TrSpec Expr State GF) (F : TrSpec Expr State GF → TrSpec Expr State GF)
    [Mono F] : Mono fun X => A →ₛ F X :=
  ⟨fun h => imp_mono (TrProp.le_refl _) (Mono.mono_le h),
   fun h => TrProp.imp_mono (TrProp.le_refl _) (Mono.mono_ext (F := F) h)⟩

@[lantana_alias trSpec_mono_forall]
instance mono_all {Y : Type _} (F : Y → TrSpec Expr State GF → TrSpec Expr State GF)
    [∀ y, Mono (F y)] : Mono fun X => all fun y => F y X :=
  ⟨fun h => all_mono fun _ => Mono.mono_le h,
   fun h => TrProp.all_mono fun y => Mono.mono_ext (F := F y) h⟩

@[lantana_alias trSpec_mono_exist]
instance mono_ex {Y : Type _} [SIdxLarge SI Y] (F : Y → TrSpec Expr State GF → TrSpec Expr State GF)
    [∀ y, Mono (F y)] : Mono fun X => ex fun y => F y X :=
  ⟨fun h => ex_mono fun _ => Mono.mono_le h,
   fun h => TrProp.ex_mono fun y => Mono.mono_ext (F := F y) h⟩

@[lantana_alias trSpec_mono_later]
instance mono_later (F : TrSpec Expr State GF → TrSpec Expr State GF) [Mono F] :
    Mono fun X => later (F X) :=
  ⟨fun h => later_mono (Mono.mono_le h), fun h => Mono.mono_ext (F := F) h⟩

@[lantana_alias trSpec_mono_next]
instance mono_next (F : TrSpec Expr State GF → TrSpec Expr State GF) [Mono F] :
    Mono fun X => next (F X) :=
  ⟨fun h => next_mono (Mono.mono_le h), fun h τ => Mono.mono_ext (F := F) h τ.next⟩

@[lantana_alias trSpec_mono_step]
instance mono_step (F : TrSpec Expr State GF → TrSpec Expr State GF) [Mono F] :
    Mono fun X => step (F X) :=
  ⟨fun h => step_mono (Mono.mono_le h), fun h => Mono.mono_ext (F := F) h⟩

@[lantana_alias trSpec_mono_shift]
instance mono_shift (F : TrSpec Expr State GF → TrSpec Expr State GF) [Mono F] :
    Mono fun X => shift (F X) :=
  ⟨fun h => shift_mono (Mono.mono_le h), fun h τ => Mono.mono_ext (F := F) h τ.next⟩

@[lantana_alias trSpec_mono_always]
instance mono_always (F : TrSpec Expr State GF → TrSpec Expr State GF) [Mono F] :
    Mono fun X => □ₛ F X :=
  ⟨fun h => always_mono (Mono.mono_le h), fun h => TrProp.always_mono (Mono.mono_ext (F := F) h)⟩

@[lantana_alias trSpec_mono_until]
instance mono_strongUntil (F₁ F₂ : TrSpec Expr State GF → TrSpec Expr State GF) [Mono F₁]
    [Mono F₂] : Mono fun X => F₁ X 𝒰ₛ F₂ X :=
  ⟨fun h => strongUntil_mono (Mono.mono_le h) (Mono.mono_le h),
   fun h => TrProp.until_mono (Mono.mono_ext (F := F₁) h) (Mono.mono_ext (F := F₂) h)⟩

/-! Instance resolution sees `fun X => later X` or `fun X => G ∧ₛ X` eta-reduced, as `later` or
`and G`, which the instances above (whose conclusions are `fun`s) do not match; hence the
eta-reduced forms. -/

instance mono_later_eta : Mono (later (Expr := Expr) (State := State) (GF := GF)) :=
  mono_later fun X => X
instance mono_next_eta : Mono (next (Expr := Expr) (State := State) (GF := GF)) :=
  mono_next fun X => X
instance mono_step_eta : Mono (step (Expr := Expr) (State := State) (GF := GF)) :=
  mono_step fun X => X
instance mono_shift_eta : Mono (shift (Expr := Expr) (State := State) (GF := GF)) :=
  mono_shift fun X => X
instance mono_always_eta : Mono (always (Expr := Expr) (State := State) (GF := GF)) :=
  mono_always fun X => X
instance mono_and_eta (G : TrSpec Expr State GF) : Mono (and G) :=
  mono_and (fun _ => G) fun X => X
instance mono_or_eta (G : TrSpec Expr State GF) : Mono (or G) :=
  mono_or (fun _ => G) fun X => X
instance mono_imp_eta (A : TrSpec Expr State GF) : Mono (imp A) :=
  mono_imp A fun X => X
instance mono_strongUntil_eta (G : TrSpec Expr State GF) : Mono (strongUntil G) :=
  mono_strongUntil (fun _ => G) fun X => X

end MonoInstances

/-! ## Continuous bodies

`F` commutes, in the logic, with unions of increasing chains indexed by ordinals. Guarded
bodies are not continuous: the step index ranges beyond `Fuel`, so `▷ ∃ α, X α` does not give
`∃ α, ▷ X α`. -/

/-- A body that commutes with unions of increasing chains indexed by ordinals. -/
@[lantana_alias TrSpecCont]
class Cont (F : TrSpec Expr State GF → TrSpec Expr State GF) : Prop where
  cont (X : Fuel → TrSpec Expr State GF) :
    (∀ α β : Fuel, α ≤ β → X α ⊑ₛ X β) → F (ex (X := Fuel) X) ⊑ₛ ex (X := Fuel) fun α => F (X α)

attribute [lantana_alias trSpec_cont] Cont.cont

section ContInstances

@[lantana_alias trSpec_cont_id]
instance cont_id : Cont (Expr := Expr) (State := State) (GF := GF) fun X => X :=
  ⟨fun _ _ => le_refl _⟩

@[lantana_alias trSpec_cont_const]
instance cont_const (G : TrSpec Expr State GF) : Cont fun _ => G :=
  ⟨fun _ _ => ex_ub (X := Fuel) (fun _ => G) 0⟩

@[lantana_alias trSpec_cont_and]
instance cont_and (F₁ F₂ : TrSpec Expr State GF → TrSpec Expr State GF) [Mono F₁] [Mono F₂]
    [Cont F₁] [Cont F₂] : Cont fun X => F₁ X ∧ₛ F₂ X where
  cont X hX := fun τ => by
    refine (BI.and_mono (Cont.cont X hX τ) (Cont.cont X hX τ)).trans ?_
    refine and_exists_right.mp.trans <| exists_elim fun α => ?_
    refine and_exists_left.mp.trans <| exists_elim fun β => ?_
    refine BI.and_mono ?_ ?_ |>.trans <| exists_intro
      (Ψ := fun γ => iprop((F₁ (X γ)).internal τ ∧ (F₂ (X γ)).internal τ)) (max α β)
    · exact Mono.mono_le (hX _ _ (Ordinals.Ordinal.le_max_left α β)) τ
    · exact Mono.mono_le (hX _ _ (Ordinals.Ordinal.le_max_right α β)) τ

@[lantana_alias trSpec_cont_or]
instance cont_or (F₁ F₂ : TrSpec Expr State GF → TrSpec Expr State GF) [Cont F₁] [Cont F₂] :
    Cont fun X => F₁ X ∨ₛ F₂ X where
  cont X hX := fun τ => (BI.or_mono (Cont.cont X hX τ) (Cont.cont X hX τ)).trans <|
    or_elim (exists_mono fun _ => or_intro_l) (exists_mono fun _ => or_intro_r)

/-- Classical: by cases on the antecedent. -/
@[lantana_alias trSpec_cont_impl]
instance cont_imp (A : TrSpec Expr State GF) (F : TrSpec Expr State GF → TrSpec Expr State GF)
    [Cont F] : Cont fun X => A →ₛ F X where
  cont X hX := fun τ => by
    by_cases hA : A.external τ
    · refine ((BI.and_intro (pure_intro hA) .rfl).trans imp_elim_right).trans <|
        (Cont.cont X hX τ).trans <| exists_mono fun _ => BI.imp_intro BI.and_elim_l
    · exact (BI.imp_intro <| pure_elim _ BI.and_elim_r fun h => absurd h hA).trans
        (exists_intro (Ψ := fun α => (A →ₛ F (X α)).internal τ) 0)

@[lantana_alias trSpec_cont_exist]
instance cont_ex {Y : Type _} [SIdxLarge SI Y] (F : Y → TrSpec Expr State GF → TrSpec Expr State GF)
    [∀ y, Cont (F y)] : Cont fun X => ex fun y => F y X where
  cont X hX := fun τ => exists_elim fun y => (Cont.cont X hX τ).trans <| exists_mono fun α =>
    exists_intro (Ψ := fun y => (F y (X α)).internal τ) y

@[lantana_alias trSpec_cont_shift]
instance cont_shift (F : TrSpec Expr State GF → TrSpec Expr State GF) [Cont F] :
    Cont fun X => shift (F X) where
  cont X hX := fun τ => Cont.cont X hX τ.next

/-! The eta-reduced forms (see `mono_later_eta`). -/

instance cont_shift_eta : Cont (shift (Expr := Expr) (State := State) (GF := GF)) :=
  cont_shift fun X => X
instance cont_and_eta (G : TrSpec Expr State GF) : Cont (and G) :=
  cont_and (fun _ => G) fun X => X
instance cont_or_eta (G : TrSpec Expr State GF) : Cont (or G) :=
  cont_or (fun _ => G) fun X => X
instance cont_imp_eta (A : TrSpec Expr State GF) : Cont (imp A) :=
  cont_imp A fun X => X

end ContInstances

/-! ## Greatest fixpoints -/

section Nu
variable (F : TrSpec Expr State GF → TrSpec Expr State GF)

/-- The internal reading of `nu F`: some post-fixpoint of `F` holds. -/
def nuInternal [ModelGS GF] [TemporalGS Expr State GF] : TrIProp Expr State GF :=
  fun τ => iprop(∃ X : TrSpec Expr State GF, ⌜X ⊑ₛ F X⌝ ∧ X.internal τ)

/-- The core of the adequacy of `nu F`: a trace predicate `S` adequate for the internal reading
of `nu F` is a post-fixpoint of the trace functor. -/
theorem nu_post [Mono F] (S : TrProp Expr State)
    (hS : ∀ [ModelGS GF] [TemporalGS Expr State GF] (F' : IProp GF) (τ : Trace Expr State),
      (iPropSatLcAtFrame F' ⊤).sat (nuInternal F τ) → S τ)
    [ModelGS GF] [TemporalGS Expr State GF] (F' : IProp GF) (τ : Trace Expr State)
    (hs : (iPropSatLcAtFrame F' ⊤).sat (nuInternal F τ)) : (F (trp S)).external τ := by
  let N : TrSpec Expr State GF := ⟨nuInternal F, S, hS⟩
  have hXN : ∀ X : TrSpec Expr State GF, X ⊑ₛ F X → X ⊑ₛ N := fun X hX => fun τ' =>
    (BI.and_intro (pure_intro (φ := X ⊑ₛ F X) hX) .rfl).trans <|
      exists_intro (Ψ := fun X => iprop(⌜X ⊑ₛ F X⌝ ∧ X.internal τ')) X
  have hIN : nuInternal F τ ⊢ (F N).internal τ :=
    exists_elim fun X => pure_elim_left fun hX => (hX τ).trans (Mono.mono_le (hXN X hX) τ)
  exact Mono.mono_ext (X := N) (Y := trp S) (TrProp.le_refl _) τ
    ((F N).adeq F' τ ((iPropSatLcAtFrame F' ⊤).mono hIN hs))

/-- The greatest fixpoint: the union of the post-fixpoints. Its adequacy avoids the existential
property over the large type `TrSpec`: the traces at which the internal reading is satisfiable
(for some instance and frame) form a post-fixpoint of the trace functor. -/
@[lantana_alias trSpec_nu]
def nu [Mono F] : TrSpec Expr State GF where
  internal := nuInternal F
  external := TrProp.gfp fun R => (F (trp R)).external
  adeq F₀ _ h :=
    ⟨fun τ' => ∃ (_ : ModelGS GF) (_ : TemporalGS Expr State GF) (F' : IProp GF),
        (iPropSatLcAtFrame F' ⊤).sat (nuInternal F τ'),
      fun τ' ⟨i₁, i₂, F', hs⟩ =>
        @nu_post _ _ _ F _ _ (fun F' _ hs => ⟨_, _, F', hs⟩) i₁ i₂ F' τ' hs,
      ⟨_, _, F₀, h⟩⟩

variable [Mono F]

@[lantana_alias trSpec_nu_coind]
theorem nu_coind {X : TrSpec Expr State GF} (hX : X ⊑ₛ F X) : X ⊑ₛ nu F := fun τ =>
  (BI.and_intro (pure_intro (φ := X ⊑ₛ F X) hX) .rfl).trans <|
    exists_intro (Ψ := fun X => iprop(⌜X ⊑ₛ F X⌝ ∧ X.internal τ)) X

@[lantana_alias trSpec_nu_unfold_l]
theorem nu_unfold_l : nu F ⊑ₛ F (nu F) := fun τ =>
  exists_elim fun _ => pure_elim_left fun hX => (hX τ).trans (Mono.mono_le (nu_coind F hX) τ)

@[lantana_alias trSpec_nu_unfold_r]
theorem nu_unfold_r : F (nu F) ⊑ₛ nu F :=
  nu_coind F (Mono.mono_le (nu_unfold_l F))

@[lantana_alias trSpec_nu_ext]
theorem nu_ext (τ : Trace Expr State) :
    (nu F).external τ ↔ TrProp.gfp (fun R => (F (trp R)).external) τ :=
  .rfl

end Nu

/-! ## Least fixpoints, with ordinal approximants -/

section Mu
variable (F : TrSpec Expr State GF → TrSpec Expr State GF)

/-- The approximant `μ_α = F (∃ β < α, μ_β)`, by well-founded recursion on `α`. -/
@[lantana_alias trSpec_mu_approx]
def muApprox (α : Fuel) : TrSpec Expr State GF :=
  Ordinals.Ordinal.lt_wf.fix (C := fun _ => TrSpec Expr State GF)
    (fun α rec => F (ex (X := { β : Fuel // β < α }) fun b => rec b.1 b.2)) α

/-- The least fixpoint: the union of the approximants. -/
@[lantana_alias trSpec_mu]
def mu : TrSpec Expr State GF := ex (X := Fuel) (muApprox F)

@[lantana_alias trSpec_mu_approx_unfold]
theorem muApprox_unfold (α : Fuel) :
    muApprox F α = F (ex (X := { β : Fuel // β < α }) fun b => muApprox F b.1) :=
  WellFounded.fix_eq _ _ _

#lantana_ignore trSpec_mu_rec "`muApprox` is defined by `WellFounded.fix`."
#lantana_ignore trSpec_mu_rec_irrel "`muApprox` is defined by `WellFounded.fix`."

variable [Mono F]

/-- Introduction with a ranking: `H α` unfolds to `F` of smaller ranks. -/
@[lantana_alias trSpec_mu_rank]
theorem mu_rank (H : Fuel → TrSpec Expr State GF)
    (hH : ∀ α, H α ⊑ₛ F (ex (X := { β : Fuel // β < α }) fun b => H b.1)) (α : Fuel) :
    H α ⊑ₛ muApprox F α := by
  induction α using Ordinals.Ordinal.lt_wf.induction with
  | _ α ih =>
  rw [muApprox_unfold]
  exact le_trans (hH α) (Mono.mono_le (ex_mono (Y := { β : Fuel // β < α }) fun b => ih b.1 b.2))

@[lantana_alias trSpec_mu_intro]
theorem mu_intro (H : Fuel → TrSpec Expr State GF)
    (hH : ∀ α, H α ⊑ₛ F (ex (X := { β : Fuel // β < α }) fun b => H b.1)) (α : Fuel) :
    H α ⊑ₛ mu F :=
  le_trans (mu_rank F H hH α) (ex_ub (X := Fuel) (muApprox F) α)

/-- Induction: `mu F` is below every pre-fixpoint. -/
@[lantana_alias trSpec_mu_ind]
theorem mu_ind {X : TrSpec Expr State GF} (hX : F X ⊑ₛ X) : mu F ⊑ₛ X := by
  refine ex_lub (X := Fuel) fun α => ?_
  induction α using Ordinals.Ordinal.lt_wf.induction with
  | _ α ih =>
  rw [muApprox_unfold]
  exact le_trans (Mono.mono_le (ex_lub (X := { β : Fuel // β < α }) fun b => ih b.1 b.2)) hX

@[lantana_alias trSpec_mu_post]
theorem mu_post : mu F ⊑ₛ F (mu F) := by
  refine ex_lub (X := Fuel) fun α => ?_
  rw [muApprox_unfold]
  exact Mono.mono_le <| ex_lub (X := { β : Fuel // β < α }) fun b =>
    ex_ub (X := Fuel) (muApprox F) b.1

@[lantana_alias trSpec_mu_approx_mono]
theorem muApprox_mono {α β : Fuel} (h : α ≤ β) : muApprox F α ⊑ₛ muApprox F β := by
  rw [muApprox_unfold F α, muApprox_unfold F β]
  exact Mono.mono_le <| ex_lub (X := { γ : Fuel // γ < α }) fun b =>
    ex_ub (X := { γ : Fuel // γ < β }) (fun b => muApprox F b.1)
      ⟨b.1, Ordinals.Ordinal.lt_of_lt_of_le b.2 h⟩

/-- The fold, for a continuous body; with `mu_post`, `mu F` is then a fixpoint. -/
@[lantana_alias trSpec_mu_unfold_r]
theorem mu_unfold_r [Cont F] : F (mu F) ⊑ₛ mu F := by
  refine le_trans (Cont.cont (muApprox F) fun _ _ h => muApprox_mono F h)
    (ex_lub (X := Fuel) fun α => ?_)
  refine le_trans ?_ (ex_ub (X := Fuel) (muApprox F) (Ordinals.Ordinal.succ α))
  rw [muApprox_unfold F (Ordinals.Ordinal.succ α)]
  exact Mono.mono_le <| ex_ub (X := { β : Fuel // β < Ordinals.Ordinal.succ α })
    (fun b => muApprox F b.1) ⟨α, Ordinals.Ordinal.lt_succ α⟩

theorem trp_mono : TrProp.Mono fun R : TrProp Expr State => (F (trp R)).external :=
  fun _ _ hR => Mono.mono_ext (X := trp _) (Y := trp _) hR

@[lantana_alias trSpec_mu_ext]
theorem mu_ext (τ : Trace Expr State) :
    (mu F).external τ → TrProp.lfp (fun R => (F (trp R)).external) τ := by
  rintro ⟨α, hα⟩
  induction α using Ordinals.Ordinal.lt_wf.induction generalizing τ with
  | _ α ih =>
  rw [muApprox_unfold] at hα
  exact TrProp.lfp_unfold_r (trp_mono F) τ <|
    Mono.mono_ext (X := ex (X := { β : Fuel // β < α }) fun b => muApprox F b.1) (Y := trp _)
      (fun τ' ⟨b, h⟩ => ih b.1 b.2 τ' h) τ hα

/-- The trace reading is a pre-fixpoint of the trace functor: the supremum of the ranks of its
traces bounds them all (classical choice of the ranks). -/
@[lantana_alias trSpec_mu_ext_pre]
theorem mu_ext_pre (τ : Trace Expr State) :
    (F (trp (mu F).external)).external τ → (mu F).external τ := by
  intro hτ
  have hf : ∀ τ' : Trace Expr State, ∃ α : Fuel, (mu F).external τ' → (muApprox F α).external τ' :=
    fun τ' => (Classical.em ((mu F).external τ')).elim (fun ⟨α, h⟩ => ⟨α, fun _ => h⟩)
      (fun hn => ⟨0, fun h => absurd h hn⟩)
  let f := fun τ' => Classical.choose (hf τ')
  have hf : ∀ τ', (mu F).external τ' → (muApprox F (f τ')).external τ' :=
    fun τ' => Classical.choose_spec (hf τ')
  let s : Fuel := Ordinals.Ordinal.sup fun t : ULift.{1} (Trace Expr State) => f t.down
  refine ⟨Ordinals.Ordinal.succ s, ?_⟩
  change (muApprox F (Ordinals.Ordinal.succ s)).external τ
  rw [muApprox_unfold]
  refine Mono.mono_ext (X := trp _)
    (Y := ex (X := { β : Fuel // β < Ordinals.Ordinal.succ s }) fun b => muApprox F b.1)
    (fun τ' h => ?_) τ hτ
  exact ⟨⟨f τ', Ordinals.Ordinal.lt_of_le_of_lt
    (Ordinals.Ordinal.le_sup (fun t : ULift.{1} (Trace Expr State) => f t.down) ⟨τ'⟩)
    (Ordinals.Ordinal.lt_succ s)⟩, hf τ' h⟩

@[lantana_alias trSpec_mu_ext_lfp]
theorem mu_ext_lfp (τ : Trace Expr State) :
    TrProp.lfp (fun R => (F (trp R)).external) τ → (mu F).external τ :=
  fun h => h _ (mu_ext_pre F)

@[lantana_alias trSpec_mu_ext_iff]
theorem mu_ext_iff (τ : Trace Expr State) :
    (mu F).external τ ↔ TrProp.lfp (fun R => (F (trp R)).external) τ :=
  ⟨mu_ext F τ, mu_ext_lfp F τ⟩

/-- On traces, `mu F` is a fixpoint of `F`, for any monotone body. -/
@[lantana_alias trSpec_mu_ext_unfold_l]
theorem mu_ext_unfold_l (τ : Trace Expr State) : (mu F).external τ → (F (mu F)).external τ := by
  rintro ⟨α, hα⟩
  rw [muApprox_unfold] at hα
  exact Mono.mono_ext (X := ex (X := { β : Fuel // β < α }) fun b => muApprox F b.1) (Y := mu F)
    (fun _ ⟨b, h⟩ => ⟨b.1, h⟩) τ hα

@[lantana_alias trSpec_mu_ext_unfold_r]
theorem mu_ext_unfold_r (τ : Trace Expr State) : (F (mu F)).external τ → (mu F).external τ :=
  fun h => mu_ext_pre F τ (Mono.mono_ext (X := mu F) (Y := trp _) (TrProp.le_refl _) τ h)

end Mu

/-! ## Always and until as fixpoints

The step-indexed readings decide a position after the step taken there, so the bodies are
`⊳ ⊚ (G ∧ shift X)` and `⊳ ⊚ (G₂ ∨ (G₁ ∧ shift X))`; on traces these read as `G ∧ ○ X` and
`G₂ ∨ (G₁ ∧ ○ X)`. -/

section LTL
variable (G G₁ G₂ : TrSpec Expr State GF)

/-- The body of `□ₛ G`. -/
@[lantana_alias F_always]
def alwaysBody (X : TrSpec Expr State GF) : TrSpec Expr State GF :=
  later (step (G ∧ₛ shift X))

/-- The body of `G₁ 𝒰ₛ G₂`. -/
@[lantana_alias F_until]
def untilBody (X : TrSpec Expr State GF) : TrSpec Expr State GF :=
  later (step (G₂ ∨ₛ (G₁ ∧ₛ shift X)))

@[lantana_alias F_always_mono]
instance alwaysBody_mono : Mono (alwaysBody G) :=
  ⟨fun h => later_mono (step_mono (and_mono (le_refl G) (shift_mono h))),
   fun h => TrProp.and_mono (TrProp.le_refl _) fun τ => h τ.next⟩

@[lantana_alias F_until_mono]
instance untilBody_mono : Mono (untilBody G₁ G₂) :=
  ⟨fun h => later_mono (step_mono (or_mono (le_refl G₂) (and_mono (le_refl G₁) (shift_mono h)))),
   fun h => TrProp.or_mono (TrProp.le_refl _) (TrProp.and_mono (TrProp.le_refl _)
     fun τ => h τ.next)⟩

/-- `□ₛ G` is `ν X. ⊳ ⊚ (G ∧ shift X)`, in both directions. -/
@[lantana_alias trSpec_always_le_nu]
theorem always_le_nu : (□ₛ G) ⊑ₛ nu (alwaysBody G) :=
  nu_coind _ fun τ => (TrIProp.always_unfold G.internal τ).mp

@[lantana_alias trSpec_nu_le_always]
theorem nu_le_always : nu (alwaysBody G) ⊑ₛ (□ₛ G) := fun τ => by
  refine exists_elim fun X => pure_elim_left fun hX => ?_
  have hl : ⊢ ∀ τ, X.internal τ -∗ TrIProp.always G.internal τ := by
    iloeb as IH
    iintro %τ H
    have h₁ : X.internal τ ⊢ TrIProp.defer iprop(G.internal τ ∧ X.internal τ.next) := hX τ
    have h₂ : TrIProp.defer iprop(G.internal τ ∧ TrIProp.always G.internal τ.next) ⊢
        TrIProp.always G.internal τ :=
      (TrIProp.always_unfold G.internal τ).mpr
    iapply h₂
    ihave H := h₁ $$ H
    iapply TrIProp.defer_wand_later $$ [] H
    inext
    iintro H
    isplit
    · icases H with ⟨H, -⟩
      iexact H
    · icases H with ⟨-, H⟩
      iapply IH
      iexact H
  exact (emp_sep.mpr.trans (sep_mono_left hl)).trans <|
    (sep_mono_left (forall_elim τ)).trans wand_elim_left

/-- On traces, `ν X. G ∧ ○ X` is `□ G`. -/
@[lantana_alias trSpec_nu_always_ext]
theorem nu_always_ext : (nu (alwaysBody G)).external ⊆ (□ₜ G.external) :=
  fun τ h => h.elim fun R h => TrProp.always_coind (X := R) h.1 τ h.2

@[lantana_alias trSpec_nu_always_ext']
theorem nu_always_ext' : (□ₜ G.external) ⊆ (nu (alwaysBody G)).external :=
  fun _ h => ⟨□ₜ G.external, fun τ' h' => ⟨TrProp.always_elim τ' h', TrProp.always_next τ' h'⟩, h⟩

/-- A ranked until. -/
@[lantana_alias trSpec_until_at]
def untilAt (a : Fuel) : TrSpec Expr State GF where
  internal := TrIProp.strongUntil G₁.internal G₂.internal a
  external := (G₁ 𝒰ₛ G₂).external
  adeq F τ h := (G₁ 𝒰ₛ G₂).adeq F τ <| (iPropSatLcAtFrame F ⊤).mono
    (exists_intro (Ψ := fun a => TrIProp.strongUntil G₁.internal G₂.internal a τ) a) h

/-- `G₁ 𝒰ₛ G₂` is below `μ X. ⊳ ⊚ (G₂ ∨ (G₁ ∧ shift X))`: its rank is a ranking. -/
@[lantana_alias trSpec_until_le_mu]
theorem until_le_mu : (G₁ 𝒰ₛ G₂) ⊑ₛ mu (untilBody G₁ G₂) := by
  refine le_trans (H := ex (X := Fuel) (untilAt G₁ G₂)) (fun _ => .rfl)
    (ex_lub (X := Fuel) fun a => ?_)
  refine mu_intro _ (untilAt G₁ G₂) (fun α => ?_) a
  intro _ _ τ
  refine (TrIProp.until_unfold G₁.internal G₂.internal α τ).mp.trans <|
    TrIProp.defer_mono <| BI.or_mono .rfl <| BI.and_mono .rfl <| exists_elim fun a' =>
      pure_elim_left fun hlt => ?_
  exact exists_intro (Ψ := fun b : { β : Fuel // β < α } => (untilAt G₁ G₂ b.1).internal τ.next)
    ⟨a', hlt⟩

@[lantana_alias trSpec_mu_until_ext]
theorem mu_until_ext : (mu (untilBody G₁ G₂)).external ⊆ (G₁.external 𝒰ₜ G₂.external) :=
  fun τ h => TrProp.lfp_ind (R := G₁.external 𝒰ₜ G₂.external)
    (fun τ h => h.elim (fun h => TrProp.until_now τ h) (fun h => TrProp.until_step τ h))
    τ (mu_ext _ τ h)

/-- Conversely, the approximant `μ_α` is the until ranked by `α`. -/
@[lantana_alias trSpec_mu_approx_le_until]
theorem muApprox_le_until (α : Fuel) : muApprox (untilBody G₁ G₂) α ⊑ₛ untilAt G₁ G₂ α := by
  induction α using Ordinals.Ordinal.lt_wf.induction with
  | _ α ih =>
  rw [muApprox_unfold]
  intro _ _ τ
  refine (TrIProp.defer_mono <| BI.or_mono .rfl <| BI.and_mono .rfl <|
    exists_elim fun b => ?_).trans
    (TrIProp.until_unfold G₁.internal G₂.internal α τ).mpr
  exact (BI.and_intro (pure_intro b.2) (ih b.1 b.2 τ.next)).trans <|
    exists_intro (Ψ := fun a' => iprop(⌜a' < α⌝ ∧
      TrIProp.strongUntil G₁.internal G₂.internal a' τ.next)) b.1

@[lantana_alias trSpec_mu_le_until]
theorem mu_le_until : mu (untilBody G₁ G₂) ⊑ₛ (G₁ 𝒰ₛ G₂) :=
  ex_lub (X := Fuel) fun α => le_trans (muApprox_le_until G₁ G₂ α)
    (show untilAt G₁ G₂ α ⊑ₛ (G₁ 𝒰ₛ G₂) from fun τ =>
      exists_intro (Ψ := fun a => TrIProp.strongUntil G₁.internal G₂.internal a τ) α)

@[lantana_alias trSpec_mu_until_ext_iff]
theorem mu_until_ext_iff (τ : Trace Expr State) :
    (mu (untilBody G₁ G₂)).external τ ↔ (G₁.external 𝒰ₜ G₂.external) τ :=
  ⟨mu_until_ext G₁ G₂ τ, fun h => mu_ext_lfp _ τ fun R hR =>
    TrProp.until_ind (X := R) (fun τ h => hR τ (.inl h)) (fun τ h => hR τ (.inr h)) τ h⟩

/-- Beyond LTL: `G` at every even position, `ν X. ⊳ ⊚ (G ∧ shift (○ X))`. -/
@[lantana_alias F_even]
def evenBody (X : TrSpec Expr State GF) : TrSpec Expr State GF :=
  later (step (G ∧ₛ shift (next X)))

@[lantana_alias F_even_mono]
instance evenBody_mono : Mono (evenBody G) :=
  ⟨fun h => later_mono (step_mono (and_mono (le_refl G) (shift_mono (next_mono h)))),
   fun h => TrProp.and_mono (TrProp.le_refl _) fun τ => h τ.next.next⟩

@[lantana_alias trSpec_nu_even_ext]
theorem nu_even_ext (τ : Trace Expr State) :
    (nu (evenBody G)).external τ ↔ ∀ k, G.external { τ with pos := τ.pos + 2 * k } := by
  constructor
  · rintro ⟨R, hR, hτ⟩
    have hk : ∀ k, R { τ with pos := τ.pos + 2 * k } := by
      intro k
      induction k with
      | zero => exact hτ
      | succ k ih =>
        have h := (hR _ ih).2
        have he : (2 * (k + 1)) = 2 * k + 1 + 1 := by omega
        simpa [shift, next, trp, Trace.next, he, Nat.add_assoc] using h
    exact fun k => (hR _ (hk k)).1
  · intro hev
    refine ⟨fun τ' => ∃ k, τ' = { τ with pos := τ.pos + 2 * k }, ?_, ⟨0, by simp⟩⟩
    rintro τ' ⟨k, rfl⟩
    refine ⟨hev k, k + 1, ?_⟩
    simp only [Trace.next, Trace.mk.injEq, and_true]
    omega

end LTL

end TrSpec
end Lantana
