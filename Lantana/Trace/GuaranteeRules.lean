/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.Guarantee

/-! # Rules for temporal guarantees

Rocq `lantana/trace/guarantee_rules.v`: the interface of `P ⊨ₜ G` (`Lantana.Trace.Guarantee`):
monotonicity in `P` (`guar_mono`) and in `G` (`guar_weaken`, `guar_cast`), the rules for the
connectives of `P`, the canonical specification `TrSpec.canon P` and its completeness, state
atoms (`StateFact`), implications and big separating conjunctions. Guarantees are inferred from
the shape of `P` (`GuarOf`) and checked against a target (`IntoGuar`). The rules for the
temporal formulas `alwaysI` and `untilI` are in `Lantana.Trace.TemporalFormula`.

The rules for the connectives combine records (`record_and`, `record_all`, `record_mono`): a
record of a conjunction or a universal is assembled from the records of its parts, against
the same system and bundle.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open Lantana.Model
open scoped Lantana.TrSpec Lantana.TrProp

variable {Expr State Val : Type} {GF : BundledGFunctors}
variable [Language Expr State Val] [ModelGS GF] [TemporalGS Expr State GF]
  [StateInterp Expr State GF]

/-! ## Combining records -/

section Records

theorem recordTrI_all {X : Sort _} (f : X → Trace Expr State → IProp GF) (n : Nat) :
    iprop(∀ x, recordTrI (f x) n) ⊢ recordTrI (fun τ => iprop(∀ x, f x τ)) n := by
  iintro #H
  iapply recordTrI_intro
  imodintro
  iintro %Sys %l %h %g %v %Ω %W %τf %γ %σ %tp #ST %Hf #B HW
  iintro %x
  iapply recordTrI_elim (f x) $$ [H] ST %Hf B HW
  iapply H

theorem recordTrI_and (f₁ f₂ : Trace Expr State → IProp GF) (n : Nat) :
    iprop(recordTrI f₁ n ∧ recordTrI f₂ n) ⊢ recordTrI (fun τ => iprop(f₁ τ ∧ f₂ τ)) n := by
  iintro ⟨#H₁, #H₂⟩
  iapply recordTrI_intro
  imodintro
  iintro %Sys %l %h %g %v %Ω %W %τf %γ %σ %tp #ST %Hf #B HW
  isplit
  · iapply recordTrI_elim f₁ $$ H₁ ST %Hf B HW
  · iapply recordTrI_elim f₂ $$ H₂ ST %Hf B HW

theorem record_all {X : Type _} (G : X → TrSpec Expr State GF) (n : Nat) :
    iprop(∀ x, record (G x) n) ⊢ record (TrSpec.all G) n :=
  recordTrI_all (fun x => (G x).internal) n

theorem record_and (G₁ G₂ : TrSpec Expr State GF) (n : Nat) :
    iprop(record G₁ n ∧ record G₂ n) ⊢ record (G₁ ∧ₛ G₂) n :=
  recordTrI_and G₁.internal G₂.internal n

/-- The right formula of an until fulfils it at once (rank `0`): a later-guarded record of the
right formula suffices, the until's step strips the later. -/
theorem record_until_now (G₁ G₂ : TrSpec Expr State GF) (n : Nat) :
    ▷ record G₂ n ⊢ record (G₁ 𝒰ₛ G₂) n := by
  iintro #H
  iapply record_intro
  imodintro
  iintro %Sys %l %h %g %v %Ω %W %τf %γ %σ %tp #ST %Hf #B HW
  have hU : ▷ G₂.internal ⟨n, τf⟩ ⊢ (G₁ 𝒰ₛ G₂).internal ⟨n, τf⟩ :=
    (later_mono or_intro_l).trans <| TrIProp.defer_intro_later.trans <|
      (TrIProp.until_unfold G₁.internal G₂.internal 0 _).mpr.trans <|
        exists_intro (Ψ := fun a : Fuel =>
          TrIProp.strongUntil G₁.internal G₂.internal a ⟨n, τf⟩) 0
  iapply hU
  inext
  iapply record_elim G₂ $$ H ST %Hf B HW

end Records

/-! ## Monotonicity -/

section Rules
variable {P Q : IProp GF} {G G₁ G₂ H : TrSpec Expr State GF}

@[lantana_alias guar_weaken]
theorem guar_weaken (h : G ⊑ₛ H) : (P ⊨ₜ G) ⊢ P ⊨ₜ H := by
  unfold Guar
  refine intuitionistically_mono ?_
  iterate 8 refine forall_mono fun _ => ?_
  exact wand_mono_right (record_mono h _)

/-- Exporting trace-level consequences. -/
@[lantana_alias guar_cast]
theorem guar_cast (R : TrProp Expr State) (pf : G.external ⊆ R) : (P ⊨ₜ G) ⊢ P ⊨ₜ G.cast R pf :=
  guar_weaken (TrSpec.cast_le R pf)

@[lantana_alias guar_mono]
theorem guar_mono : □ (Q -∗ P) ⊢ (P ⊨ₜ G) -∗ Q ⊨ₜ G := by
  iintro #HQP #HG
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, MI, HQ⟩
  iapply guar_elim P G h n σ tp m i Ω W $$ HG
  iframe HI MI
  iapply HQP $$ HQ

/-! ## Connectives -/

@[lantana_alias guar_true]
theorem guar_true : ⊢@{IProp GF} P ⊨ₜ TrSpec.true (Expr := Expr) (State := State) := by
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W -
  iapply record_intro
  imodintro
  iintro %Sys %l %h' %g %v %Ω' %W' %τf %γ %σ' %tp' - - - -
  have hτ : ⊢@{IProp GF} TrSpec.true.internal (⟨n, τf⟩ : Trace Expr State) := pure_intro trivial
  iapply hτ

@[lantana_alias guar_pure]
theorem guar_pure (φ : Prop) :
    ⊢@{IProp GF} iprop(⌜φ⌝) ⊨ₜ TrSpec.pure (Expr := Expr) (State := State) φ := by
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨-, -, %hφ⟩
  iapply record_intro
  imodintro
  iintro %Sys %l %h' %g %v %Ω' %W' %τf %γ %σ' %tp' - - - -
  have hτ : ⊢@{IProp GF} (TrSpec.pure φ).internal (⟨n, τf⟩ : Trace Expr State) := pure_intro hφ
  iapply hτ

@[lantana_alias guar_and]
theorem guar_and : (P ⊨ₜ G₁) ⊢ (Q ⊨ₜ G₂) -∗ iprop(P ∧ Q) ⊨ₜ (G₁ ∧ₛ G₂) := by
  iintro #HG₁ #HG₂
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, MI, HPQ⟩
  iapply record_and
  isplit
  · iapply guar_elim P G₁ h n σ tp m i Ω W $$ HG₁
    iframe HI MI
    icases HPQ with ⟨HP, -⟩
    iexact HP
  · iapply guar_elim Q G₂ h n σ tp m i Ω W $$ HG₂
    iframe HI MI
    icases HPQ with ⟨-, HQ⟩
    iexact HQ

@[lantana_alias guar_sep]
theorem guar_sep : (P ⊨ₜ G₁) ⊢ (Q ⊨ₜ G₂) -∗ iprop(P ∗ Q) ⊨ₜ (G₁ ∧ₛ G₂) := by
  iintro #HG₁ #HG₂
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, MI, HP, HQ⟩
  iapply record_and
  isplit
  · iapply guar_elim P G₁ h n σ tp m i Ω W $$ HG₁
    iframe
  · iapply guar_elim Q G₂ h n σ tp m i Ω W $$ HG₂
    iframe

@[lantana_alias guar_or]
theorem guar_or : (P ⊨ₜ G₁) ⊢ (Q ⊨ₜ G₂) -∗ iprop(P ∨ Q) ⊨ₜ (G₁ ∨ₛ G₂) := by
  iintro #HG₁ #HG₂
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, MI, HP | HQ⟩
  · iapply record_mono (G := G₁) (fun _ => or_intro_l)
    iapply guar_elim P G₁ h n σ tp m i Ω W $$ HG₁
    iframe
  · iapply record_mono (G := G₂) (fun _ => or_intro_r)
    iapply guar_elim Q G₂ h n σ tp m i Ω W $$ HG₂
    iframe

/-- An until fulfilled now (rank `0`; the until's step strips the later). -/
@[lantana_alias guar_until_now]
theorem guar_until_now : ▷ (P ⊨ₜ G₂) ⊢ P ⊨ₜ (G₁ 𝒰ₛ G₂) := by
  iintro #HG
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, MI, HP⟩
  iapply record_until_now
  iapply guar_elim_later_guar P G₂ h n σ tp m i Ω W $$ HG
  iframe

/-- Universal quantification over any type. -/
@[lantana_alias guar_forall]
theorem guar_all {X : Type _} (P : X → IProp GF) (G : X → TrSpec Expr State GF) :
    (∀ x, P x ⊨ₜ G x) ⊢ iprop(∀ x, P x) ⊨ₜ TrSpec.all G := by
  iintro #HG
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, MI, HP⟩
  iapply record_all
  iintro %x
  iapply guar_elim (P x) (G x) h n σ tp m i Ω W $$ HG
  iframe HI MI
  iapply HP

/-- Trace-visible existential quantification, over small types. -/
@[lantana_alias guar_exist]
theorem guar_ex {X : Type _} [SIdxLarge SI X] (P : X → IProp GF) (G : X → TrSpec Expr State GF) :
    (∀ x, P x ⊨ₜ G x) ⊢ iprop(∃ x, P x) ⊨ₜ TrSpec.ex G := by
  iintro #HG
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, MI, %x, HP⟩
  iapply record_mono (G := G x) (fun τ => exists_intro (Ψ := fun x => (G x).internal τ) x)
  iapply guar_elim (P x) (G x) h n σ tp m i Ω W $$ HG
  iframe

/-- A ghost existential: the witness is not trace-visible. -/
@[lantana_alias guar_exist_ghost]
theorem guar_ex_ghost {X : Type _} (P : X → IProp GF) :
    (∀ x, P x ⊨ₜ G) ⊢ iprop(∃ x, P x) ⊨ₜ G := by
  iintro #HG
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, MI, %x, HP⟩
  iapply guar_elim (P x) G h n σ tp m i Ω W $$ HG
  iframe

/-- An iProp carrying its own guarantee: such pairs can be stored in invariants and saved
propositions, and quantified over. -/
@[lantana_alias guar_packed]
theorem guar_packed (G : TrSpec Expr State GF) :
    ⊢@{IProp GF} iprop(∃ P : IProp GF, P ∗ (P ⊨ₜ G)) ⊨ₜ G := by
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, MI, %P, HP, #HG⟩
  iapply guar_elim P G h n σ tp m i Ω W $$ HG
  iframe

@[lantana_alias guar_persistently]
theorem guar_persistently : (P ⊨ₜ G) ⊢ iprop(□ P) ⊨ₜ G := by
  iintro #HG
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, MI, #HP⟩
  iapply guar_elim P G h n σ tp m i Ω W $$ HG
  iframe HI MI
  iexact HP

/-- A persistent token `C` excluding `A`: a guarantee of `B` is one of `A ∨ B`. -/
@[lantana_alias guar_or_excl]
theorem guar_or_excl (A B C : IProp GF) [Persistent C] (hexcl : C ∗ A ⊢ False) :
    C ⊢ (B ⊨ₜ G) -∗ iprop(A ∨ B) ⊨ₜ G := by
  iintro #HC #HB
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, MI, HA | HB'⟩
  · iexfalso
    iapply hexcl
    isplitr [HA]
    · iexact HC
    · iexact HA
  · iapply guar_elim B G h n σ tp m i Ω W $$ HB
    iframe

/-! ## Implications

The antecedent of `A →ₛ G` is read on the trace (`TrSpec.imp`), so `A →ₛ G` is `¬A ∨ G`
(`TrSpec.imp_or_not`), a statement about traces: the general way to export one is the cast of
a guarantee (`guar_cast`) after trace-level reasoning. The rules below stay in the logic and
produce `TrSpec.imp` itself: from a complete antecedent (`guar_imp_intro`), by weakening
(`guar_imp_weaken`), and for a pure antecedent of an iProp implication (`guar_imp`). -/

@[lantana_alias guar_impl_intro]
theorem guar_imp_intro (A : TrSpec Expr State GF) [TrSpec.Complete A] (h : (A ∧ₛ H) ⊑ₛ G) :
    (P ⊨ₜ H) ⊢ P ⊨ₜ (A →ₛ G) :=
  guar_weaken (TrSpec.imp_intro h)

@[lantana_alias guar_impl_weaken]
theorem guar_imp_weaken (A : TrSpec Expr State GF) : (P ⊨ₜ G) ⊢ P ⊨ₜ (A →ₛ G) :=
  guar_weaken TrSpec.imp_intro_le

/-- A pure antecedent is decided outside the logic (classical). -/
@[lantana_alias guar_impl]
theorem guar_imp (φ : Prop) : (P ⊨ₜ G) ⊢ iprop(⌜φ⌝ → P) ⊨ₜ (⌜φ⌝ₛ →ₛ G) := by
  by_cases hφ : φ
  · refine .trans ?_ (guar_imp_weaken ⌜φ⌝ₛ)
    iintro #HG
    iapply guar_mono $$ [] HG
    imodintro
    iintro HP
    iapply HP
    ipureintro
    exact hφ
  · refine .trans ?_ (guar_weaken (G := TrSpec.true) fun τ =>
      BI.imp_intro (pure_elim _ and_elim_r fun h => absurd h hφ))
    exact (true_intro).trans guar_true

end Rules

end Lantana
