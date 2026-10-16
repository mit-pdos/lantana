/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TrSpec
public import Lantana.ProgramLogic.WeakestPre

/-! # Temporal guarantees `P ⊨ₜ G`

Rocq `lantana/trace/guarantee.v` and `guarantee_rules.v`: a persistent guarantee `P ⊨ₜ G`
states that whenever `P` holds, the rest of the execution satisfies the trace specification
`G`. Guarantees are inferred from the shape of `P` (`GuarOf`) and checked against a target
(`IntoGuar`); `TrSpec.canon P` is the canonical (strongest) specification guaranteed by `P`.

**Skeleton (M1):** `Guar` is opaque (its definition through records, certificates, bundles and
the one-step property `sysStep` comes with the adequacy proof, M6); the rules are `sorry`.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open scoped Lantana.TrSpec Lantana.TrProp

variable {Expr State : Type} {GF : BundledGFunctors}
variable [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF] [TlcGS GF]
  [BIFUpdate (IProp GF)]

/-- `P ⊨ₜ G`: whenever `P` holds, the rest of the execution satisfies `G`. (The instance
arguments are bound explicitly: an `opaque` includes only the variables its type mentions.) -/
@[lantana_alias guar]
opaque Guar [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF] [TlcGS GF]
    [BIFUpdate (IProp GF)] (P : IProp GF) (G : TrSpec Expr State GF) : IProp GF

scoped infix:25 " ⊨ₜ " => Guar

instance Guar.persistent (P : IProp GF) (G : TrSpec Expr State GF) : Persistent (P ⊨ₜ G) := sorry

instance Guar.ne (G : TrSpec Expr State GF) : OFE.NonExpansive (fun P : IProp GF => P ⊨ₜ G) :=
  sorry

/-! ## Rules -/

section Rules
variable {P Q : IProp GF} {G G₁ G₂ H : TrSpec Expr State GF}

@[lantana_alias guar_weaken]
theorem guar_weaken (h : G ⊑ₛ H) : (P ⊨ₜ G) ⊢ P ⊨ₜ H := sorry

/-- Exporting trace-level consequences. -/
@[lantana_alias guar_cast]
theorem guar_cast (R : TrProp Expr State) (pf : G.external ⊆ R) : (P ⊨ₜ G) ⊢ P ⊨ₜ G.cast R pf :=
  sorry

@[lantana_alias guar_mono]
theorem guar_mono : □ (Q -∗ P) ⊢ (P ⊨ₜ G) -∗ Q ⊨ₜ G := sorry

@[lantana_alias guar_true]
theorem guar_true : ⊢@{IProp GF} P ⊨ₜ TrSpec.true (Expr := Expr) (State := State) := sorry

@[lantana_alias guar_pure]
theorem guar_pure (φ : Prop) :
    ⊢@{IProp GF} iprop(⌜φ⌝) ⊨ₜ TrSpec.pure (Expr := Expr) (State := State) φ := sorry

@[lantana_alias guar_and]
theorem guar_and : (P ⊨ₜ G₁) ⊢ (Q ⊨ₜ G₂) -∗ iprop(P ∧ Q) ⊨ₜ (G₁ ∧ₛ G₂) := sorry

@[lantana_alias guar_sep]
theorem guar_sep : (P ⊨ₜ G₁) ⊢ (Q ⊨ₜ G₂) -∗ iprop(P ∗ Q) ⊨ₜ (G₁ ∧ₛ G₂) := sorry

@[lantana_alias guar_or]
theorem guar_or : (P ⊨ₜ G₁) ⊢ (Q ⊨ₜ G₂) -∗ iprop(P ∨ Q) ⊨ₜ (G₁ ∨ₛ G₂) := sorry

/-- An until fulfilled now (rank `0`; the until's step strips the later). -/
@[lantana_alias guar_until_now]
theorem guar_until_now : ▷ (P ⊨ₜ G₂) ⊢ P ⊨ₜ (G₁ 𝒰ₛ G₂) := sorry

@[lantana_alias guar_forall]
theorem guar_all {X : Type _} (P : X → IProp GF) (G : X → TrSpec Expr State GF) :
    (∀ x, P x ⊨ₜ G x) ⊢ iprop(∀ x, P x) ⊨ₜ TrSpec.all G := sorry

@[lantana_alias guar_exist]
theorem guar_ex {X : Type _} [SIdxLarge SI X] (P : X → IProp GF) (G : X → TrSpec Expr State GF) :
    (∀ x, P x ⊨ₜ G x) ⊢ iprop(∃ x, P x) ⊨ₜ TrSpec.ex G := sorry

/-- A ghost existential: the witness is not trace-visible. -/
@[lantana_alias guar_exist_ghost]
theorem guar_ex_ghost {X : Type _} (P : X → IProp GF) :
    (∀ x, P x ⊨ₜ G) ⊢ iprop(∃ x, P x) ⊨ₜ G := sorry

@[lantana_alias guar_persistently]
theorem guar_persistently : (P ⊨ₜ G) ⊢ iprop(□ P) ⊨ₜ G := sorry

@[lantana_alias guar_impl]
theorem guar_imp (φ : Prop) : (P ⊨ₜ G) ⊢ iprop(⌜φ⌝ → P) ⊨ₜ (⌜φ⌝ₛ →ₛ G) := sorry

end Rules

/-! ## The canonical specification -/

/-- The canonical specification guaranteed by `Q`: the meet of all specifications validly
guaranteed by `Q`. -/
@[lantana_alias trSpec_canon]
def TrSpec.canon (Q : IProp GF) : TrSpec Expr State GF :=
  TrSpec.all fun G : { G : TrSpec Expr State GF // ⊢ Q ⊨ₜ G } => G.1

@[lantana_alias guar_canon]
theorem guar_canon (Q : IProp GF) :
    ⊢@{IProp GF} Q ⊨ₜ TrSpec.canon (Expr := Expr) (State := State) Q := sorry

@[lantana_alias trSpec_canon_le]
theorem TrSpec.canon_le {Q : IProp GF} {G : TrSpec Expr State GF} (h : ⊢ Q ⊨ₜ G) :
    TrSpec.canon Q ⊑ₛ G := sorry

@[lantana_alias guar_canon_complete]
theorem guar_canon_complete (Q : IProp GF) (G : TrSpec Expr State GF) :
    (⊢ Q ⊨ₜ G) ↔ TrSpec.canon Q ⊑ₛ G := sorry

/-! ## State facts -/

/-- `StateFact P φ`: the state interpretation and `P` determine the state predicate `φ`; the
atoms of trace properties. -/
@[lantana_alias StateFact]
class StateFact (P : IProp GF) (φ : outParam (State → ThreadPool Expr → Prop)) : Prop where
  state_fact : ∀ (σ : State) (tp : ThreadPool Expr), stateInterp σ tp ∗ P ⊢ ⌜φ σ tp⌝

@[lantana_alias guar_state_fact]
theorem guar_state_fact (P : IProp GF) (φ : State → ThreadPool Expr → Prop) [StateFact P φ] :
    ⊢@{IProp GF} P ⊨ₜ TrSpec.state φ := sorry

/-! ## Inference (D21): `GuarOf` infers from the shape, `IntoGuar` checks against a target -/

/-- The specification inferred from the shape of `P`. -/
class GuarOf (P : IProp GF) (G : outParam (TrSpec Expr State GF)) : Prop where
  guar_of : ⊢ P ⊨ₜ G

/-- `P` guarantees the given `G`. -/
@[lantana_alias IntoGuar]
class IntoGuar (P : IProp GF) (G : TrSpec Expr State GF) : Prop where
  into_guar : ⊢ P ⊨ₜ G

instance (priority := low) intoGuar_of_guarOf (P : IProp GF) (G : TrSpec Expr State GF)
    [GuarOf P G] : IntoGuar P G := ⟨GuarOf.guar_of⟩

instance (priority := low) guarOf_default (P : IProp GF) : GuarOf P (TrSpec.true (Expr := Expr) (State := State)) :=
  ⟨guar_true⟩

end Lantana
