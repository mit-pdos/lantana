/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TemporalFormulaRules

/-! # Inferring guarantees

Rocq `lantana/trace/guarantee_infer.v` (D21). The guarantee of a formula is computed from its
shape by instance resolution, with the two classes of `Lantana.Trace.GuaranteeRules`:
`GuarOf P G` infers the specification `G` (an `outParam`) of `P`, and `IntoGuar P G` checks `P`
against a given `G`; both fall back to `TrSpec.true`. This file completes the inference
instances of `GuaranteeRules` and `TemporalFormulaRules` (existentials, implications, universals,
`□`, the big separating conjunctions, the forms of the temporal formulas with explicit readings)
and gives the checking instances, which follow the shape of the target.

Existentials (Rocq `SimplExist`). When inferring, the guarantee `Gx x` of the body of `∃ x, P x`
is inferred for a generic witness, then `SimplEx Gx G` collapses the family: to its value if
it does not depend on the witness (a ghost existential, over any type), else to `TrSpec.ex Gx`
if the type has the existential property of the step index (`SIdxLarge SI X`, every type up to
`Type 3`: `Nat`, `Fuel`, ghost names, finite maps, but not `IProp GF : Type 4`), else to
`TrSpec.true`. When checking, an existential is trace-visible exactly when the target is a
`TrSpec.ex` over the same type, and ghost otherwise.

`trSpecOf P` and `trOf P` (Rocq's `trSpec_of`/`tr_of` tactics) read the inferred specification
and trace property: they reduce to closed terms, which `rfl` checks (the unit checks below).
`IntoTrace P R` (`trCanon P ⊆ R`) is the form adequacy takes; its trace property is computed
through `TrSpec.Ext`, which reads `TrSpec.canon P` through `GuarOf` (`TrSpec.ext_canon`).

The unit checks of the Rocq file close the file, with the unsoundness of a naive rule for
iProp implications (`naiveImpRule_unsound`).
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open Lantana.Model
open Iris.Std LawfulPartialMap
open scoped Lantana.TrSpec Lantana.TrProp

universe u

variable {Expr State Val : Type} {GF : BundledGFunctors} [Language Expr State Val]
-- Named, to be passed explicitly to `TrSpec.canon_le`.
variable [instM : ModelGS GF] [instT : TemporalGS Expr State GF] [StateInterp Expr State GF]

#lantana_ignore trSpec_inferred "`trSpecOf`."
#lantana_ignore trSpec_of "A tactic; `trSpecOf P` reduces to the inferred specification."
#lantana_ignore tr_inferred "`trOf`."
#lantana_ignore tr_of "A tactic; `trOf P` reduces to the inferred trace property."
#lantana_ignore evar_headed "A tactic for Rocq's hints; `GuarOf` has an `outParam` instead."
#lantana_ignore IntoGuarExist "`guarOf_ex` (inference) and the checking instances `intoGuar_ex_*`."
#lantana_ignore IntoGuarExistCheck "The checking instances `intoGuar_ex_visible/ghost`."
#lantana_ignore into_guar_exist_body "The field of `IntoGuarExist`."
#lantana_ignore into_guar_exist_check_body "The field of `IntoGuarExistCheck`."
#lantana_ignore into_guar_exist_check "Checking is `IntoGuar` itself."
#lantana_ignore into_guar_exist "`guarOf_ex` and `intoGuar_ex_visible/ghost`."

attribute [lantana_alias into_guar_default] guarOf_default

/-! ## Existentials -/

section Exist

/-- A ghost existential over any type (`guar_ex_ghost` is over `Type`s). -/
theorem guar_ex_ghost_sort {X : Sort u} (P : X → IProp GF) (G : TrSpec Expr State GF) :
    (∀ x, P x ⊨ₜ G) ⊢ iprop(∃ x, P x) ⊨ₜ G := by
  iintro #HG
  iapply guar_intro
  imodintro
  iintro %h %n %σ %tp %m %i %Ω %W ⟨HI, MI, %x, HP⟩
  iapply guar_elim (P x) G h n σ tp m i Ω W $$ HG
  iframe

/-- How an existential over a family of guarantees is guaranteed, when inferring. -/
@[lantana_alias SimplExist]
class SimplEx {X : Sort u} (G : X → TrSpec Expr State GF)
    (G' : outParam (TrSpec Expr State GF)) : Prop where
  simpl_ex (P : X → IProp GF) : (∀ x, P x ⊨ₜ G x) ⊢ iprop(∃ x, P x) ⊨ₜ G'

attribute [lantana_alias simpl_exist] SimplEx.simpl_ex

/-- The guarantee of the body does not depend on the witness: a ghost existential. -/
@[lantana_alias simpl_exist_ghost]
instance (priority := high) simplEx_ghost {X : Sort u} (G : TrSpec Expr State GF) :
    SimplEx (fun _ : X => G) G :=
  ⟨fun P => guar_ex_ghost_sort P G⟩

/-- It does, over a type with the existential property: a trace-visible existential. -/
@[lantana_alias simpl_exist_visible]
instance simplEx_visible {X : Type u} (G : X → TrSpec Expr State GF) [SIdxLarge SI X] :
    SimplEx G (TrSpec.ex G) :=
  ⟨fun P => guar_ex P G⟩

/-- Total, so that inference never backtracks into the body. -/
@[lantana_alias simpl_exist_true]
instance (priority := low) simplEx_true {X : Sort u} (G : X → TrSpec Expr State GF) :
    SimplEx G TrSpec.true :=
  ⟨fun _ => true_intro.trans guar_true⟩

/-- Inference: the body's guarantee for a generic witness, collapsed by `SimplEx`. -/
@[lantana_alias into_guar_exist_infer]
instance guarOf_ex {X : Sort u} (P : X → IProp GF) (Gx : X → TrSpec Expr State GF)
    (G : TrSpec Expr State GF) [h : ∀ x, GuarOf (P x) (Gx x)] [SimplEx Gx G] :
    GuarOf iprop(∃ x, P x) G :=
  ⟨(forall_intro fun x => (h x).guar_of).trans (SimplEx.simpl_ex P)⟩

/-- Checking against an existential over the same type: trace-visible. -/
@[lantana_alias into_guar_exist_visible_check]
instance intoGuar_ex_visible {X : Type u} (P : X → IProp GF) (G : X → TrSpec Expr State GF)
    [h : ∀ x, IntoGuar (P x) (G x)] [SIdxLarge SI X] : IntoGuar iprop(∃ x, P x) (TrSpec.ex G) :=
  ⟨(forall_intro fun x => (h x).into_guar).trans (guar_ex P G)⟩

/-- Checking against any other target: ghost. -/
@[lantana_alias into_guar_exist_ghost_check]
instance (priority := mid) intoGuar_ex_ghost {X : Sort u} (P : X → IProp GF)
    (G : TrSpec Expr State GF) [h : ∀ x, IntoGuar (P x) G] : IntoGuar iprop(∃ x, P x) G :=
  ⟨(forall_intro fun x => (h x).into_guar).trans (guar_ex_ghost_sort P G)⟩

end Exist

/-! ## Inference: the remaining connectives and the temporal formulas -/

section Infer
variable {N : Namespace} {k : Oid} {q : Qp} {P Q : IProp GF}

instance guarOf_imp (φ : Prop) (G : TrSpec Expr State GF) [GuarOf P G] :
    GuarOf iprop(⌜φ⌝ → P) (⌜φ⌝ₛ →ₛ G) :=
  ⟨GuarOf.guar_of.trans (guar_imp φ)⟩

instance guarOf_all {X : Type u} (P : X → IProp GF) (G : X → TrSpec Expr State GF)
    [h : ∀ x, GuarOf (P x) (G x)] : GuarOf iprop(∀ x, P x) (TrSpec.all G) :=
  ⟨(forall_intro fun x => (h x).guar_of).trans (guar_all P G)⟩

instance guarOf_persistently (G : TrSpec Expr State GF) [GuarOf P G] :
    GuarOf iprop(□ P) G :=
  ⟨GuarOf.guar_of.trans guar_persistently⟩

instance guarOf_alwaysIGuar (G : TrSpec Expr State GF) :
    GuarOf (alwaysIGuar N P G) (□ₛ G) :=
  ⟨guar_alwaysIGuar⟩

instance guarOf_alwaysIAs (V : IProp GF) (G : TrSpec Expr State GF) [GuarOf V G] :
    GuarOf (alwaysIAs (Expr := Expr) (State := State) N P V) (□ₛ G) :=
  ⟨guar_alwaysIAs_valid GuarOf.guar_of⟩

instance guarOf_untilIGuar (G₁ G₂ : TrSpec Expr State GF) :
    GuarOf (untilIGuar N k q P Q G₁ G₂) (G₁ 𝒰ₛ G₂) :=
  ⟨guar_untilIGuar⟩

/-- A finally is inferred as such (`finallyI` is not unfolded by instance resolution). -/
instance guarOf_finallyI (G : TrSpec Expr State GF) [GuarOf Q G] :
    GuarOf (finallyI (Expr := Expr) (State := State) N k q Q) (◇ₛ G) :=
  ⟨guar_untilI_valid guar_true GuarOf.guar_of⟩

/-- A done until has no left formula: it is inferred as a finally. -/
instance guarOf_untilIDoneGuar (G₂ : TrSpec Expr State GF) :
    GuarOf (untilIDoneGuar k Q G₂) (◇ₛ G₂) :=
  ⟨guar_untilIDoneGuar TrSpec.true G₂⟩

instance guarOf_bigSepL {A : Type _} (l : List A) (Φ : Nat → A → IProp GF)
    (G : Nat → A → TrSpec Expr State GF) [h : ∀ k x, GuarOf (Φ k x) (G k x)] :
    GuarOf iprop([∗list] k ↦ x ∈ l, Φ k x) (∀ₛ k, ∀ₛ x, (⌜l[k]? = some x⌝ₛ →ₛ G k x)) :=
  ⟨(forall_intro fun k => forall_intro fun x => (h k x).guar_of).trans (guar_bigSepL l Φ G)⟩

instance guarOf_bigSepM {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K] (m : M V)
    (Φ : K → V → IProp GF) (G : K → V → TrSpec Expr State GF)
    [h : ∀ k x, GuarOf (Φ k x) (G k x)] :
    GuarOf iprop([∗map] k ↦ x ∈ m, Φ k x) (∀ₛ k, ∀ₛ x, (⌜get? m k = some x⌝ₛ →ₛ G k x)) :=
  ⟨(forall_intro fun k => forall_intro fun x => (h k x).guar_of).trans (guar_bigSepM m Φ G)⟩

instance guarOf_bigSepS {S A : Type _} [LawfulFiniteSet S A] (X : S) (Φ : A → IProp GF)
    (G : A → TrSpec Expr State GF) [h : ∀ x, GuarOf (Φ x) (G x)] :
    GuarOf iprop([∗set] x ∈ X, Φ x) (∀ₛ x, (⌜x ∈ X⌝ₛ →ₛ G x)) :=
  ⟨(forall_intro fun x => (h x).guar_of).trans (guar_bigSepS X Φ G)⟩

end Infer

/-! ## Checking against a target

The instances follow the shape of the target; the fallback is inference
(`intoGuar_of_guarOf`). -/

section Check
variable {N : Namespace} {k : Oid} {q : Qp} {P Q : IProp GF}

/-- The canonical specification is always guaranteed. -/
instance intoGuar_canon : IntoGuar P (TrSpec.canon (Expr := Expr) (State := State) P) :=
  ⟨guar_canon P⟩

@[lantana_alias into_guar_pure]
instance intoGuar_pure (φ : Prop) :
    IntoGuar (iprop(⌜φ⌝) : IProp GF) (TrSpec.pure (Expr := Expr) (State := State) φ) :=
  ⟨guar_pure φ⟩

@[lantana_alias into_guar_sep]
instance intoGuar_sep (G₁ G₂ : TrSpec Expr State GF) [IntoGuar P G₁] [IntoGuar Q G₂] :
    IntoGuar iprop(P ∗ Q) (G₁ ∧ₛ G₂) :=
  ⟨(IntoGuar.into_guar (P := Q)).trans
    (wand_entails ((IntoGuar.into_guar (P := P)).trans guar_sep))⟩

@[lantana_alias into_guar_and]
instance intoGuar_and (G₁ G₂ : TrSpec Expr State GF) [IntoGuar P G₁] [IntoGuar Q G₂] :
    IntoGuar iprop(P ∧ Q) (G₁ ∧ₛ G₂) :=
  ⟨(IntoGuar.into_guar (P := Q)).trans
    (wand_entails ((IntoGuar.into_guar (P := P)).trans guar_and))⟩

@[lantana_alias into_guar_or]
instance intoGuar_or (G₁ G₂ : TrSpec Expr State GF) [IntoGuar P G₁] [IntoGuar Q G₂] :
    IntoGuar iprop(P ∨ Q) (G₁ ∨ₛ G₂) :=
  ⟨(IntoGuar.into_guar (P := Q)).trans
    (wand_entails ((IntoGuar.into_guar (P := P)).trans guar_or))⟩

@[lantana_alias into_guar_impl]
instance intoGuar_imp (φ : Prop) (G : TrSpec Expr State GF) [IntoGuar P G] :
    IntoGuar iprop(⌜φ⌝ → P) (⌜φ⌝ₛ →ₛ G) :=
  ⟨IntoGuar.into_guar.trans (guar_imp φ)⟩

@[lantana_alias into_guar_forall]
instance intoGuar_all {X : Type u} (P : X → IProp GF) (G : X → TrSpec Expr State GF)
    [h : ∀ x, IntoGuar (P x) (G x)] : IntoGuar iprop(∀ x, P x) (TrSpec.all G) :=
  ⟨(forall_intro fun x => (h x).into_guar).trans (guar_all P G)⟩

@[lantana_alias into_guar_persistently]
instance intoGuar_persistently (G : TrSpec Expr State GF) [IntoGuar P G] :
    IntoGuar iprop(□ P) G :=
  ⟨IntoGuar.into_guar.trans guar_persistently⟩

/-- A finally target, as the until of `TrSpec.true` (`◇ₛ` is not unfolded by instance
resolution). -/
instance intoGuar_eventually (G : TrSpec Expr State GF) [IntoGuar P (TrSpec.true 𝒰ₛ G)] :
    IntoGuar P (◇ₛ G) :=
  ⟨IntoGuar.into_guar (G := TrSpec.true 𝒰ₛ G)⟩

@[lantana_alias into_guar_alwaysI_guar]
instance intoGuar_alwaysIGuar (G : TrSpec Expr State GF) :
    IntoGuar (alwaysIGuar N P G) (□ₛ G) :=
  ⟨guar_alwaysIGuar⟩

@[lantana_alias into_guar_alwaysI_as]
instance intoGuar_alwaysIAs (V : IProp GF) (G : TrSpec Expr State GF) [IntoGuar V G] :
    IntoGuar (alwaysIAs (Expr := Expr) (State := State) N P V) (□ₛ G) :=
  ⟨guar_alwaysIAs_valid IntoGuar.into_guar⟩

@[lantana_alias into_guar_alwaysI]
instance intoGuar_alwaysI (G : TrSpec Expr State GF) [IntoGuar P G] :
    IntoGuar (alwaysI (Expr := Expr) (State := State) N P) (□ₛ G) :=
  ⟨guar_alwaysI_valid IntoGuar.into_guar⟩

@[lantana_alias into_guar_untilI_guar]
instance intoGuar_untilIGuar (G₁ G₂ : TrSpec Expr State GF) :
    IntoGuar (untilIGuar N k q P Q G₁ G₂) (G₁ 𝒰ₛ G₂) :=
  ⟨guar_untilIGuar⟩

@[lantana_alias into_guar_untilI]
instance intoGuar_untilI (G₁ G₂ : TrSpec Expr State GF) [IntoGuar P G₁] [IntoGuar Q G₂] :
    IntoGuar (untilI (Expr := Expr) (State := State) N k q P Q) (G₁ 𝒰ₛ G₂) :=
  ⟨guar_untilI_valid IntoGuar.into_guar IntoGuar.into_guar⟩

instance intoGuar_finallyI (G₁ G₂ : TrSpec Expr State GF) [IntoGuar iprop(True) G₁]
    [IntoGuar Q G₂] : IntoGuar (finallyI (Expr := Expr) (State := State) N k q Q) (G₁ 𝒰ₛ G₂) :=
  ⟨guar_untilI_valid IntoGuar.into_guar IntoGuar.into_guar⟩

/-- A done until, against an until with any left formula. -/
@[lantana_alias into_guar_untilI_done_guar]
instance intoGuar_untilIDoneGuar (G₁ G₂ : TrSpec Expr State GF) :
    IntoGuar (untilIDoneGuar k Q G₂) (G₁ 𝒰ₛ G₂) :=
  ⟨guar_untilIDoneGuar G₁ G₂⟩

@[lantana_alias into_guar_untilI_done]
instance intoGuar_untilIDone (G₁ G₂ : TrSpec Expr State GF) [IntoGuar Q G₂] :
    IntoGuar (untilIDone (Expr := Expr) (State := State) k Q) (G₁ 𝒰ₛ G₂) :=
  ⟨guar_untilIDone_valid G₁ IntoGuar.into_guar⟩

/-- A state fact guarantees its state atom. -/
@[lantana_alias into_guar_state_fact]
instance intoGuar_stateFact (φ : State → ThreadPool Expr → Prop) [StateFact P φ] :
    IntoGuar P (TrSpec.state φ) :=
  ⟨guar_state_fact P φ⟩

@[lantana_alias into_guar_big_sepL]
instance intoGuar_bigSepL {A : Type _} (l : List A) (Φ : Nat → A → IProp GF)
    (G : Nat → A → TrSpec Expr State GF) [h : ∀ k x, IntoGuar (Φ k x) (G k x)] :
    IntoGuar iprop([∗list] k ↦ x ∈ l, Φ k x) (∀ₛ k, ∀ₛ x, (⌜l[k]? = some x⌝ₛ →ₛ G k x)) :=
  ⟨(forall_intro fun k => forall_intro fun x => (h k x).into_guar).trans (guar_bigSepL l Φ G)⟩

@[lantana_alias into_guar_big_sepM]
instance intoGuar_bigSepM {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K] (m : M V)
    (Φ : K → V → IProp GF) (G : K → V → TrSpec Expr State GF)
    [h : ∀ k x, IntoGuar (Φ k x) (G k x)] :
    IntoGuar iprop([∗map] k ↦ x ∈ m, Φ k x) (∀ₛ k, ∀ₛ x, (⌜get? m k = some x⌝ₛ →ₛ G k x)) :=
  ⟨(forall_intro fun k => forall_intro fun x => (h k x).into_guar).trans (guar_bigSepM m Φ G)⟩

@[lantana_alias into_guar_big_sepS]
instance intoGuar_bigSepS {S A : Type _} [LawfulFiniteSet S A] (X : S) (Φ : A → IProp GF)
    (G : A → TrSpec Expr State GF) [h : ∀ x, IntoGuar (Φ x) (G x)] :
    IntoGuar iprop([∗set] x ∈ X, Φ x) (∀ₛ x, (⌜x ∈ X⌝ₛ →ₛ G x)) :=
  ⟨(forall_intro fun x => (h x).into_guar).trans (guar_bigSepS X Φ G)⟩

end Check

/-! ## Reading the inferred specification -/

section Read

/-- The specification inferred for `P` (Rocq `trSpec_inferred`, read with `trSpec_of`): it
reduces to a closed term, which no longer mentions the instance of `GuarOf`. -/
abbrev trSpecOf (P : IProp GF) {G : TrSpec Expr State GF} [GuarOf P G] : TrSpec Expr State GF :=
  G

@[lantana_alias guar_inferred]
theorem guar_trSpecOf (P : IProp GF) {G : TrSpec Expr State GF} [GuarOf P G] :
    ⊢ P ⊨ₜ trSpecOf P (G := G) :=
  GuarOf.guar_of

/-- `TrSpec.true` reads as `⌜True⌝ₜ`. -/
instance TrSpec.ext_true :
    TrSpec.Ext (TrSpec.true (Expr := Expr) (State := State) (GF := GF)) ⌜True⌝ₜ :=
  ⟨TrProp.le_refl _⟩

/-- The trace reading of the canonical specification of `P`, through its inferred
specification. -/
@[lantana_alias trSpec_ext_canon]
instance TrSpec.ext_canon (P : IProp GF) (G : TrSpec Expr State GF) (R : TrProp Expr State)
    [GuarOf P G] [TrSpec.Ext G R] : TrSpec.Ext (TrSpec.canon P) R :=
  ⟨fun _ hτ => TrSpec.Ext.ext_of (G := G) _ (TrSpec.canon_external GuarOf.guar_of hτ)⟩

/-- `P` guarantees the trace property `R`: the form adequacy takes. -/
@[lantana_alias IntoTrace]
class IntoTrace (P : IProp GF) (R : outParam (TrProp Expr State)) : Prop where
  into_trace : trCanon (Expr := Expr) (State := State) P ⊆ R

attribute [lantana_alias into_trace] IntoTrace.into_trace

@[lantana_alias into_trace_of]
instance intoTrace_of (P : IProp GF) (G : TrSpec Expr State GF) (R : TrProp Expr State)
    [GuarOf P G] [TrSpec.Ext G R] : IntoTrace P R :=
  ⟨(trCanon_le P R).mpr ⟨G, GuarOf.guar_of, TrSpec.Ext.ext_of⟩⟩

/-- The trace property inferred for `P` (Rocq `tr_inferred`, read with `tr_of`). -/
abbrev trOf (P : IProp GF) {R : TrProp Expr State} [IntoTrace P R] : TrProp Expr State := R

end Read

/-! ## Examples and unit checks -/

namespace GuaranteeInfer

section Examples
variable {E : CoPset} {N N₁ N₂ : Namespace} {k : Oid}

/-- Ghost quantification over iProp, scoping over two temporal operators. -/
@[lantana_alias ex_iprop]
theorem ex_iprop :
    ⊢@{IProp GF} iprop(∃ Ψ : IProp GF, alwaysI (Expr := Expr) (State := State) N₁ Ψ ∗
      finallyI (Expr := Expr) (State := State) N₂ k 1 Ψ) ⊨ₜ (□ₛ TrSpec.true ∧ₛ ◇ₛ TrSpec.true) :=
  (forall_intro fun Ψ => (guar_untilI_valid (N := N₂) (k := k) (q := 1) (P := iprop(True))
      (Q := Ψ) guar_true guar_true).trans
    (wand_entails ((guar_alwaysI_valid (N := N₁) (P := Ψ) guar_true).trans guar_sep))).trans
    (guar_ex_ghost _)

/-- An invariant whose content changes over time, each content carrying its own guarantee. -/
@[lantana_alias ex_dynamic_inv]
theorem ex_dynamic_inv (G : TrSpec Expr State GF) :
    ⊢@{IProp GF} alwaysI N iprop(∃ P : IProp GF, P ∗ (P ⊨ₜ G)) ⊨ₜ □ₛ G :=
  guar_alwaysI_valid (guar_packed G)

/-- The same guarantee as `ex_iprop`, inferred (Rocq writes the finally as the until of
`trSpec_pure True`, which `◇ₛ` is by definition). -/
@[lantana_alias ex_iprop_inferred]
theorem ex_iprop_inferred :
    ⊢@{IProp GF} iprop(∃ Ψ : IProp GF, alwaysI (Expr := Expr) (State := State) N₁ Ψ ∗
      finallyI (Expr := Expr) (State := State) N₂ k 1 Ψ) ⊨ₜ (□ₛ TrSpec.true ∧ₛ ◇ₛ TrSpec.true) :=
  GuarOf.guar_of

/-- Trace-visible quantification over a small type is inferred when the guarantee of the body
depends on the witness. -/
@[lantana_alias ex_visible_inferred]
theorem ex_visible_inferred (f : Nat → Prop) :
    ⊢@{IProp GF} iprop(∃ n : Nat, alwaysI (Expr := Expr) (State := State) N iprop(⌜f n⌝)) ⊨ₜ
      TrSpec.ex fun n : Nat => □ₛ ⌜f n⌝ₛ :=
  GuarOf.guar_of

/-- The inferred trace specification as a closed term. -/
@[lantana_alias ex_trSpec_of]
def exTrSpecOf (N₁ N₂ : Namespace) (k : Oid) : TrSpec Expr State GF :=
  trSpecOf iprop(∃ Ψ : IProp GF, alwaysI (Expr := Expr) (State := State) N₁ Ψ ∗
    finallyI (Expr := Expr) (State := State) N₂ k 1 Ψ)

@[lantana_alias ex_trSpec_of_eq]
theorem ex_trSpec_of_eq :
    exTrSpecOf (Expr := Expr) (State := State) (GF := GF) N₁ N₂ k =
      (□ₛ TrSpec.true ∧ₛ ◇ₛ TrSpec.true) :=
  rfl

/-- A done until, allocated with its right formula at hand, exports the until of any left
formula in the form the adequacy takes: a formula, its guarantee, and the formula back. -/
@[lantana_alias ex_until_done_export]
theorem ex_until_done_export (p : Parent) (K : Oids) (ℓ : Layer) (μ : Measure) (Q : IProp GF)
    (φ : State → ThreadPool Expr → Prop) [StateFact Q φ] (G₁ : TrSpec Expr State GF) :
    parLe (GF := GF) p ℓ ⊢ Par.kids p K -∗ Q -∗
      |={E}=>m Par.kids p K ∗
        ∃ P : IProp GF, (P ⊨ₜ (G₁ 𝒰ₛ TrSpec.state φ)) ∗ P ∗ (P -∗ Q) := by
  iintro B Kp HQ
  imod Obl.new E p K ℓ μ $$ B Kp with ⟨%k, %hk, Kp, Kk, Oa, -, -⟩
  have hmem : k ∈ K.insert k := Std.ExtTreeSet.mem_insert_self
  have heq : (K.insert k).erase k = K := Std.ExtTreeSet.ext_mem fun a => by
    simp only [Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.mem_insert, ne_eq,
      Std.LawfulEqCmp.compare_eq_iff_eq]
    constructor
    · rintro ⟨hne, h | h⟩
      · exact absurd h hne
      · exact h
    · intro h
      exact ⟨fun hka => by subst hka; exact hk h, .inr h⟩
  have hinit := untilIDone_init (E := E) (Expr := Expr) (State := State) (Q := Q) p
    (K.insert k) hmem
  rw [heq] at hinit
  imod hinit $$ Oa Kp Kk HQ with ⟨U, Kp⟩
  imodintro
  iframe Kp
  iexists untilIDone (Expr := Expr) (State := State) k Q
  iframe U
  isplitl []
  · iapply (IntoGuar.into_guar :
      ⊢ untilIDone (Expr := Expr) (State := State) k Q ⊨ₜ (G₁ 𝒰ₛ TrSpec.state φ))
  · iintro U
    icases untilIDone_elim $$ U with ⟨HQ, -⟩
    iexact HQ

/-- A strong until, once discharged, is a done until with the same guarantee. -/
@[lantana_alias ex_until_discharged]
theorem ex_until_discharged (p : Parent) (K : Oids) (Q : IProp GF)
    (φ : State → ThreadPool Expr → Prop) [StateFact Q φ] (P : IProp GF) (hN : ↑N ⊆ E)
    (hk : k ∈ K) :
    £ₙ 1 ⊢ untilI (Expr := Expr) (State := State) N k 1 P Q -∗ Par.kids p K -∗ oblKids k ∅ -∗
      Q -∗ |={E}=>m ∃ U : IProp GF, (U ⊨ₜ (TrSpec.canon P 𝒰ₛ TrSpec.state φ)) ∗ U ∗
        Par.kids p (K.erase k) := by
  iintro LC HU Kp Kk HQ
  imod untilI_discharge_done hN $$ HU with HU
  iapply lc_mupd_add_later $$ LC
  inext
  icases HU with ⟨-, HU⟩
  imod HU $$ %p %K %hk Kp Kk HQ %(E \ ↑N) with HU
  imod HU with ⟨U, Kp⟩
  imodintro
  iexists untilIDone (Expr := Expr) (State := State) k Q
  iframe U Kp
  iapply (IntoGuar.into_guar :
    ⊢ untilIDone (Expr := Expr) (State := State) k Q ⊨ₜ (TrSpec.canon P 𝒰ₛ TrSpec.state φ))

/-- The inferred specification of a done until is the finally of its right formula. -/
@[lantana_alias ex_trSpec_of_done]
def exTrSpecOfDone (k : Oid) (Q : IProp GF) (φ : State → ThreadPool Expr → Prop)
    [StateFact Q φ] : TrSpec Expr State GF :=
  trSpecOf (untilIDone (Expr := Expr) (State := State) k Q)

@[lantana_alias ex_trSpec_of_done_eq]
theorem ex_trSpec_of_done_eq (Q : IProp GF) (φ : State → ThreadPool Expr → Prop)
    [StateFact Q φ] : exTrSpecOfDone (Expr := Expr) (State := State) k Q φ = ◇ₛ TrSpec.state φ :=
  rfl

@[lantana_alias ex_finally_done]
theorem ex_finally_done (Q : IProp GF) (φ : State → ThreadPool Expr → Prop) [StateFact Q φ] :
    ⊢@{IProp GF} untilIDone (Expr := Expr) (State := State) k Q ⊨ₜ ◇ₛ TrSpec.state φ :=
  IntoGuar.into_guar

/-- A higher-order specification quantifies over the content together with its guarantee (the
guarantee of the content of an `alwaysI` must be valid, not a hypothesis). -/
@[lantana_alias ex_higher_order]
theorem ex_higher_order (G : TrSpec Expr State GF) :
    ⊢@{IProp GF} iprop(∃ P : IProp GF, alwaysI (Expr := Expr) (State := State) N
      iprop(P ∗ (P ⊨ₜ G))) ⊨ₜ □ₛ G := by
  have hP : ∀ P : IProp GF, ⊢ iprop(P ∗ (P ⊨ₜ G)) ⊨ₜ G := fun P => by
    iapply guar_mono (P := iprop(∃ P' : IProp GF, P' ∗ (P' ⊨ₜ G))) $$ []
    · imodintro
      iintro ⟨HP, #HG⟩
      iexists P
      iframe HP HG
    · iapply guar_packed
  exact (forall_intro fun P => guar_alwaysI_valid (hP P)).trans (guar_ex_ghost _)

/-- A temporal antecedent used in the logic: by completeness, the in-logic reading of
"eventually `φ`" strengthens a guarantee. -/
@[lantana_alias ex_impl_guar]
theorem ex_imp_guar (P : IProp GF) (φ : State → ThreadPool Expr → Prop)
    (G : TrSpec Expr State GF) :
    (P ⊨ₜ G) ⊢ P ⊨ₜ (◇ₛ TrSpec.state φ →ₛ (◇ₛ TrSpec.state φ ∧ₛ G)) :=
  guar_imp_intro _ (TrSpec.le_refl _)

/-- The inferred trace property of an iProp, as a trace predicate. -/
@[lantana_alias ex_tr_of]
theorem ex_tr_of :
    trOf iprop(∃ Ψ : IProp GF, alwaysI (Expr := Expr) (State := State) N₁ Ψ ∗
      finallyI (Expr := Expr) (State := State) N₂ k 1 Ψ) = (□ₜ ⌜True⌝ₜ ∧ₜ ◇ₜ ⌜True⌝ₜ) :=
  rfl

/-- An implication exported on traces: the inferred trace property of a case split implies it
(compare `guar_imp`). -/
@[lantana_alias ex_impl_cast]
theorem ex_imp_cast (φ : Prop) (P Q : IProp GF) (G H : TrSpec Expr State GF) [GuarOf P G]
    [GuarOf Q H] :
    trCanon (Expr := Expr) (State := State) iprop((⌜φ⌝ ∗ P) ∨ (⌜¬φ⌝ ∗ Q)) ⊆
      (⌜φ⌝ₜ →ₜ G.external) :=
  TrProp.le_trans IntoTrace.into_trace fun _ h hφ => by
    rcases h with ⟨-, hG⟩ | ⟨hnφ, -⟩
    · exact hG
    · exact absurd hφ hnφ

/-- Unsound: an iProp implication guaranteeing the implication of the guarantees (the
antecedent's resources are not determined by the trace). -/
@[lantana_alias naive_impl_rule_unsound]
theorem naiveImpRule_unsound
    (hrule : ∀ (P₁ P₂ : IProp GF) (G₁ G₂ : TrSpec Expr State GF), (⊢ P₁ ⊨ₜ G₁) →
      (⊢ P₂ ⊨ₜ G₂) → ⊢ iprop(P₁ → P₂) ⊨ₜ (G₁ →ₛ G₂)) :
    ⊢@{IProp GF} iprop(True) ⊨ₜ (TrSpec.true (Expr := Expr) (State := State) →ₛ ⌜False⌝ₛ) := by
  have hF : ∀ G : TrSpec Expr State GF, ⊢ iprop(False) ⊨ₜ G := fun G => by
    iapply guar_intro
    imodintro
    iintro %h %n %σ %tp %m %i %Ω %W ⟨-, -, %hf⟩
    exact hf.elim
  iapply guar_mono (P := iprop(False → False)) $$ []
  · imodintro
    iintro - HF
    iexact HF
  · iapply hrule iprop(False) iprop(False) TrSpec.true ⌜False⌝ₛ guar_true (hF _)

omit instM instT [StateInterp Expr State GF] in
/-- The conclusion of the naive rule holds on no trace. -/
@[lantana_alias trSpec_impl_true_false_empty]
theorem trSpec_imp_true_false_empty (τ : Trace Expr State) :
    ¬ (TrSpec.true (Expr := Expr) (State := State) (GF := GF) →ₛ ⌜False⌝ₛ).external τ :=
  fun h => h trivial

end Examples

end GuaranteeInfer

end Lantana
