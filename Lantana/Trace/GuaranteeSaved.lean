/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.GuaranteeInfer
public import Iris.Instances.Lib.SavedProp
public import Iris.Instances.Lib.GhostMap

/-! # Temporal formulas in ghost state

Rocq `lantana/trace/guarantee_saved.v`: a saved proposition names a temporal formula; stored
with its guarantee, the pair guarantees that property by itself (`savedGuar`). The world
requirement is Iris-Lean's `SavedPropG GF` (Rocq `savedPropG Σ`). Also a ghost map of formulas
chosen at run time, one per request (`requestMapInv`), whose invariant guarantees at all
times the trace property of every registered request: the requests' names are ghost (they do
not show), the map is trace-visible (`RequestMap` is small).
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open Lantana.Model
open Iris.Std LawfulPartialMap
open scoped Lantana.TrSpec Lantana.TrProp

variable {Expr State Val : Type} {GF : BundledGFunctors} [Language Expr State Val]
variable [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF]

/-! ## Saved guarantees -/

section Saved
variable [SavedPropG GF]

/-- `γ` names the temporal formula `P`, which guarantees `G`. -/
@[lantana_alias saved_guar]
def savedGuar (γ : GName) (P : IProp GF) (G : TrSpec Expr State GF) : IProp GF :=
  iprop(saved_prop_own γ .discard P ∗ (P ⊨ₜ G))

@[lantana_alias saved_guar_persistent]
instance savedGuar_persistent (γ : GName) (P : IProp GF) (G : TrSpec Expr State GF) :
    Persistent (savedGuar γ P G) := by
  unfold savedGuar; infer_instance

@[lantana_alias saved_guar_alloc]
theorem savedGuar_alloc (P : IProp GF) (G : TrSpec Expr State GF) :
    (P ⊨ₜ G) ⊢ |==> ∃ γ, savedGuar γ P G := by
  iintro #HG
  imod saved_prop_alloc P .discard DFrac.valid_discard with ⟨%γ, #Hγ⟩
  imodintro
  iexists γ
  unfold savedGuar
  iframe Hγ HG

@[lantana_alias saved_guar_agree]
theorem savedGuar_agree (γ : GName) (P Q : IProp GF) (G G' : TrSpec Expr State GF) :
    savedGuar γ P G ⊢ savedGuar γ Q G' -∗ ▷ internalEq P Q := by
  unfold savedGuar
  iintro ⟨HP, -⟩ ⟨HQ, -⟩
  iapply saved_prop_agree γ .discard .discard P Q
  iframe HP HQ

omit [SavedPropG GF] in
/-- A formula packed with its guarantee guarantees that property. -/
theorem guar_packed_sep (P : IProp GF) (G : TrSpec Expr State GF) :
    ⊢ iprop((P ⊨ₜ G) ∗ P) ⊨ₜ G := by
  iapply guar_mono (P := iprop(∃ P' : IProp GF, P' ∗ (P' ⊨ₜ G))) $$ []
  · imodintro
    iintro ⟨#HG, HP⟩
    iexists P
    iframe HP HG
  · iapply guar_packed

theorem guar_savedGuar_sep (γ : GName) (P : IProp GF) (G : TrSpec Expr State GF) :
    ⊢ iprop(savedGuar γ P G ∗ P) ⊨ₜ G := by
  iapply guar_mono (P := iprop((P ⊨ₜ G) ∗ P)) $$ []
  · imodintro
    iintro ⟨H, HP⟩
    unfold savedGuar
    icases H with ⟨-, #HG⟩
    iframe HP HG
  · iapply guar_packed_sep

/-- Inferred before the guarantee of a separating conjunction (Rocq priority 5). -/
instance (priority := high) guarOf_packed (P : IProp GF) (G : TrSpec Expr State GF) :
    GuarOf iprop((P ⊨ₜ G) ∗ P) G :=
  ⟨guar_packed_sep P G⟩

instance (priority := high) guarOf_savedGuar (γ : GName) (P : IProp GF)
    (G : TrSpec Expr State GF) : GuarOf iprop(savedGuar γ P G ∗ P) G :=
  ⟨guar_savedGuar_sep γ P G⟩

/-- Checked before the guarantee of a separating conjunction (Rocq priority 5). -/
@[lantana_alias into_guar_packed]
instance (priority := high) intoGuar_packed (P : IProp GF) (G : TrSpec Expr State GF) :
    IntoGuar iprop((P ⊨ₜ G) ∗ P) G :=
  ⟨guar_packed_sep P G⟩

@[lantana_alias into_guar_saved_guar]
instance (priority := high) intoGuar_savedGuar (γ : GName) (P : IProp GF)
    (G : TrSpec Expr State GF) : IntoGuar iprop(savedGuar γ P G ∗ P) G :=
  ⟨guar_savedGuar_sep γ P G⟩

end Saved

/-! ## A ghost map of temporal formulas -/

/-- Finite maps from requests (Rocq `gmap nat`). -/
abbrev RequestMap (V : Type _) := Std.ExtTreeMap Nat V compare

section RequestMap
variable [SavedPropG GF] [GhostMapG GF Nat GName RequestMap]

/-- The invariant of a ghost map of requests: each registered request `r` has a formula,
which holds and guarantees `G r`. -/
@[lantana_alias request_map_inv]
def requestMapInv (γm : GName) (G : Nat → TrSpec Expr State GF) : IProp GF :=
  iprop(∃ m : RequestMap GName, (γm ↪●MAP m) ∗
    [∗map] r ↦ γr ∈ m, ∃ P : IProp GF, savedGuar γr P (G r) ∗ P)

/-- Inferred: the requests' names are ghost, the map is trace-visible. -/
@[lantana_alias guar_request_map]
theorem guar_requestMap (N : Namespace) (γm : GName) (G : Nat → TrSpec Expr State GF) :
    ⊢ alwaysI (Expr := Expr) (State := State) N (requestMapInv γm G) ⊨ₜ
      □ₛ (TrSpec.ex fun m : RequestMap GName =>
        TrSpec.true ∧ₛ ∀ₛ r, ∀ₛ γr, (⌜get? m r = some γr⌝ₛ →ₛ G r)) := by
  unfold requestMapInv
  exact IntoGuar.into_guar

/-- Allocation, with no request registered yet: a registered invariant. -/
@[lantana_alias request_map_alloc]
theorem requestMap_alloc (E : CoPset) (N : Namespace) (G : Nat → TrSpec Expr State GF) :
    ⊢ |={E}=>m ∃ γm : GName, alwaysI (Expr := Expr) (State := State) N (requestMapInv γm G) := by
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := GName)
    (H := RequestMap) with ⟨%γm, Ha⟩
  imod alwaysI_alloc (E := E) (N := N) (P := requestMapInv γm G) $$ [Ha] with H
  · inext
    unfold requestMapInv
    iexists ∅
    iframe Ha
    iapply BigSepM.bigSepM_empty.mpr
    iempintro
  imodintro
  iexists γm
  iexact H

end RequestMap

end Lantana
