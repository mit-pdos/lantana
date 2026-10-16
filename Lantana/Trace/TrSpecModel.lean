/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TrSpecFixpoint
public import Lantana.Trace.Adequacy.Temporal

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode Ordinals

section Alloc

variable {GF : BundledGFunctors} [InvGpreS GF]

/-- The ghost state of world satisfaction and of the credits at the given names. -/
@[reducible] def invGSOfNames (γ : GName × GName × GName × GName) : InvGS GF where
  toWsatGS :=
    { inv := WsatGpreS.inv, enabled := WsatGpreS.enabled, disabled := WsatGpreS.disabled,
      invariant_name := γ.1, enabled_name := γ.2.1, disabled_name := γ.2.2.1 }
  toCreditGS := { elem := CreditGpreS.elem, name := γ.2.2.2 }

/-- The resources of the satisfiability predicate of adequacy. -/
def invRes [InvGS GF] : IProp GF := iprop((∃ x : Ordinal.{1}, ●£ₒ x) ∗ wsat ∗ ownE ⊤)

theorem invGS_alloc_names :
    ⊢@{IProp GF} |==> ∃ γ : GName × GName × GName × GName, @invRes GF (invGSOfNames γ) := by
  imod iOwn_alloc (E := (inferInstance : WsatGpreS GF).inv) (HeapView.Auth (.own 1) ∅)
    HeapView.auth_one_valid with ⟨%γi, Hi⟩
  imod iOwn_alloc (E := (inferInstance : WsatGpreS GF).enabled) (DisjointLeibnizSet.valid ⊤) ⟨⟩
    with ⟨%γe, He⟩
  imod iOwn_alloc (E := (inferInstance : WsatGpreS GF).disabled) (DisjointLeibnizSet.valid ∅) ⟨⟩
    with ⟨%γd, -⟩
  imod iOwn_alloc (E := (inferInstance : TlcGpreS GF).elem)
    ((Auth.auth (.own 1) (0 : Ordinal.{1})) • (Auth.frag (0 : Ordinal.{1})))
    (Auth.auth_both_valid_discrete.mpr ⟨CMRA.inc_refl _, CreditCamera.valid_trivial _⟩)
    with ⟨%γc, Hc⟩
  icases iOwn_op $$ Hc with ⟨Hc, -⟩
  imodintro
  iexists (γi, γe, γd, γc)
  unfold invRes
  isplitl [Hc]
  · iexists 0
    unfold supply
    iexact Hc
  isplitl [Hi]
  · unfold wsat
    iexists ∅
    isplitl
    · have H : liftInv (∅ : InvMap (IProp GF)) = ∅ := by
        simp only [liftInv, Iris.Std.LawfulPartialMap.map_empty]
      rw [invMap, H]
      iexact Hi
    · iapply BigSepM.bigSepM_empty
      itrivial
  · unfold ownE
    iexact He

end Alloc

section Instances

variable {GF : BundledGFunctors}

/-- The ghost state of the model with world satisfaction and credits `Gi`; the other names
are arbitrary. -/
@[reducible] def modelGSOf [ModelGpreS GF] (Gi : InvGS GF) : ModelGS GF where
  toInvGS := Gi
  toOSatGS := { stateName := 0, namesName := 0 }
  toOWitGS := { namesName := 0 }
  toOForestGS := { kidsName := 0, statusName := 0 }
  toMHistGS := { name := 0 }

/-- The ghost state of the temporal layer, at arbitrary names. -/
@[reducible] def temporalGSOf (Expr State : Type) [TemporalGpreS Expr State GF] :
    TemporalGS Expr State GF where
  name := 0
  regName := 0

end Instances

namespace TrSpec

variable {Expr State : Type} {GF : BundledGFunctors}

theorem valid_ext [TemporalGpreS Expr State GF] (G : TrSpec Expr State GF)
    (τ : Trace Expr State) (hG : ∀ [ModelGS GF] [TemporalGS Expr State GF], ⊢ G.internal τ) :
    G.external τ := by
  have h := iPropSat.mono (true_emp.mp.trans invGS_alloc_names) (iPropSat_intro (GF := GF))
  obtain ⟨γ, hγ⟩ := iPropSat.sat_exists (iPropSat.sat_bupd h)
  letI : ModelGS GF := modelGSOf (invGSOfNames γ)
  letI : TemporalGS Expr State GF := temporalGSOf Expr State
  refine G.adeq iprop(emp) τ (iPropSatLcAtFrame_sat.mpr (iPropSat.mono ?_ hγ))
  unfold invRes
  iintro ⟨Hc, Hw, HE⟩
  iframe Hc Hw HE
  isplitl []
  · itrivial
  · iapply hG

end TrSpec

end Lantana
