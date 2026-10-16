/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.Guarantee

/-! # Temporal formulas: `alwaysI`, `untilI`, `finallyI`

Rocq `lantana/trace/temporal_formula.v` and `temporal_formula_rules.v`: temporal formulas are
`IProp`s. `alwaysI N P` is a registered invariant; `untilI N k q P Q` ("`P` until `Q`") is a
registered obligation invariant over the obligation `k`, which holds `P` while `k` is live and
`Q` once it is discharged; `finallyI N k q Q` is `untilI N k q True Q`; `untilIDone k Q` is a
fulfilled until. Each has a guarantee (`guar_alwaysI`, `guar_untilI`, `guar_untilIDone`).

**Skeleton (M1):** the formulas are opaque (they are defined with the registry in M6) and the
rules are `sorry`.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open scoped Lantana.TrSpec Lantana.TrProp

variable {Expr State : Type} {GF : BundledGFunctors}
variable [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF] [TlcGS GF]
  [BIFUpdate (IProp GF)] [TemporalInterp Expr State GF]

/-- `alwaysI N P`: a registered invariant holding `P` (Rocq `alwaysI`). -/
@[lantana_alias alwaysI]
opaque alwaysI [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF] [TlcGS GF]
    [BIFUpdate (IProp GF)] [TemporalInterp Expr State GF] (N : Namespace) (P : IProp GF) :
    IProp GF

/-- `untilI N k q P Q`: `P` until `Q`, on the obligation `k` (fraction `q`). -/
@[lantana_alias untilI]
opaque untilI [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF] [TlcGS GF]
    [BIFUpdate (IProp GF)] [TemporalInterp Expr State GF] (N : Namespace) (k : Oid) (q : Qp)
    (P Q : IProp GF) : IProp GF

/-- `finallyI N k q Q`: eventually `Q`, on the obligation `k`. -/
@[lantana_alias finallyI]
def finallyI (N : Namespace) (k : Oid) (q : Qp) (Q : IProp GF) : IProp GF :=
  untilI N k q iprop(True) Q

/-- A fulfilled until: `Q` holds and `k` is discharged. -/
@[lantana_alias untilI_done]
opaque untilIDone [ModelGS GF] [TemporalGS Expr State GF] [StateInterp Expr State GF] [TlcGS GF]
    [BIFUpdate (IProp GF)] [TemporalInterp Expr State GF] (k : Oid) (Q : IProp GF) : IProp GF

instance alwaysI_persistent (N : Namespace) (P : IProp GF) : Persistent (alwaysI N P) := sorry
instance alwaysI_contractive (N : Namespace) : OFE.Contractive (alwaysI (GF := GF) N) := sorry
instance untilI_fractional (N : Namespace) (k : Oid) (P Q : IProp GF) :
    Fractional (fun q => untilI N k q P Q) := sorry
instance untilI_contractive_left (N : Namespace) (k : Oid) (q : Qp) (Q : IProp GF) :
    OFE.Contractive (fun P => untilI N k q P Q) := sorry
instance untilI_contractive_right (N : Namespace) (k : Oid) (q : Qp) (P : IProp GF) :
    OFE.Contractive (fun Q => untilI N k q P Q) := sorry

section Rules
variable {E : CoPset} {N : Namespace} {k : Oid} {q : Qp} {P Q : IProp GF}

/-! ## Always -/

@[lantana_alias alwaysI_acc]
theorem alwaysI_acc (hN : ↑N ⊆ E) :
    alwaysI N P ⊢ |={E, E \ ↑N}=> ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True) := sorry

@[lantana_alias alwaysI_alloc]
theorem alwaysI_alloc : ▷ P ⊢ |={E}=>m alwaysI N P := sorry

@[lantana_alias guar_alwaysI]
theorem guar_alwaysI : ⊢@{IProp GF} alwaysI N P ⊨ₜ □ₛ TrSpec.canon P := sorry

/-! ## Until -/

/-- Allocation: a new obligation below `p` with its fuel and witness, and the right to turn it
into an until with any formulas. -/
@[lantana_alias untilI_alloc]
theorem untilI_alloc (p : Parent) (K : Oids) (ℓ : Layer) (μ : Measure) :
    parLe (GF := GF) p ℓ ⊢ Par.kids p K -∗
      |={E}=>m ∃ k : Oid, ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ oblKids k ∅ ∗ Obl.fuel k ℓ μ ∗
        Wit.layer k ℓ ∗
        ∀ (E' : CoPset) (N : Namespace) (P Q : IProp GF), ▷ P -∗ |={E'}=>m untilI N k 1 P Q := sorry

@[lantana_alias untilI_init]
theorem untilI_init : Obl.assigned k 1 ⊢ ▷ P -∗ |={E}=>m untilI N k 1 P Q := sorry

@[lantana_alias untilI_acc]
theorem untilI_acc (hN : ↑N ⊆ E) :
    untilI N k q P Q ⊢ |={E, E \ ↑N}=> ▷ (P ∗ (▷ P ={E \ ↑N, E}=∗ untilI N k q P Q)) := sorry

/-- Discharge: open the until, then discharge the leaf obligation `k` with `Q`. -/
@[lantana_alias untilI_discharge]
theorem untilI_discharge (hN : ↑N ⊆ E) :
    untilI N k 1 P Q ⊢ |={E, E \ ↑N}=> ▷ (P ∗
      ∀ (p : Parent) (K : Oids), ⌜k ∈ K⌝ → Par.kids p K -∗ oblKids k ∅ -∗ Q -∗
        ∀ E' : CoPset, |={E'}=>m |={E \ ↑N, E}=> (Q ∗ Par.kids p (K.erase k) ∗ Obl.discharged k)) :=
  sorry

@[lantana_alias untilI_discharge_done]
theorem untilI_discharge_done (hN : ↑N ⊆ E) :
    untilI N k 1 P Q ⊢ |={E, E \ ↑N}=> ▷ (P ∗
      ∀ (p : Parent) (K : Oids), ⌜k ∈ K⌝ → Par.kids p K -∗ oblKids k ∅ -∗ Q -∗
        ∀ E' : CoPset, |={E'}=>m |={E \ ↑N, E}=> (untilIDone k Q ∗ Par.kids p (K.erase k))) :=
  sorry

@[lantana_alias finallyI_discharge]
theorem finallyI_discharge (p : Parent) (K : Oids) (hN : ↑N ⊆ E) (hk : k ∈ K) :
    £ₙ 1 ⊢ Par.kids p K -∗ oblKids k ∅ -∗ finallyI N k 1 Q -∗ Q -∗
      |={E}=>m Q ∗ Par.kids p (K.erase k) ∗ Obl.discharged k := sorry

@[lantana_alias untilI_discharged_false]
theorem untilI_discharged_false : untilI N k q P Q ⊢ Obl.discharged k -∗ False := sorry

@[lantana_alias untilI_frac_split]
theorem untilI_frac_split {q₁ q₂ : Qp} (h : q = q₁ + q₂) :
    untilI N k q P Q ⊢ untilI N k q₁ P Q ∗ untilI N k q₂ P Q := sorry

@[lantana_alias untilI_frac_add]
theorem untilI_frac_add {q₁ q₂ : Qp} {P' Q' : IProp GF} (h : q = q₁ + q₂) :
    untilI N k q₁ P Q ⊢ untilI N k q₂ P' Q' -∗ untilI N k q P Q := sorry

@[lantana_alias guar_untilI]
theorem guar_untilI : ⊢@{IProp GF} untilI N k q P Q ⊨ₜ (TrSpec.canon P 𝒰ₛ TrSpec.canon Q) := sorry

/-! ## Done untils -/

@[lantana_alias untilI_done_init]
theorem untilIDone_init (p : Parent) (K : Oids) (hk : k ∈ K) :
    Obl.assigned k 1 ⊢ Par.kids p K -∗ oblKids k ∅ -∗ Q -∗
      |={E}=>m untilIDone k Q ∗ Par.kids p (K.erase k) := sorry

@[lantana_alias untilI_done_elim]
theorem untilIDone_elim : untilIDone k Q ⊢ Q ∗ Obl.discharged k := sorry

@[lantana_alias guar_untilI_done]
theorem guar_untilIDone (G₁ : TrSpec Expr State GF) :
    ⊢@{IProp GF} untilIDone k Q ⊨ₜ (G₁ 𝒰ₛ TrSpec.canon Q) := sorry

/-! ## Inference -/

instance guarOf_alwaysI (G : TrSpec Expr State GF) [GuarOf P G] : GuarOf (alwaysI N P) (□ₛ G) :=
  sorry
instance guarOf_untilI (G₁ G₂ : TrSpec Expr State GF) [GuarOf P G₁] [GuarOf Q G₂] :
    GuarOf (untilI N k q P Q) (G₁ 𝒰ₛ G₂) := sorry
instance guarOf_untilIDone (G₂ : TrSpec Expr State GF) [GuarOf Q G₂] :
    GuarOf (untilIDone k Q) (◇ₛ G₂) := sorry
instance guarOf_stateFact (φ : State → ThreadPool Expr → Prop) [StateFact P φ] :
    GuarOf P (TrSpec.state φ) := ⟨guar_state_fact P φ⟩
instance guarOf_sep (G₁ G₂ : TrSpec Expr State GF) [GuarOf P G₁] [GuarOf Q G₂] :
    GuarOf iprop(P ∗ Q) (G₁ ∧ₛ G₂) := sorry
instance guarOf_pure (φ : Prop) :
    GuarOf (iprop(⌜φ⌝) : IProp GF) (TrSpec.pure (Expr := Expr) (State := State) φ) :=
  ⟨guar_pure φ⟩

end Rules

end Lantana
