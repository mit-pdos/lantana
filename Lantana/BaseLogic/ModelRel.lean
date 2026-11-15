/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.BaseLogic.Witness

/-! # Round relations of the obligation model

A round of the model update may change several obligations at once (moving a subtree changes
the owner of all its nodes), so rounds use pointwise relations (Rocq
`lantana/base_logic/model_rel.v`): `Obligations.NoDischarge` (every obligation stays or makes progress; new
ones may be added), `Obligations.StayOrStep` (also discharges), and `Witnesses.NoDischarge` / `Witnesses.StayOrStep`
(witnesses do not increase). `Obligations.StayOrStep` implies the order `Obligations.le` seen by adequacy.

The witness invariant `OwitInv η Ω W` (Rocq `owit_inv`, in `owit.v`) relates every obligation
to its witness: same status, and the bound of an assigned witness is at most `η` of the fuel.
After any `Obligations.StayOrStep` round, witnesses that keep the invariants exist
(`owitInv_exists_witnesses`).

Rocq's class-bound inflationary function `η` is the explicit parameter `η` of the generic
definitions; the model uses `η := fairMeasureUb` (`OwitInvFair`, `OwitInvLbMonoFair`). No lemma
of this file needs a property of `η`.
-/

@[expose] public section

namespace Lantana.Model

open Iris.Std LawfulPartialMap
open Ordinals

/-! ## Round relations -/

namespace Obligations

/-- No discharge: every obligation stays or makes progress; new ones may be added. -/
@[lantana_alias obls_ndf]
def NoDischarge (Ω₁ Ω₂ : Obligations) : Prop :=
  ∀ k g₁, get? Ω₁ k = some g₁ → ∃ g₂, get? Ω₂ k = some g₂ ∧ (g₂ = g₁ ∨ g₁.Progress g₂)

/-- Every obligation stays or takes a step; new ones may be added. -/
@[lantana_alias obls_lef]
def StayOrStep (Ω₁ Ω₂ : Obligations) : Prop :=
  ∀ k g₁, get? Ω₁ k = some g₁ → ∃ g₂, get? Ω₂ k = some g₂ ∧ (g₂ = g₁ ∨ g₁.Step g₂)

end Obligations

namespace Witness

/-- The bound does not increase; discharge is allowed. -/
@[lantana_alias wit_le]
def le : Witness → Witness → Prop
  | assigned a₁, assigned a₂ => a₂ ≤ a₁
  | assigned _, discharged => True
  | discharged, discharged => True
  | discharged, assigned _ => False

instance : LE Witness := ⟨le⟩

theorem le_refl (w : Witness) : le w w := by
  cases w
  · exact Ordinal.le_rfl
  · trivial

theorem le_of_noDischargeLe {w₁ w₂ : Witness} (h : NoDischargeLe w₁ w₂) : le w₁ w₂ := by
  cases w₁ <;> cases w₂ <;> simp_all [NoDischargeLe, le]

end Witness

namespace Witnesses

/-- No discharge: every witness keeps its status and its bound does not increase. -/
@[lantana_alias wits_ndf]
def NoDischarge (W₁ W₂ : Witnesses) : Prop :=
  ∀ k w₁, get? W₁ k = some w₁ → ∃ w₂, get? W₂ k = some w₂ ∧ w₁.NoDischargeLe w₂

/-- Every witness is discharged or its bound does not increase. -/
@[lantana_alias wits_lef]
def StayOrStep (W₁ W₂ : Witnesses) : Prop :=
  ∀ k w₁, get? W₁ k = some w₁ → ∃ w₂, get? W₂ k = some w₂ ∧ w₁.le w₂

end Witnesses

namespace Obligations

@[lantana_alias obls_ndf_refl]
theorem noDischarge_refl (Ω : Obligations) : NoDischarge Ω Ω :=
  fun _ g h => ⟨g, h, .inl rfl⟩

@[lantana_alias obls_lef_refl]
theorem stayOrStep_refl (Ω : Obligations) : StayOrStep Ω Ω :=
  fun _ g h => ⟨g, h, .inl rfl⟩

@[lantana_alias obls_ndf_obls_lef]
theorem NoDischarge.stayOrStep {Ω₁ Ω₂ : Obligations} (h : NoDischarge Ω₁ Ω₂) : StayOrStep Ω₁ Ω₂ := fun k g₁ hk =>
  let ⟨g₂, hg₂, hr⟩ := h k g₁ hk
  ⟨g₂, hg₂, hr.imp_right .inl⟩

theorem noDischarge_trans {Ω₁ Ω₂ Ω₃ : Obligations} (h₁₂ : NoDischarge Ω₁ Ω₂) (h₂₃ : NoDischarge Ω₂ Ω₃) : NoDischarge Ω₁ Ω₃ := by
  intro k g₁ e₁
  obtain ⟨g₂, e₂, h₁⟩ := h₁₂ k g₁ e₁
  obtain ⟨g₃, e₃, h₂⟩ := h₂₃ k g₂ e₂
  refine ⟨g₃, e₃, ?_⟩
  rcases h₁ with rfl | h₁ <;> rcases h₂ with rfl | h₂
  · exact .inl rfl
  · exact .inr h₂
  · exact .inr h₁
  · right
    cases g₁ <;> cases g₂ <;> cases g₃ <;> simp_all [Obligation.Progress]
    exact Ordinal.lt_trans h₂ h₁

theorem stayOrStep_trans {Ω₁ Ω₂ Ω₃ : Obligations} (h₁₂ : StayOrStep Ω₁ Ω₂) (h₂₃ : StayOrStep Ω₂ Ω₃) : StayOrStep Ω₁ Ω₃ := by
  intro k g₁ e₁
  obtain ⟨g₂, e₂, h₁⟩ := h₁₂ k g₁ e₁
  obtain ⟨g₃, e₃, h₂⟩ := h₂₃ k g₂ e₂
  refine ⟨g₃, e₃, ?_⟩
  rcases h₁ with rfl | h₁ <;> rcases h₂ with rfl | h₂
  · exact .inl rfl
  · exact .inr h₂
  · exact .inr h₁
  · right
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
      cases g₁ <;> cases g₂ <;> cases g₃ <;>
      simp_all [Obligation.Step, Obligation.Progress, Obligation.Discharge]
    exact Ordinal.lt_trans h₂ h₁

/-- The bridge to the order seen by adequacy. -/
@[lantana_alias obls_lef_obls_le]
theorem StayOrStep.le {Ω₁ Ω₂ : Obligations} (h : StayOrStep Ω₁ Ω₂) : le Ω₁ Ω₂ := by
  refine ⟨fun k hk => ?_, fun k g₁ g₂ e₁ e₂ => ?_⟩
  · cases e₁ : get? Ω₁ k with
    | none => simp [e₁] at hk
    | some g₁ =>
      obtain ⟨g₂, e₂, _⟩ := h k g₁ e₁
      simp [e₂]
  · obtain ⟨g₂', e₂', hr⟩ := h k g₁ e₁
    rw [e₂] at e₂'
    cases e₂'
    rcases hr with rfl | hs
    · exact Obligation.le_refl _
    · exact Obligation.step_le hs

@[lantana_alias obls_ndf_insert_fresh]
theorem noDischarge_insert_fresh {Ω : Obligations} {k : Oid} (g : Obligation) (hk : get? Ω k = none) :
    NoDischarge Ω (insert Ω k g) := by
  intro x g₁ hx
  refine ⟨g₁, ?_, .inl rfl⟩
  rw [get?_insert_ne (fun h => by subst h; simp [hk] at hx)]
  exact hx

@[lantana_alias obls_lef_insert_step]
theorem stayOrStep_insert_step {Ω : Obligations} {k : Oid} {g₁ g₂ : Obligation} (hk : get? Ω k = some g₁)
    (hs : g₁.Step g₂) : StayOrStep Ω (insert Ω k g₂) := by
  intro x g hx
  by_cases hxk : k = x
  · subst hxk
    rw [hk] at hx
    cases hx
    exact ⟨g₂, get?_insert_eq rfl, .inr hs⟩
  · exact ⟨g, by rw [get?_insert_ne hxk]; exact hx, .inl rfl⟩

end Obligations

namespace Witnesses

@[lantana_alias wits_ndf_wits_lef]
theorem NoDischarge.stayOrStep {W₁ W₂ : Witnesses} (h : NoDischarge W₁ W₂) : StayOrStep W₁ W₂ := fun k w₁ hk =>
  let ⟨w₂, hw₂, hle⟩ := h k w₁ hk
  ⟨w₂, hw₂, Witness.le_of_noDischargeLe hle⟩

@[lantana_alias wits_ndf_wits_mon]
theorem NoDischarge.mono {W₁ W₂ : Witnesses} (h : NoDischarge W₁ W₂)
    (hdom : ∀ k, (get? W₂ k).isSome → (get? W₁ k).isSome) : Mono W₁ W₂ := by
  refine mapForall2_intro fun k => ?_
  cases e₁ : get? W₁ k with
  | none =>
    refine .inl ⟨rfl, ?_⟩
    cases e₂ : get? W₂ k with
    | none => rfl
    | some w₂ => have := hdom k (by simp [e₂]); simp [e₁] at this
  | some w₁ =>
    obtain ⟨w₂, e₂, hle⟩ := h k w₁ e₁
    exact .inr ⟨w₁, w₂, rfl, e₂, hle⟩

end Witnesses

/-! ## The witness invariant -/

section OWit

variable (η : Fuel → Fuel)

/-- The relation between an obligation and its witness: same status, and the bound of an
assigned witness is at most `η` of the fuel. -/
def OwitRel : Obligation → Witness → Prop
  | .assigned a _, .assigned b => b ≤ η a
  | .discharged, .discharged => True
  | _, _ => False

/-- The witness invariant: every obligation has a witness, related by `OwitRel η` (Rocq
`owit_inv`). -/
@[lantana_alias owit_inv]
def OwitInv (Ω : Obligations) (W : Witnesses) : Prop :=
  MapForall2 (fun _ => OwitRel η) Ω W

variable {η}

@[lantana_alias owit_inv_empty]
theorem owitInv_empty : OwitInv η ∅ ∅ :=
  mapForall2_empty

@[lantana_alias owit_inv_dom]
theorem OwitInv.dom {Ω : Obligations} {W : Witnesses} (h : OwitInv η Ω W) (k : Oid) :
    (get? Ω k).isSome ↔ (get? W k).isSome :=
  MapForall2.isSome_iff h k

theorem owitRel_assigned_iff {g : Obligation} {w : Witness} (h : OwitRel η g w) :
    (∃ a t, g = .assigned a t) ↔ (∃ b, w = .assigned b) := by
  cases g <;> cases w <;> simp_all [OwitRel]

theorem owitRel_discharged_iff {g : Obligation} {w : Witness} (h : OwitRel η g w) :
    g = .discharged ↔ w = .discharged := by
  cases g <;> cases w <;> simp_all [OwitRel]

/-- If no obligation was discharged, no witness was either. -/
@[lantana_alias wits_lef_wits_ndf]
theorem Witnesses.noDischarge_of_stayOrStep {Ω₁ Ω₂ : Obligations} {W₁ W₂ : Witnesses} (hI₁ : OwitInv η Ω₁ W₁)
    (hΩ : Ω₁.NoDischarge Ω₂) (hW : W₁.StayOrStep W₂) (hI₂ : OwitInv η Ω₂ W₂) : W₁.NoDischarge W₂ := by
  intro k w₁ e₁
  obtain ⟨w₂, e₂, hle⟩ := hW k w₁ e₁
  refine ⟨w₂, e₂, ?_⟩
  cases w₁ with
  | discharged => cases w₂ <;> simp_all [Witness.le, Witness.NoDischargeLe]
  | assigned a₁ =>
    cases w₂ with
    | assigned a₂ => exact hle
    | discharged =>
      exfalso
      obtain ⟨g₁, eg₁, hr₁⟩ := MapForall2.lookup_right hI₁ e₁
      obtain ⟨g₂, eg₂, hg⟩ := hΩ k g₁ eg₁
      have hr₂ : OwitRel η g₂ .discharged := MapForall2.lookup hI₂ eg₂ e₂
      rcases hg with rfl | hg
      · cases g₂ <;> simp_all [OwitRel]
      · cases g₁ <;> cases g₂ <;> simp_all [OwitRel, Obligation.Progress]

/-- The case "obligations unchanged". -/
@[lantana_alias wits_lef_same_wits_mon]
theorem Witnesses.stayOrStep_same_mono {Ω : Obligations} {W₁ W₂ : Witnesses} (hI₁ : OwitInv η Ω W₁)
    (hW : W₁.StayOrStep W₂) (hI₂ : OwitInv η Ω W₂) : W₁.Mono W₂ :=
  Witnesses.NoDischarge.mono (Witnesses.noDischarge_of_stayOrStep hI₁ (Obligations.noDischarge_refl Ω) hW hI₂) fun k hk =>
    (hI₁.dom k).1 ((hI₂.dom k).2 hk)

/-- The witnesses after a round that added a fresh obligation `k` with witness `w` (Rocq's
freshness hypothesis `Ω₁ !! k = None` is not needed). -/
@[lantana_alias wits_ndf_insert_wits_mon]
theorem Witnesses.noDischarge_insert_mono {Ω₁ : Obligations} {W₁ W₂ : Witnesses} {k : Oid} {g : Obligation}
    {w : Witness} (hI₁ : OwitInv η Ω₁ W₁) (hW : W₁.NoDischarge W₂)
    (hI₂ : OwitInv η (insert Ω₁ k g) W₂) (hw : ∀ w₂, get? W₂ k = some w₂ → w.NoDischargeLe w₂) :
    Witnesses.Mono (insert W₁ k w) W₂ := by
  refine mapForall2_intro fun x => ?_
  by_cases hxk : k = x
  · subst hxk
    rw [get?_insert_eq rfl]
    obtain ⟨w₂, e₂, _⟩ := MapForall2.lookup_left hI₂
      (get?_insert_eq rfl : get? (insert Ω₁ k g) k = some g)
    exact .inr ⟨w, w₂, rfl, e₂, hw w₂ e₂⟩
  · rw [get?_insert_ne hxk]
    cases e₁ : get? W₁ x with
    | some w₁ =>
      obtain ⟨w₂, e₂, hle⟩ := hW x w₁ e₁
      exact .inr ⟨w₁, w₂, rfl, e₂, hle⟩
    | none =>
      refine .inl ⟨rfl, ?_⟩
      have h₁ := hI₁.dom x
      have h₂ := hI₂.dom x
      rw [get?_insert_ne hxk] at h₂
      cases e₂ : get? W₂ x <;> simp_all

/-- The witnesses after a round that discharged `k` (Rocq's hypothesis that `k` was assigned
is not needed). -/
@[lantana_alias wits_lef_discharge_wits_mon]
theorem Witnesses.stayOrStep_discharge_mono {Ω₁ : Obligations} {W₁ W₂ : Witnesses} {k : Oid}
    (hI₁ : OwitInv η Ω₁ W₁) (hW : W₁.StayOrStep W₂) (hI₂ : OwitInv η (insert Ω₁ k .discharged) W₂) :
    Witnesses.Mono (insert W₁ k .discharged) W₂ := by
  refine mapForall2_intro fun x => ?_
  by_cases hxk : k = x
  · subst hxk
    rw [get?_insert_eq rfl]
    obtain ⟨w₂, e₂, hr⟩ := MapForall2.lookup_left hI₂
      (get?_insert_eq rfl : get? (insert Ω₁ k Obligation.discharged) k = some .discharged)
    refine .inr ⟨.discharged, w₂, rfl, e₂, ?_⟩
    cases w₂ <;> simp_all [OwitRel, Witness.NoDischargeLe]
  · rw [get?_insert_ne hxk]
    cases e₁ : get? W₁ x with
    | some w₁ =>
      obtain ⟨w₂, e₂, hle⟩ := hW x w₁ e₁
      refine .inr ⟨w₁, w₂, rfl, e₂, ?_⟩
      obtain ⟨g, eg, hr₁⟩ := MapForall2.lookup_right hI₁ e₁
      have hr₂ : OwitRel η g w₂ :=
        MapForall2.lookup hI₂ (by rw [get?_insert_ne hxk]; exact eg) e₂
      cases g <;> cases w₁ <;> cases w₂ <;> simp_all [OwitRel, Witness.le, Witness.NoDischargeLe]
    | none =>
      refine .inl ⟨rfl, ?_⟩
      have h₁ := hI₁.dom x
      have h₂ := hI₂.dom x
      rw [get?_insert_ne hxk] at h₂
      cases e₂ : get? W₂ x <;> simp_all

end OWit

/-! ## Choice of witnesses

`OwitInvLb γ Ω W`: the witness of every assigned obligation (fuel `a`, owner `i`) is at least
`γ i a`. After a round `Obligations.StayOrStep Ω₁ Ω₂`, witnesses that keep the invariants exist. -/

section WitnessChoice

/-- The lower bound `γ` on witnesses, pointwise. -/
def OwitLbRel (γ : ThreadId → Fuel → Fuel) : Obligation → Witness → Prop
  | .assigned a i, .assigned b => γ i a ≤ b
  | .discharged, .discharged => True
  | _, _ => False

/-- The witness of every assigned obligation (fuel `a`, owner `i`) is at least `γ i a`. -/
@[lantana_alias owit_inv_lb]
def OwitInvLb (γ : ThreadId → Fuel → Fuel) (Ω : Obligations) (W : Witnesses) : Prop :=
  MapForall2 (fun _ => OwitLbRel γ) Ω W

/-- `γ` is strictly monotone in the fuel (whatever the threads) and below `η`. -/
@[lantana_alias owit_inv_lb_mon]
def OwitInvLbMono (η : Fuel → Fuel) (γ : ThreadId → Fuel → Fuel) : Prop :=
  (∀ a b i j, a < b → γ i a < γ j b) ∧ ∀ i a, γ i a ≤ η a

/-- The witness chosen for an obligation that changed. -/
@[lantana_alias wit_of]
def witOf (γ : ThreadId → Fuel → Fuel) : Obligation → Witness
  | .assigned a i => .assigned (γ i a)
  | .discharged => .discharged

@[lantana_alias owit_inv_exists_witnesses]
theorem owitInv_exists_witnesses {η : Fuel → Fuel} {γ : ThreadId → Fuel → Fuel}
    {Ω₁ Ω₂ : Obligations} {W₁ : Witnesses} (hγ : OwitInvLbMono η γ) (hΩ : Ω₁.StayOrStep Ω₂)
    (hI : OwitInv η Ω₁ W₁) (hLb : OwitInvLb γ Ω₁ W₁) :
    ∃ W₂ : Witnesses, W₁.StayOrStep W₂ ∧ OwitInv η Ω₂ W₂ ∧ OwitInvLb γ Ω₂ W₂ := by
  obtain ⟨hmono, hsched⟩ := hγ
  obtain ⟨W₂, hW₂⟩ := mapForall2_choice (B := Witness)
    (P := fun k g₂ w₂ => OwitRel η g₂ w₂ ∧ OwitLbRel γ g₂ w₂ ∧
      ∀ w₁, get? W₁ k = some w₁ → w₁.le w₂) Ω₂ (by
    intro k g₂ e₂
    by_cases hsame : get? Ω₁ k = some g₂
    · obtain ⟨w₁, ew₁, hr⟩ := MapForall2.lookup_left hI hsame
      have hl : OwitLbRel γ g₂ w₁ := MapForall2.lookup hLb hsame ew₁
      refine ⟨w₁, hr, hl, fun w₁' e => ?_⟩
      rw [ew₁] at e
      cases e
      exact Witness.le_refl w₁
    · refine ⟨witOf γ g₂, ?_, ?_, fun w₁ ew₁ => ?_⟩
      · cases g₂ with
        | assigned a i => exact hsched i a
        | discharged => trivial
      · cases g₂ with
        | assigned a i => exact Ordinal.le_rfl
        | discharged => trivial
      · obtain ⟨g₁, eg₁, hr₁⟩ := MapForall2.lookup_right hI ew₁
        obtain ⟨g₂', eg₂', hs⟩ := hΩ k g₁ eg₁
        rw [e₂] at eg₂'
        cases eg₂'
        have hl₁ : OwitLbRel γ g₁ w₁ := MapForall2.lookup hLb eg₁ ew₁
        rcases hs with rfl | hs
        · exact absurd eg₁ hsame
        · rcases hs with hs | hs
          · cases g₁ with
            | discharged => simp at hs
            | assigned a i =>
              cases g₂ with
              | discharged => simp at hs
              | assigned a' j =>
                cases w₁ with
                | discharged => simp [OwitRel] at hr₁
                | assigned b =>
                  exact Ordinal.le_of_lt
                    (Ordinal.lt_of_lt_of_le (hmono a' a j i hs) hl₁)
          · cases g₁ <;> cases g₂ <;> cases w₁ <;>
              simp_all [Obligation.Discharge, OwitRel, witOf, Witness.le])
  refine ⟨W₂, ?_, hW₂.imp fun _ _ _ h => h.1, hW₂.imp fun _ _ _ h => h.2.1⟩
  intro k w₁ ew₁
  obtain ⟨g₁, eg₁, _⟩ := MapForall2.lookup_right hI ew₁
  obtain ⟨g₂, eg₂, _⟩ := hΩ k g₁ eg₁
  obtain ⟨w₂, ew₂, _, _, hle⟩ := MapForall2.lookup_left hW₂ eg₂
  exact ⟨w₂, ew₂, hle w₁ ew₁⟩

end WitnessChoice

/-! ## The model's instance `η := fairMeasureUb` -/

/-- The witness invariant of the model, with `η := fairMeasureUb`. -/
abbrev OwitInvFair (Ω : Obligations) (W : Witnesses) : Prop :=
  OwitInv fairMeasureUb Ω W

/-- `OwitInvLbMono` for the model's `η := fairMeasureUb`. -/
abbrev OwitInvLbMonoFair (γ : ThreadId → Fuel → Fuel) : Prop :=
  OwitInvLbMono fairMeasureUb γ

end Lantana.Model
