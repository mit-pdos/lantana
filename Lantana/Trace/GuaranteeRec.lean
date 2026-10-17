/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lantana.Trace.GuaranteeInfer
public import Lantana.Trace.TrSpecFixpoint

/-! # Guarantees of fixpoints and recursive structures

Rocq `lantana/trace/guarantee_rec.v`: guarantees of the fixpoints of trace specifications
(`guar_nu_coind`, `guar_nu_canon`, `guar_mu_rank`, `guar_mu_fold`), and two structures defined
by guarded recursion (Iris-Lean's `fixpoint`) through the temporal formulas, whose readings
are greatest fixpoints:

* `nest N Q G`, invariants nested forever: an `alwaysIGuar` whose content is `Q` and the
  structure itself, read as `G ∧ ν X. □ (G ∧ X)`. The guarantee of its content is a closed
  proof: the recursion is in the structure, not in the proof. Allocation opens the new
  invariant, registers it, and gets the record of its content by Löb induction (`nest_alloc`).
* `renew N Q G`, a self-renewing commitment: an until whose right formula is `Q` and the next
  link, read as `G ∧ ν X. ◇ (G ∧ X)`. A thread renews by allocating the next link and
  discharging the current one with it. On traces the reading is just `◇ G` (the eventuality
  is not strict, `TrSpec.nu_renew_ext`); `□ ◇ G` ("infinitely often") is the guarantee of an
  always over a finally (`guar_always_finally`).

The recursion goes through the forms with explicit readings (`alwaysIGuar`, `untilIGuar`),
which are contractive in their contents (`alwaysIGuar_contractive`,
`untilIGuar_contractive_right`); the canonical forms are not.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open Lantana.Model
open scoped Lantana.TrSpec Lantana.TrProp

variable {Expr State Val : Type} {GF : BundledGFunctors} [Language Expr State Val]
-- Named, to be passed explicitly to `TrSpec.canon_le`.
variable [instM : ModelGS GF] [instT : TemporalGS Expr State GF] [StateInterp Expr State GF]

/-! ## Guarantees of fixpoints -/

section Fixpoints
variable (F : TrSpec Expr State GF → TrSpec Expr State GF) [TrSpec.Mono F] {P : IProp GF}

@[lantana_alias guar_nu_coind]
theorem guar_nu_coind {H : TrSpec Expr State GF} (hH : H ⊑ₛ F H) :
    (P ⊨ₜ H) ⊢ P ⊨ₜ TrSpec.nu F :=
  guar_weaken (TrSpec.nu_coind F hH)

/-- How guarded-recursive formulas get fixpoint guarantees. -/
@[lantana_alias guar_nu_canon]
theorem guar_nu_canon (hP : ⊢ P ⊨ₜ F (TrSpec.canon P)) : ⊢ P ⊨ₜ TrSpec.nu F :=
  (guar_canon P).trans
    (guar_weaken (TrSpec.nu_coind F (@TrSpec.canon_le _ _ _ _ _ instM instT _ _ _ hP)))

@[lantana_alias guar_mu_rank]
theorem guar_mu_rank (H : Fuel → TrSpec Expr State GF)
    (hH : ∀ α, H α ⊑ₛ F (TrSpec.ex (X := { β : Fuel // β < α }) fun b => H b.1)) (α : Fuel) :
    (P ⊨ₜ H α) ⊢ P ⊨ₜ TrSpec.mu F :=
  guar_weaken (TrSpec.mu_intro F H hH α)

/-- Introduction without a ranking, for a continuous body. -/
@[lantana_alias guar_mu_fold]
theorem guar_mu_fold [TrSpec.Cont F] : (P ⊨ₜ F (TrSpec.mu F)) ⊢ P ⊨ₜ TrSpec.mu F :=
  guar_weaken (TrSpec.mu_unfold_r F)

end Fixpoints

/-! ## Invariants nested forever -/

section Nest
variable {E : CoPset} {N : Namespace} {Q : IProp GF} {G : TrSpec Expr State GF}

/-- The body of the reading of a nested invariant (Rocq `F_nest`). -/
@[lantana_alias F_nest]
def nestBody (G X : TrSpec Expr State GF) : TrSpec Expr State GF := □ₛ (G ∧ₛ X)

@[lantana_alias F_nest_mono]
instance nestBody_mono (G : TrSpec Expr State GF) : TrSpec.Mono (nestBody G) := by
  unfold nestBody; infer_instance

/-- The reading of a nested invariant. -/
@[lantana_alias nest_trSpec]
def nestTrSpec (G : TrSpec Expr State GF) : TrSpec Expr State GF :=
  G ∧ₛ TrSpec.nu (nestBody G)

@[lantana_alias nest_pre]
def nestPre (N : Namespace) (Q : IProp GF) (G : TrSpec Expr State GF) (X : IProp GF) :
    IProp GF :=
  alwaysIGuar N iprop(Q ∗ X) (nestTrSpec G)

@[lantana_alias nest_pre_contractive]
instance nestPre_contractive (N : Namespace) (Q : IProp GF) (G : TrSpec Expr State GF) :
    OFE.Contractive (nestPre N Q G) where
  distLater_dist h :=
    (alwaysIGuar_contractive N (nestTrSpec G)).distLater_dist fun m hm => sep_ne.ne .rfl (h m hm)

/-- `nest N Q G`: an invariant holding `Q` and `nest N Q G` itself, read as `nestTrSpec G`. -/
@[lantana_alias nest]
def nest (N : Namespace) (Q : IProp GF) (G : TrSpec Expr State GF) : IProp GF :=
  fixpoint (nestPre N Q G)

@[lantana_alias nest_unfold]
theorem nest_unfold (N : Namespace) (Q : IProp GF) (G : TrSpec Expr State GF) :
    nest N Q G = alwaysIGuar N iprop(Q ∗ nest N Q G) (nestTrSpec G) :=
  fixpoint_unfold (nestPre N Q G).toContractiveHom

theorem nest_intro : alwaysIGuar N iprop(Q ∗ nest N Q G) (nestTrSpec G) ⊢ nest N Q G :=
  (nest_unfold N Q G).to_bi.mpr

@[lantana_alias nest_persistent]
instance nest_persistent (N : Namespace) (Q : IProp GF) (G : TrSpec Expr State GF) :
    Persistent (nest N Q G) := by
  rw [nest_unfold]; infer_instance

@[lantana_alias guar_nest]
theorem guar_nest : ⊢@{IProp GF} nest N Q G ⊨ₜ TrSpec.nu (nestBody G) := by
  rw [nest_unfold]
  exact guar_alwaysIGuar.trans (guar_weaken (TrSpec.nu_unfold_r (nestBody G)))

@[lantana_alias guar_nest_content]
theorem guar_nest_content (hQ : ⊢ Q ⊨ₜ G) :
    ⊢@{IProp GF} iprop(Q ∗ nest N Q G) ⊨ₜ nestTrSpec G :=
  guar_nest.trans (wand_entails (hQ.trans guar_sep))

/-- Allocation: the invariant is opened at once, registered, and the record of its content
(which holds the structure, whose own record is later-guarded) is obtained by Löb
induction. -/
@[lantana_alias nest_alloc]
theorem nest_alloc (hN : ↑N ⊆ E) (hQ : ⊢ Q ⊨ₜ G) : ▷ Q ⊢ |={E}=>m nest N Q G := by
  have hC := guar_nest_content (N := N) hQ
  iintro HQ
  iapply mupd_read_fupd
  iintro %h %n %σ %tp HI TI
  imod savedTrI_alloc (nestTrSpec G).internal with ⟨%γ, #Hγ⟩
  imod inv_alloc_open N E iprop(Q ∗ nest N Q G) hN with ⟨#Hinv, Hclose⟩
  ihave #HE := historyInterp_histEvent_now h n σ tp $$ HI
  iunfold regState at TI
  imod regRegister regEntryInterp (.always N γ) h n σ tp $$ TI [] HI with ⟨HI, TI, %j, #Hj⟩
  · iintro %st -
    simp only [regEntryInterp]
    iexists iprop(Q ∗ nest N Q G), nestTrSpec G
    iframe Hγ Hinv
    inext
    iapply hC
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hcl %g %i %Ω %W MI
  -- the record of the content at `n`, by Löb induction
  ihave #T : ▷ record (nestTrSpec G) n $$ [HQ HI MI]
  · iloeb as IH
    ihave #Hnest : ▷ nest N Q G $$ [HQ HI MI]
    · inext
      iapply nest_intro
      rw [alwaysIGuar_unfold]
      iexists j, n, γ, (σ, tp)
      iframe Hj HE Hγ Hinv
      isplitr
      · inext
        iapply hC
      · iapply IH $$ [HQ] HI MI
        inext
        iexact HQ
    iapply guar_elim_later_guar iprop(Q ∗ nest N Q G) (nestTrSpec G) h n σ tp g i Ω W $$ []
      [HQ HI MI]
    · inext
      iapply hC
    · iframe HI MI
      inext
      iframe HQ Hnest
  iframe MI
  imod Hcl with -
  imod Hclose $$ [HQ] with -
  · inext
    iframe HQ
    iapply nest_intro
    rw [alwaysIGuar_unfold]
    iexists j, n, γ, (σ, tp)
    iframe Hj HE Hγ Hinv T
    inext
    iapply hC
  imodintro
  iframe HI
  isplitl [TI]
  · iunfold regState
    iexact TI
  iapply nest_intro
  rw [alwaysIGuar_unfold]
  iexists j, n, γ, (σ, tp)
  iframe Hj HE Hγ Hinv T
  inext
  iapply hC

end Nest

/-! ## A commitment that renews itself -/

section Renew
variable {E : CoPset} {N : Namespace} {k : Oid} {Q : IProp GF} {G : TrSpec Expr State GF}

/-- The body of the reading of a self-renewing commitment (Rocq `F_renew`). -/
@[lantana_alias F_renew]
def renewBody (G X : TrSpec Expr State GF) : TrSpec Expr State GF := ◇ₛ (G ∧ₛ X)

@[lantana_alias F_renew_mono]
instance renewBody_mono (G : TrSpec Expr State GF) : TrSpec.Mono (renewBody G) := by
  unfold renewBody TrSpec.eventually; infer_instance

/-- The reading of the right formula of a link. -/
@[lantana_alias renew_trSpec]
def renewTrSpec (G : TrSpec Expr State GF) : TrSpec Expr State GF :=
  G ∧ₛ TrSpec.nu (renewBody G)

@[lantana_alias renew_pre]
def renewPre (N : Namespace) (Q : IProp GF) (G : TrSpec Expr State GF) (X : IProp GF) :
    IProp GF :=
  iprop(∃ k : Oid, untilIGuar N k 1 iprop(True) iprop(Q ∗ X) TrSpec.true (renewTrSpec G))

@[lantana_alias renew_pre_contractive]
instance renewPre_contractive (N : Namespace) (Q : IProp GF) (G : TrSpec Expr State GF) :
    OFE.Contractive (renewPre N Q G) where
  distLater_dist h := exists_ne fun k =>
    (untilIGuar_contractive_right N k 1 iprop(True) TrSpec.true (renewTrSpec G)).distLater_dist
      fun m hm => sep_ne.ne .rfl (h m hm)

/-- `renew N Q G`: an until of `True` on some obligation, whose right formula is `Q` and the
next link, read as `renewTrSpec G`. -/
@[lantana_alias renew]
def renew (N : Namespace) (Q : IProp GF) (G : TrSpec Expr State GF) : IProp GF :=
  fixpoint (renewPre N Q G)

@[lantana_alias renew_unfold]
theorem renew_unfold (N : Namespace) (Q : IProp GF) (G : TrSpec Expr State GF) :
    renew N Q G = iprop(∃ k : Oid,
      untilIGuar N k 1 iprop(True) iprop(Q ∗ renew N Q G) TrSpec.true (renewTrSpec G)) :=
  fixpoint_unfold (renewPre N Q G).toContractiveHom

@[lantana_alias renew_intro]
theorem renew_intro (k : Oid) :
    untilIGuar N k 1 iprop(True) iprop(Q ∗ renew N Q G) TrSpec.true (renewTrSpec G) ⊢
      renew N Q G := by
  refine .trans ?_ (renew_unfold N Q G).to_bi.mpr
  exact exists_intro (Ψ := fun k : Oid =>
    untilIGuar N k 1 iprop(True) iprop(Q ∗ renew N Q G) TrSpec.true (renewTrSpec G)) k

@[lantana_alias guar_renew]
theorem guar_renew : ⊢@{IProp GF} renew N Q G ⊨ₜ TrSpec.nu (renewBody G) := by
  have h₁ : ⊢ iprop(∃ k : Oid, untilIGuar N k 1 iprop(True) iprop(Q ∗ renew N Q G) TrSpec.true
      (renewTrSpec G)) ⊨ₜ (TrSpec.true 𝒰ₛ renewTrSpec G) :=
    (forall_intro fun k => guar_untilIGuar (N := N) (k := k) (q := 1) (P := iprop(True))
      (Q := iprop(Q ∗ renew N Q G))).trans (guar_ex_ghost _)
  have h₂ : (TrSpec.true 𝒰ₛ renewTrSpec G) ⊑ₛ TrSpec.nu (renewBody G) :=
    TrSpec.nu_unfold_r (renewBody G)
  rw [renew_unfold]
  exact h₁.trans (guar_weaken h₂)

@[lantana_alias guar_renew_content]
theorem guar_renew_content (hQ : ⊢ Q ⊨ₜ G) :
    ⊢@{IProp GF} iprop(Q ∗ renew N Q G) ⊨ₜ renewTrSpec G :=
  guar_renew.trans (wand_entails (hQ.trans guar_sep))

/-- Allocation of a link, with a fresh obligation `k` below `p`. -/
@[lantana_alias renew_alloc]
theorem renew_alloc (p : Parent) (K : Oids) (ℓ : Layer) (μ : Measure) (hQ : ⊢ Q ⊨ₜ G) :
    parLe (GF := GF) p ℓ ⊢ Par.kids p K -∗
      |={E}=>m ∃ k : Oid, ⌜k ∉ K⌝ ∗ Par.kids p (K.insert k) ∗ oblKids k ∅ ∗ Obl.fuel k ℓ μ ∗
        Wit.layer k ℓ ∗
        untilIGuar N k 1 iprop(True) iprop(Q ∗ renew N Q G) TrSpec.true (renewTrSpec G) := by
  have hC := guar_renew_content (N := N) hQ
  iintro B Kp
  imod untilIGuar_alloc (E := E) p K ℓ μ $$ B Kp with ⟨%k, %hk, Kp, Kk, F, #W, ACC⟩
  imod ACC $$ %E %N %iprop(True) %iprop(Q ∗ renew N Q G) %TrSpec.true %(renewTrSpec G) [] []
    [] with U
  · inext
    iapply guar_true
  · inext
    iapply hC
  · inext
    ipureintro
    trivial
  imodintro
  iexists k
  isplitr
  · ipureintro
    exact hk
  iframe Kp Kk F U
  iexact W

/-- Renewal: the link `k` is discharged with `Q` and the next link at hand. -/
@[lantana_alias renew_discharge]
theorem renew_discharge (p : Parent) (K : Oids) (hN : ↑N ⊆ E) (hk : k ∈ K) :
    £ₙ 1 ⊢ Par.kids p K -∗ oblKids k ∅ -∗
      untilIGuar N k 1 iprop(True) iprop(Q ∗ renew N Q G) TrSpec.true (renewTrSpec G) -∗ Q -∗
      renew N Q G -∗
      |={E}=>m Q ∗ renew N Q G ∗ Par.kids p (K.erase k) ∗ Obl.discharged k := by
  iintro LC Kp Kk U HQ R
  imod untilIGuar_discharge_lc p K hN hk $$ LC Kp Kk U [HQ R] with ⟨⟨HQ, R⟩, Kp, D⟩
  · iframe HQ R
  imodintro
  iframe HQ R Kp D

/-! ### The readings on traces -/

omit instM instT [StateInterp Expr State GF] in
/-- On traces, `ν X. ◇ (G ∧ X)` is `◇ G`: the eventuality is not strict. -/
@[lantana_alias trSpec_nu_renew_ext]
theorem TrSpec.nu_renew_ext (G : TrSpec Expr State GF) :
    (TrSpec.nu (renewBody G)).external ⊆ ◇ₜ G.external := by
  rintro τ ⟨R, hR, hτ⟩
  obtain ⟨m, hm, ⟨hG, -⟩, -⟩ := hR τ hτ
  exact ⟨m, hm, hG, fun _ _ _ => trivial⟩

omit instM instT [StateInterp Expr State GF] in
@[lantana_alias trSpec_nu_renew_ext']
theorem TrSpec.nu_renew_ext' (G : TrSpec Expr State GF) :
    (◇ₜ G.external) ⊆ (TrSpec.nu (renewBody G)).external := by
  rintro τ ⟨m, hm, hG, -⟩
  refine ⟨fun τ' => ∃ m', τ'.pos ≤ m' ∧ G.external { τ' with pos := m' }, ?_, m, hm, hG⟩
  rintro τ' ⟨m', hm', hG'⟩
  exact ⟨m', hm', ⟨hG', m', Nat.le_refl _, hG'⟩, fun _ _ _ => trivial⟩

omit instM instT [StateInterp Expr State GF] in
/-- `□ ◇ G` reads as `□ ◇` of the reading of `G`: `G` infinitely often. -/
@[lantana_alias trSpec_always_finally_ext]
theorem TrSpec.always_eventually_ext (G : TrSpec Expr State GF) :
    (□ₛ ◇ₛ G).external = □ₜ ◇ₜ G.external :=
  rfl

/-- An always over a finally guarantees "infinitely often". -/
@[lantana_alias guar_always_finally]
theorem guar_always_finally (N' : Namespace) (q : Qp) :
    ⊢@{IProp GF} alwaysI (Expr := Expr) (State := State) N
      iprop(∃ k : Oid, finallyI (Expr := Expr) (State := State) N' k q Q) ⊨ₜ
      □ₛ ◇ₛ TrSpec.canon Q :=
  guar_alwaysI_valid ((forall_intro fun _ => guar_untilI_valid guar_true (guar_canon Q)).trans
    (guar_ex_ghost _))

end Renew

end Lantana
