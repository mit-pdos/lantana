/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Trace.TrSpec
public import Lantana.Trace.Adequacy.Step
public import Lantana.ProgramLogic.WeakestPre

/-! # Temporal guarantees `P ⊨ₜ G`: records, certificates and the one-step property

Rocq `lantana/trace/guarantee.v`: a persistent guarantee `P ⊨ₜ G` states that whenever `P`
holds, the rest of the execution satisfies the trace specification `G`; adequacy concludes
`G.external`.

At position `n`, `P ⊨ₜ G` turns `P` (with the history and model interpretations) into a
persistent **record** `record G n`, which gives the internal reading of `G` at `n` once the step
from `n` is made. A record may be written in the pre-step update of step `n` (e.g. by
discharging an until), so it is eliminated after the step, against the **bundle** of
certificates for `n`: each registered structure (`TemporalRegistry`) has its content certified
at every position (`certPre`, a later-guarded record). A record holds for any running system
with the **one-step property** `sysStep` (`lWP` is one, `Adequacy/Temporal`).

The pure facts about the run (D18): the trace is a behavior from the current position, the
fairness counters are an explicit sequence `γ : Nat → ThreadId → Nat` along the trace
(`BehFscnt`), the witnesses are bounded below by the fair-scheduler measure of the current
counters (`owitInvLb`), the ghost history is a prefix of the trace (`histTrace`), and across a
step every assigned obligation's measure drops (`oblsDrop`). Records are a guarded fixpoint
(`recordTrI`): the certificates hold the records under a later.

`TrSpec.canon P` is the canonical (strongest) specification guaranteed by `P`. The rules are in
`Lantana.Trace.GuaranteeRules`; the class `StateFact` of the atoms of trace specifications is
here, so that a language can provide its instances without the rules.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI
open Lantana.Model
open scoped Lantana.TrSpec Lantana.TrProp

variable {Expr State Val : Type} {GF : BundledGFunctors}

/-! ## Records, certificates and the one-step property -/

/-- The ghost history `h` is a prefix of the trace `τf`. -/
@[lantana_alias hist_trace]
def histTrace (h : List (HistEntry Expr State)) (τf : Nat → TraceState Expr State) : Prop :=
  ∀ n' σ' tp', h[n']? = some (σ', tp') → ∃ i', τf n' = ⟨(tp', σ'), i'⟩

/-- Records: a reading `f` at a position (Rocq `recT`). -/
abbrev RecT (Expr State : Type) (GF : BundledGFunctors) :=
  (Trace Expr State → IProp GF) → Nat → IProp GF

/-- A running system: a resource indexed by the position and the configuration
(Rocq `sysT`). -/
abbrev SysT (Expr State : Type) (GF : BundledGFunctors) :=
  Nat → State → ThreadPool Expr → IProp GF

section Pre
variable [ModelGS GF] [TemporalGS Expr State GF]

/-- The certificate of a registered item at `n`: a later-guarded record of its content at `n`.
For an until, the record of its left or right formula at `n`, or, if it was discharged at
`n' ≤ n`, the record of its right formula at `n'`. -/
@[lantana_alias cert_pre]
def certPre (tg : RecT Expr State GF) (n : Nat) : RegEntry → IProp GF
  | .mark => iprop(True)
  | .always _ γ => iprop(∃ f : Trace Expr State → IProp GF, savedTrI γ f ∗ ▷ tg f n)
  | .until _ k γP γQ => iprop(∃ fP fQ : Trace Expr State → IProp GF,
      savedTrI γP fP ∗ savedTrI γQ fQ ∗
      (▷ (tg fP n ∨ tg fQ n) ∨
        ▷ (∃ (n' i' : Nat) (Ω' : Obls),
          ⌜n' ≤ n⌝ ∗ eventObl i' (n', Ω') k .discharged ∗ tg fQ n')))

/-- The bundle for position `n`: a registry prefix ending with the marker of `n` and the
certificates of its entries. -/
@[lantana_alias bundle_pre]
def bundlePre (tg : RecT Expr State GF) (l : List (Nat × RegEntry)) (n : Nat) : IProp GF :=
  iprop(regLb l ∗ ⌜l.getLast? = some (n, .mark)⌝ ∗ [∗list] pe ∈ l, certPre tg n pe.2)

variable [Language Expr State Val] [StateInterp Expr State GF]

/-- The one-step property of `Sys`: from a consistent system at `n`, the bundle for `n` (the
check), then after the step the system at `n + 1`, the facts about the step and `c` later
credits. The modalities are those of `TrIProp.defer`. -/
@[lantana_alias sys_step_pre]
def sysStepPre (tg : RecT Expr State GF) (Sys : SysT Expr State GF) : IProp GF :=
  iprop(□ ∀ (c : Nat) (h : List (HistEntry Expr State)) (n : Nat) (σ : State)
      (tp : ThreadPool Expr) (g : List MEvent) (v : Nat) (Ω : Obls) (W : Witnesses)
      (τf : Nat → TraceState Expr State) (γ : Nat → ThreadId → Nat),
    ⌜IsBehavior (⟨n, τf⟩ : Trace Expr State) ∧ BehFscnt ⟨n, τf⟩ γ ∧
      owitInvLb (fairMeasure (γ n)) Ω W ∧ histTrace h τf⌝ -∗
    historyInterp h n σ tp ∗ modelInterp g v Ω W n tp.length ∗ Sys n σ tp -∗
    |={⊤,∅}=> ∃ l, bundlePre tg l n ∗ ▷ |={∅,⊤}=> |={⊤,∅}=> ALC iprop(|={∅,⊤}=>
      ∃ (σ' : State) (tp' : ThreadPool Expr) (g' : List MEvent) (v' : Nat) (Ω' : Obls)
        (W' : Witnesses),
        ⌜IsBehavior (⟨n + 1, τf⟩ : Trace Expr State) ∧ BehFscnt ⟨n + 1, τf⟩ γ ∧
          owitInvLb (fairMeasure (γ (n + 1))) Ω' W' ∧ histTrace (h ++ [(σ', tp')]) τf ∧
          oblsDrop (fairMeasure (γ n)) (fairMeasure (γ (n + 1))) Ω Ω'⌝ ∗
        £ₙ c ∗ historyInterp (h ++ [(σ', tp')]) (n + 1) σ' tp' ∗
        modelInterp g' v' Ω' W' (n + 1) tp'.length ∗ Sys (n + 1) σ' tp'))

/-- A record for `f` at `n`: for any system with the one-step property, given the bundle for
`n` and the system at `n + 1` consistent with the trace, `f` holds at `n` on the trace. -/
@[lantana_alias record_pre]
def recordPre (tg : RecT Expr State GF) : RecT Expr State GF := fun f n =>
  iprop(□ ∀ (Sys : SysT Expr State GF) (l : List (Nat × RegEntry))
      (h : List (HistEntry Expr State)) (g : List MEvent) (v : Nat) (Ω : Obls) (W : Witnesses)
      (τf : Nat → TraceState Expr State) (γ : Nat → ThreadId → Nat) (σ : State)
      (tp : ThreadPool Expr),
    sysStepPre tg Sys -∗
    ⌜IsBehavior (⟨n, τf⟩ : Trace Expr State) ∧ BehFscnt ⟨n + 1, τf⟩ γ ∧
      owitInvLb (fairMeasure (γ (n + 1))) Ω W ∧ histTrace h τf⌝ -∗
    bundlePre tg l n -∗
    historyInterp h (n + 1) σ tp ∗ modelInterp g v Ω W (n + 1) tp.length ∗ Sys (n + 1) σ tp -∗
    f ⟨n, τf⟩)

end Pre

/-! ### Contractiveness: the certificates hold the records under a later -/

section Contractive
variable [ModelGS GF] [TemporalGS Expr State GF]

@[lantana_alias cert_pre_contractive]
theorem certPre_contractive {k : SI} {tg₁ tg₂ : RecT Expr State GF} (h : OFE.DistLater k tg₁ tg₂)
    (n : Nat) (e : RegEntry) : certPre tg₁ n e ≡{k}≡ certPre tg₂ n e := by
  rcases e with _ | ⟨N, γ⟩ | ⟨N, o, γP, γQ⟩
  · exact .rfl
  · exact exists_ne fun f => sep_ne.ne .rfl <|
      OFE.Contractive.distLater_dist (f := BIBase.later) fun m hm => h m hm f n
  · exact exists_ne fun fP => exists_ne fun fQ => sep_ne.ne .rfl <| sep_ne.ne .rfl <|
      or_ne.ne
        (OFE.Contractive.distLater_dist (f := BIBase.later) fun m hm =>
          or_ne.ne (h m hm fP n) (h m hm fQ n))
        (OFE.Contractive.distLater_dist (f := BIBase.later) fun m hm =>
          exists_ne fun n' => exists_ne fun _ => exists_ne fun _ =>
            sep_ne.ne .rfl (sep_ne.ne .rfl (h m hm fQ n')))

@[lantana_alias bundle_pre_contractive]
theorem bundlePre_contractive {k : SI} {tg₁ tg₂ : RecT Expr State GF}
    (h : OFE.DistLater k tg₁ tg₂) (l : List (Nat × RegEntry)) (n : Nat) :
    bundlePre tg₁ l n ≡{k}≡ bundlePre tg₂ l n :=
  sep_ne.ne .rfl <| sep_ne.ne .rfl <|
    BigSepL.bigSepL_dist fun _ => certPre_contractive h n _

variable [Language Expr State Val] [StateInterp Expr State GF]

@[lantana_alias sys_step_pre_contractive]
theorem sysStepPre_contractive {k : SI} {tg₁ tg₂ : RecT Expr State GF}
    (h : OFE.DistLater k tg₁ tg₂) (Sys : SysT Expr State GF) :
    sysStepPre tg₁ Sys ≡{k}≡ sysStepPre tg₂ Sys := by
  unfold sysStepPre
  refine intuitionistically_ne.ne ?_
  iterate 11 refine forall_ne fun _ => ?_
  exact wand_ne.ne .rfl <| wand_ne.ne .rfl <| fupd_ne.ne <| exists_ne fun l =>
    sep_ne.ne (bundlePre_contractive h l _) .rfl

@[lantana_alias record_pre_contractive]
instance recordPre_contractive :
    OFE.Contractive (recordPre (Expr := Expr) (State := State) (GF := GF)) where
  distLater_dist h f n := by
    unfold recordPre
    refine intuitionistically_ne.ne ?_
    iterate 11 refine forall_ne fun _ => ?_
    exact wand_ne.ne (sysStepPre_contractive h _) <| wand_ne.ne .rfl <|
      wand_ne.ne (bundlePre_contractive h _ _) .rfl

end Contractive

/-! ### Records, bundles, certificates and the one-step property -/

section Records
variable [ModelGS GF] [TemporalGS Expr State GF] [Language Expr State Val]
  [StateInterp Expr State GF]

/-- Records of step-indexed readings: the guarded fixpoint of `recordPre`. -/
@[lantana_alias record_trI]
def recordTrI : RecT Expr State GF := fixpoint recordPre

theorem recordTrI_eq (f : Trace Expr State → IProp GF) (n : Nat) :
    recordTrI f n = recordPre recordTrI f n :=
  congrFun (congrFun (fixpoint_unfold (recordPre (Expr := Expr) (State := State)
    (GF := GF)).toContractiveHom) f) n

@[lantana_alias record_trI_unfold]
theorem recordTrI_unfold (f : Trace Expr State → IProp GF) (n : Nat) :
    recordTrI f n ⊣⊢ recordPre recordTrI f n :=
  BiEntails.of_eq (recordTrI_eq f n)

@[lantana_alias record_trI_persistent]
instance recordTrI_persistent (f : Trace Expr State → IProp GF) (n : Nat) :
    Persistent (recordTrI f n) := by
  rw [recordTrI_eq]
  unfold recordPre
  infer_instance

@[lantana_alias record_trI_ne]
instance recordTrI_ne (n : Nat) :
    OFE.NonExpansive (fun f : Trace Expr State → IProp GF => recordTrI f n) where
  ne k f₁ f₂ hf := by
    simp only [recordTrI_eq]
    unfold recordPre
    refine intuitionistically_ne.ne ?_
    iterate 11 refine forall_ne fun _ => ?_
    exact wand_ne.ne .rfl <| wand_ne.ne .rfl <| wand_ne.ne .rfl <| wand_ne.ne .rfl (hf _)

/-- Records of internally equal readings (the agreement of saved readings is internal). -/
@[lantana_alias record_trI_eq]
theorem recordTrI_internalEq (f g : Trace Expr State → IProp GF) (n : Nat) :
    iprop(f ≡ g) ⊢ recordTrI f n -∗ recordTrI g n :=
  wand_intro <| sep_and.trans <| imp_elim (internalEq.rewrite (fun f => recordTrI f n))

/-- The record of a trace specification at `n`. -/
@[lantana_alias record]
def record (G : TrSpec Expr State GF) (n : Nat) : IProp GF := recordTrI G.internal n

/-- The bundle for `n`, with records as the certified readings. Irreducible, so that `inext`
does not strip the laters of the certificates. -/
@[lantana_alias bundle, irreducible]
def bundle (l : List (Nat × RegEntry)) (n : Nat) : IProp GF :=
  bundlePre (recordTrI (Expr := Expr) (State := State)) l n

/-- The certificate of an entry at `n` (irreducible, as `bundle`). -/
@[lantana_alias cert, irreducible]
def cert (n : Nat) (e : RegEntry) : IProp GF :=
  certPre (recordTrI (Expr := Expr) (State := State)) n e

/-- The one-step property of a running system (irreducible, as `bundle`). -/
@[lantana_alias sys_step, irreducible]
def sysStep (Sys : SysT Expr State GF) : IProp GF := sysStepPre recordTrI Sys

theorem bundle_eq (l : List (Nat × RegEntry)) (n : Nat) :
    bundle (Expr := Expr) (State := State) (GF := GF) l n = bundlePre recordTrI l n := by
  unfold bundle; rfl

theorem cert_eq (n : Nat) (e : RegEntry) :
    cert (Expr := Expr) (State := State) (GF := GF) n e = certPre recordTrI n e := by
  unfold cert; rfl

theorem sysStep_eq (Sys : SysT Expr State GF) : sysStep Sys = sysStepPre recordTrI Sys := by
  unfold sysStep; rfl

@[lantana_alias record_persistent]
instance record_persistent (G : TrSpec Expr State GF) (n : Nat) : Persistent (record G n) := by
  unfold record; infer_instance

@[lantana_alias cert_pre_persistent]
instance certPre_persistent (n : Nat) (e : RegEntry) :
    Persistent (certPre (recordTrI (Expr := Expr) (State := State) (GF := GF)) n e) := by
  rcases e with _ | ⟨N, γ⟩ | ⟨N, o, γP, γQ⟩ <;> unfold certPre <;> infer_instance

@[lantana_alias cert_persistent]
instance cert_persistent (n : Nat) (e : RegEntry) :
    Persistent (cert (Expr := Expr) (State := State) (GF := GF) n e) := by
  rw [cert_eq]; infer_instance

@[lantana_alias bundle_persistent]
instance bundle_persistent (l : List (Nat × RegEntry)) (n : Nat) :
    Persistent (bundle (Expr := Expr) (State := State) (GF := GF) l n) := by
  rw [bundle_eq]; unfold bundlePre; infer_instance

@[lantana_alias sys_step_persistent]
instance sysStep_persistent (Sys : SysT Expr State GF) : Persistent (sysStep Sys) := by
  rw [sysStep_eq]; unfold sysStepPre; infer_instance

end Records

end Lantana
