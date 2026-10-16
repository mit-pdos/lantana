/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Examples.TicketLock2
public import Lantana.Examples.World

/-! # A client of the starvation-free ticket lock

Rocq `examples/ticket_lock2_client.v`: the main thread creates a ticket lock, acquires and
releases it, and returns `42`. Besides termination, its adequacy theorem exports the starvation
freedom of the lock (`TicketLock2.fairLock_starvationFree`), from the lock's guarantee
(`TicketLock2.guar_isFairLock`) through a commitment obligation `kc`: the main thread commits
to creating a fair lock (`finallyI Nc kc 1 (∃ tl γ, isFairLock tl γ True)`), which it keeps
right after `init`.

The layers: the lock is at level `0`; the main thread's obligations `kr` (to return `42`) and
`kc` are at the layer `aleph` (`0 + aleph`), above the lock's waiting at `ω`, as `acquire`
requires (Rocq: layer `ℵ`, see `TicketLock2.aleph`). The measure is
`100 + μ_init + μ_acquire + μ_release`, as in Rocq; the unlock obligation returned by `acquire`
gets `2 + μ_release` for the two steps before `release` and for `release` itself.

`ticketLockClient_adequacy` (Rocq `ticket_lock_client_adequacy`) is the end-to-end statement,
from `lwp_adequacy_temporal` in the closed world `ExGF` (with `TicketLock2G ExGF` from its slots
40–42), `ticketLockClient_safety_adequacy` the safety statement, from `lwp_adequacy_safety`,
and `ticketLockClient_liveness_safety` both. Statement adaptations: thread ids are list
positions, so the main thread is `0`; the initial heap is empty. Everything here is proved.
-/

@[expose] public noncomputable section

namespace Lantana.Examples.TicketLock2Client

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open Lantana.Examples.TicketLock2 (TicketLock2G TicketLockName isFairLock aleph fairLockTrSpec
  starvationFree fairLock_starvationFree)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The program -/

/-- `λ _, let l := init (); acquire l; release l; 42`. -/
@[lantana_alias ticket_lock2_client.TicketLockClient.main]
def main : Val :=
  hl_val(λ _,
    let l := v(&TicketLock2.init) #();
    v(&TicketLock2.acquire) l;
    v(&TicketLock2.release) l;
    #42)

/-- The value returned. -/
def v42 : Val := hl_val(#42)

/-- The namespaces of the main thread's commitments: to return, to create a fair lock. -/
def Nr : Namespace := nroot.@"tl_client_ret"
def Nc : Namespace := nroot.@"tl_client_lock"

/-! ## The specification -/

section Spec
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [TicketLock2G GF]

/-- What the main thread commits to: a fair lock exists. -/
abbrev someFairLock : IProp GF :=
  iprop(∃ (tl : Val) (γ : TicketLockName), isFairLock tl γ iprop(True))

/-- The main proof. Besides returning, the main thread commits to creating a fair lock. Its
obligations live at the layer `aleph`, above the lock's waiting (`acquire` at lock level
`0`). -/
@[lantana_alias ticket_lock2_client.TicketLockClient_main_spec]
theorem main_spec : ∃ μ : Measure, ∀ (i : ThreadId) (kr kc : Oid),
    ⊢@{IProp GF} l{{{ threadExpr i [] hl(v(&main) #()) ∗ thKids i {kr, kc} ∗
          ([∗set] g ∈ ({kr, kc} : Oids), Obl.fuel g aleph μ) ∗ ⌜kr ≠ kc⌝ ∗ oblKids kr ∅ ∗
          oblKids kc ∅ ∗ finallyI Nr kr 1 (exits v42 @ i) ∗ finallyI Nc kc 1 someFairLock }}}
        hl(v(&main) #()) @ i
      l{{{ (w : Val), RET w; threadExpr i [] hl(v(&w)) ∗ ⌜w = v42⌝ ∗
        liftTerm i (fun _ _ => iprop(True)) w }}} := by
  obtain ⟨μi, hinit⟩ := TicketLock2.init_spec (GF := GF)
  obtain ⟨μa, hacq⟩ := TicketLock2.acquire_spec (GF := GF)
  obtain ⟨μr, hrel⟩ := TicketLock2.release_spec (GF := GF)
  refine ⟨100 + μi + μa + μr, fun i kr kc => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, %hne, Hkr, Hkc, HFr, HFc⟩ HΦ
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, HFrel⟩
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, HFacq⟩
  icases (Obl.fuel_add_set _ _ _ _).mp $$ HF with ⟨HF, HFini⟩
  ihave HF := oblFuels_init _ _ _ $$ HF
  unfold main
  lwp_step HT HG HF with Hc : Ordinals.Ordinal.ofNat (1 + 1)
  icases (tlc_split_nat 1 1).mp $$ Hc with ⟨Hc1, Hc2⟩
  lwp_expr_simp
  -- `init`.
  lwp_bind hl(v(&TicketLock2.init) #()) HT
  iapply hinit 0 0 i {kr, kc} _ $$ [HT HG HFini]
  · iframe HT HG
    iapply oblFuels_init _ _ _ $$ HFini
  iintro %tl %γ ⟨HT, -, HG, CF, Hmk⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  imod Hmk $$ %⊤ %iprop(True) [] with #Hfl
  · ipureintro
    trivial
  -- Keep the commitment: the lock exists.
  ihave Hc1 := tlc_one_nat.mpr $$ Hc1
  imod finallyI_discharge (E := ⊤) (.thread i) {kr, kc} (fun _ _ => CoPset.mem_full) (by simp)
    $$ Hc1 HG Hkc HFc [] with ⟨-, HG, -⟩
  · iexists tl, γ
    iexact Hfl
  ihave HG := Par.kids_congr (B := {kr}) ?_ $$ HG
  · intro z
    simp
    grind
  ihave HF := oblFuels_subset _ (B := {kr}) (fun z hz => by simp_all) $$ HF
  ihave HFacq := BigSepS.bigSepS_subseteq (Y := ({kr} : Oids)) (fun z hz => by simp_all)
    $$ HFacq
  ihave HFrel := BigSepS.bigSepS_subseteq (Y := ({kr} : Oids)) (fun z hz => by simp_all)
    $$ HFrel
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- `acquire`, at lock level `0`; the unlock obligation `κu` gets `2 + μr`.
  lwp_bind hl(v(&TicketLock2.acquire) v(&tl)) HT
  have hacq' := hacq 0 (2 + μr) i {kr} tl γ (.own 1) 0 iprop(True)
  rw [Ordinals.Ordinal.zero_nadd] at hacq'
  iapply hacq' _ $$ [HT HG HFacq CF]
  · iframe HT HG HFacq CF
    iexact Hfl
  iintro %κu ⟨HT, -, %hκu, HG, Kκu, Fκu, -, Htok, -⟩
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  icases (Obl.fuel_add κu _ _ _).mp $$ Fκu with ⟨Fκu, Fκur⟩
  icases oblFuels_add 2 95 _ $$ HF with ⟨HF2, HF⟩
  ihave HF2 := oblFuels_add_obl {kr} κu 0 _ $$ Fκu HF2
  lwp_step HT HG HF2
  lwp_step HT HG HF2
  lwp_expr_simp
  -- `release`.
  lwp_bind hl(v(&TicketLock2.release) v(&tl)) HT
  ihave HFrel := oblFuels_init _ _ _ $$ HFrel
  ihave HFrel := oblFuels_add_obl {kr} κu 0 _ $$ Fκur HFrel
  iapply hrel 0 i (({kr} : Oids).insert κu) tl γ iprop(True) κu _ $$ [HT HG HFrel Kκu Htok]
  · iframe HT HG HFrel Kκu Htok
    isplitr
    · ipureintro
      exact Std.ExtTreeSet.mem_insert_self
    isplitr
    · ipureintro
      trivial
    · iexact Hfl
  iintro ⟨HT, -, HG⟩
  ihave HG := Par.kids_congr (B := {kr}) ?_ $$ HG
  · intro z
    simp at hκu ⊢
    grind
  ihave HT := (threadExpr_fill i [] _ _).mpr $$ HT
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  -- Return `42`, keeping the other commitment.
  rw [show (hl(#42) : Exp) = .val v42 from rfl]
  iapply lwp_value_mupd'.mpr
  ihave Hc2 := tlc_one_nat.mpr $$ Hc2
  imod threadExpr_terminate_finally i ⊤ v42 kr Nr (fun _ _ => CoPset.mem_full)
    $$ HT Hc2 HG Hkr HFr with ⟨HT, #Hd⟩
  imodintro
  iapply HΦ
  iframe HT
  isplitr
  · ipureintro
    rfl
  · unfold liftTerm
    isplitl
    · iexact Hd
    · ipureintro
      trivial

/-- The commitments of the main thread `i` and its resources (Rocq `Φ_P`). -/
def mainRes (i : ThreadId) (μ : Measure) : IProp GF :=
  iprop(∃ kr kc : Oid, finallyI Nr kr 1 (exits v42 @ i) ∗ finallyI Nc kc 1 someFairLock ∗
    (thKids i {kr, kc} ∗ oblKids kr ∅ ∗ oblKids kc ∅ ∗ ⌜kr ≠ kc⌝ ∗
      [∗set] g ∈ ({kr, kc} : Oids), Obl.fuel g aleph μ))

/-- The postcondition of the main thread. -/
abbrev mainPost : ThreadId → Val → IProp GF := fun _ w => iprop(⌜w = v42⌝)

/-- From the main thread's token and its empty set of children: its commitments, and its
`lWP` from them (Rocq `main_pre`). -/
@[lantana_alias ticket_lock2_client.main_pre]
theorem main_pre (i : ThreadId) :
    threadExpr (GF := GF) i [] hl(v(&main) #()) ⊢ thKids i ∅ -∗
      |={⊤}=>m ∃ μ : Measure, mainRes i μ ∗
        (mainRes i μ -∗ |={⊤}=>m lWP hl(v(&main) #()) @ i; ⊤ {{ liftTerm i mainPost }}) := by
  obtain ⟨μ, hmain⟩ := main_spec (GF := GF)
  iintro HT HG
  imod untilI_alloc (E := ⊤) (.thread i) ∅ aleph μ $$ [] HG with
    ⟨%kr, -, HG, Hkr, Fkr, -, Akr⟩
  · iapply parLe_thread
  imod Akr $$ %⊤ %Nr %iprop(True) %(exits v42 @ i) [] with Ur
  · inext
    ipureintro
    trivial
  imod untilI_alloc (E := ⊤) (.thread i) _ aleph μ $$ [] HG with
    ⟨%kc, %hkc, HG, Hkc, Fkc, -, Akc⟩
  · iapply parLe_thread
  imod Akc $$ %⊤ %Nc %iprop(True) %(someFairLock (GF := GF)) [] with Uc
  · inext
    ipureintro
    trivial
  have hne : kr ≠ kc := by
    rintro rfl
    exact hkc Std.ExtTreeSet.mem_insert_self
  imodintro
  iexists μ
  isplitl [Ur Uc HG Hkr Hkc Fkr Fkc]
  · unfold mainRes finallyI
    iexists kr, kc
    iframe Ur Uc Hkr Hkc
    isplitl [HG]
    · iapply Par.kids_congr _ $$ HG
      intro z
      simp
      grind
    isplitr
    · ipureintro
      exact hne
    iapply (bigSepS_pair hne).mpr
    iframe
  iintro HP
  unfold mainRes
  icases HP with ⟨%kr, %kc, HFr, HFc, HG, Hkr, Hkc, %hne, HF⟩
  imodintro
  iapply hmain i kr kc $$ [HT HG HF Hkr Hkc HFr HFc]
  · iframe
    ipureintro
    exact hne
  iintro %w ⟨-, %hw, Hd⟩
  unfold liftTerm
  icases Hd with ⟨Hd, -⟩
  iframe Hd
  ipureintro
  exact hw

end Spec

/-! ## Traces and the guarantee -/

section Guarantee
variable {GF : BundledGFunctors}

/-- The main thread `i` returns `42`, and a ticket lock gets created that is starvation free
(Rocq `client_spec`). -/
@[lantana_alias ticket_lock2_client.client_spec]
def clientSpec (i : ThreadId) : TrProp Exp State :=
  ◇ₜ TrProp.state (threadExprSat i [] (.val v42)) ∧ₜ
    ◇ₜ (∃ₜ (next : Loc) (curr : Loc), starvationFree next curr)

/-- What the commitments guarantee (Rocq `G_main`). -/
def gMain (i : ThreadId) : TrSpec Exp State GF :=
  ◇ₛ TrSpec.state (threadExprSat i [] (.val v42)) ∧ₛ ◇ₛ (∃ₛ tl : Val, fairLockTrSpec tl) ∧ₛ
    TrSpec.true

@[lantana_alias ticket_lock2_client.G_main_impl]
theorem gMain_impl (i : ThreadId) : (gMain (GF := GF) i).external ⊆ clientSpec i := by
  rintro τ ⟨hr, ⟨m, hm, ⟨tl, htl⟩, hbef⟩, -⟩
  obtain ⟨next, curr, -, hsf⟩ := fairLock_starvationFree (GF := GF) tl _ htl
  exact ⟨hr, m, hm, ⟨next, curr, hsf⟩, hbef⟩

variable [ModelGS GF] [HeapGS GF] [TicketLock2G GF]

@[lantana_alias ticket_lock2_client.guar_Φ_P]
theorem guar_mainRes (i : ThreadId) (μ : Measure) :
    ⊢@{IProp GF} mainRes i μ ⊨ₜ gMain i := by
  unfold mainRes gMain finallyI
  iapply guar_ex_ghost
  iintro %kr
  iapply guar_ex_ghost
  iintro %kc
  iapply guar_sep
  · iapply (GuarOf.guar_of (P := untilI (Expr := Exp) (State := State) Nr kr 1 iprop(True)
      (exits v42 @ i)))
  iapply guar_sep
  · iapply (GuarOf.guar_of (P := untilI (Expr := Exp) (State := State) Nc kc 1 iprop(True)
      (someFairLock (GF := GF))))
  iapply guar_true

end Guarantee

/-! ## Adequacy -/

section Adequacy

instance : TicketLock2G ExGF := {}

/-- The initial pool: the main thread `0`. -/
abbrev tp0 : ThreadPool Exp := [hl(v(&main) #())]

/-- The initial state: the empty heap. -/
abbrev σ0 : State := ⟨∅⟩

/-- In every fair behavior from the initial configuration, the main thread returns `42`, and a
ticket lock gets created that is starvation free. -/
@[lantana_alias ticket_lock2_client.ticket_lock_client_adequacy]
theorem ticketLockClient_adequacy (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    clientSpec 0 τ := by
  refine lwp_adequacy_temporal (GF := ExGF) σ0 tp0 0 (gMain 0) (clientSpec 0)
    (gMain_impl 0) τ hbeh hfair hpos hinit ?_
  intro _ _
  refine ⟨2, ?_⟩
  imod heapState_init σ0 tp0 with ⟨%hs, Hσ, -, HT⟩
  letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
  imodintro
  iexists instStateInterp, (fun _ _ => iprop(True)), mainPost
  isplitl [Hσ]
  · iexact Hσ
  iintro Hc HG
  rw [show List.range (List.length tp0) = [0] from rfl]
  ihave HG := BigSepL.bigSepL_singleton.mp $$ HG
  ihave HT := BigSepL.bigSepL_singleton.mp $$ HT
  imod main_pre 0 $$ HT HG with ⟨%μ, HP, Hwp⟩
  imodintro
  iexists mainRes 0 μ
  isplitr
  · iapply guar_mainRes
  iframe HP
  iintro HP
  imod Hwp $$ HP with Hwp
  imodintro
  iapply BigSepL.bigSepL_singleton.mpr
  iexact Hwp

/-- Safety: in every fair behavior from the initial configuration, the scheduled thread is never
stuck, and once the main thread has returned, its value is `42`. -/
@[lantana_alias ticket_lock2_client.ticket_lock_client_safety_adequacy]
theorem ticketLockClient_safety_adequacy (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    safetyIris 0 (fun _ w => w = v42) τ := by
  refine lwp_adequacy_safety (GF := ExGF) σ0 tp0 0 0 _ τ hbeh hfair hpos hinit (by decide) ?_
  intro _ _
  refine ⟨2, ?_⟩
  imod heapState_init σ0 tp0 with ⟨%hs, Hσ, -, HT⟩
  letI : HeapGS ExGF := { toTemporalGS := ‹_›, toHeapStateGS := hs }
  imodintro
  iexists instStateInterp, (fun _ _ => iprop(True)), mainPost
  isplit
  · ipureintro
    exact fun _ => .rfl
  isplitl [Hσ]
  · iexact Hσ
  iintro Hc HG
  rw [show List.range (List.length tp0) = [0] from rfl]
  ihave HG := BigSepL.bigSepL_singleton.mp $$ HG
  ihave HT := BigSepL.bigSepL_singleton.mp $$ HT
  imod main_pre 0 $$ HT HG with ⟨%μ, HP, Hwp⟩
  imod Hwp $$ HP with Hwp
  imodintro
  iapply BigSepL.bigSepL_singleton.mpr
  iexact Hwp

/-- Liveness and safety together, over the same fair behaviors: the main thread returns `42`,
a starvation-free lock gets created, and no scheduled thread is ever stuck. -/
@[lantana_alias ticket_lock2_client.ticket_lock_client_liveness_safety]
theorem ticketLockClient_liveness_safety (τ : Trace Exp State) (hbeh : IsBehavior τ)
    (hfair : fairScheduling τ) (hpos : τ.pos = 0) (hinit : τ.seq 0 = ⟨(tp0, σ0), 0⟩) :
    clientSpec 0 τ ∧ safetyIris 0 (fun _ w => w = v42) τ :=
  ⟨ticketLockClient_adequacy τ hbeh hfair hpos hinit,
    ticketLockClient_safety_adequacy τ hbeh hfair hpos hinit⟩

end Adequacy

end Lantana.Examples.TicketLock2Client
