/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.Examples.World

/-! # The no-credit rule is unsound

Rocq `examples/paradox.v`. The class `LwpNoLc` assumes, for HeapLang, a rule for one pure step
that pays no fuel and gives no later credits, yet yields a witness credit for each observed
obligation that is not discharged (`lwp_pure_step_no_lc`; compare `lwp_pure_step`: no thread
token, no children with their fuel, no `ALC`/`£`). With it, two threads running
`rec loop _ := loop ()` prove "eventually `False`" (`loop_paradox`), and a fair run of the loops
refutes the rule (`no_lc_absurd`).

Thread `0` holds the commitment `untilI N1 z 1 True False`, which it never keeps, and steps by
the assumed rule, observing in every step the current obligation `ck` of thread `1` as a
witness: a witness credit decreases its witness fuel (`Wit.fuels_ind`, well-founded); once `ck`
is discharged, thread `0` reads the next obligation and ten later credits from the invariant
`px` and continues by Löb induction (`px_loop1_spec`). Thread `1` pays its steps honestly with
the fuel of `ck`; in each iteration it allocates the next obligation `ck1`, registers it with
ten later credits in the invariant at the next index, and discharges `ck` (`px_loop2_spec`).
The invariant `pxInv` keeps, per index `a`, the obligation `k` registered there, its witness,
and either the ten credits or a lower bound of thread `0`'s counter past `a` (the credits have
been taken), and either half of the until on `k` or its discharge with the next entry.

The assumed rule is a hypothesis of the theorems (the class, assumed for every instance of the
ghost state of the closed world `ExGF`), never an axiom. Statement adaptations: thread ids are
list positions (Rocq `i`, `j` are `0`, `1`); the counters are two mono-nat ghost names (Rocq: one
`gmap positive mono_nat` camera with fresh keys); the hypothesis is over `ExGF` only (Rocq: over
every `Σ` with `heapGS Σ`), which makes the theorems stronger.
-/

@[expose] public noncomputable section

namespace Lantana.Examples.Paradox

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open Iris.Std (get? insert)
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The assumed rule -/

/-- The no-credit rule (Rocq `lantanaGS_no_lc`): one pure step that pays no fuel and gives no
later credits, yet yields a witness credit for each obligation of `R` that is not discharged. -/
@[lantana_alias lantanaGS_no_lc]
class LwpNoLc (GF : BundledGFunctors) [ModelGS GF] [HeapGS GF] : Prop where
  lwp_pure_step_no_lc (s : Stuckness) (i : ThreadId) (E E' : CoPset) (e₁ e₂ : Exp) (φ : Prop)
    (Φ : Val → IProp GF) : PureExec φ 1 e₁ e₂ → φ →
    (|={E,E'}=> ∃ R : Oids, witLayers R ∗
      (witCreds R -∗ |={E',E}=> |={E}=>m lWP e₂ @ s; i; E {{ Φ }})) ⊢
      lWP e₁ @ s; i; E {{ Φ }}

attribute [lantana_alias lwp_pure_step_no_lc] LwpNoLc.lwp_pure_step_no_lc

/-! ## The program -/

/-- `rec loop _ := loop ()`. -/
@[lantana_alias paradox.loop]
def loop : Val := hl_val(rec loop _ := loop #())

/-! ## The ghost state: counters and a ghost map of obligations -/

/-- Finite maps from indices. -/
abbrev IdxMap : Type → Type := OidMap

/-- The cameras of the paradox (Rocq `mcntsG`): mono-nat counters and a ghost map from indices
to obligations. -/
@[lantana_alias mcntsG]
class ParadoxG (GF : BundledGFunctors) where
  [cntG : MonoNatG GF]
  [mapG : GhostMapG GF Nat Oid IdxMap]

attribute [reducible, instance] ParadoxG.cntG ParadoxG.mapG

instance : ParadoxG ExGF where

section Counters
variable {GF : BundledGFunctors} [ParadoxG GF]

/-- The fraction `q` of the authority of the counter `γ`, at `n`. -/
@[lantana_alias cnt_auth]
def cntAuth (γ : GName) (n : Nat) (q : Qp) : IProp GF := MonoNat.auth_own γ (.own q) ⟨n⟩

/-- The counter `γ` is at least `n`. -/
@[lantana_alias cnt_lb]
def cntLb (γ : GName) (n : Nat) : IProp GF := MonoNat.lb_own γ ⟨n⟩

@[lantana_alias cnt_lb_persistent]
instance cntLb_persistent (γ : GName) (n : Nat) : Persistent (cntLb (GF := GF) γ n) := by
  unfold cntLb; infer_instance

@[lantana_alias cnt_auth_timeless]
instance cntAuth_timeless (γ : GName) (n : Nat) (q : Qp) : Timeless (cntAuth (GF := GF) γ n q) := by
  unfold cntAuth; infer_instance

@[lantana_alias cnt_lb_timeless]
instance cntLb_timeless (γ : GName) (n : Nat) : Timeless (cntLb (GF := GF) γ n) := by
  unfold cntLb; infer_instance

/-- The authority is two halves. -/
theorem cntAuth_halves (γ : GName) (n : Nat) :
    cntAuth (GF := GF) γ n 1 ⊣⊢ cntAuth γ n (1 : Qp).half ∗ cntAuth γ n (1 : Qp).half := by
  have h := (inferInstance : Fractional (PROP := IProp GF)
    (fun q : Qp => MonoNat.auth_own γ (.own q) (⟨n⟩ : MaxNat))).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

@[lantana_alias get_cnt_lb]
theorem cntAuth_lb (γ : GName) {m n : Nat} (q : Qp) (h : m ≤ n) :
    cntAuth (GF := GF) γ n q ⊢ cntLb γ m := by
  unfold cntAuth cntLb
  iintro H
  ihave H := MonoNat.lb_own_get γ _ _ $$ H
  iapply MonoNat.lb_own_le γ ⟨n⟩ ⟨m⟩ h $$ H

@[lantana_alias cnt_auth_op_valid]
theorem cntAuth_agree (γ : GName) (n₁ n₂ : Nat) (q₁ q₂ : Qp) :
    cntAuth (GF := GF) γ n₁ q₁ ⊢ cntAuth γ n₂ q₂ -∗ ⌜n₁ = n₂⌝ := by
  unfold cntAuth
  iintro H₁ H₂
  ihave %h := MonoNat.auth_own_agree γ _ _ _ _ $$ H₁ H₂
  ipureintro
  exact congrArg MaxNat.toNat h.2

@[lantana_alias cnt_auth_lb_valid]
theorem cntAuth_lb_valid (γ : GName) (n m : Nat) (q : Qp) :
    cntAuth (GF := GF) γ n q ⊢ cntLb γ m -∗ ⌜m ≤ n⌝ := by
  unfold cntAuth cntLb
  iintro H₁ H₂
  ihave %h := MonoNat.auth_lb_own_valid γ _ _ _ $$ H₁ H₂
  ipureintro
  exact h.2

@[lantana_alias cnt_auth_update]
theorem cntAuth_update (γ : GName) {n m : Nat} (h : n ≤ m) :
    cntAuth (GF := GF) γ n 1 ⊢ |==> cntAuth γ m 1 := by
  unfold cntAuth
  iintro H
  imod MonoNat.own_update γ ⟨n⟩ ⟨m⟩ h $$ H with ⟨H, -⟩
  imodintro
  iexact H

@[lantana_alias alloc_cnt_auth]
theorem cntAuth_alloc (n : Nat) : ⊢@{IProp GF} |==> ∃ γ : GName, cntAuth γ n 1 := by
  unfold cntAuth
  imod MonoNat.own_alloc (GF := GF) ⟨n⟩ with ⟨%γ, H, -⟩
  imodintro
  iexists γ
  iexact H

end Counters

end Lantana.Examples.Paradox
