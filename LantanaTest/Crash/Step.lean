/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LantanaTest.Crash.Lang

/-! # A language whose threads crash: the step rule and the facts about the pool

`lwp_step` is the library's `lwp_lift_step_gen_si` for this language: before the step the thread
chooses, having seen the configuration, to pay its bill (running) or nothing (crashed); after it,
under the step's later credits, a model update at the empty mask hands in the nodes of the
threads the step crashes and receives those of the threads it recovers (`Th.nodes`). The facts
about the pool say which threads a step crashes or recovers.
-/

@[expose] public noncomputable section

namespace LantanaTest.Crash

open Iris Iris.BI Iris.ProofMode Iris.Std
open Ordinals Ordinal Lantana Lantana.Model
open Iris.ProgramLogic (toVal Language PrimStep EvContext EvContextOps)

/-! ## The pool -/

theorem fill_eq (K : Unit) (e : Exp) : EvContext.fill K e = e := rfl

theorem crashed_cfg_iff {tp : ThreadPool Exp} {σ : St} {j : ThreadId} :
    Cfg.crashed (tp, σ) j ↔ (∃ n, tp[j]? = some (.work n)) ∧ σ = false := by
  constructor
  · rintro ⟨e, he, ⟨n, rfl⟩, hσ⟩
    exact ⟨⟨n, he⟩, hσ⟩
  · rintro ⟨⟨n, hn⟩, hσ⟩
    exact ⟨_, hn, ⟨n, rfl⟩, hσ⟩

/-- While the worker is alive, no thread is crashed. -/
theorem not_crashed_true (tp : ThreadPool Exp) (j : ThreadId) : ¬ Cfg.crashed (tp, true) j :=
  fun h => Bool.noConfusion (crashed_cfg_iff.mp h).2

/-- A step of a thread that is not a worker, to an expression that is not a worker, keeping the
state, keeps the statuses. -/
theorem crashed_set_eq {tp : ThreadPool Exp} {i : ThreadId} {e₁ e₂ : Exp} {σ : St}
    (hi : tp[i]? = some e₁) (h₁ : ∀ n, e₁ ≠ .work n) (h₂ : ∀ n, e₂ ≠ .work n) :
    Cfg.crashed (tp.set i e₂, σ) = Cfg.crashed (tp, σ) := by
  refine Cfg.crashed_eq_of_iff fun j => ?_
  simp only [crashed_cfg_iff]
  by_cases hj : i = j
  · subst hj
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hi).1, hi]
    simp only [Option.some.injEq]
    constructor
    · rintro ⟨⟨n, hn⟩, -⟩
      exact (h₂ n hn).elim
    · rintro ⟨⟨n, hn⟩, -⟩
      exact (h₁ n hn).elim
  · rw [List.getElem?_set_ne hj]

/-- A step of the worker keeps the statuses: alive, nobody is crashed; crashed, it loops. -/
theorem crashed_set_eq_worker {tp : ThreadPool Exp} {n : Nat} {e₂ : Exp} {σ₁ σ₂ : St}
    (hi : tp[0]? = some (.work n)) (hs : Step (.work n) σ₁ e₂ σ₂) :
    Cfg.crashed (tp.set 0 e₂, σ₂) = Cfg.crashed (tp, σ₁) := by
  cases hs with
  | work n =>
    exact Cfg.crashed_eq_of_iff fun j =>
      ⟨fun h => (not_crashed_true _ j h).elim, fun h => (not_crashed_true _ j h).elim⟩
  | finish =>
    exact Cfg.crashed_eq_of_iff fun j =>
      ⟨fun h => (not_crashed_true _ j h).elim, fun h => (not_crashed_true _ j h).elim⟩
  | idle n =>
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hi
    rw [← heq, List.set_getElem_self hlt]

theorem fin_set_ne {tp : ThreadPool Exp} {i : ThreadId} (hi : i ≠ 0) (e : Exp) :
    fin (tp.set i e) = fin tp := by
  unfold fin
  rw [List.getElem?_set_ne hi]

/-- A step of another thread than the worker, to an expression that is not a worker, keeps the
shape of the pool. -/
theorem Shape.set_ne {tp : ThreadPool Exp} (hS : Shape tp) {i : ThreadId} (hi : i ≠ 0) {e : Exp}
    (he : ∀ n, e ≠ .work n) : Shape (tp.set i e) := by
  refine ⟨fun j n hj => ?_, ?_⟩
  · by_cases hij : i = j
    · subst hij
      have hlt : i < tp.length := by
        have := (List.getElem?_eq_some_iff.mp hj).1
        simpa using this
      rw [List.getElem?_set_self hlt] at hj
      exact (he n (Option.some.inj hj)).elim
    · rw [List.getElem?_set_ne hij] at hj
      exact hS.1 j n hj
  · rw [List.getElem?_set_ne hi]
    exact hS.2

/-- A step of the worker, to a worker or to the value, keeps the shape of the pool. -/
theorem Shape.set_zero {tp : ThreadPool Exp} (hS : Shape tp) {e : Exp}
    (he : (∃ n, e = .work n) ∨ e = .ret) : Shape (tp.set 0 e) := by
  have hlt : 0 < tp.length := by
    rcases hS.2 with ⟨n, h⟩ | h <;> exact (List.getElem?_eq_some_iff.mp h).1
  refine ⟨fun j n hj => ?_, ?_⟩
  · by_cases hj0 : 0 = j
    · exact hj0.symm
    · rw [List.getElem?_set_ne hj0] at hj
      exact hS.1 j n hj
  · rw [List.getElem?_set_self hlt]
    rcases he with ⟨n, rfl⟩ | rfl
    · exact .inl ⟨n, rfl⟩
    · exact .inr rfl

/-- While the worker has not finished, it is a worker. -/
theorem Shape.work_of_fin {tp : ThreadPool Exp} (hS : Shape tp) (hf : fin tp = false) :
    ∃ n, tp[0]? = some (.work n) := by
  rcases hS.2 with h | h
  · exact h
  · unfold fin at hf
    rw [h] at hf
    simp at hf

/-- Once the worker has finished, no thread is crashed. -/
theorem not_crashed_fin {tp : ThreadPool Exp} (hS : Shape tp) (hf : fin tp = true) (σ : St)
    (j : ThreadId) : ¬ Cfg.crashed (tp, σ) j := by
  rintro h
  obtain ⟨⟨n, hn⟩, -⟩ := crashed_cfg_iff.mp h
  have hj := hS.1 j n hn
  subst hj
  unfold fin at hf
  rw [hn] at hf
  simp at hf

/-! ## The step rule -/

section Lifting
variable {GF : BundledGFunctors} [ModelGS GF] [CrashGS GF]
variable {s : Stuckness} {i : ThreadId} {E : CoPset} {e₁ : Exp} {Φ : Unit → IProp GF}

/-- `lwp_lift_step_gen_si` for this language, which has no context, no fork and no witness: having
seen the configuration, the thread pays its bill `G` (`G' = G`) or, crashed, nothing (`G' = ∅`);
after the step, a model update at the empty mask hands in the nodes of the threads the step
crashes and receives those of the threads it recovers. -/
theorem lwp_step (he : toVal e₁ = none) :
    (∀ (σ₁ : St) (tp : ThreadPool Exp), ⌜tp[i]? = some e₁⌝ →
      stateInterp σ₁ tp ={E,∅}=∗
        ⌜s.maybeReducible e₁ σ₁⌝ ∗
        ∃ G G', thCarriers i G ∗ (oblFuels G 1 ∗ ⌜G' = G⌝ ∨ ⌜Cfg.crashed (tp, σ₁) i ∧ G' = ∅⌝) ∗
        ∀ (e₂ : Exp) (σ₂ : St), ⌜Step e₁ σ₁ e₂ σ₂⌝ ={∅}=∗
          stateInterp σ₂ (tp.set i e₂) ∗
          (thCarriers i G' -∗ ALC (|={∅}=>m
            Th.nodes tp.length (fun j =>
              ¬Cfg.crashed (tp, σ₁) j ∧ Cfg.crashed (tp.set i e₂, σ₂) j) ∗
            (Th.nodes tp.length (fun j =>
                Cfg.crashed (tp, σ₁) j ∧ ¬Cfg.crashed (tp.set i e₂, σ₂) j) -∗
              |={∅,E}=> |={E}=>m lWP e₂ @ s; i; E {{ Φ }}))))
      ⊢ lWP e₁ @ s; i; E {{ Φ }} := by
  iintro H
  iapply lwp_lift_step_gen_si he
  iintro %K %σ₁ %tp %_ %hi Hs
  imod H $$ %σ₁ %tp %hi Hs with ⟨%hred, %G, %G', HG, HF, H⟩
  imodintro
  isplitr
  · ipureintro
    exact hred
  iexists G, G'
  iframe HG HF
  iexists ∅
  isplitr
  · iunfold witLayers
    iapply BigSepS.bigSepS_empty.mpr
    iempintro
  iintro %obs %e₂ %σ₂ %efs %hstep
  obtain ⟨hst, rfl⟩ := primStep_iff.mp hstep
  imod H $$ %e₂ %σ₂ %hst with ⟨Hs, H⟩
  imodintro
  simp only [fill_eq, List.append_nil, List.length_nil, Nat.add_zero]
  iframe Hs
  iintro HG - -
  ispecialize H $$ HG
  iapply ALC_wand $$ [] H
  iintro H
  iapply mupd_wand $$ [] H
  iintro ⟨Hin, Hout⟩
  iframe Hin
  iintro Hout'
  imod Hout $$ Hout' with H
  imodintro
  iapply mupd_wand $$ [] H
  iintro H
  iframe H
  iapply BigSepL.bigSepL_nil.mpr
  iempintro

end Lifting

end LantanaTest.Crash
