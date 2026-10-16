module

public import Lantana

/-! Tests of the examples: the trace-level facts of the flags, the programs of `nondet` and of the
handoff, the closed world of the adequacy corollaries, and the `exits` notation. -/

namespace LantanaTest.Examples

open Lantana Lantana.HeapLang Lantana.Examples
open scoped Lantana.TrProp Lantana.TrSpec

variable {GF : Iris.BundledGFunctors}

/-- The run `0, 1, 0, 1, 1, …` separates the guarantees of the two flags. -/
example (l : Loc) : ∃ τ : Trace Exp State,
    (Flag.flagTrSpec (GF := GF) l).external τ ∧
      ¬ (FlagStable.flagTrSpec (GF := GF) l).external τ :=
  ⟨_, Flag.flagRun_satisfies_guarantee l, FlagStable.flagRun_violates_guarantee l⟩

/-- Both flags respond: a `0` is eventually followed by a `1`. -/
example (l : Loc) : (FlagStable.flagTrSpec (GF := GF) l).external ⊆ Flag.flagResponse l :=
  fun τ h m hm h₀ => TrProp.eventually_mono TrProp.always_elim _
    (FlagStable.flagResponse_ext l τ h m hm h₀)

/-- The flag is `1` at the positions `1`, `3`, `4`, … of the run. -/
example (l : Loc) : Flag.pointsToTr l Flag.v1 ⟨3, Flag.flagRun l⟩ :=
  (Flag.flagRun_at l 3 _).mpr rfl

/-- `nondet` forks `nest` on the flag it creates and waits for it. -/
example : Nondet.nondet = hl_val(λ _,
    let n := chooseNat();
    let x := v(&Flag.init) #();
    fork(v(&Nondet.nest) x n);
    v(&Flag.wait) x) := rfl

set_option linter.deprecated false in
example : @RocqLantana.flag_stable.flag_run_violates_guarantee =
    @FlagStable.flagRun_violates_guarantee := rfl

set_option linter.deprecated false in
example : RocqLantana.Nondet.nest = Nondet.nest := rfl

/-- The closed world of the examples has the ghost state of the temporal layer and of HeapLang
before allocation, and the handoff's camera. -/
noncomputable example : TemporalGpreS Exp State ExGF := inferInstance
noncomputable example : HeapStateGpreS ExGF := inferInstance
noncomputable example : Handoff.HandoffG ExGF := inferInstance

/-- `exits v @ i` is the final expression of thread `i` (the notation parses identifiers). -/
example [HeapStateGS GF] (i : ThreadId) (v : Val) :
    (exits v @ i : Iris.IProp GF) = threadExpr i [] (.val v) := rfl

/-- `main` of the paper (§2) forks the setter of the flag it waits for. -/
example : FlagFork.main = hl_val(λ _,
    let x := v(&Flag.init) #();
    fork(v(&Flag.set) x);
    v(&Flag.wait) x;
    #42) := rfl

/-- The receiver runs the task it finds in the cell. -/
example : Handoff.receive =
    hl_val(rec loop b := match !b with | none() => loop b | some(x) => (fst(x)) (snd(x))) :=
  rfl

/-- The end-to-end statement of `flag_fork.v`, liveness and safety. -/
example (τ : Trace Exp State) (hbeh : IsBehavior τ) (hfair : fairScheduling τ) (hpos : τ.pos = 0)
    (hinit : τ.seq 0 = ⟨(FlagFork.tp0, FlagFork.σ0), 0⟩) :
    FlagFork.rMain 0 τ ∧ safetyIris 0 (fun _ v => v = FlagFork.v42) τ :=
  FlagFork.main_liveness_safety τ hbeh hfair hpos hinit

/-- The handoff's guarantee: the cell always holds `NONE` or a task. -/
example (b : Loc) : (□ₛ Handoff.handoffInvTrSpec (GF := GF) b).external ⊆ Handoff.handoffTr b :=
  Handoff.handoffInvTrSpec_ext b

set_option linter.deprecated false in
example : @RocqLantana.flag_fork.main_adequacy = @FlagFork.main_adequacy := rfl

set_option linter.deprecated false in
example : @RocqLantana.handoff_client_adequacy = @HandoffClient.handoffClient_adequacy := rfl

/-! The end-to-end corollaries of the examples depend only on the standard axioms. -/

/--
info: 'Lantana.Examples.FlagFork.main_liveness_safety' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FlagFork.main_liveness_safety

/--
info: 'Lantana.Examples.FlagClient.flagClient_liveness_safety' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FlagClient.flagClient_liveness_safety

/--
info: 'Lantana.Examples.HandoffClient.handoffClient_liveness_safety' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms HandoffClient.handoffClient_liveness_safety

end LantanaTest.Examples
