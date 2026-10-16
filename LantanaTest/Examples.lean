module

public import Lantana

/-! Tests of the examples: the trace-level facts of the flags, and the programs of `nondet`. -/

namespace LantanaTest.Examples

open Lantana Lantana.HeapLang Lantana.Examples
open scoped Lantana.TrProp

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

end LantanaTest.Examples
