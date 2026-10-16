module

public import Lantana

/-! Tests of the case studies that test the adequacy theorem: `cert_discharge.v` (the program,
the end-to-end corollaries and their axioms). -/

namespace LantanaTest.ExamplesAdequacy

open Lantana Lantana.HeapLang Lantana.Examples
open scoped Lantana.TrProp Lantana.TrSpec

/-- `main` stores `1`, then `2`, into its first argument. -/
example : CertDischarge.main = hl_val(λ x y, x ← #1; x ← #2; #()) := rfl

/-- The initial heap of the end-to-end statement holds `0` at `x` and `7` at `y`. -/
example : CertDischarge.σ0.get? CertDischarge.x0 = some (some CertDischarge.v0) ∧
    CertDischarge.σ0.get? CertDischarge.y0 = some (some CertDischarge.v7) := by
  simp only [State.get?, Iris.Std.LawfulPartialMap.get?_insert]
  decide

/-- The end-to-end statement of `cert_discharge.v`, liveness and safety. -/
example (τ : Trace Exp State) (hbeh : IsBehavior τ) (hfair : fairScheduling τ) (hpos : τ.pos = 0)
    (hinit : τ.seq 0 = ⟨(CertDischarge.tp0, CertDischarge.σ0), 0⟩) :
    CertDischarge.rMain CertDischarge.x0 CertDischarge.y0 τ ∧
      safetyIris 0 (fun _ v => v = hl_val(#())) τ :=
  CertDischarge.certDischarge_liveness_safety τ hbeh hfair hpos hinit

set_option linter.deprecated false in
example : @RocqLantana.cert_discharge_adequacy = @CertDischarge.certDischarge_adequacy := rfl

/-! The end-to-end corollaries depend only on the standard axioms. -/

/--
info: 'Lantana.Examples.CertDischarge.certDischarge_liveness_safety' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CertDischarge.certDischarge_liveness_safety

end LantanaTest.ExamplesAdequacy
