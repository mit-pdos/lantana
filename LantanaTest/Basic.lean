module

public import Lantana
public import Iris.Algebra.StepIndexChoice

/-! Smoke tests: the package imports Iris, the ordinal step index is in force, and the porting
attribute works. -/

example : Iris.SI = Ordinals.Ordinal.{3} := rfl

@[lantana_alias test_decl]
def testDecl : Nat := 0

#lantana_ignore test_ignored "a test entry"

set_option linter.deprecated false in
example : RocqLantana.test_decl = 0 := rfl
