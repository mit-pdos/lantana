/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Lantana.BaseLogic.Obligation
public import Lantana.BaseLogic.Witness
public import Lantana.BaseLogic.ModelRel
public import Lantana.BaseLogic.Forest
public import Lantana.BaseLogic.Model.ModelHistory
public import Lantana.BaseLogic.Model.OSat
public import Lantana.BaseLogic.Model.OWit
public import Lantana.BaseLogic.Model.OInv
public import Lantana.BaseLogic.Model.OPredsBase

/-! # The obligation model

The model of obligations (Rocq `lantana/base_logic/`, files `obligation.v` to `opreds.v`). Its
pure part: obligations and witnesses with their steps and relations
(`Obligation`, `Witness`), the round relations and the choice of witnesses (`ModelRel`), and the
pure forest invariant `ForestWf` with its shape-change lemmas (`Forest`). Its ghost state, so far:
the model history (`Model.ModelHistory`) and the ghost state of obligations with its invariant
`osat` (`Model.OSat`). Everything lives in the namespace `Lantana.Model`.
-/
