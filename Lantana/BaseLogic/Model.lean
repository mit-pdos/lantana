/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
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
public import Lantana.BaseLogic.Model.OForest
public import Lantana.BaseLogic.Model.MUpd
public import Lantana.BaseLogic.Model.OPreds

/-! # The obligation model

The model of obligations (Rocq `lantana/base_logic/`, files `obligation.v` to `opreds.v`). Its
pure part: obligations and witnesses with their steps and relations
(`Obligation`, `Witness`), the round relations and the choice of witnesses (`ModelRel`), and the
pure forest invariant `ForestWf` with its shape-change lemmas (`Forest`). Its ghost state: the
model history (`Model.ModelHistory`), the obligations with `osat` (`Model.OSat`), the witnesses
with `owit` (`Model.OWit`), invariants over obligation states (`Model.OInv`), the user predicates
on obligations and witnesses (`Model.OPredsBase`), and the forest with the thread statuses,
`oforest` (`Model.OForest`), and the model interpretation with the model update `mupd` and the
rounds `mprog`/`mphys` of a physical step (`Model.MUpd`; `ModelGS` itself is `Lantana.ModelGS`),
and the children predicates with the forest operations as model updates (`Model.OPreds`).
Everything else lives in the namespace `Lantana.Model`.
-/
