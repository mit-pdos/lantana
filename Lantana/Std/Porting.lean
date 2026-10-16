/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from Iris-Lean's `Iris.Std.RocqPorting`, whose header reads:
  Copyright (c) The Iris-Lean Contributors
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Markus de Medeiros, Zongyuan Liu
Modified by the Lantana-Lean Contributors; the module documentation describes the changes.
-/
module

import Lean.Elab.DeclarationRange
public meta import Lean.Elab.Command

/-!
# Correspondence with the Rocq development of Lantana

`@[lantana_alias rocqName]` records that a Lean declaration reimplements the Rocq declaration
`rocqName` of Lantana-Rocq (`lantana/`, `lantana_heap_lang/`), by creating a `@[deprecated]`
alias `RocqLantana.rocqName`. `#lantana_ignore rocqName "reason"` records a Rocq declaration
that is deliberately not reimplemented. Adapted from Iris-Lean's `@[rocq_alias]`
(`Iris.Std.RocqPorting`), which is reserved for the Iris-Rocq names.

The Rocq name is the fully qualified one (module prefix included, sections ignored), e.g.
`@[lantana_alias oblf.obl_new]`, `@[lantana_alias heap_lang.lwp_load]`.
-/

open Lean Elab Command

/-- Records the Rocq declaration a Lean declaration reimplements, as a `@[deprecated]` alias in
the `RocqLantana` namespace. -/
syntax (name := lantana_alias) "lantana_alias " ident : attr

initialize registerBuiltinAttribute {
  name := `lantana_alias
  descr := "Creates a @[deprecated] alias in the RocqLantana namespace (Rocq↔Lean correspondence)"
  applicationTime := .afterTypeChecking
  add := fun declName stx _kind => do
    let `(attr| lantana_alias $rocqId) := stx
      | throwError "invalid @[lantana_alias] syntax"
    let aliasName := `RocqLantana ++ rocqId.getId
    let env ← getEnv
    if env.find? aliasName |>.isSome then
      throwError s!"duplicate lantana_alias: `{aliasName}` already exists"
    let some info := env.find? declName
      | throwError s!"unknown declaration '{declName}'"
    let levels := info.levelParams.map mkLevelParam
    let value := mkConst declName levels
    match info with
    | .thmInfo val =>
      addDecl (.thmDecl { name := aliasName, levelParams := val.levelParams, type := val.type, value })
    | _ =>
      addDecl (.defnDecl { name := aliasName, levelParams := info.levelParams, type := info.type,
                           value, hints := .abbrev, safety := .safe })
    Elab.addDeclarationRangesFromSyntax aliasName stx rocqId
    let declIdent := mkIdent declName
    let depStx ← `(attr| deprecated $declIdent (since := "reimplemented in Lantana-Lean"))
    Attribute.add aliasName `deprecated depStx .global
}

/-- The `#lantana_ignore` entries, as `(rocqName, reason)` pairs. -/
public meta initialize lantanaIgnoreExt :
    SimplePersistentEnvExtension (Name × String) (Array (Name × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.foldl (fun acc a => a.foldl Array.push acc) #[]
  }

/-- `#lantana_ignore rocqName "reason"`: the Rocq declaration is deliberately not reimplemented. -/
@[expose]
elab "#lantana_ignore " id:ident ppSpace reason:str : command => do
  modifyEnv (lantanaIgnoreExt.addEntry · (id.getId, reason.getString))
