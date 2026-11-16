/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Declaration dump for the naming review (`docs/naming.md`)

`lake env lean --run scripts/naming/Dump.lean [Module ...]` (default `Lantana`; run from the
package root on a built tree) prints one TSV row per declaration of `import Module ...` whose
module is in `Lantana`, `LantanaTest` or `Iris`:

  name, kind, module, private, aliases, result sort, line, statement hash

- kind: theorem, def, abbrev, opaque, instance, class, structure, inductive, ctor, field, axiom;
- aliases: the Rocq names, `lan:n` from `@[lantana_alias n]` and `iris:n` from Iris-Lean's
  `@[rocq_alias n]` (both create a `@[deprecated]` alias `RocqLantana.n` / `Rocq.n`);
- result sort: `Prop`/`Type` when the type ends in a sort after its binders, otherwise `-`
  (syntactic: `IProp GF` and `TrProp C` count as `-`).

`scripts/naming/lint.sh` runs it on `Lantana` and on each test module.  To compare with
Iris-Lean, run it once with `Lantana` and once with `Iris` (Iris-Lean's and Lantana's HeapLang
notations cannot be imported together).
-/

open Lean Meta

/-- The sort a type ends in after its binders, if it is syntactically one. -/
partial def retSort : Expr → String
  | .forallE _ _ b _ => retSort b
  | .mdata _ e => retSort e
  | .sort u => if u.isZero then "Prop" else "Type"
  | _ => "-"

/-- The kind of a constant, instances first (a Prop-class instance is a theorem). -/
def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : String :=
  if isInstanceCore env n then "instance" else
  match ci with
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .recInfo _ => "rec"
  | .ctorInfo _ => "ctor"
  | .inductInfo _ =>
    if isClass env n then "class" else if isStructure env n then "structure" else "inductive"
  | .defnInfo _ =>
    if (env.getProjectionFnInfo? n).isSome then "field"
    else match getReducibilityStatusCore env n with
      | .reducible => "abbrev"
      | _ => "def"

unsafe def main (args : List String) : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let roots := if args.isEmpty then ["Lantana"] else args
  let env ← importModules (roots.map fun r => { module := r.toName }).toArray {} (loadExts := true)
  let mods := env.header.moduleNames
  -- Rocq aliases: target → Rocq names.
  let mut aliasMap : Std.HashMap Name (Array String) := {}
  for (n, _) in env.constants.toList do
    let r := n.getRoot
    if r == `RocqLantana || r == `Rocq then
      if let some e := Linter.deprecatedAttr.getParam? env n then
        if let some t := e.newName? then
          let tag := (if r == `Rocq then "iris:" else "lan:") ++ (n.replacePrefix r .anonymous).toString
          aliasMap := aliasMap.insert t ((aliasMap.getD t #[]).push tag)
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    unless m.getRoot == `Lantana || m.getRoot == `Iris || m.getRoot == `LantanaTest do continue
    if n.getRoot == `RocqLantana || n.getRoot == `Rocq then continue
    -- a private declaration is checked under its user-facing name
    let priv := if isPrivateName n then "private" else ""
    let n0 := n
    let n := (privateToUserName? n).getD n
    if n.isInternalDetail then continue
    if isAuxRecursor env n || isNoConfusion env n then continue
    let s := n.toString
    if s.endsWith ".inj" || s.endsWith ".injEq" || s.endsWith ".sizeOf_spec" ||
        s.endsWith ".ctorIdx" then continue
    let k := kindOf env n0 ci
    if k == "rec" then continue
    let al := ",".intercalate (aliasMap.getD n0 #[]).toList
    let ln := match declRangeExt.find? (level := .exported) env n0 with
      | some r => toString r.range.pos.line
      | none => "?"
    IO.println s!"{n}\t{k}\t{m}\t{priv}\t{al}\t{retSort ci.type}\t{ln}\t{ci.type.hash}"
