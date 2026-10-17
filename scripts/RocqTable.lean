/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lantana

/-!
# The Rocq↔Lean correspondence table

Prints (to stdout) a Markdown document of the correspondence between the Rocq development of
Lantana and this library, read from the environment of `import Lantana`:

1. the `@[lantana_alias rocqName]` declarations (the `@[deprecated]` aliases
   `RocqLantana.rocqName`), as Rocq name, Lean declaration and Lean file;
2. the `#lantana_ignore rocqName "reason"` entries (`lantanaIgnoreExt`), with their reasons;
3. if a Rocq checkout is given, the Rocq declarations that are neither aliased nor ignored.

Run it with `scripts/rocq-table.sh`, which writes `docs/rocq-correspondence.md`; directly:
`ROCQ_LANTANA=<rocq checkout> lake env lean scripts/RocqTable.lean > out.md`.

Environment variables:
- `ROCQ_LANTANA`: a checkout of the Rocq development (with `lantana/` and
  `lantana_heap_lang/`). With it the aliases and ignores are grouped by Rocq file and a coverage
  report is added; without it they are grouped by Lean module.
- `ROCQ_LANTANA_REV`: a description of that checkout (branch, commit), printed in the header.

The Rocq scanner is a heuristic: it strips comments, splits the files into sentences (ended by
`.` and whitespace) and reads the declaring ones (`Definition`, `Lemma`, `Instance`, …, with
their attributes and qualifiers; the constructors of inductives, the constructors and fields of
records and classes; notations, tactics and `Let`s are matched but not counted), tracking
`Module`/`Section`/`End`. A Rocq declaration `n` of the file `lantana/d/f.v` (logical path
`lantana.d.f`; `lantana_heap_lang/f.v` is `lantana.heap_lang.f`) inside the modules
`M₁.….Mₖ` is matched by every name `S.M'.n` with `S` a suffix of its logical path or of its
logical directory and `M'` a suffix of `M₁.….Mₖ` (so `n`, `Mₖ.n`, `f.n`, `heap_lang.n`,
`f.M₁.….Mₖ.n`, … all refer to it). A name matching declarations of several files is resolved
to the one whose file is in the Rocq directory of the Lean module's layer, then whose file stem
is the Lean module's name in `snake_case`.
-/

open Lean Elab Command

namespace RocqTable

/-! ## Strings -/

/-- Replaces the characters of the (nested) Rocq comments `(* … *)` by spaces, keeping the line
breaks (so line numbers are preserved). -/
def stripComments (s : String) : String := Id.run do
  let mut out : Array Char := #[]
  let mut depth := 0
  let mut inStr := false
  let mut cs := s.toList
  while true do
    match cs with
    | [] => break
    | '(' :: '*' :: rest =>
      if inStr then
        out := out.push '(' |>.push '*'
      else
        depth := depth + 1
        out := out.push ' ' |>.push ' '
      cs := rest
    | '*' :: ')' :: rest =>
      if depth > 0 && !inStr then
        depth := depth - 1
        out := out.push ' ' |>.push ' '
      else
        out := out.push '*' |>.push ')'
      cs := rest
    | c :: rest =>
      if c == '"' && depth == 0 then inStr := !inStr
      out := out.push (if depth > 0 && c != '\n' then ' ' else c)
      cs := rest
  return String.ofList out.toList

/-- The whitespace-separated words of a line. -/
def words (s : String) : List String :=
  let rec go : List Char → List Char → List String
    | [], acc => if acc.isEmpty then [] else [String.ofList acc.reverse]
    | c :: cs, acc =>
      if c.isWhitespace then
        (if acc.isEmpty then go cs [] else String.ofList acc.reverse :: go cs [])
      else go cs (c :: acc)
  go s.toList []

/-- The characters of a Rocq identifier (approximately). -/
def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c.val ≥ 128

/-- The identifier at the start of a word (`foo:` ↦ `foo`, `foo.` ↦ `foo`). -/
def identPrefix (w : String) : String :=
  String.ofList (w.toList.takeWhile isIdentChar)

/-- Splits a string at the dots. -/
def dotSplit (s : String) : List String := s.splitOn "."

/-- Escapes a Markdown table cell. -/
def cell (s : String) : String := s.replace "|" "\\|"

/-- Lexicographic order on pairs. -/
def lexLt (a b : Nat × String) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- A name as code in a table cell. -/
def code (s : String) : String := s!"`{cell s}`"

/-- `snake_case` of a Lean module component: `TicketLock2` ↦ `ticket_lock2`. -/
def snake (s : String) : String := Id.run do
  let mut out : Array Char := #[]
  let mut prevLower := false
  for c in s.toList do
    if c.isUpper then
      if prevLower then out := out.push '_'
      out := out.push c.toLower
      prevLower := false
    else
      out := out.push c
      prevLower := c.isLower || c.isDigit
  return String.ofList out.toList

/-! ## The Rocq scanner -/

/-- A declaration of the Rocq development, as found by `scanFile`. -/
structure RocqDecl where
  /-- The file, relative to the checkout, e.g. `lantana/base_logic/opreds.v`. -/
  file : String
  /-- The logical path of the file, e.g. `[lantana, base_logic, opreds]`. -/
  logical : List String
  /-- The enclosing `Module`s, outermost first (sections are ignored). -/
  mods : List String
  /-- The short name. -/
  name : String
  /-- The vernacular command (`Lemma`, `Definition`, `Instance`, …). -/
  kind : String
  /-- The line (1-based). -/
  line : Nat
  deriving Inhabited

/-- The qualified name inside the file: `M₁.….Mₖ.n`. -/
def RocqDecl.qualName (d : RocqDecl) : String := ".".intercalate (d.mods ++ [d.name])

/-- Whether a declaration counts for the coverage report: section-local `Let`s, notations and
tactics and module aliases are matched against the aliases and ignores but not reported as
missing. -/
def RocqDecl.isCounted (d : RocqDecl) : Bool :=
  !["Let", "Notation", "Ltac", "Module"].contains d.kind

/-- The Rocq names that refer to `d` (see the module docstring). -/
def RocqDecl.candidates (d : RocqDecl) : List String :=
  let suffixes {α} (l : List α) : List (List α) := (List.range (l.length + 1)).map (l.drop ·)
  -- the suffixes of the logical path, and of the logical directory (without the file stem)
  let prefixes := (suffixes d.logical ++ suffixes d.logical.dropLast).eraseDups
  prefixes.flatMap fun s =>
    (suffixes d.mods).map fun m => ".".intercalate (s ++ m ++ [d.name])

/-- The commands that declare a name. -/
def declKinds : List String :=
  ["Definition", "Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Example",
   "Instance", "Fixpoint", "CoFixpoint", "Inductive", "CoInductive", "Variant", "Record",
   "Structure", "Class", "Canonical", "Let", "Equations", "Notation", "Ltac"]

/-- The qualifiers that may precede a declaration. -/
def qualifiers : List String :=
  ["Global", "Local", "Program", "Polymorphic", "Monomorphic", "Cumulative", "NonCumulative",
   "Private", "Declare", "Open"]

/-- Drops the bullets, attributes `#[…]` and qualifiers at the start of a sentence. -/
partial def dropPrefix : List String → List String
  | w :: ws =>
    if w.startsWith "#[" then
      if w.endsWith "]" then dropPrefix ws
      else dropPrefix ((ws.dropWhile (!·.endsWith "]")).drop 1)
    else if qualifiers.contains w || ["-", "+", "*", "{", "}", "--", "++", "**"].contains w then
      dropPrefix ws
    else w :: ws
  | [] => []

/-- The logical path of a file of the checkout: `lantana/d/f.v` ↦ `[lantana, d, f]`,
`lantana_heap_lang/d/f.v` ↦ `[lantana, heap_lang, d, f]`. -/
def logicalPath (file : String) : List String :=
  let comps := file.splitOn "/"
  let comps := comps.dropLast ++ [(comps.getLast?.getD "").replace ".v" ""]
  match comps with
  | "lantana_heap_lang" :: rest => "lantana" :: "heap_lang" :: rest
  | l => l

/-- Splits a (comment-free) Rocq file into its sentences, each with the line of its first
character: a sentence ends with a `.` followed by whitespace (outside strings). -/
def sentences (s : String) : Array (List Char × Nat) := Id.run do
  let mut out := #[]
  let mut cur : Array Char := #[]
  let mut start := 1
  let mut line := 1
  let mut inStr := false
  let mut cs := s.toList
  while true do
    match cs with
    | [] => break
    | c :: rest =>
      if cur.isEmpty && c.isWhitespace then
        if c == '\n' then line := line + 1
        start := line
        cs := rest
        continue
      if c == '"' then inStr := !inStr
      if c == '\n' then line := line + 1
      let isEnd := c == '.' && !inStr && (rest.head?.all Char.isWhitespace)
      cur := cur.push c
      if isEnd then
        out := out.push (cur.toList, start)
        cur := #[]
      cs := rest
  if !cur.isEmpty then out := out.push (cur.toList, start)
  return out

/-- The part of a sentence after its first top-level `:=`, with the number of line breaks
before it. -/
def afterDef (cs : List Char) : Option (List Char × Nat) := Id.run do
  let mut depth := 0
  let mut nl := 0
  let mut rest := cs
  while true do
    match rest with
    | [] => return none
    | ':' :: '=' :: r => if depth == 0 then return some (r, nl) else rest := r
    | c :: r =>
      if c == '(' || c == '[' || c == '{' then depth := depth + 1
      if (c == ')' || c == ']' || c == '}') && depth > 0 then depth := depth - 1
      if c == '\n' then nl := nl + 1
      rest := r
  return none

/-- Splits at a separator at bracket depth 0, keeping each chunk's number of preceding line
breaks. -/
def splitTop (sep : Char) (cs : List Char) (nl0 : Nat) : List (List Char × Nat) := Id.run do
  let mut out := #[]
  let mut cur : Array Char := #[]
  let mut curNl := nl0
  let mut nl := nl0
  let mut depth := 0
  for c in cs do
    if c == sep && depth == 0 then
      out := out.push (cur.toList, curNl)
      cur := #[]
      curNl := nl
      continue
    if c == '(' || c == '[' || c == '{' then depth := depth + 1
    if (c == ')' || c == ']' || c == '}') && depth > 0 then depth := depth - 1
    if c == '\n' then nl := nl + 1
    cur := cur.push c
  out := out.push (cur.toList, curNl)
  return out.toList

/-- Whether a chunk has a `:` at bracket depth 0 (a field `f binders : T`). -/
def hasTopColon (cs : List Char) : Bool := Id.run do
  let mut depth := 0
  for c in cs do
    if c == ':' && depth == 0 then return true
    if c == '(' || c == '[' || c == '{' then depth := depth + 1
    if (c == ')' || c == ']' || c == '}') && depth > 0 then depth := depth - 1
  return false

/-- The first identifier of a chunk (after whitespace and attributes), with the line breaks
before it. -/
def firstIdent (cs : List Char) (nl : Nat) : Option (String × Nat) := Id.run do
  let mut cs := cs
  let mut nl := nl
  while true do
    match cs with
    | c :: r =>
      if c.isWhitespace then
        if c == '\n' then nl := nl + 1
        cs := r
      else if c == '#' && r.head? == some '[' then
        cs := (r.dropWhile (· != ']')).drop 1
      else break
    | [] => break
  let n := String.ofList (cs.takeWhile isIdentChar)
  if n.isEmpty || (n.toList.head?.any Char.isDigit) then none else some (n, nl)

/-- The fields of a `Record`/`Structure`/`Class` and the constructors of an `Inductive`, with
their line breaks from the start of the sentence. -/
def subNames (kind : String) (cs : List Char) : List (String × String × Nat) := Id.run do
  let some (body, nl) := afterDef cs | return []
  if kind == "Inductive" || kind == "CoInductive" || kind == "Variant" then
    -- the constructors `| C …`, and the types of a mutual `with T …`
    return (splitTop '|' body nl).flatMap fun (chunk, n) =>
      let ws := words (String.ofList chunk)
      let mutualTys := (ws.zip (ws.drop 1)).filterMap fun (w, t) =>
        if w == "with" && !(identPrefix t).isEmpty then some ("Inductive", identPrefix t, n)
        else none
      ((firstIdent chunk n).map fun (c, l) => ("constructor", c, l)).toList ++ mutualTys
  else if kind == "Record" || kind == "Structure" || kind == "Class" then
    -- `:= Mk { f₁ : T₁; … }`, `:= { f₁ : T₁; … }`, or the definitional class `:= f : T`
    let (beforeBrace, fromBrace) := body.span (· != '{')
    let nlBefore := nl + (beforeBrace.filter (· == '\n')).length
    let ctor := if fromBrace.isEmpty then [] else
      ((firstIdent beforeBrace nl).map fun (c, l) => ("constructor", c, l)).toList
    match fromBrace with
    | '{' :: inner =>
      let inner := (splitTop '}' inner nlBefore).head?.getD ([], nlBefore)
      return ctor ++ (splitTop ';' inner.1 inner.2).filterMap fun (chunk, n) =>
        if hasTopColon chunk then (firstIdent chunk n).map fun (f, l) => ("field", f, l)
        else none
    | _ =>
      return ((firstIdent body nl).map fun (f, l) => ("field", f, l)).toList
  else return []

/-- The declarations of a Rocq file. -/
def scanFile (file contents : String) : Array RocqDecl := Id.run do
  let logical := logicalPath file
  -- the stack of open `Module`s (`true`) and `Section`s (`false`)
  let mut stack : List (String × Bool) := []
  let mut out := #[]
  for (cs, line) in sentences (stripComments contents) do
    let mods := (stack.filter (·.2)).reverse.map (·.1)
    match dropPrefix (words (String.ofList cs)) with
    | "Module" :: rest =>
      let rest := rest.dropWhile (fun w => w == "Import" || w == "Export" || w == "Type")
      if let some w := rest.head? then
        -- `Module M := N.` opens no scope
        if !rest.contains ":=" && !(w.endsWith ":=") then
          stack := (identPrefix w, true) :: stack
        else
          out := out.push { file, logical, mods, name := identPrefix w, kind := "Module", line }
    | "Section" :: w :: _ => stack := (identPrefix w, false) :: stack
    | "End" :: _ :: _ => stack := stack.drop 1
    | kind :: rest =>
      if declKinds.contains kind then
        let rest := if kind == "Canonical" && rest.head? == some "Structure" then rest.drop 1
          else rest
        if let some w := rest.head? then
          -- `Notation "…"` declares no name
          let n := identPrefix w
          if !n.isEmpty && !(w.startsWith "\"") then
            out := out.push { file, logical, mods, name := n, kind, line }
            for (k, sub, nl) in subNames kind cs do
              out := out.push { file, logical, mods, name := sub, kind := k, line := line + nl }
    | [] => pure ()
  return out

/-- The declarations of the Rocq checkout `root` (`lantana/`, `lantana_heap_lang/`). -/
def scanRocq (root : System.FilePath) : IO (Array RocqDecl) := do
  let mut out := #[]
  for dir in ["lantana", "lantana_heap_lang"] do
    let files ← System.FilePath.walkDir (root / dir)
    let files : Array String := (files.filter (·.extension == some "v")).map (·.toString)
    for f in files.qsort (· < ·) do
      let rel := String.ofList (f.toList.drop (root.toString.length + 1))
      out := out ++ scanFile rel (← IO.FS.readFile f)
  return out

/-! ## The Lean side -/

/-- A `@[lantana_alias]` entry. -/
structure AliasEntry where
  /-- The Rocq name. -/
  rocq : String
  /-- The Lean declaration. -/
  target : Name
  /-- The Lean module of the declaration. -/
  module : Name
  /-- The line of the declaration, if known. -/
  line : Option Nat
  deriving Inhabited

/-- A `#lantana_ignore` entry. -/
structure IgnoreEntry where
  /-- The Rocq name. -/
  rocq : String
  /-- The reason. -/
  reason : String
  /-- The Lean module containing the `#lantana_ignore`. -/
  module : Name
  deriving Inhabited

/-- The source file of a Lean module, relative to the package root. -/
def moduleFile (m : Name) : String := "/".intercalate (m.components.map (·.toString)) ++ ".lean"

/-- A Lean declaration name for display (private names are shown with their user name). -/
def showName (n : Name) : String :=
  match privateToUserName? n with
  | some u => s!"{u.toString (escape := false)} (private)"
  | none => n.toString (escape := false)

/-- The layers of the library in dependency order, with their Rocq directories. -/
def layers : List (String × String) :=
  [("Std", ""), ("Init", ""), ("Prelude", "lantana/prelude/"), ("Algebra", "lantana/algebra/"),
   ("BaseLogic", "lantana/base_logic/"), ("ProgramLogic", "lantana/program_logic/"),
   ("Trace", "lantana/trace/"), ("HeapLang", "lantana_heap_lang/"),
   ("Examples", "lantana_heap_lang/examples/")]

/-- The layer of a Lean module `Lantana.L.…` (its index in `layers`). -/
def layerOf (m : Name) : Nat :=
  match m.components with
  | _ :: l :: _ => (layers.findIdx? (·.1 == l.toString)).getD layers.length
  | _ => layers.length

/-- The Rocq directory of a Lean module's layer. -/
def rocqDirOf (m : Name) : String := ((layers[layerOf m]?).map (·.2)).getD ""

/-- Whether a Rocq file is in the directory of the Lean module `m`. -/
def inDirOf (m : Name) (file : String) : Bool :=
  let dir := rocqDirOf m
  !dir.isEmpty && file.startsWith dir &&
    (dir != "lantana_heap_lang/" || !file.startsWith "lantana_heap_lang/examples/")

/-- The sort key of a Rocq file: its layer, then its path. -/
def rocqFileKey (file : String) : Nat × String :=
  let i := (layers.findIdx? fun (_, d) =>
    !d.isEmpty && file.startsWith d &&
      (d != "lantana_heap_lang/" || !file.startsWith "lantana_heap_lang/examples/")).getD 99
  (i, file)

/-- The Rocq declaration a name refers to, among `ds` (see the module docstring); `m` is the
Lean module where the name is recorded. -/
def resolve (decls : Array RocqDecl) (ds : Array Nat) (m : Name) : Option Nat :=
  let stem := snake ((m.components.getLast?.map (·.toString)).getD "")
  let score (i : Nat) : Nat :=
    let d := decls[i]!
    (if inDirOf m d.file then 4 else 0) +
      (if (d.logical.getLast?.getD "") == stem then 2 else 0) +
      (if d.isCounted then 1 else 0)
  ds.foldl (init := none) fun best i =>
    match best with
    | none => some i
    | some j => if score i > score j then some i else some j

/-- Collects the aliases and the ignores of the environment. -/
def collect : CommandElabM (Array AliasEntry × Array IgnoreEntry) := do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if (`RocqLantana).isPrefixOf n then acc.push n else acc
  let mut aliases := #[]
  for n in names do
    let some target := Linter.getDeprecatedNewName env n | continue
    let module := (env.getModuleIdxFor? target).map (env.header.moduleNames[·]!) |>.getD .anonymous
    let line ← liftCoreM do
      return (← findDeclarationRanges? target).map (·.range.pos.line)
    let rocq := (n.replacePrefix `RocqLantana .anonymous).toString (escape := false)
    aliases := aliases.push { rocq, target, module, line }
  let mut ignores := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let module := env.header.moduleNames[i]
    for (n, reason) in PersistentEnvExtension.getModuleEntries lantanaIgnoreExt env i do
      ignores := ignores.push { rocq := n.toString (escape := false), reason, module }
  return (aliases, ignores)

/-! ## The document -/

/-- The Lean-file cell of an alias: a link to the declaration. -/
def leanFileCell (a : AliasEntry) : String :=
  let f := moduleFile a.module
  match a.line with
  | some l => s!"[{f}:{l}](../{f}#L{l})"
  | none => s!"[{f}](../{f})"

/-- An alias table. -/
def aliasTable (als : Array AliasEntry) : String :=
  let rows := als.toList.map fun a =>
    s!"| {code a.rocq} | {code (showName a.target)} | {leanFileCell a} |"
  "\n".intercalate (["| Rocq | Lean | Lean file |", "|---|---|---|"] ++ rows) ++ "\n"

/-- An ignore table. -/
def ignoreTable (is : Array IgnoreEntry) (withModule : Bool) : String :=
  let rows := is.toList.map fun i =>
    let reason := cell ((i.reason.replace "\n" " ").replace "\r" "")
    if withModule then s!"| {code i.rocq} | {reason} | `{moduleFile i.module}` |"
    else s!"| {code i.rocq} | {reason} |"
  let header := if withModule then ["| Rocq | Reason | Lean file |", "|---|---|---|"]
    else ["| Rocq | Reason |", "|---|---|"]
  "\n".intercalate (header ++ rows) ++ "\n"

/-- Groups an array by a key, keeping the first-occurrence order of the keys. -/
def groupBy {α} [Inhabited α] (xs : Array α) (key : α → String) : Array (String × Array α) :=
  Id.run do
    let mut keys : Array String := #[]
    let mut m : Std.HashMap String (Array α) := {}
    for x in xs do
      let k := key x
      if !m.contains k then keys := keys.push k
      m := m.insert k ((m.getD k #[]).push x)
    return keys.map fun k => (k, m.getD k #[])

/-- Sorts the aliases of a Lean-module group by line. -/
def byLine (als : Array AliasEntry) : Array AliasEntry :=
  als.qsort fun a b => lexLt (a.line.getD 0, a.rocq) (b.line.getD 0, b.rocq)

/-- The sort key of a Lean module: its layer, then its name. -/
def moduleKey (m : Name) : Nat × String := (layerOf m, m.toString)

/-- The document. -/
def document (rev : String) (decls? : Option (Array RocqDecl)) (aliases : Array AliasEntry)
    (ignores : Array IgnoreEntry) : String := Id.run do
  let mut out := "# Correspondence between Lantana-Rocq and Lantana-Lean\n\n"
  out := out ++ "Generated by `scripts/rocq-table.sh` (`scripts/RocqTable.lean`) from the " ++
    "environment of `import Lantana`; do not edit by hand. A Lean declaration carrying " ++
    "`@[lantana_alias rocqName]` reimplements the Rocq declaration `rocqName` (and " ++
    "`#check RocqLantana.rocqName` finds it); `#lantana_ignore rocqName \"reason\"` records a " ++
    "Rocq declaration deliberately not reimplemented (`Lantana/Std/Porting.lean`).\n\n"
  if !rev.isEmpty then
    out := out ++ s!"Rocq reference: {rev}.\n\n"
  let targets := (aliases.map (·.target)).toList.eraseDups.length
  let leanMods := (aliases.map (·.module.toString)).toList.eraseDups.length
  let ignMods := (ignores.map (·.module.toString)).toList.eraseDups.length
  out := out ++ "## Summary\n\n"
  out := out ++ s!"- **{aliases.size}** Rocq names aliased (`@[lantana_alias]`), to {targets} " ++
    s!"Lean declarations in {leanMods} Lean modules.\n"
  out := out ++ s!"- **{ignores.size}** Rocq names ignored (`#lantana_ignore`), recorded in " ++
    s!"{ignMods} Lean modules.\n"
  match decls? with
  | none =>
    out := out ++ "\n(No Rocq checkout given: no coverage report; the tables are grouped by " ++
      "Lean module.)\n\n"
    out := out ++ "## 1. Aliased Rocq declarations, by Lean module\n\n"
    let groups := groupBy (aliases.qsort fun a b => lexLt (moduleKey a.module) (moduleKey b.module))
      (·.module.toString)
    for (m, als) in groups do
      out := out ++ s!"### `{m}`\n\n" ++ aliasTable (byLine als) ++ "\n"
    out := out ++ "## 2. Ignored Rocq declarations, by Lean module\n\n"
    let groups := groupBy (ignores.qsort fun a b => lexLt (moduleKey a.module) (moduleKey b.module))
      (·.module.toString)
    for (m, is) in groups do
      out := out ++ s!"### `{m}`\n\n" ++ ignoreTable is false ++ "\n"
    return out
  | some decls =>
    -- the index: Rocq name ↦ the declarations it may refer to
    let mut index : Std.HashMap String (Array Nat) := {}
    for h : i in [0:decls.size] do
      for c in decls[i].candidates do
        index := index.insert c ((index.getD c #[]).push i)
    let resolveName (n : String) (m : Name) : Option Nat :=
      resolve decls (index.getD n #[]) m
    let nFiles (n : String) : Nat :=
      ((index.getD n #[]).toList.map (decls[·]!.file)).eraseDups.length
    let aliasRes := aliases.map fun a => (a, resolveName a.rocq a.module)
    let ignoreRes := ignores.map fun i => (i, resolveName i.rocq i.module)
    let nAmbiguous := (aliases.filter (nFiles ·.rocq > 1)).size +
      (ignores.filter (nFiles ·.rocq > 1)).size
    let aliased : Std.HashSet Nat := aliasRes.foldl (init := {}) fun s (_, r) =>
      match r with | some i => s.insert i | none => s
    let ignored : Std.HashSet Nat := ignoreRes.foldl (init := {}) fun s (_, r) =>
      match r with | some i => s.insert i | none => s
    let isIgnoredOnly (i : Nat) : Bool := ignored.contains i && !aliased.contains i
    let counted := (List.range decls.size).filter fun i => decls[i]!.isCounted
    let nAliased := (counted.filter aliased.contains).length
    let nIgnored := (counted.filter isIgnoredOnly).length
    let nBoth := (counted.filter fun i => ignored.contains i && aliased.contains i).length
    let missing := counted.filter fun i => !aliased.contains i && !ignored.contains i
    let unresolvedA := (aliasRes.filter (·.2.isNone)).map (·.1)
    let unresolvedI := (ignoreRes.filter (·.2.isNone)).map (·.1)
    let files := (decls.map (·.file)).toList.eraseDups.toArray.qsort
      fun a b => lexLt (rocqFileKey a) (rocqFileKey b)
    -- Rocq order: by file (layer, path), then line, then name
    let declLt (i j : Nat) : Bool :=
      let (di, dj) := (decls[i]!, decls[j]!)
      lexLt (rocqFileKey di.file) (rocqFileKey dj.file) ||
        (di.file == dj.file && lexLt (di.line, di.qualName) (dj.line, dj.qualName))
    let nOther := decls.size - counted.length
    out := out ++ s!"- Coverage: the scanner finds **{counted.length}** declarations " ++
      "(definitions, lemmas, instances, inductives, records and classes with their " ++
      s!"constructors and fields) in {files.size} Rocq files of `lantana/` and " ++
      s!"`lantana_heap_lang/` (and {nOther} section-local `Let`s, notations, tactics and " ++
      s!"module aliases, matched but not counted): **{nAliased}** aliased, **{nIgnored}** " ++
      s!"ignored, **{missing.length}** neither (section 3)" ++
      (if nBoth > 0 then s!"; {nBoth} of the aliased ones are also ignored" else "") ++ ".\n"
    out := out ++ s!"- {unresolvedA.size} aliases and {unresolvedI.size} ignores name no " ++
      "declaration the scanner finds; they are listed at the end of sections 1 and 2. " ++
      s!"{nAmbiguous} names match declarations of several Rocq files and are resolved by " ++
      "the Lean module's directory and name.\n\n"
    out := out ++ "The scanner and the name resolution are heuristic (see " ++
      "`scripts/RocqTable.lean`).\n\n"
    -- per-file summary
    out := out ++ "| Rocq file | Declarations | Aliased | Ignored | Neither | Lean modules |\n"
    out := out ++ "|---|--:|--:|--:|--:|---|\n"
    for f in files do
      let is := counted.filter (decls[·]!.file == f)
      let a := (is.filter aliased.contains).length
      let ig := (is.filter isIgnoredOnly).length
      let mods := ((aliasRes.filter fun (_, r) => r.any (decls[·]!.file == f)).map
        (·.1.module)).toList.eraseDups.toArray.qsort (fun a b => lexLt (moduleKey a) (moduleKey b))
      let modsStr := ", ".intercalate (mods.toList.map fun m =>
        s!"`{(m.replacePrefix `Lantana .anonymous).toString}`")
      out := out ++ s!"| `{f}` | {is.length} | {a} | {ig} | {is.length - a - ig} | {modsStr} |\n"
    out := out ++ "\n## 1. Aliased Rocq declarations, by Rocq file\n\n"
    let resolved := (aliasRes.filterMap fun (a, r) => r.map (a, ·)).qsort
      fun (a, i) (b, j) => declLt i j || (i == j && a.rocq < b.rocq)
    for (f, als) in groupBy resolved (fun (_, i) => decls[i]!.file) do
      out := out ++ s!"### `{f}`\n\n" ++ aliasTable (als.map (·.1)) ++ "\n"
    out := out ++ "### Aliases with no Rocq declaration found by the scanner\n\n"
    out := out ++ aliasTable (unresolvedA.qsort fun a b =>
      lexLt (moduleKey a.module) (moduleKey b.module) ||
        (a.module == b.module && lexLt (a.line.getD 0, a.rocq) (b.line.getD 0, b.rocq))) ++ "\n"
    out := out ++ "## 2. Ignored Rocq declarations, by Rocq file\n\n"
    let resolvedI := (ignoreRes.filterMap fun (a, r) => r.map (a, ·)).qsort
      fun (a, i) (b, j) => declLt i j || (i == j && a.rocq < b.rocq)
    for (f, is) in groupBy resolvedI (fun (_, i) => decls[i]!.file) do
      out := out ++ s!"### `{f}`\n\n" ++ ignoreTable (is.map (·.1)) true ++ "\n"
    out := out ++ "### Ignores with no Rocq declaration found by the scanner\n\n"
    out := out ++ (if unresolvedI.isEmpty then "None.\n" else ignoreTable unresolvedI true) ++ "\n"
    out := out ++ "## 3. Rocq declarations neither aliased nor ignored\n\n"
    out := out ++ "A coverage report, not a to-do list: the declarations the scanner finds and " ++
      "no alias or ignore names, with their kind and Rocq line. Typical entries are sealing " ++
      "boilerplate (`_def`/`_aux`/`_unseal`), `Proper` and proof-mode instances, constructors " ++
      "and fields of ghost-state classes, and HeapLang infrastructure that comes with the " ++
      "fork of Iris-Lean's HeapLang; the entries are not reviewed one by one.\n\n"
    for (f, is) in groupBy (missing.toArray.qsort declLt) (decls[·]!.file) do
      out := out ++ s!"- `{f}` ({is.size}): " ++
        ", ".intercalate (is.toList.map fun i =>
          s!"`{decls[i]!.qualName}` ({decls[i]!.kind}, l. {decls[i]!.line})") ++ "\n"
    return out

end RocqTable

open RocqTable in
run_cmd do
  let (aliases, ignores) ← collect
  let root? ← IO.getEnv "ROCQ_LANTANA"
  let rev := (← IO.getEnv "ROCQ_LANTANA_REV").getD ""
  let decls? ← match root? with
    | some r => if r.isEmpty then pure none else some <$> scanRocq r
    | none => pure none
  IO.print (document rev decls? aliases ignores)
