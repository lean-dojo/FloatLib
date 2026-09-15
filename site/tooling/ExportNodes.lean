/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals
import Lean

/-!
# Site proof-map exporter

This program is the Lean half of the site data pipeline (see `site/tooling/README.md`). It is
run against the already built library with

```
source tests/lib/lake.sh && lake -KbuildDir="$FLOATLIB_BUILD_DIR" env lean --run site/tooling/ExportNodes.lean \
  site/content/phases.json _out/site-data/nodes.raw.json
```

It reads the curated phase list, resolves every listed constant in the imported environment, and
writes one JSON record per constant: kind, pretty-printed signature, docstring, module, source
file, declaration range, transitive axioms, and the selected constants it depends on. The Python
glue (`export_atlas.py`) turns those records into `site/data/nodes.json`.

We resolve names against the real environment rather than parsing source text so that a typo in
`phases.json` fails the export instead of producing a node with no statement. Every missing name
is reported before the program exits with a nonzero status.

Dependencies are computed the way the Conway refinement blueprint computes them: starting from the
constants used by a node's type and value, we walk through unselected constants transitively and
stop at selected ones. Three details are specific to this library. First, we walk with the private
import level, so theorem proofs and non-exposed definition bodies of `module` files are visible
even though the library uses the module system. Second, we never descend into constants that are
not declared in a `FloatLib` module: Mathlib and core cannot reference FloatLib constants, so
they cannot reach a selected node, and skipping them keeps the walk to a few seconds. Third, when
the node is a theorem, the walk treats unselected definitions in `Runtime` modules as interfaces:
it follows their types but not their bodies. A runtime body dispatches to whichever kernel the
format is eligible for, so following it would make a theorem about the status flags of `sqrt`
depend on two-word integers and the binary32 layout, which is not what a reader means by
"depends on". Definitions keep the full walk, since for them the body is the point.
-/

open Lean Meta

namespace SiteExport

/-- One curated node as written in `phases.json`. -/
structure NodeSpec where
  name : String
  phase : String
  title : Option String
  deriving Repr

/-- The parsed `phases.json`: modules to import and the flattened node list. -/
structure Spec where
  imports : Array Name
  nodes : Array NodeSpec

/-- Parse `phases.json`. Node entries may be bare strings or objects with `name` and optional
`title`. -/
def parseSpec (text : String) : Except String Spec := do
  let json ← Json.parse text
  let imports ← match json.getObjVal? "imports" with
    | .ok arr => do
        let items ← arr.getArr?
        items.mapM fun item => do return String.toName (← item.getStr?)
    | .error _ => pure #[`FloatLib]
  let phases ← (← json.getObjVal? "phases").getArr?
  let mut nodes : Array NodeSpec := #[]
  for phase in phases do
    let id ← (← phase.getObjVal? "id").getStr?
    let entries ← (← phase.getObjVal? "nodes").getArr?
    for entry in entries do
      match entry with
      | .str name =>
          nodes := nodes.push { name, phase := id, title := none }
      | .obj _ =>
          let name ← (← entry.getObjVal? "name").getStr?
          let title := match entry.getObjVal? "title" with
            | .ok t => t.getStr?.toOption
            | .error _ => none
          nodes := nodes.push { name, phase := id, title }
      | _ => throw s!"phase {id}: node entries must be strings or objects"
  return { imports, nodes }

/-- Whether `c` is declared in one of the imported `FloatLib` modules. Constants outside the
project cannot depend on project constants, so the dependency walk never enters them. -/
def inProject (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => (`FloatLib).isPrefixOf m
      | none => false
  | none => false

/-- Module that declares `c`, when it is an imported constant. -/
def moduleOf (env : Environment) (c : Name) : Option Name :=
  match env.getModuleIdxFor? c with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => none

/-- Whether `c` is declared in a `Runtime` module, the executable half of the library's
`Runtime`/`Proof` module pairs. -/
def inRuntimeModule (env : Environment) (c : Name) : Bool :=
  match moduleOf env c with
  | some m => m.components.any fun part => part == `Runtime
  | none => false

/-- Constants used by the type of a declaration. -/
def typeUses (ci : ConstantInfo) : NameSet :=
  ci.type.getUsedConstantsAsSet

/-- Constants used by the value of a declaration, including theorem proofs, plus the constructors
of an inductive type (so that a structure depends on the types of its fields). -/
def valueUses (ci : ConstantInfo) : NameSet :=
  match ci.value? (allowOpaque := true) with
  | some v => v.getUsedConstantsAsSet
  | none =>
    match ci with
    | .inductInfo val => NameSet.ofList val.ctors
    | _ => {}

/-- All constants directly used by a declaration, in a stable order. -/
def directUses (ci : ConstantInfo) : Array Name :=
  ((typeUses ci).union (valueUses ci)).toArray

/-- The constants the walk follows out of the unselected constant `c`. With `interfaces` set (the
walk for a theorem node), a definition in a `Runtime` module contributes only the constants of its
type: a theorem about a runtime function depends on the function's interface, not on the kernels
its body dispatches to. Structures and theorems are followed in full either way. -/
def childrenOf (env : Environment) (interfaces : Bool) (c : Name) (ci : ConstantInfo) : Array Name :=
  if interfaces && inRuntimeModule env c then
    match ci with
    | .defnInfo _ | .opaqueInfo _ => (typeUses ci).toArray
    | _ => directUses ci
  else directUses ci

/-- A frame of the explicit depth-first search stack. -/
structure Frame where
  name : Name
  children : Array Name
  index : Nat := 0
  acc : NameSet := {}

/-- Reachability state shared across all nodes: for every unselected project constant already
finished, the set of selected nodes reachable from it. The two walks (full, and interfaces-only
for runtime definitions) reach different sets, so each has its own memo. -/
structure ReachState where
  memo : Std.HashMap Name NameSet := {}
  memoInterfaces : Std.HashMap Name NameSet := {}

def ReachState.lookup (st : ReachState) (interfaces : Bool) (c : Name) : Option NameSet :=
  if interfaces then st.memoInterfaces[c]? else st.memo[c]?

def ReachState.record (st : ReachState) (interfaces : Bool) (c : Name) (s : NameSet) : ReachState :=
  if interfaces then { st with memoInterfaces := st.memoInterfaces.insert c s }
  else { st with memo := st.memo.insert c s }

/--
Selected nodes reachable from `children` through unselected project constants. Selected constants
are boundaries: they are recorded and not entered. The search is iterative so that long
dependency chains cannot overflow the interpreter stack, and finished constants are memoized so
each project constant is expanded at most once over the whole export.
-/
def reachFrom (env : Environment) (selected : NameSet) (interfaces : Bool) (children : Array Name) :
    StateM ReachState NameSet := do
  let mut stack : Array Frame := #[{ name := .anonymous, children }]
  let mut inProgress : NameSet := {}
  let mut result : NameSet := {}
  while h : stack.size > 0 do
    let top := stack[stack.size - 1]
    if hi : top.index < top.children.size then
      let child := top.children[top.index]
      stack := stack.set! (stack.size - 1) { top with index := top.index + 1 }
      if selected.contains child then
        stack := stack.modify (stack.size - 1) fun f => { f with acc := f.acc.insert child }
      else if !inProject env child then
        pure ()
      else
        match (← get).lookup interfaces child with
        | some s =>
            stack := stack.modify (stack.size - 1) fun f => { f with acc := f.acc.union s }
        | none =>
            if inProgress.contains child then
              pure ()
            else
              match env.find? child with
              | some ci =>
                  inProgress := inProgress.insert child
                  stack := stack.push { name := child, children := childrenOf env interfaces child ci }
              | none => pure ()
    else
      stack := stack.pop
      if top.name.isAnonymous then
        result := top.acc
      else
        modify fun st => st.record interfaces top.name top.acc
        inProgress := inProgress.erase top.name
        if stack.size > 0 then
          stack := stack.modify (stack.size - 1) fun f => { f with acc := f.acc.union top.acc }
  return result

/-- The site's kind vocabulary for a constant. -/
def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : String :=
  let isInst := (instanceExtension.getState env).instanceNames.contains n
  match ci with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => if isInst then "instance" else "def"
  | .opaqueInfo _ => "def"
  | .inductInfo _ =>
      if isClass env n then "class" else if isStructure env n then "structure" else "inductive"
  | .axiomInfo _ => "axiom"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "def"
  | .quotInfo _ => "def"

/-- Pretty-print the signature with names shortened relative to the declaration's own namespace,
which is how the statement reads in its source file. -/
def prettySignature (n : Name) : MetaM String := do
  let fmt ← withTheReader Core.Context (fun c => { c with currNamespace := n.getPrefix })
    (PrettyPrinter.ppSignature n)
  return fmt.fmt.pretty 96

def namesJson (names : NameSet) : Json :=
  .arr <| (names.toArray.qsort Name.lt).map fun n => .str n.toString

/-- Export one node. Fails only if the constant vanished between the existence check and here. -/
def nodeJson (spec : NodeSpec) (selected : NameSet) (state : IO.Ref ReachState) : MetaM Json := do
  let env ← getEnv
  let n := spec.name.toName
  let some ci := env.find? n | throwError "constant {n} disappeared"
  let statement ← prettySignature n
  let doc := (← findDocString? env n).getD ""
  -- A structure field is exported as its projection function. Fields often carry no doc comment
  -- of their own, so we also report the structure and its docstring; the Python half uses them
  -- as a fallback when the field's own docstring is empty.
  let (parent, parentDoc) ← match env.getProjectionFnInfo? n with
    | some info =>
        match env.find? info.ctorName with
        | some (.ctorInfo c) => do
            let parentDoc := (← findDocString? env c.induct).getD ""
            pure (Json.str c.induct.toString, Json.str parentDoc)
        | _ => pure (Json.null, Json.null)
    | none => pure (Json.null, Json.null)
  let axioms ← Lean.collectAxioms n
  let (module, file) := match moduleOf env n with
    | some m => (m.toString, (m.toString.replace "." "/") ++ ".lean")
    | none => ("", "")
  let (line, endLine) := match ← findDeclarationRanges? n with
    | some r => (r.range.pos.line, r.range.endPos.line)
    | none => (0, 0)
  let interfaces := match ci with
    | .thmInfo _ => true
    | _ => false
  let st ← state.get
  let (typeDeps, st) := (reachFrom env selected interfaces (typeUses ci).toArray).run st
  let (valueDeps, st) := (reachFrom env selected interfaces (valueUses ci).toArray).run st
  state.set st
  let typeDeps := typeDeps.erase n
  let valueDeps := NameSet.ofList <|
    (valueDeps.erase n).toList.filter fun d => !typeDeps.contains d
  return Json.mkObj [
    ("name", n.toString),
    ("phase", spec.phase),
    ("title", match spec.title with | some t => .str t | none => .null),
    ("kind", kindOf env n ci),
    ("statement", statement),
    ("docstring", doc),
    ("module", module),
    ("file", file),
    ("line", line),
    ("endLine", endLine),
    ("axioms", .arr <| (axioms.qsort Name.lt).map fun a => .str a.toString),
    ("statementDependencies", namesJson typeDeps),
    ("proofDependencies", namesJson valueDeps),
    ("structureParent", parent),
    ("structureDocstring", parentDoc)
  ]

/-- Report every curation error at once: names that do not resolve and names listed twice. -/
def checkNames (env : Environment) (nodes : Array NodeSpec) : IO Unit := do
  let mut missing : Array String := #[]
  let mut seen : Std.HashSet String := {}
  let mut duplicates : Array String := #[]
  for node in nodes do
    if seen.contains node.name then duplicates := duplicates.push node.name
    seen := seen.insert node.name
    if (env.find? node.name.toName).isNone then missing := missing.push node.name
  if !missing.isEmpty || !duplicates.isEmpty then
    let mut message := ""
    if !missing.isEmpty then
      message := message ++ s!"{missing.size} listed constants do not exist in the imported environment:\n"
      for m in missing do message := message ++ s!"  {m}\n"
    if !duplicates.isEmpty then
      message := message ++ s!"{duplicates.size} constants are listed more than once:\n"
      for d in duplicates do message := message ++ s!"  {d}\n"
    throw <| IO.userError message

end SiteExport

open SiteExport in
unsafe def main (args : List String) : IO UInt32 := do
  let (specPath, outPath) ← match args with
    | [s, o] => pure (s, o)
    | _ => do
        IO.eprintln "usage: lean --run site/tooling/ExportNodes.lean <phases.json> <out.json>"
        return 2
  let text ← IO.FS.readFile specPath
  let spec ← match parseSpec text with
    | .ok s => pure s
    | .error e => throw <| IO.userError s!"{specPath}: {e}"
  Lean.enableInitializersExecution
  let env ← importModules (loadExts := true)
    (spec.imports.map fun m => { module := m }) {} 0
  checkNames env spec.nodes
  let selected : NameSet := spec.nodes.foldl (init := {}) fun s node => s.insert node.name.toName
  let opts := (Options.empty.setBool `pp.unicode.fun true).set `maxHeartbeats (0 : Nat)
  let ctx : Core.Context := { fileName := "<site-export>", fileMap := default, options := opts }
  let state ← IO.mkRef ({} : ReachState)
  let (records, _) ← (spec.nodes.mapM fun node => nodeJson node selected state).run' {}
    |>.toIO ctx { env := env }
  let output := Json.mkObj [
    ("imports", .arr <| spec.imports.map fun m => .str m.toString),
    ("nodes", .arr records)
  ]
  if let some dir := (System.FilePath.mk outPath).parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile outPath (output.pretty ++ "\n")
  IO.println s!"site-export: wrote {records.size} nodes to {outPath}"
  return 0
