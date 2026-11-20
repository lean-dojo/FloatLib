/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Compiler.NoncomputableAttr
public meta import Lean.Elab.Command
public meta import Lean.Meta.Tactic.Simp
public import FloatLib.Tactic.KernelOptimize

/-!
# `kernel_twin`: a whole program rewritten for Lean's kernel, proved equal

`simp only [kernel_optimize]` rewrites a statement with the tagged kernel rules. It does not reach
a program whose arithmetic is inside its definitions: a checker `Their.check input = true`, from a
library with its own soundness theorem, shows the rules nothing to rewrite. `kernel_twin` rewrites
the definitions instead, without editing them:

```lean
namespace Twin
kernel_twin Their.check within Their
end Twin
```

goes through every definition that `Their.check` depends on among the modules whose name starts
with `Their` (several prefixes may be given), dependencies first. The body of each is rewritten
with the tagged rules and with the equations of the twins made so far. A definition whose body
changes gets

* a twin `Twin.Their.f` (the current namespace, then the original name) with the rewritten body,
* the theorem `Twin.Their.f.twin_eq : Their.f = Twin.Their.f`, with the proof that the rewriting
  produced. Lean's kernel checks it like every theorem.

A definition that no rule changes is used as it is. The originals and the theorems about them are
untouched, so the kernel can evaluate the twin for a statement about the original:

```lean
theorem ok : Their.check input = true := by
  rw [Twin.Their.check.twin_eq]
  decide +kernel
```

The command reports how many definitions it went through and how many it rewrote. It also names
every twin whose body still mentions a definition that has a twin: there the rewriting could not
replace an occurrence (inside a proof term or a dependent argument), and the kernel will run that
occurrence as written. A twin is a definition for the kernel only: no code is compiled for it.

Omitting `within` restricts the search to the current module, which makes an example independent
of its file name.

Scope. The rewriting is `simp` with the tagged rules, so it covers what `simp` can rewrite:
definitions by structural or well-founded recursion are rewritten in their compiled form
(recursors and matchers), instances are treated like other definitions, and `partial`, `opaque`
and `unsafe` constants are left alone. A rule changes an operation and not a data structure: a
program that fills an `Array` by pushes still copies the array once per push after the rewrite.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.Backend.Tag

open Lean Meta Elab Command

/-- The definitions that `root` depends on among the constants declared in a module whose name
starts with one of `scopes` (the module being elaborated counts), each after the definitions that
it uses. -/
partial def twinClosure (env : Environment) (scopes : Array Name) (root : Name) : Array Name :=
  let rec visit (name : Name) (state : NameSet × Array Name) : NameSet × Array Name := Id.run do
    if state.1.contains name then return state
    let mut state := (state.1.insert name, state.2)
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless scopes.any (·.isPrefixOf moduleName) do return state
    let some (.defnInfo info) := env.find? name | return state
    if info.safety != .safe then return state
    for used in info.value.getUsedConstants do
      state := visit used state
    return (state.1, state.2.push name)
  (visit root ({}, #[])).2

/-- What `kernel_twin` did: the definitions it went through, the pairs of an original and its
twin, and the twins whose body still mentions a definition that has a twin. -/
structure TwinReport where
  /-- The definitions that the root depends on in the given modules. -/
  examined : Array Name
  /-- Each rewritten definition with its twin. -/
  twins : Array (Name × Name)
  /-- The twins that still mention a rewritten definition. -/
  leftovers : Array Name

/--
The tagged kernel rules as a rewrite set whose rules fire before the subterms are visited.
`addTwins` uses `singlePass`: a replacement's body is not repeatedly rewritten. Rule direction
and priority come from the shared registry, including reversed registrations.
-/
def twinRules : MetaM SimpTheorems := do
  let mut rules : SimpTheorems := {}
  for rule in ← kernelRules do
    rules ← if rule.unfold then rules.addDeclToUnfold rule.declName
      else rules.addConst rule.declName (post := false) (inv := rule.inverted) (prio :=
        rule.priority)
  return rules

/--
Add the twins of the definitions that `root` depends on in the modules under `scopes`, under the
namespace `ns`: for each definition `f` whose body the tagged kernel rules change, the definition
`ns ++ f` with the rewritten body and the theorem `(ns ++ f).twin_eq : f = ns ++ f`.
-/
def addTwins (root : Name) (scopes : Array Name) (ns : Name) : MetaM TwinReport := do
  let examined := twinClosure (← getEnv) scopes root
  let congrTheorems ← getSimpCongrTheorems
  let mut rules ← twinRules
  let mut twins : Array (Name × Name) := #[]
  let mut twinned : NameSet := {}
  let mut leftovers : Array Name := #[]
  for name in examined do
    let .defnInfo info ← getConstInfo name | continue
    let ctx ← Simp.mkContext (config := { maxSteps := 10000000, singlePass := true })
      (simpTheorems := #[rules])
      (congrTheorems := congrTheorems)
    let (result, _) ← simp info.value ctx
    if result.expr == info.value then continue
    let twin := ns ++ privateToUserName name
    if (← getEnv).contains twin then
      throwError "kernel_twin: `{twin}` already exists; use another namespace for the twins"
    let levels := info.levelParams.map mkLevelParam
    addDecl <| .defnDecl
      { name := twin, levelParams := info.levelParams, type := info.type, value := result.expr,
        hints := info.hints, safety := .safe }
    modifyEnv (addNoncomputable · twin)
    addDocStringCore twin
      s!"`{name}` with its body rewritten by the `@[kernel_optimize]` rules: the form that \
        Lean's kernel evaluates (`{twin ++ `twin_eq}`)."
    let statement ← mkEq (mkConst name levels) (mkConst twin levels)
    let proof ← match result.proof? with
      | some proof => pure proof
      | none => mkEqRefl (mkConst name levels)
    let equation := twin ++ `twin_eq
    addDecl <| .thmDecl
      { name := equation, levelParams := info.levelParams, type := statement, value := proof }
    addDocStringCore equation
      s!"`{name}` is equal to its kernel twin `{twin}`, by the proofs of the rules that \
        rewrote its body."
    rules ← rules.addConst equation (post := false)
    if result.expr.getUsedConstants.any twinned.contains then
      leftovers := leftovers.push twin
    twins := twins.push (name, twin)
    twinned := twinned.insert name
  return { examined, twins, leftovers }

/--
`kernel_twin f within M₁ M₂ …` adds, under the current namespace `N`, a twin `N.g` of every
definition `g` that `f` depends on in the modules whose name starts with one of `M₁ M₂ …` and
whose body the `@[kernel_optimize]` rules change, with the kernel-checked theorem
`N.g.twin_eq : g = N.g`. A statement about `f` is then proved by evaluating `N.f` in the kernel:
`rw [N.f.twin_eq]; decide +kernel`. The originals are not changed. The command does not reserve
the word `within`: it stays a name that definitions and variables may have.
-/
elab "kernel_twin " root:ident &" within " scopes:(ppSpace colGt ident)+ : command => do
  let ns ← getCurrNamespace
  if ns.isAnonymous then
    throwError "kernel_twin: open a namespace first; the twins are declared in it"
  let rootName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let report ← liftTermElabM <| addTwins rootName (scopes.map (·.getId)) ns
  if report.examined.isEmpty then
    throwError "kernel_twin: `{rootName}` is not a definition in a module under \
      {scopes.map (·.getId)}"
  let unreached := if report.leftovers.isEmpty then m!"" else
    m!"; a rewritten definition is still used as written in {report.leftovers}"
  logInfo m!"kernel_twin: definitions examined: {report.examined.size}, rewritten: \
    {report.twins.size}{unreached}"

/-- `kernel_twin f` rewrites dependencies in the current module; use `within` to include imports. -/
elab "kernel_twin " root:ident : command => do
  let scope := mkIdent (← getEnv).mainModule
  elabCommand (← `(kernel_twin $root within $scope))

end FloatLib.Floats.ExecFloat.Backend.Tag
