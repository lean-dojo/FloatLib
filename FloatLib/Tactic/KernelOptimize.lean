/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public meta import Lean.Meta.Tactic.Simp.Attr
public import FloatLib.Util.Provenance

/-!
# `@[kernel_optimize]`: implementations for Lean's kernel

Lean's kernel computes natively only on natural-number literals, so an operation that a proof
evaluates (`decide +kernel`, `float_decide`) needs an implementation on encodings. A format
family, or any later module, registers one by tagging the theorem that proves it:

```lean
@[kernel_optimize (cost := 52)]
theorem mul_eq (x y : ExecFloat F) : x * y = Value.mul .nearest x y
```

The statement names the reference operation (left) and the implementation (right), and its
binders and instance arguments say which formats it covers. `float_decide` rewrites with every
tagged equation whose left side matches. When several match one term, the one with the lowest
declared cost is tried first, so a better implementation is used as soon as the module that
tags it is imported.

* The tag goes on a **theorem** whose conclusion is an equation, an `↔`, or a conjunction of
  them. Anything else is refused: an implementation is registered by its proof.
* `@[kernel_optimize ←]` reads the theorem from right to left, `implementation = reference`,
  which is how the equations of `Numerics.Kernel` are stated (`Z.add_eq : Z.add a b = a + b`).
  The theorem itself is the rule, with no mirrored copy.
* The proof must be complete (`Provenance.requireProved`): no `sorry`, no axiom beyond the
  standard three. The same holds for an unfolded selector and what it depends on.
* `(cost := n)` declares the kernel cost of one use in microseconds. A rule without a declared
  cost is tried after every rule with one. `#kernel_cost t` (`FloatLib.Tactic.KernelCost`)
  measures a term as written and after the rewrite with the tagged rules, so that a declared
  cost can be chosen and checked.
* `@[kernel_optimize unfold]` goes on a **definition** that only selects among operations (a
  mode-taking wrapper): `float_decide` unfolds it to reach the operations inside.

`kernelRules` lists what is registered, and `#kernel_rules` prints it.

See Note [FloatLib registry trust] for the shared proof checks.
-/

public meta section

/--
`@[kernel_optimize]` registers a theorem `reference = implementation` as a kernel implementation
that `float_decide` rewrites with, and `@[kernel_optimize ←]` a theorem
`implementation = reference`. `(cost := n)` declares its kernel cost in microseconds (the
cheapest matching rule is tried first), and `unfold` marks a selector definition to be unfolded.
-/
syntax (name := Parser.Attr.kernel_optimize) "kernel_optimize" (" ←")?
  (" (" &"cost" " := " num ")")? (ppSpace &"unfold")? : attr

namespace FloatLib.Floats.ExecFloat.Backend.Tag

open Lean Meta Elab
open FloatLib.Numerics.Provenance

/-- One entry of the kernel registry. -/
structure KernelRule where
  /-- The tagged declaration: the proof, or the selector that is unfolded. -/
  declName : Name
  /-- The declared kernel cost of one use, in microseconds. -/
  cost : Option Nat
  /-- Whether the declaration is a selector definition that is unfolded. -/
  unfold : Bool
  /-- Whether the theorem is read from right to left (`@[kernel_optimize ←]`). -/
  inverted : Bool := false
  /-- The head constant of the reference side: the operation that the rule implements. -/
  operation : Option Name
  deriving Inhabited

/-- Costs at or above this bound all rank last. -/
def costCeiling : Nat := 100000

/--
The rewrite priority of a rule: `1000` (the default priority of a rewrite rule) without a
declared cost, and higher by `costCeiling - cost` with one, so that the cheapest rule is tried
first.
-/
def KernelRule.priority (rule : KernelRule) : Nat :=
  1000 + (costCeiling - min (rule.cost.getD costCeiling) costCeiling)

/-- The rewrite set behind `@[kernel_optimize]`, which `float_decide` rewrites with. -/
initialize kernelOptimizeExt : SimpExtension ← mkSimpExt

/-- The registry of tagged kernel rules, by declaration name. -/
initialize kernelRuleExt : SimpleScopedEnvExtension KernelRule (NameMap KernelRule) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun rules rule => rules.insert rule.declName rule }

/-- The registered kernel rules. -/
def kernelRules : CoreM (Array KernelRule) :=
  return (kernelRuleExt.getState (← getEnv)).foldl (fun rules _ rule => rules.push rule) #[]

/-- Whether `statement` is an equation, an `↔`, or a conjunction of such statements. -/
partial def isEquation (statement : Expr) : Bool :=
  statement.isEq || statement.isAppOfArity ``Iff 2 ||
    (statement.isAppOfArity ``And 2 &&
      isEquation statement.appFn!.appArg! && isEquation statement.appArg!)

/-- The head constant of the reference side of the first equation in `statement`: the left
side, or the right side of an inverted rule. -/
partial def operationOf (statement : Expr) (inverted : Bool := false) : Option Name :=
  if statement.isAppOfArity ``And 2 then operationOf statement.appFn!.appArg! inverted
  else if statement.isEq || statement.isAppOfArity ``Iff 2 then
    (if inverted then statement.appArg! else statement.appFn!.appArg!).getAppFn.constName?
  else none

/-- Register `declName` with the options of the attribute syntax `stx`. -/
def addKernelRule (declName : Name) (stx : Syntax) (kind : AttributeKind) : MetaM Unit := do
  let inverted := !stx[1].isNone
  let cost := if stx[2].isNone then none else some stx[2][3].toNat
  let unfold := !stx[3].isNone
  let info ← getConstInfo declName
  let rule : KernelRule := { declName, cost, unfold, inverted, operation := none }
  if ← isProp info.type then
    if unfold then
      throwError "`@[kernel_optimize unfold]` is for a definition that selects among \
        operations; `{.ofConstName declName}` is a theorem, tag it with `@[kernel_optimize]`"
    let (accepted, operation) ← forallTelescope info.type fun _ conclusion => do
      let conclusion ← instantiateMVars conclusion
      return (isEquation conclusion, operationOf conclusion inverted)
    unless accepted do
      throwError "`@[kernel_optimize]` cannot register `{.ofConstName declName}`: its \
        statement is not an equation `reference = implementation` (or an `↔`, or a \
        conjunction of them)."
    requireProved `kernel_optimize declName
    addSimpTheorem kernelOptimizeExt declName (post := true) (inv := inverted) kind rule.priority
    kernelRuleExt.add { rule with operation } kind
  else
    if inverted then
      throwError "`@[kernel_optimize ←]` is for a theorem `implementation = reference`; \
        `{.ofConstName declName}` is a definition"
    unless unfold do
      throwError "`@[kernel_optimize]` cannot register `{.ofConstName declName}`: it is a \
        definition, not a proof. Tag the theorem that proves the implementation equal to the \
        reference operation, which is what registers it. (A definition that only selects \
        among operations can be unfolded by `float_decide` with `@[kernel_optimize unfold]`.)"
    requireProved `kernel_optimize declName
      "A selector is unfolded only when it and the operations it selects among are proved"
    unless ← addDeclToUnfold kernelOptimizeExt declName (post := true) (inv := false)
        rule.priority kind do
      throwError "`@[kernel_optimize unfold]` cannot register `{.ofConstName declName}`: it \
        is not a definition"
    kernelRuleExt.add { rule with operation := some declName } kind

initialize
  registerBuiltinAttribute {
    name := `kernel_optimize
    descr := "kernel implementation of an operation, registered by its proof of equality"
    applicationTime := .afterCompilation
    add := fun declName stx kind => discard <| (addKernelRule declName stx kind).run {} {}
    erase := fun declName => do
      let inverted :=
        ((kernelRuleExt.getState (← getEnv)).find? declName).any (·.inverted)
      let rules ← (kernelOptimizeExt.getState (← getEnv)).erase
        (.decl declName (inv := inverted))
      modifyEnv fun env => kernelOptimizeExt.modifyState env fun _ => rules
      -- The registry forgets the rule too, so that `#kernel_rules` lists what rewrites.
      modifyEnv fun env => kernelRuleExt.modifyState env (·.erase declName) }
  -- `simp only [kernel_optimize]` names the rewrite set.
  simpExtensionMapRef.modify fun extensions =>
    extensions.insert `kernel_optimize kernelOptimizeExt

end FloatLib.Floats.ExecFloat.Backend.Tag
