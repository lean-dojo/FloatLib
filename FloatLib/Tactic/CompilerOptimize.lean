/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Compiler.NoncomputableAttr
public meta import Batteries.Tactic.Lint.Misc
public meta import FloatLib.Util.Declaration

public import FloatLib.Kernels.Selection.Portfolio
public import FloatLib.Util.Provenance

/-!
# `@[compiler_optimize]`: implementations for compiled code

A compiled backend is a `Backend.Certified spec`: an executable kernel, its cost estimate and the
proof `run = spec`. Tagging a definition of one registers it with the planner:

```lean
@[compiler_optimize]
def tableAdd (format : FloatFormat) (plan : StoragePlan format) :
    Option (Certified (Spec.add (format := format) (plan := plan))) := ...
```

The specification in the type says which operation and which formats the candidate covers. Its
value may be a `Certified spec`, an `Option` of one or a `List` of them, so that a candidate can
decline a format it does not support. Every argument must appear in the specification or be an
instance argument, since instance search fills the arguments in from the format in use.

A family's capability asks for `Portfolio spec`. Instance search answers with the list of
**all** tagged candidates in scope whose specification matches, and the planner
(`selectCertified` with the `PolicyFor` in scope) picks the best of them and the family's
baseline. So a candidate tagged in any imported module takes part in the selection, and the
cheapest admissible one runs, with no edit to the family.

The collection happens where a capability is asked for, so an operation is planned over the
candidates that its module imports. A definition that fixes its format (`def f (x : Binary32) :=
x + x`) keeps the capability found where it was written, and a definition that is generic in the
capability (`[ExecFloat.Add F]`) receives its caller's.

The tag has four forms.

* `@[compiler_optimize]`: an alternative, collected by `Tagged`.
* `@[compiler_optimize direct]`: an alternative that its family's capability names and calls
  without a closure when the planner selects it (`Backend.selectCertified_of_winsAfter`). It is
  registered and checked, and the capability lists it after the collected alternatives.
* `@[compiler_optimize baseline]`: the family's mandatory reference implementation. It is
  registered and checked, and the capability names it.
* `@[compiler_optimize reference]`: the executable specification itself. Its certificate is
  the shared `Certified.reference`, available as `compiled_reference% operation using estimate`.
  No separate identity-certificate definition is needed for each operation.

Every form requires a complete proof (`Provenance.requireProved`): the candidate's type contains
the proof `run = spec`, and a candidate whose proof uses `sorry` or another axiom is refused. A
declaration whose type is not a certified implementation is refused, except for the explicit
`reference` form, which requires a safe computable definition and uses the shared identity proof.

The proof is about Lean definitions, and compiled code runs what the compiler puts in their
place. So every form also requires that the candidate's code is the code of its definitions
(`Provenance.requireCompiled`): a candidate that reaches an `@[implemented_by]` or `@[extern]`
replacement outside Lean's own library is refused, unless the replacement has a registered
proof (`@[replacement_proof]`) or is the read of the constructor tag that Lean generates for
the constructor index of an inductive type (`Provenance.isGeneratedCtorIdx`). The check reads
the definition bodies that the tagging module can see.

## How the collection works

Each tagged candidate has a rank below `Tagged.top`, computed from the name of its module and
its position among the module's tags. Its instance says: the candidates below a bound above its
rank are this candidate followed by the candidates below its rank. Instance priorities follow
the ranks, so the search visits the matching candidates from the highest rank down and returns
them all, also when two imported modules each tag candidates the other does not know.
Alternatives of one module come in the order in which the module tags them. `compilerBackends`
lists the registry, and `#compiler_backends` prints it.

See Note [FloatLib registry trust] for the shared proof checks.
-/

@[expose] public meta section

/--
`@[compiler_optimize]` registers a certified implementation with the planner: a definition whose
type ends in `Backend.Certified spec`, `Option (Backend.Certified spec)` or
`List (Backend.Certified spec)`. `direct` and `baseline` mark the candidates that a family's
capability names itself. `reference` marks an executable specification, certified by the shared
`Certified.reference` constructor.
-/
syntax (name := Parser.Attr.compiler_optimize) "compiler_optimize" (ppSpace (&"direct" <|>
    &"baseline" <|> &"reference"))? :
  attr

namespace FloatLib.Floats.ExecFloat.Backend.Tag

open Lean Meta Elab
open FloatLib.Numerics.Provenance

/-- How a tagged compiled candidate takes part in its family's capability. -/
inductive Role where
  /-- Collected by `Tagged`. -/
  | alternative
  /-- Named by the family's capability and called without a closure when selected. -/
  | direct
  /-- The family's mandatory reference implementation. -/
  | baseline
  /-- An executable specification certified by the shared identity constructor. -/
  | reference
  deriving DecidableEq, Repr, Inhabited

/-- One entry of the compiled registry. -/
structure CompiledBackend where
  /-- The tagged declaration. -/
  declName : Name
  /-- How the candidate takes part in its family's capability. -/
  role : Role
  /-- The rank that orders collected alternatives. -/
  rank : Nat
  /-- The head constant of the specification: the family's reference operation. -/
  specification : Name
  deriving Inhabited

/-- The registry of tagged compiled backends, by declaration name. -/
initialize compiledBackendExt :
    SimpleScopedEnvExtension CompiledBackend (NameMap CompiledBackend) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun backends backend => backends.insert backend.declName backend }

/-- The registered compiled backends. -/
def compilerBackends : CoreM (Array CompiledBackend) :=
  return (compiledBackendExt.getState (← getEnv)).foldl
    (fun backends _ backend => backends.push backend) #[]

/-- The number of alternatives tagged so far in the module being elaborated. -/
initialize taggedCountExt : EnvExtension Nat ← registerEnvExtension (pure 0)

/--
The rank of the next alternative tagged in the current module: a number below `Tagged.top` that
is the same for no other candidate. Its high part comes from the module's name, and its low part
decreases with every tag, so the alternatives of one module are collected in the order in which
the module tags them.
-/
def nextRank : CoreM Nat := do
  let env ← getEnv
  let count := taggedCountExt.getState env
  modifyEnv fun env => taggedCountExt.setState env (count + 1)
  return (env.mainModule.hash.toNat % 1099511627776) * 1048576 + (1048575 - count % 1048576)

/--
Read the type of a candidate applied to its arguments: the `Certified spec` it offers, and the
candidate as a list of certificates.
-/
def offer (declName : Name) (body candidate : Expr) : MetaM (Expr × Expr) := do
  let body ← whnfR body
  if body.isAppOfArity ``Certified 2 then
    let list ← mkAppM ``List.cons #[candidate, ← mkAppOptM ``List.nil #[some body]]
    return (body, list)
  if body.isAppOfArity ``Option 1 then
    let certified ← whnfR body.appArg!
    if certified.isAppOfArity ``Certified 2 then
      return (certified, ← mkAppM ``Option.toList #[candidate])
  if body.isAppOfArity ``List 1 then
    let certified ← whnfR body.appArg!
    if certified.isAppOfArity ``Certified 2 then
      return (certified, candidate)
  throwError "`@[compiler_optimize]` cannot register `{.ofConstName declName}`: it is not a \
    certified implementation. Its type must end in `Backend.Certified spec`, \
    `Option (Backend.Certified spec)` or `List (Backend.Certified spec)`: the kernel together \
    with its estimate and the proof `run = spec`, for example \
    `Certified.binary estimate spec run run_eq_spec`. An implementation without that proof \
    cannot be registered."

/--
Declare the instance that puts the alternative `declName` into every `Tagged` collection whose
specification it matches, and return the head constant of the specification.
-/
def addTaggedInstance (declName : Name) (rank : Nat) (kind : AttributeKind) : MetaM Name := do
  let info ← getConstInfo declName
  let levels := info.levelParams.map mkLevelParam
  let instanceName := declName ++ `tagged
  let (type, value, specification) ← forallTelescope info.type fun arguments body => do
    let candidate := mkAppN (mkConst declName levels) arguments
    let (certified, alternatives) ← offer declName body candidate
    let carrier := certified.getArg! 0
    let spec := certified.getArg! 1
    let universes := certified.getAppFn.constLevels!
    -- Instance search fills in the arguments from the specification.
    for argument in arguments do
      let declaration ← argument.fvarId!.getDecl
      unless declaration.binderInfo.isInstImplicit do
        let determined ← arguments.anyM fun other => do
          return (← instantiateMVars (← inferType other)).containsFVar argument.fvarId! &&
            (← other.fvarId!.getDecl).binderInfo.isInstImplicit
        unless spec.containsFVar argument.fvarId! || carrier.containsFVar argument.fvarId! ||
            determined do
          throwError "`@[compiler_optimize]` cannot register `{.ofConstName declName}`: its \
            argument `{argument}` does not appear in the specification{indentExpr spec}\nso \
            the format in use does not determine it. Decide eligibility inside the candidate \
            and return `none` or `[]` for a format it does not support."
    let listType ← inferType alternatives
    withLocalDecl `gap .implicit (mkConst ``Nat) fun gap =>
      withLocalDecl `lower .implicit listType fun lower => do
        let taggedConst := mkConst ``Tagged universes
        let lowerClass := mkApp4 taggedConst carrier spec (mkNatLit rank) lower
        withLocalDecl `collected .instImplicit lowerClass fun collected => do
          let bound := mkNatAdd gap (mkNatLit (rank + 1))
          let all ← mkAppM ``List.append #[alternatives, lower]
          let conclusion := mkApp4 taggedConst carrier spec bound all
          let proof := mkApp4 (mkConst ``Tagged.mk universes) carrier spec bound all
          let binders := arguments ++ #[gap, lower, collected]
          let type ← mkForallFVars binders conclusion
          let value ← mkLambdaFVars binders proof
          return (type, value, spec.getAppFn.constName?.getD .anonymous)
  -- Explicit arguments of the candidate are found by unification, like the implicit ones.
  let type := type.inferImplicit info.type.getForallBinderNames.length false
  withExporting (isExporting := !isPrivateName declName) do
    addDecl <| .thmDecl
      { name := instanceName, levelParams := info.levelParams, type, value }
    addDocStringCore instanceName
      s!"Puts the candidate `{declName}` into every collection `Tagged` of its specification, \
        above the candidates collected before it. `@[compiler_optimize]` declares this instance."
  -- `Tagged` has no field, so the proof does not use the collection below the candidate.
  setEnv (← ofExcept <|
    Batteries.Tactic.Lint.nolintAttr.setParam (← getEnv) instanceName #[`unusedArguments])
  addInstance instanceName kind (rank + 1)
  return specification

/-- The head constant of the specification of a candidate that its family names. -/
def specificationOf (declName : Name) : MetaM Name := do
  let info ← getConstInfo declName
  forallTelescope info.type fun arguments body => do
    let levels := info.levelParams.map mkLevelParam
    let (certified, _) ← offer declName body (mkAppN (mkConst declName levels) arguments)
    return (certified.getArg! 1).getAppFn.constName?.getD .anonymous

/-- Register `declName` with the role of the attribute syntax `stx`. -/
def addCompiledBackend (declName : Name) (stx : Syntax) (kind : AttributeKind) :
    MetaM Unit := do
  let named (word : String) : Bool :=
    (stx[1].find? fun part => part.isAtom && part.getAtomVal == word).isSome
  let role : Role :=
    if named "direct" then .direct
    else if named "baseline" then .baseline
    else if named "reference" then .reference
    else .alternative
  let rank ← if role == .alternative then nextRank else pure 0
  for (other, backend) in compiledBackendExt.getState (← getEnv) do
    if backend.rank == rank && other != declName && backend.role == .alternative &&
        role == .alternative then
      throwError "`@[compiler_optimize]` cannot register `{.ofConstName declName}`: its rank \
        {rank} is the rank of `{.ofConstName other}`, which is tagged in a module whose name \
        has the same hash. Rename one of the two modules."
  -- The checks come first: a refused candidate leaves no instance behind.
  let named ← if role == .reference then do
      let .defnInfo info ← getConstInfo declName
        | throwError "`@[compiler_optimize reference]` requires a safe computable definition"
      unless info.safety == .safe && !isNoncomputable (← getEnv) declName do
        throwError "`@[compiler_optimize reference]` requires a safe computable definition"
      requireProved `compiler_optimize ``Certified.reference
      requireCompiled `compiler_optimize ``Certified.reference
      pure declName
    else specificationOf declName
  requireProved `compiler_optimize declName
  requireCompiled `compiler_optimize declName
  let specification ←
    match role with
    | .alternative => addTaggedInstance declName rank kind
    | .direct | .baseline | .reference => pure named
  compiledBackendExt.add { declName, role, rank, specification } kind

initialize
  registerBuiltinAttribute {
    name := `compiler_optimize
    descr := "compiled implementation of an operation, registered with its proof of equality"
    applicationTime := .afterCompilation
    add := fun declName stx kind =>
      discard <| (addCompiledBackend declName stx kind).run {} {} }

/--
Construct the shared identity certificate for an operation tagged
`@[compiler_optimize reference]`. Arguments may specialize the operation before certification;
the supplied estimate never participates in its equality proof.
-/
elab (name := compiledReference) "compiled_reference% " operation:term " using " estimate:term :
    term => do
  let operation ← Term.elabTerm operation none
  let some name := operation.getAppFn.constName?
    | throwError "a compiled reference must have a registered definition as its head"
  let some backend := (compiledBackendExt.getState (← getEnv)).find? name
    | throwError "the operation is not tagged `@[compiler_optimize reference]`"
  unless backend.role == .reference do
    throwError "the operation is not tagged `@[compiler_optimize reference]`"
  let estimate ← Term.elabTermEnsuringType estimate (mkConst ``Candidate)
  mkAppM ``Certified.reference #[estimate, operation]

end FloatLib.Floats.ExecFloat.Backend.Tag

namespace FloatLib.Floats.ExecFloat.Backend.Tag.Role

/-- Reconstruct a `Role` constructor from its constructor index. -/
add_decl_doc ofNat_ctorIdx

end FloatLib.Floats.ExecFloat.Backend.Tag.Role
