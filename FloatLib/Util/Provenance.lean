/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Compiler.ExternAttr
public meta import Lean.Compiler.ImplementedByAttr
public meta import Lean.Meta.Basic
public meta import Lean.Meta.Constructions.CtorIdx
public meta import Lean.Util.CollectAxioms
public meta import Lean.Util.Recognizers
public import Mathlib.Init -- Standard source linters.

/-!
# What a registry requires of a declaration

The logical and compiled-code checks shared by FloatLib's registries are described in
Note [FloatLib registry trust].

-/

public meta section

library_note «FloatLib registry trust» /--
FloatLib's registries (`@[kernel_optimize]`, `@[compiler_optimize]`, `@[lane_call]`) accept an
implementation only together with its proof. Two checks say what "proof" means.

`requireProved` is the logical check. The declaration and everything it depends on must use no
axiom beyond `propext`, `Classical.choice` and `Quot.sound`. A declaration that contains `sorry`,
or that rests on an axiom of its own, is refused with an error that names the axiom.

`requireCompiled` is the check on the code that runs. An equality between Lean definitions says
nothing about a definition that the compiler replaces: `@[implemented_by f]` and `@[extern]` put
other code in its place without a proof. The check follows the definitions that the compiled code
of a declaration calls, through every body this module can read, and refuses a replacement unless

* it is declared in Lean's own library (the modules `Init`, `Std` and `Lean`), whose replacements
  are the primitives of the compiler, or
* it is the implementation `T.ctorIdx._impl` that Lean generates for the constructor index of
  an inductive type `T` with several constructors (since Lean 4.36). `isGeneratedCtorIdx`
  recognizes the pair by both bodies: `T.ctorIdx` is the cases of its argument with the index of
  each constructor, and `T.ctorIdx._impl` reads the constructor tag of its argument. No theorem
  relates the tag read to `T.ctorIdx`: that the tag of a constructor object is the constructor's
  index is trusted as the rest of code generation is, or
* it is an `@[implemented_by]` replacement with a registered proof: a theorem tagged
  `@[replacement_proof]` that states `replacement x₁ … xₙ = definition x₁ … xₙ` for all arguments
  and no other premise.

Proofs and types are not followed, because compiled code does not run them. A definition whose
body the module system does not export to the registering module is not followed either; the
repository's audit (`tests/FloatLibTests/Conformance/Trust/Axioms.lean`) lists every replacement of
the library itself. Neither check says anything about the machine code that Lean's compiler and
the C compiler produce, or about foreign code behind an `@[extern]` of Lean's library.
-/

namespace FloatLib.Numerics.Provenance

open Lean Meta

/-- The three axioms of Lean's standard library that a registered declaration may depend on. -/
def standardAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/--
Fail unless `declName` is proved: it and its dependencies use no axiom beyond the standard three.
`tag` is the attribute's name and `rule` the sentence that states the registry's rule, both for
the message.
-/
def requireProved (tag : Name) (declName : Name)
    (rule : String := "A backend is registered only with a complete proof that it equals the \
      reference operation") : CoreM Unit := do
  let axioms ← collectAxioms declName
  let other := axioms.filter fun name => !standardAxioms.contains name
  unless other.isEmpty do
    let reason :=
      if other.contains (Name.mkSimple "sorryAx") then m!"its proof contains `sorry`"
      else m!"it depends on {other.toList.map MessageData.ofConstName}"
    throwError "`@[{tag}]` cannot register `{.ofConstName declName}`: {reason}. \
      {rule} (no axiom beyond `propext`, `Classical.choice` and `Quot.sound`)."

/--
Fail unless `proof` is a theorem whose conclusion is `replacement x₁ … xₙ = definition x₁ … xₙ`,
with `x₁ … xₙ` all its universally quantified arguments in order: equality on every argument,
with neither extra hypotheses nor restricted inputs.
-/
def checkReplacementEquality (definition replacement proof : Name) : MetaM Unit := do
  let info ← getConstInfo proof
  unless ← isProp info.type do
    throwError "replacement proof `{.ofConstName proof}` is not a theorem"
  forallTelescope info.type fun arguments conclusion => do
    let some (_, lhs, rhs) := conclusion.eq?
      | throwError "replacement proof `{.ofConstName proof}` does not conclude an equality"
    unless lhs.getAppFn.constName? == some replacement &&
        rhs.getAppFn.constName? == some definition &&
        lhs.getAppArgs == arguments && rhs.getAppArgs == arguments do
      throwError "replacement proof `{.ofConstName proof}` must equate \
        `{.ofConstName replacement}` and `{.ofConstName definition}` on all universally \
        quantified arguments, without additional hypotheses"

/-- The registered replacement proofs: the replaced definition and the theorem. -/
initialize replacementProofExt : SimpleScopedEnvExtension (Name × Name) (NameMap Name) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun table (definition, proof) => table.insert definition proof }

/-- The registered proof of the compiler replacement of `definition`, if there is one. -/
def replacementProof? (env : Environment) (definition : Name) : Option Name :=
  (replacementProofExt.getState env).find? definition

/-- Whether `module` belongs to Lean's own library, whose replacements are compiler primitives. -/
def isToolchainModule (module : Name) : Bool :=
  [`Init, `Std, `Lean].contains module.getRoot

/--
Whether a definition body is `fun x₁ … xₙ => getObjTagNat _ xₙ`: the read of the constructor tag
of its last argument.
-/
def isTagRead (value : Expr) : Bool :=
  let body := value.getLambdaBody
  value.isLambda && body.isAppOfArity ``getObjTagNat 2 && body.appArg! == .bvar 0

/--
Whether `value` is the constructor index of the inductive type `induct` as Lean generates it:
`fun … x => T.casesOn … x (fun … => 0) … (fun … => n - 1)`, the cases of the last argument with
the index of each constructor as a literal.
-/
def isCtorIdxBody (induct : InductiveVal) (value : Expr) : Bool :=
  let body := value.getLambdaBody
  let arguments := body.getAppArgs
  let major := induct.numParams + 1 + induct.numIndices
  value.isLambda && body.getAppFn.isConstOf (mkCasesOnName induct.name) &&
    arguments.size == major + 1 + induct.numCtors && arguments[major]! == .bvar 0 &&
    (List.range induct.numCtors).all fun index =>
      arguments[major + 1 + index]!.getLambdaBody == .lit (.natVal index)

/--
Whether `definition` and `code` are the constructor index of an inductive type `T` and the
implementation that Lean generates for it (`Lean.mkCtorIdx`, since Lean 4.36): `definition` is
`T.ctorIdx` with the generated body (`isCtorIdxBody`), and `code` is `T.ctorIdx._impl` with the
type of `T.ctorIdx` and the tag read of its last argument as body (`isTagRead`). A pair written
by hand under these names with another body on either side is not recognized.
-/
def isGeneratedCtorIdx (env : Environment) (definition code : Name) : Bool :=
  match isCtorIdxCore? env definition, env.find? definition, env.find? code with
  | some induct, some (.defnInfo logical), some (.defnInfo generated) =>
    code == definition ++ `_impl && generated.type == logical.type &&
      isCtorIdxBody induct logical.value && isTagRead generated.value
  | _, _, _ => false

/-- A compiler replacement that `requireCompiled` found. -/
structure Replacement where
  /-- The definition that the compiler replaces. -/
  definition : Name
  /-- The `@[implemented_by]` code, or `none` for an `@[extern]`. -/
  code : Option Name

/--
The compiler replacements without a registered proof among the definitions that the compiled code
of `declName` calls, outside Lean's own library and Lean's generated constructor-index tag reads
(`isGeneratedCtorIdx`). The search follows the bodies of definitions and of the code that replaces
them. It does not follow proofs, types, or a body that the environment does not hold.
-/
partial def unprovedReplacements (declName : Name) : CoreM (Array Replacement) := do
  let env := (← getEnv).setExporting false
  let rec visit (name : Name) (state : NameSet × Array Replacement) :
      NameSet × Array Replacement := Id.run do
    let (seen, found) := state
    if seen.contains name then return state
    let seen := seen.insert name
    if let some index := env.getModuleIdxFor? name then
      if isToolchainModule env.header.moduleNames[index.toNat]! then return (seen, found)
    let body (name : Name) : Array Name :=
      match env.find? name with
      | some (.defnInfo info) => info.value.getUsedConstants
      | some (.opaqueInfo info) => info.value.getUsedConstants
      | _ => #[]
    if let some code := Compiler.getImplementedBy? env name then
      if isGeneratedCtorIdx env name code then return (seen, found)
      let found :=
        if (replacementProof? env name).isSome then found
        else found.push { definition := name, code := some code }
      return visit code (seen, found)
    let found := if isExtern env name then found.push { definition := name, code := none } else
      found
    return (body name).foldl (fun state used => visit used state) (seen, found)
  return (visit declName ({}, #[])).2

/--
Fail unless the code of `declName` is the code of its definitions: every compiler replacement it
reaches outside Lean's own library is a constructor-index tag read generated by Lean or has a
registered proof (`@[replacement_proof]`). `tag` is the attribute's name, for the message.
-/
def requireCompiled (tag : Name) (declName : Name) : CoreM Unit := do
  let found ← unprovedReplacements declName
  unless found.isEmpty do
    let describe (replacement : Replacement) : MessageData :=
      match replacement.code with
      | some code =>
        m!"`{.ofConstName replacement.definition}` is implemented by `{.ofConstName code}`"
      | none => m!"`{.ofConstName replacement.definition}` is external code"
    throwError "`@[{tag}]` cannot register `{.ofConstName declName}`: its compiled code is not \
      the code of its definitions, because {MessageData.joinSep (found.toList.map describe) ", "}. \
      The proof `run = spec` is about the definitions. Register the proof that a replacement \
      computes its definition with `@[replacement_proof]`, or use a `@[csimp]` equation."

end FloatLib.Numerics.Provenance
