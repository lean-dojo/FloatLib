/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.LabelAttribute
public meta import Lean.Meta.Tactic.Simp.Simproc

/-!
# Registering rules and containers with `roundoff`

`[roundoff_rule]` registers an existing numerical bound, observation equality, finiteness
theorem or order fact with the `roundoff` analysis. Matching uses the whole theorem, including
its arithmetic capabilities and side conditions. Imported theorems can be registered as they are,
and local registrations stay in their scope. Compiler replacements carrying both `csimp` and
`roundoff_rule` normalize optimized programs back to their proved source code.

A library adds its containers through one `Extension`, which says

* how an entry is read,
* which loops the analysis carries an invariant through, and the lemmas that lift a step bound
  through them,
* which reductions are sums,
* the laws that read an entry through the producer that computes it,
* and the implementation equalities that identify its dictionary methods with FloatLib's correctly
  rounded functions.

`@[roundoff_extension]` registers a meta definition of type `Extension`. FloatLib registers lists,
arrays, vectors, functions on `Fin n` and matrices, and another library registers its own tensors
the same way. Registrations live in the environment, as attributes do. A module sees those of the
modules it imports, in import order, each declaration once, and a local or scoped registration ends
with its scope. Registration checks that the extension names declared constants and argument
positions within the arities it gives. This module is lightweight, so that a module defining a
container or a dictionary can register it without importing the analysis.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta

/-- A scalar or container observation, shape equality, error bound, or proved compiler
replacement. Exact observations contribute zero local error and keep all their premises. -/
initialize roundoffRules : LabelExtension ←
  registerLabelAttr `roundoff_rule "register a proved numerical observation or error bound"

initialize registerTraceClass `roundoff

/-- A function reading one entry of a container: its name, its number of arguments, and the
position of the container counted back from the last argument (`2` when the container is
followed only by the index). -/
structure Read where
  /-- The reading function. -/
  head : Name
  /-- Its number of arguments. -/
  arity : Nat
  /-- The position of the container, counted back from the end of the arguments. -/
  fromEnd : Nat := 2
  /-- Whether this is the container's canonical read, to which its other getters normalize. -/
  canonical : Bool := true
  /-- The container types it reads. An entry of another type is not analyzed as this read. -/
  types : Array Name := #[]
  /-- For a class method, the position of its dictionary, counted back from the end of the
  arguments. -/
  dictionary : Option Nat := none
  /-- The dictionaries through which the method selects a stored entry, which must be those of
  Lean's own getters of lists, arrays and vectors (`getterDictionaries`). A read through another
  one, which may compute with the entry, is not this read. -/
  dictionaries : Array Name := #[]
  /-- Dictionaries that pass the read on to the dictionary they take last, which must be one of
  `dictionaries` or of these in turn, such as `Fin.instGetElemFinVal`. -/
  forwarding : Array Name := #[]
  /-- The classes, such as the storage of a tensor, whose dictionaries the read trusts.
  Registration checks that `laws` pin each of their methods (`Read.checkLaws`), and when the read
  selects stored entries (`Read.isCertified`), index data may use their dictionaries as far as
  those laws allow. -/
  trusts : Array Name := #[]
  /-- The methods of `trusts` that observe the entries a container holds, such as the array view of
  a buffer, which a selection certificate may read an entry from. -/
  observers : Array Name := #[]
  /-- A theorem that the read selects a stored entry (`Read.checkSelection`): for the read of its
  own variables, an entry that a getter of lists, arrays and vectors, or an earlier selecting read,
  takes from an observation of the container through its structure fields and `observers`. A read
  without a dictionary selects entries only with one, and otherwise it is analyzed as the function
  it is. -/
  selection : Option Name := none
  /-- The laws that pin the methods of `trusts` to the `observers`, and the injectivity of the
  observers that they state a method under, in the order `Read.checkLaws` reads them. -/
  laws : Array Name := #[]
  deriving Inhabited

/-- The dictionaries through which Lean's getter `GetElem.getElem` selects a stored entry of a list,
an array or a vector, the only reads that may select through dictionaries (`Read.dictionaries`). -/
def getterDictionaries : Array Name :=
  #[``List.instGetElemNatLtLength, ``Array.instGetElemNatLtSize, ``Vector.instGetElemNatLt]

/-- The dictionaries that pass Lean's getter on to one of `getterDictionaries`, as
`Fin.instGetElemFinVal` does for an index of `Fin n` (`Read.forwarding`). -/
def getterForwarding : Array Name := #[``Fin.instGetElemFinVal]

/-- Whether the `.olean` of `module` lies in the library directory of the running Lean. -/
def leanLibraryModule (module : Name) : IO Bool := do
  try
    let olean ← IO.FS.realPath (← findOLean module)
    let library ← IO.FS.realPath (← getLibDir (← getBuildDir))
    return library.components.isPrefixOf olean.components
  catch _ => return false

/-- Whether `name` is a constant of Lean's core library other than `Classical.choice`: of a module
under `Init`, `Std` or `Lean` that Lean's own library holds (`leanLibraryModule`). A constant of
another package that takes such a name does not count. The module system exports many core
definitions without their values, such as `Nat.land`, which every compiled sparse match uses. The
only other core axiom that is data stands for a `sorry`, which the build already rejects. -/
def coreConstant (name : Name) : CoreM Bool := do
  if name == ``Classical.choice then return false
  let environment ← getEnv
  let some index := environment.getModuleIdxFor? name | return false
  let some module := environment.header.moduleNames[index.toNat]? | return false
  unless [`Init, `Std, `Lean].contains module.getRoot do return false
  leanLibraryModule module

/-- Whether the dictionary `dictionary` is one through which `read` selects a stored entry
(`Read.dictionaries`), directly or through `Read.forwarding`. -/
partial def Read.selectsThrough (read : Read) (dictionary : Lean.Expr) : Bool :=
  match dictionary.consumeMData.getAppFn.constName? with
  | some name =>
      read.dictionaries.contains name ||
        (read.forwarding.contains name && dictionary.getAppNumArgs > 0 &&
          read.selectsThrough dictionary.consumeMData.appArg!)
  | none => false

/-- Whether `value`, an application of `read`'s head, is this read: a read without a registered
dictionary always is, a class method only through one of its `Read.dictionaries`. -/
def Read.selects (read : Read) (value : Lean.Expr) : Bool :=
  match read.dictionary with
  | none => true
  | some fromEnd =>
      value.getAppNumArgs ≥ fromEnd &&
        read.selectsThrough value.getAppArgs[value.getAppNumArgs - fromEnd]!

/-- Whether stored-read status may be granted to `read`: a getter through Lean's own dictionaries
(`Read.dictionaries`), or a read with a selection certificate (`Read.selection`), both of which
registration checks. -/
def Read.isCertified (read : Read) : Bool :=
  read.dictionary.isSome || read.selection.isSome

/-- Whether `term` observes `container` through structure fields and the `observers` of `read`
only: it is `container`, a field of an observation, or an observer applied to one of
`dictionaries` and to one observation, its only argument after the dictionary that is neither a
type nor a proof. -/
partial def Read.observes (read : Read) (dictionaries : Array Lean.Expr)
    (container term : Lean.Expr) : MetaM Bool := do
  let term := term.consumeMData
  if term == container then return true
  if let .proj owner _ record := term then
    return !isClass (← getEnv) owner && (← read.observes dictionaries container record)
  let some name := term.getAppFn.constName? | return false
  let some field ← getProjectionFnInfo? name | return false
  let arguments := term.getAppArgs
  if arguments.size ≤ field.numParams then return false
  unless field.fromClass do
    return arguments.size == field.numParams + 1 &&
      (← read.observes dictionaries container arguments[field.numParams]!)
  unless read.observers.contains name && dictionaries.contains arguments[field.numParams]! do
    return false
  let data ← (arguments.extract (field.numParams + 1) arguments.size).filterM fun argument => do
    return !(← isType argument) && !(← isProof argument)
  let #[receiver] := data | return false
  read.observes dictionaries container receiver

/-- Check the selection certificate of `read` (`Read.selection`), given the reads registered
before it. Its statement must conclude, for variables standing for every argument of the read in
order, that the read of them equals a read of `earlier` that selects stored entries, at an
observation of the read's container (`Read.observes`). The error, if any, says what is wrong. -/
def Read.checkSelection (read : Read) (earlier : Array Read) : MetaM (Option MessageData) := do
  let some certificate := read.selection | return none
  let name := MessageData.ofConstName certificate
  let some info := (← getEnv).find? certificate | return some m!"`{name}` is not declared"
  forallTelescopeReducing info.type fun binders conclusion => do
    let fail (message : MessageData) : MetaM (Option MessageData) := do
      return some (← addMessageContext m!"`{name}` {message}")
    let some (_, left, right) := conclusion.consumeMData.eq? |
      fail m!"does not conclude an equality"
    unless left.isAppOfArity read.head read.arity && left.getAppArgs == binders do
      return ← fail m!"does not state the read `{.ofConstName read.head}` of its own variables"
    -- The read at every universe, not one instance of them.
    let levels := left.getAppFn.constLevels!
    let parameters := (← getConstInfo read.head).levelParams.length
    let names := levels.filterMap fun | .param name => some name | _ => none
    unless levels.length == parameters && names.length == parameters &&
        names.eraseDups.length == parameters do
      return ← fail m!"states the read `{.ofConstName read.head}` at fixed universes"
    let container := binders[read.arity - read.fromEnd]!
    let right := right.consumeMData
    let some selecting := earlier.find? fun other =>
        right.isAppOfArity other.head other.arity && other.selects right && other.isCertified |
      fail m!"does not equate the read with a read that selects entries"
    let observed := right.getAppArgs[right.getAppNumArgs - selecting.fromEnd]!
    let dictionaries ← binders.filterM fun binder => do
      return (← isClass? (← inferType binder)).any read.trusts.contains
    unless ← read.observes dictionaries container observed do
      return ← fail m!"reads `{observed}`, which is not an observation of the container through \
        its fields and the observers of the read"
    return none

/-- What a field of a class that a read trusts (`Read.trusts`) holds. -/
private inductive Read.FieldKind where
  /-- A proof. -/
  | proof
  /-- A type, such as the buffer of a tensor's storage. -/
  | type
  /-- An observer of the read (`Read.observers`), a function of the container. -/
  | observer
  /-- A decision of the equality of two of its arguments that are values, which holds no data. -/
  | decision
  /-- A decision of equality under `Option`, whose tag is data. -/
  | optionalDecision
  /-- Any other function, which a law pins (`Read.laws`). -/
  | method
  /-- Any other value, which no law pins: a trusted class has none. -/
  | value
  deriving Inhabited, BEq

/-- Whether `type` decides the equality of two of its arguments that are values, not types, as
`DecidableEq α` does for entries of `α`. -/
private def isEqualityDecision (type : Lean.Expr) : MetaM Bool :=
  forallTelescopeReducing type fun binders body => do
    let body ← whnfR body
    unless body.isAppOfArity ``Decidable 1 do return false
    let some (decided, left, right) := body.appArg!.consumeMData.eq? | return false
    return binders.contains left && binders.contains right && !(← whnfR decided).isSort

/-- The fields of the class `name`, which `read` trusts, in order: each projection with what it
holds, read after the class's parameters and dictionary. A proof or a type is one also when the
read names it as an observer (`Read.observers`). -/
private def Read.fields (read : Read) (name : Name) : MetaM (Array (Name × Read.FieldKind)) := do
  let some info := getStructureInfo? (← getEnv) name | return #[]
  info.fieldNames.filterMapM fun field => do
    let some projection := getProjFnForField? (← getEnv) name field | return none
    let some projectionInfo ← getProjectionFnInfo? projection | return none
    let kind ← forallBoundedTelescope (← getConstInfo projection).type
        (some (projectionInfo.numParams + 1)) fun _ type => do
      if ← isProp type then return Read.FieldKind.proof
      if ← forallTelescopeReducing type fun _ result => do return (← whnfD result).isSort then
        return .type
      if read.observers.contains projection then
        return if (← whnfR type).isForall then Read.FieldKind.observer else .value
      let type ← whnfR type
      if type.isAppOfArity ``Option 1 then
        if ← isEqualityDecision type.appArg! then return .optionalDecision
      if ← isEqualityDecision type then return .decision
      return if type.isForall then .method else .value
    return some (projection, kind)

/-- The fields of the class `name`, which `read` trusts, that decide the equality of values under
`Option`, as `Option (DecidableEq α)` does: their tag is data that no law pins. -/
def Read.optionalDecisions (read : Read) (name : Name) : MetaM (Array Name) := do
  return (← read.fields name).filterMap fun (field, kind) =>
    if kind == .optionalDecision then some field else none

/-- For the first `count` arguments of the constant `name`, whether its parameter has a sort as its
type, as `α : Sort u` in `@Eq α`, and whether it is a proof, as the bound of a getter. A constant
that the environment does not show, such as an auxiliary proof of an imported module, has
neither. -/
private def parameterKinds (name : Name) (count : Nat) : MetaM (Array (Bool × Bool)) := do
  let some info := (← getEnv).find? name | return Array.replicate count (false, false)
  let kinds ← forallTelescopeReducing info.type fun binders _ =>
    binders.mapM fun binder => do
      let type ← inferType binder
      return ((← whnfR type).isSort, ← isProp type)
  return (kinds.extract 0 count) ++ Array.replicate (count - kinds.size) (false, false)

/-- Whether `term` uses the types that the projections `types` give for `dictionary`, also applied
to arguments as a family of types is, only as types: as the type of a binder or as an argument that
a constant takes for a parameter whose type is a sort, never as a term, as an equality of types or a
predicate on types would, nor as a type of a heterogeneous equality (`HEq`). This reads `term` as
written: an argument that a constant takes for a proof parameter, such as the bound of a getter, is
not read, a definition it calls is not unfolded, and a type built from these types, such as
`ULift Code`, is not followed. -/
private partial def isTypeOpaque (types : Array Name) (dictionary term : Lean.Expr) : MetaM Bool :=
  visit true term
where
  /-- `term` at a position that takes a type (`asType`) or any term. -/
  visit (asType : Bool) (term : Lean.Expr) : MetaM Bool := do
    unless term.containsFVar dictionary.fvarId! do return true
    match term with
    | .app .. =>
        let head := term.getAppFn
        let arguments := term.getAppArgs
        let some name := head.constName? |
          return (← visit false head) && (← arguments.allM (visit false))
        if types.contains name then
          if let some projection ← getProjectionFnInfo? name then
            if arguments[projection.numParams]? == some dictionary then
              unless asType do return false
              return ← (arguments.extract (projection.numParams + 1) arguments.size).allM
                (visit false)
        if name == ``HEq then return ← arguments.allM (visit false)
        let kinds ← parameterKinds name arguments.size
        (arguments.zip kinds).allM fun (argument, sort, proof) =>
          if proof then pure true else visit sort argument
    | .proj owner index record =>
        if record == dictionary then
          let some field := (getStructureInfo? (← getEnv) owner).bind (·.fieldNames[index]?) |
            return false
          return asType || !(getProjFnForField? (← getEnv) owner field).any types.contains
        visit false record
    | .forallE _ type body _ => return (← visit true type) && (← visit true body)
    | .lam _ type body _ => return (← visit true type) && (← visit asType body)
    | .letE _ type value body _ =>
        return (← visit true type) && (← visit false value) && (← visit asType body)
    | .mdata _ inner => visit asType inner
    | _ => return true

/-- The observer of `read` that `law` states injective, as `Function.Injective toArray` for
variables standing for the observer's class parameters and dictionary, if it is such a law. -/
private def Read.injectivity? (read : Read) (law : Name) : MetaM (Option Name) := do
  let some info := (← getEnv).find? law | return none
  forallTelescopeReducing info.type fun binders conclusion => do
    let some (_, left, right) := conclusion.consumeMData.eq? | return none
    let #[first, second] := binders.extract (binders.size - 3) (binders.size - 1) | return none
    unless left == first && right == second do return none
    let some (_, observedFirst, observedSecond) :=
        (← inferType binders.back!).consumeMData.eq? | return none
    let some observer := observedFirst.getAppFn.constName? | return none
    unless read.observers.contains observer do return none
    let some projection ← getProjectionFnInfo? observer | return none
    let variables := binders.extract 0 (projection.numParams + 1)
    unless binders.size == projection.numParams + 4 &&
        observedFirst == mkAppN observedFirst.getAppFn (variables.push first) &&
        observedSecond == mkAppN observedFirst.getAppFn (variables.push second) do
      return none
    let levels := observedFirst.getAppFn.constLevels!
    let names := levels.filterMap fun | .param name => some name | _ => none
    unless names.length == levels.length && names.eraseDups.length == levels.length &&
        levels.length == (← getConstInfo observer).levelParams.length do
      return none
    return some observer

/-- Whether `term` uses the dictionary `dictionary` only as the dictionary of a field of the class
`name` that `admits` accepts, or in a proof that a constant takes, such as the bound of a getter,
which holds no data. -/
private partial def usesOnly (name : Name) (admits : Name → Bool) (dictionary term : Lean.Expr) :
    MetaM Bool := do
  unless term.containsFVar dictionary.fvarId! do return true
  match term with
  | .proj owner index record =>
      if record != dictionary then return ← usesOnly name admits dictionary record
      let some field := (getStructureInfo? (← getEnv) owner).bind (·.fieldNames[index]?) |
        return false
      return owner == name && (getProjFnForField? (← getEnv) owner field).any admits
  | .app .. =>
      let arguments := term.getAppArgs
      if let some field := term.getAppFn.constName? then
        if let some projection ← getProjectionFnInfo? field then
          if arguments[projection.numParams]? == some dictionary then
            unless (← getEnv).getProjectionStructureName? field == some name && admits field do
              return false
            let others := arguments.extract 0 projection.numParams ++
              arguments.extract (projection.numParams + 1) arguments.size
            return ← others.allM (usesOnly name admits dictionary)
        let kinds ← parameterKinds field arguments.size
        return ← (arguments.zip kinds).allM fun (argument, _, proof) =>
          if proof then pure true else usesOnly name admits dictionary argument
      (arguments.push term.getAppFn).allM (usesOnly name admits dictionary)
  | .lam _ type body _ | .forallE _ type body _ =>
      return (← usesOnly name admits dictionary type) && (← usesOnly name admits dictionary body)
  | .letE _ type value body _ =>
      return (← usesOnly name admits dictionary type) &&
        (← usesOnly name admits dictionary value) && (← usesOnly name admits dictionary body)
  | .mdata _ inner => usesOnly name admits dictionary inner
  | _ => return false

/-- Check the laws (`Read.laws`) of the classes that `read` trusts (`Read.trusts`). Each class is
a structure class whose parameters take no dictionary, and each of its fields is a proof, a type or
a family of types, an observer of the read, which is a function and neither of those, a decision of
the equality of values, possibly under `Option`, or a method: any other function. No proof field
uses a type of the class, also applied, as a term or as a type of a heterogeneous equality, as
`Code = (α → Nat)` or `Code () = (α → Nat)` would; this screen reads the statement as written, not
the proofs that constants take as arguments, the definitions it calls or the types built from the
class's types. Each method is pinned by a law: a declaration whose statement concludes,
for variables standing for every argument of the method in order and nothing else, that the method
of them, alone or under an observer that another law states injective (`Function.Injective`),
equals a term that does not mention the method and uses the dictionary only through fields that are
no method or that an earlier law pins. The method is stated at all its universes, no other variable
is a dictionary, and the law passes the same screen of types. The error, if any, says what is
wrong, for a method without a law the shape of the law it needs. -/
def Read.checkLaws (read : Read) : MetaM (Option MessageData) := do
  let mut classes : Array (Name × Array (Name × Read.FieldKind)) := #[]
  for name in read.trusts do
    unless isClass (← getEnv) name && isStructure (← getEnv) name do
      return some m!"`{.ofConstName name}` is not a structure class"
    if ← forallTelescopeReducing (← getConstInfo name).type fun parameters _ =>
        parameters.anyM fun parameter => do return (← isClass? (← inferType parameter)).isSome then
      return some m!"`{.ofConstName name}` takes a dictionary"
    let fields ← read.fields name
    if let some (field, _) := fields.find? (·.2 == .value) then
      return some m!"`{.ofConstName field}` of the trusted class `{.ofConstName name}` holds a \
        value that no law pins"
    if let some (field, kind) := fields.find? fun (field, kind) =>
        read.observers.contains field && (kind == .proof || kind == .type) then
      return some m!"`{.ofConstName field}`, an observer of the read, holds a \
        {if kind == .proof then "proof" else "type"}, not a function of a container"
    let types := fields.filterMap fun (field, kind) => if kind == .type then some field else none
    for (field, kind) in fields do
      unless kind == .proof do continue
      let some projection ← getProjectionFnInfo? field | continue
      unless ← forallBoundedTelescope (← getConstInfo field).type (some (projection.numParams + 1))
          fun binders statement => isTypeOpaque types binders.back! statement do
        return some m!"`{.ofConstName field}` relates a type of `{.ofConstName name}` to another \
          type"
    classes := classes.push (name, fields)
  let mut injective : Array Name := #[]
  for law in read.laws do
    if let some observer ← read.injectivity? law then injective := injective.push observer
  let mut pinned : Array Name := #[]
  for law in read.laws do
    let some info := (← getEnv).find? law | return some m!"`{law}` is not declared"
    if let some observer ← read.injectivity? law then
      let some (name, fields) := classes.find? (·.2.contains (observer, .observer)) | continue
      let types := fields.filterMap fun (field, kind) => if kind == .type then some field else none
      let some projection ← getProjectionFnInfo? observer | continue
      unless ← forallBoundedTelescope info.type (some (projection.numParams + 1))
          fun binders statement => isTypeOpaque types binders.back! statement do
        return some m!"`{.ofConstName law}` relates a type of `{.ofConstName name}` to another \
          type"
      continue
    let pins ← forallTelescopeReducing info.type fun binders conclusion => do
      let fail (message : MessageData) : MetaM (Except MessageData Name) := do
        return .error (← addMessageContext m!"`{.ofConstName law}` {message}")
      let some (_, left, right) := conclusion.consumeMData.eq? |
        fail m!"does not conclude an equality"
      -- The method of the law's variables, alone or under an injective observer at its dictionary.
      let method? (side : Lean.Expr) : MetaM (Option (Name × Name × Lean.Expr)) := do
        let mut side := side.consumeMData
        if let some observer := side.getAppFn.constName? then
          if injective.contains observer then
            let some projection ← getProjectionFnInfo? observer | return none
            unless side.getAppNumArgs == projection.numParams + 2 &&
                side.getAppArgs.pop == binders.extract 0 (projection.numParams + 1) do
              return none
            side := side.appArg!.consumeMData
        let some method := side.getAppFn.constName? | return none
        let some (name, _) := classes.find? (·.2.contains (method, .method)) | return none
        unless side.getAppArgs == binders do return none
        return some (method, name, side)
      let (method, name, application, other) ← match ← method? left, ← method? right with
        | some (method, name, application), _ => pure (method, name, application, right)
        | none, some (method, name, application) => pure (method, name, application, left)
        | none, none => return ← fail m!"does not state a method of a trusted class of exactly its \
            own variables, in order, alone or under an injective observer"
      let methodName := MessageData.ofConstName method
      let levels := application.getAppFn.constLevels!
      let names := levels.filterMap fun | .param name => some name | _ => none
      unless names.length == levels.length && names.eraseDups.length == levels.length &&
          levels.length == (← getConstInfo method).levelParams.length do
        return ← fail m!"states `{methodName}` at fixed universes"
      let some projection ← getProjectionFnInfo? method | fail m!"states no method"
      let dictionary := binders[projection.numParams]!
      for binder in binders do
        if binder != dictionary && (← isClass? (← inferType binder)).isSome then
          return ← fail m!"takes the dictionary `{binder}`, through which it may compute"
      if (other.find? (·.isConstOf method)).isSome then
        return ← fail m!"reads `{methodName}` through itself"
      let fields := (classes.find? (·.1 == name)).map (·.2) |>.getD #[]
      let admits (field : Name) := !fields.contains (field, .method) || pinned.contains field
      unless ← usesOnly name admits dictionary other do
        return ← fail m!"reads `{methodName}` through a method of `{.ofConstName name}` that no \
          earlier law pins"
      let types := fields.filterMap fun (field, kind) => if kind == .type then some field else none
      let statement := (← binders.mapM inferType).push conclusion
      unless ← statement.allM (isTypeOpaque types dictionary) do
        return ← fail m!"relates a type of `{.ofConstName name}` to another type"
      return .ok method
    match pins with
    | .error message => return some message
    | .ok method => pinned := pinned.push method
  for (name, fields) in classes do
    for (field, kind) in fields do
      if kind == .method && !pinned.contains field then
        let method := MessageData.ofConstName field
        return some m!"`{method}`, a method of the trusted class `{.ofConstName name}`, has no \
          law: `laws` needs one concluding `{method} x = t`, or `o ({method} x) = t` for an \
          observer `o` that another law states injective, where `x` are variables for all its \
          arguments in order, with no other premise"
  return none

/-- A loop the analysis carries a relational invariant through, with the lemmas that lift the
bound of one step through it. The positions locate the element type, the accumulator type, the
step, the initial accumulator and the traversed input among the loop's arguments. The lemmas
take the arguments of `List.fold_error` and `List.fold_mixedError`, in the same order. -/
structure Loop where
  /-- The loop's head, such as `List.foldl`. -/
  fold : Name
  /-- The number of arguments of a complete loop. -/
  arity : Nat
  /-- The position of the type of the traversed elements. -/
  element : Nat
  /-- The position of the type of the accumulator. -/
  state : Nat
  /-- The position of the step function. -/
  step : Nat
  /-- The position of the initial accumulator. -/
  initial : Nat
  /-- The position of the traversed input. -/
  input : Nat
  /-- One iteration of absolute-error propagation, as `List.foldStep`. -/
  foldStep : Name
  /-- The conditions at the visited steps, as `List.AllSteps`. -/
  allSteps : Name
  /-- Conditions read on the original accumulator, as `List.AllSteps.of_map`. -/
  allStepsOfMap : Name
  /-- Conditions that hold everywhere, as `List.AllSteps.of_forall`. -/
  allStepsOfForall : Name
  /-- The accumulated absolute error, as `List.foldError`. -/
  foldError : Name
  /-- A budget kept by every step, as `List.foldError_identity`. -/
  foldErrorIdentity : Name
  /-- The absolute bound through the loop, as `List.fold_error`. -/
  errorBound : Name
  /-- One iteration of mixed-error propagation, as `List.mixedFoldStep`. -/
  mixedFoldStep : Name
  /-- The accumulated relative error, as `List.foldRelative`. -/
  foldRelative : Name
  /-- The accumulated absolute error of a mixed bound, as `List.foldAbsolute`. -/
  foldAbsolute : Name
  /-- The mixed bound through the loop, as `List.fold_mixedError`. -/
  mixedBound : Name
  /-- An invariant kept by every step, as `List.foldl_induction`. -/
  induction : Name
  /-- Zero budgets kept zero by every step, as `List.foldBudgets_eq_zero`. -/
  exactBudgets : Option Name := none
  /-- The canonical traversal of the input's coordinates, with the equality that rewrites any
  loop to it, when entries are read by coordinate. -/
  coordinates : Option (Name × Name) := none
  /-- The exact result of a loop that changes its accumulator at one coordinate only. -/
  single : Option Name := none
  /-- Positivity of a sum of positive terms over the coordinates. -/
  positiveSum : Option Name := none
  /-- Equalities, used from left to right, that write a loop over a computed container as a loop
  over the containers its producer reads, with the producer moved into the step, such as
  `List.foldl_map`, and those exposing such a producer under a conversion, such as
  `Array.toList_map`. A loop without coordinates traverses its input entry by entry, and an entry
  is exact data, so the analysis applies them first to a container that does not store inputs. -/
  fusions : Array Name := #[]
  /-- The first component of a loop over pairs whose step computes it from the accumulator's
  first component alone is the loop of that component, as `foldl_fst`. -/
  projection : Option Name := none
  /-- One iteration of a loop beside its shadow state and budgets, the budgets it accumulates and
  the relation it carries through the loop, as `List.relationFoldStep`, `List.foldBudget` and
  `List.fold_relation`. A loop whose state is a tuple is analyzed through them. -/
  relation : Option (Name × Name × Name) := none
  /-- Whether a repeated complete loop is named by a `let` in a generated statement. -/
  named : Bool := true
  deriving Inhabited

/-- A sum: a reduction that adds its terms to zero in the order of one of the `loops`. Its laws
write it as that loop, through which the analysis bounds it, checks it finite and signs it. A
complete sum of configured values is also decoded as that loop, and a generated statement names a
repeated one `computedSum`. -/
structure Sum where
  /-- The head of a complete sum, or with `entries` the producer of a container whose entries are
  sums. -/
  head : Name
  /-- Equalities that write a complete sum or an entry as a loop, the most specific first, each
  with `true` to rewrite from its right side to its left. A sum without one unfolds its head. -/
  laws : Array (Name × Bool) := #[]
  /-- Whether the sums are the entries of the container that `head` produces. The laws then read
  an entry, and they take precedence over the program's other reads of it. -/
  entries : Bool := false
  /-- Whether the sum adds exact real numbers, as `Finset.sum` does, so that only mixed analysis
  writes it as its loop. -/
  exact : Bool := false
  deriving Inhabited

/-- A relation that one step of a loop preserves, such as Kahan's bound on the sum minus its
compensation, with the lemmas that start it and read a bound off it. An inline loop whose step
unfolds to the relation's step is analyzed through the loop's relation law. -/
structure StepRelation where
  /-- `∀ ..., ∀ state shadow budgets value, condition → relation state shadow budgets →
  relation (step state value) (reference shadow value) (budget state shadow budgets value)`, the
  `hstep` premise of the loop's relation law. The reference reads neither `state` nor `budgets`. -/
  preservation : Name
  /-- Lemmas `∀ ..., relation initial shadow budgets` for the initial states they state. -/
  initial : Array Name := #[]
  /-- Lemmas concluding a bound, or finiteness and a bound, on an observation of the state from
  a hypothesis `relation state shadow budgets`. -/
  readers : Array Name := #[]
  deriving Inhabited

/-- What a library adds to `roundoff`. Every field defaults to nothing. -/
structure Extension where
  /-- Types whose values the program normalization keeps intact, such as tensors. -/
  containers : Array Name := #[]
  /-- Namespaces of storage definitions that are never unfolded. -/
  storage : Array Name := #[]
  /-- The functions that read one entry of a container. -/
  reads : Array Read := #[]
  /-- Heads whose occurrence means an entry is still read through its container, so that the
  coordinate laws normalize it. -/
  observations : Array Name := #[]
  /-- Surface getters, normalized by the coordinate laws in a premise. -/
  surfaces : Array Name := #[]
  /-- Loops carried by a relational invariant. -/
  loops : Array Loop := #[]
  /-- Relations that one step of a loop preserves, read through the loop's relation law. -/
  stepRelations : Array StepRelation := #[]
  /-- Reductions written as one of the `loops` by the fold laws. -/
  reductions : Array Name := #[]
  /-- Further reductions, such as a dot product, whose finiteness is derived through their loop and
  whose goal is first normalized as a loop. -/
  loopHeads : Array Name := #[]
  /-- Sums, written as loops by their laws. -/
  sums : Array Sum := #[]
  /-- Equalities that write another loop as one of the `loops`, each with `true` to rewrite from
  its right side to its left. -/
  conversions : Array (Name × Bool) := #[]
  /-- Definitions the coordinate laws unfold. -/
  coordinateUnfold : Array Name := #[]
  /-- Coordinate laws. A name missing from the environment is skipped. -/
  coordinateRewrites : Array Name := #[]
  /-- Laws reading an entry through the producer that computes it. They also tidy references,
  budgets and conditions. -/
  readRewrites : Array Name := #[]
  /-- Definitions the fold laws unfold. -/
  foldUnfold : Array Name := #[]
  /-- Fold laws, each with `true` to rewrite from its right side to its left. -/
  foldRewrites : Array (Name × Bool) := #[]
  /-- Program rewrites, each with its simp priority. -/
  programRewrites : Array (Name × Nat) := #[]
  /-- Codec laws that decode a real observation through a dictionary's methods. -/
  decodingRewrites : Array Name := #[]
  /-- Definitions and laws that the exact decoding of an equality uses. -/
  decodeLemmas : Array Name := #[]
  /-- Reads recovered from another getter: the getter, its number of arguments and the equality
  that recovers the read. -/
  readRecoveries : Array (Name × Nat × Name) := #[]
  /-- Equalities reading an entry of a producer when nothing else exposes it. -/
  readFallbacks : Array Name := #[]
  /-- Implementation equalities: a correctly rounded primitive and the theorem equating a
  dictionary method with it. A method gets the primitive's contract through such a theorem, or
  when its selected implementation unfolds to the primitive call. -/
  bridges : Array (Name × Name) := #[]
  /-- Local rounding theorems of further operations, such as a cast into the format: the
  operation's head and the theorem. A finite result has relative error `u` and no absolute
  error. -/
  roundings : Array (Name × Name) := #[]
  /-- Exact operations, each with the theorem that its result is finite under the same hypotheses,
  or `none` when there is no such theorem. -/
  exactOperations : Array (Name × Option Name) := #[]
  /-- Simplification procedures every program normalizer runs, after the built-in ones: a name,
  `true` to run after the subterms are simplified (post) or `false` before (pre), and the
  procedure. -/
  procedures : Array (Name × Bool × (Simp.Simproc ⊕ Simp.DSimproc)) := #[]
  /-- Restate a read at another form where more rules apply: the restated read, the observation
  it applies and an equality between the two entries. -/
  restate : Array (Expr → MetaM (Option (Expr × Expr × Expr))) := #[]
  /-- Whether a container value, or a container its producer reads, has a shape that is not
  literal. -/
  symbolic : Array (Expr → MetaM Bool) := #[]
  /-- The skeleton of a container value's shape: the number of axes it lists and whether the list
  ends there. A registered read that reads its producer again at the same skeleton makes no
  progress. -/
  skeleton : Array (Expr → MetaM (Option (Nat × Bool))) := #[]
  /-- The registered reads of producers whose definition depends on a shape. -/
  readRules : Array (Environment → Array Name) := #[]

/-- The extension that adds nothing. -/
instance : Inhabited Extension := ⟨{}⟩

/-- Both extensions, `other` after `extension`. -/
def Extension.append (extension other : Extension) : Extension where
  containers := extension.containers ++ other.containers
  storage := extension.storage ++ other.storage
  reads := extension.reads ++ other.reads
  observations := extension.observations ++ other.observations
  surfaces := extension.surfaces ++ other.surfaces
  loops := extension.loops ++ other.loops
  stepRelations := extension.stepRelations ++ other.stepRelations
  reductions := extension.reductions ++ other.reductions
  loopHeads := extension.loopHeads ++ other.loopHeads
  sums := extension.sums ++ other.sums
  conversions := extension.conversions ++ other.conversions
  coordinateUnfold := extension.coordinateUnfold ++ other.coordinateUnfold
  coordinateRewrites := extension.coordinateRewrites ++ other.coordinateRewrites
  readRewrites := extension.readRewrites ++ other.readRewrites
  foldUnfold := extension.foldUnfold ++ other.foldUnfold
  foldRewrites := extension.foldRewrites ++ other.foldRewrites
  programRewrites := extension.programRewrites ++ other.programRewrites
  decodingRewrites := extension.decodingRewrites ++ other.decodingRewrites
  decodeLemmas := extension.decodeLemmas ++ other.decodeLemmas
  readRecoveries := extension.readRecoveries ++ other.readRecoveries
  readFallbacks := extension.readFallbacks ++ other.readFallbacks
  bridges := extension.bridges ++ other.bridges
  roundings := extension.roundings ++ other.roundings
  exactOperations := extension.exactOperations ++ other.exactOperations
  procedures := extension.procedures ++ other.procedures
  restate := extension.restate ++ other.restate
  symbolic := extension.symbolic ++ other.symbolic
  skeleton := extension.skeleton ++ other.skeleton
  readRules := extension.readRules ++ other.readRules

/-- The extension that the meta definition `name`, of type `Extension`, defines. -/
def evalExtension (name : Name) : ImportM Extension := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck Extension opts ``Extension name

/-- The registered extensions: the declarations defining them, each once, in the order they were
registered, and the extension combining them in that order. -/
structure Registered where
  /-- The declarations of the registered extensions. -/
  names : Array Name := #[]
  /-- The registered extensions, combined in the order of `names` by `Extension.append`. -/
  extension : Extension := {}

/-- No registered extension. -/
instance : Inhabited Registered := ⟨{}⟩

/-- The extensions registered with `roundoff_extension`, by declaration. The olean records the
declaration's name, and an importing module evaluates it again. -/
initialize extensions : ScopedEnvExtension Name (Name × Extension) Registered ←
  registerScopedEnvExtension {
    mkInitial := pure {}
    ofOLeanEntry := fun _ name => return (name, ← evalExtension name)
    toOLeanEntry := (·.1)
    addEntry := fun registered (name, extension) =>
      if registered.names.contains name then registered
      else { names := registered.names.push name
             extension := registered.extension.append extension } }

/-- Check that `extension`, the value of `declaration`, names declared constants, apart from the
coordinate laws, which may be missing, gives argument positions within the arities it states, reads
a class method only at its dictionary through instances of Lean's own library, and gives each
read's selection certificate the statement it needs (`Read.checkSelection`). The error names the
field and the declaration. -/
def Extension.validate (extension : Extension) (declaration : Name) : CoreM Unit := do
  let fail (field : String) (message : MessageData) : CoreM Unit :=
    throwError "roundoff_extension: `{field}` of `{.ofConstName declaration}`: {message}"
  let declared (field : String) (name : Name) : CoreM Unit := do
    unless (← getEnv).contains name do fail field m!"`{name}` is not declared"
  -- The arguments of `name` up to reducible unfolding of its type.
  let arguments (name : Name) : CoreM Nat := do
    let type := (← getConstInfo name).type
    MetaM.run' (Meta.forallTelescopeReducing type fun binders _ => pure binders.size)
  let applied (field : String) (name : Name) (arity : Nat) : CoreM Unit := do
    declared field name
    let count ← arguments name
    unless arity ≤ count do fail field m!"`{name}` takes {count} arguments, not {arity}"
  let mut earlier := (extensions.getState (← getEnv)).extension.reads
  for read in extension.reads do
    applied "reads" read.head read.arity
    unless 0 < read.fromEnd && read.fromEnd ≤ read.arity do
      fail "reads" m!"the container of `{read.head}` is argument {read.fromEnd} from the end \
        of {read.arity}"
    for type in read.types do declared "reads" type
    if let some position := read.dictionary then
      -- A read through dictionaries is a method of a class, at its dictionary, through instances of
      -- Lean's own library: Lean's getters of lists, arrays and vectors.
      let method ← getProjectionFnInfo? read.head
      unless method.any (fun method => method.fromClass &&
          read.arity - position == method.numParams) && position ≤ read.arity do
        fail "reads" m!"`{.ofConstName read.head}` is not a class method read at its dictionary"
      for name in read.dictionaries ++ read.forwarding do
        declared "reads" name
        unless Meta.isInstanceCore (← getEnv) name && (← coreConstant name) do
          fail "reads" m!"`{.ofConstName name}` is not an instance of Lean's own library"
      -- A dictionary that takes another dictionary passes the read on to it, so it forwards.
      for name in read.dictionaries do
        let forwards ← MetaM.run' <| forallTelescopeReducing (← getConstInfo name).type
          fun binders _ => binders.anyM fun binder => do
            return (← isClass? (← inferType binder)).isSome
        if forwards then
          fail "reads" m!"`{.ofConstName name}` passes the read on to another dictionary; it \
            belongs to `forwarding`"
      -- Of these, only Lean's getters of lists, arrays and vectors select stored entries.
      unless read.head == ``GetElem.getElem && read.arity == 8 && read.fromEnd == 3 &&
          position == 4 && read.dictionaries.all getterDictionaries.contains &&
          read.forwarding.all getterForwarding.contains do
        fail "reads" m!"`{.ofConstName read.head}` at these positions and dictionaries is not \
          Lean's getter of lists, arrays and vectors"
    if let some message ← MetaM.run' (read.checkSelection earlier) then fail "reads" message
    if let some message ← MetaM.run' read.checkLaws then fail "reads" message
    earlier := earlier.push read
  for loop in extension.loops do
    applied "loops" loop.fold loop.arity
    for (part, position) in [("element", loop.element), ("state", loop.state),
        ("step", loop.step), ("initial", loop.initial), ("input", loop.input)] do
      unless position < loop.arity do
        fail "loops" m!"the {part} of `{loop.fold}` is at position {position}, past its \
          {loop.arity} arguments"
    for name in #[loop.foldStep, loop.allSteps, loop.allStepsOfMap, loop.allStepsOfForall,
        loop.foldError, loop.foldErrorIdentity, loop.errorBound, loop.mixedFoldStep,
        loop.foldRelative, loop.foldAbsolute, loop.mixedBound, loop.induction] ++
        (loop.coordinates.map fun (traversal, law) => #[traversal, law]).getD #[] ++
        loop.exactBudgets.toArray ++ loop.single.toArray ++ loop.positiveSum.toArray ++
        loop.fusions ++ loop.projection.toArray ++
        (loop.relation.map fun (step, budget, bound) => #[step, budget, bound]).getD #[] do
      declared "loops" name
  for relation in extension.stepRelations do
    applied "stepRelations" relation.preservation 6
    for name in relation.initial do declared "stepRelations" name
    for name in relation.readers do applied "stepRelations" name 1
  for sum in extension.sums do
    declared "sums" sum.head
    for (law, _) in sum.laws do declared "sums" law
  for (getter, arity, law) in extension.readRecoveries do
    applied "readRecoveries" getter arity
    declared "readRecoveries" law
  for (field, names) in [("containers", extension.containers),
      ("observations", extension.observations), ("surfaces", extension.surfaces),
      ("reductions", extension.reductions), ("loopHeads", extension.loopHeads),
      ("conversions", extension.conversions.map (·.1)),
      ("coordinateUnfold", extension.coordinateUnfold), ("readRewrites", extension.readRewrites),
      ("foldUnfold", extension.foldUnfold), ("foldRewrites", extension.foldRewrites.map (·.1)),
      ("programRewrites", extension.programRewrites.map (·.1)),
      ("decodingRewrites", extension.decodingRewrites), ("decodeLemmas", extension.decodeLemmas),
      ("readFallbacks", extension.readFallbacks),
      ("bridges", extension.bridges.flatMap fun (primitive, law) => #[primitive, law]),
      ("roundings", extension.roundings.flatMap fun (head, law) => #[head, law]),
      ("exactOperations", extension.exactOperations.flatMap fun (rule, finite?) =>
        #[rule] ++ finite?.toArray)] do
    for name in names do declared field name

/-- `@[roundoff_extension]` registers an `Extension`, a meta definition, with `roundoff`. -/
initialize registerBuiltinAttribute {
  name := `roundoff_extension
  descr := "register an extension of the roundoff analysis"
  applicationTime := .afterCompilation
  add := fun declaration arguments kind => do
    Attribute.Builtin.ensureNoArgs arguments
    ensureAttrDeclIsMeta `roundoff_extension declaration kind
    let extension ← evalExtension declaration
    extension.validate declaration
    extensions.add (declaration, extension) kind }

/-- The extensions registered in the current environment, combined in their order. -/
def extension : CoreM Extension :=
  return (extensions.getState (← getEnv)).extension

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
