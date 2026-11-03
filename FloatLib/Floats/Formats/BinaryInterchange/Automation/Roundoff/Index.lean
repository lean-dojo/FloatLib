/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Normalize

/-!
# Rule indexing for `roundoff`

Inputs, the entries of a stored function read at index data, stored container entries, canonical
literals and casts of index data are exact data; index data computes no numerical value, also
through the definitions it calls: it compares, selects and stores stored values through FloatLib's
own order dictionaries, registered reads and the classes they trust, and applies a numerical
function, a variable or a field or the value of a constant at the arguments its type names, such as
an entry that a getter reads from a container, fully and to index data whose types hold no number
only, while a definition it hands a value that can hold one, such as a list of numerical functions,
is read through its value. Local definitions in types are expanded first. Registered rules are
classified by their conclusions: numerical bounds and observations, mixed bounds, finiteness
theorems and order facts. Each is prepared once per call, its container reads normalized like the
analyzed program, and indexed in a discrimination tree by the complete computation it concerns;
retrieval ignores instances, but applying a candidate checks its whole statement, selected
dictionaries included.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- Recognize scalar reads and coordinate maps that can still hide container indexing work: the
registered observations, function coercions and `GetElem.getElem`. -/
def hasObservation (expression : Lean.Expr) : CoreM Bool := do
  let heads := (← extension).observations ++ #[``CoeFun.coe, ``GetElem.getElem]
  return (expression.find? fun term =>
    heads.contains (term.getAppFn.constName?.getD .anonymous)).isSome

/-- Data fields of an input are inputs too. Class methods and applied function fields still
need their implementation or a numerical rule; treating them as data would hide computation. -/
partial def isInputValue (value : Lean.Expr) : MetaM Bool := do
  match value with
  | .fvar id => return (← id.getDecl).value?.isNone
  | .proj name _ source =>
      if isClass (← getEnv) name then return false
      isInputValue source
  | .mdata _ source => isInputValue source
  | _ =>
      let some name := value.getAppFn.constName? | return false
      let some field ← getProjectionFnInfo? name | return false
      if field.fromClass || value.getAppNumArgs != field.numParams + 1 then return false
      isInputValue value.getAppArgs[field.numParams]!

/-- Whether `value` reads a stored function, such as a vector on `Fin n` or a matrix, at indices: a
local variable without a value applied to arguments of type `Fin n` or `Nat` only. -/
def isAppliedInput (value : Lean.Expr) : MetaM Bool := do
  let .fvar id := value.getAppFn | return false
  if value.getAppNumArgs == 0 then return false
  if (← id.getDecl).value?.isSome then return false
  value.getAppArgs.allM fun argument => do
    let type ← whnfR (← inferType argument)
    return type.isAppOfArity ``Fin 1 || type.isConstOf ``Nat

/-- Whether a hypothesis states that `value`, computed rather than an input or a read of a stored
container, is finite. Such an operand is not analyzed ahead of the rules that might need its error:
exact operations take its finiteness from the hypothesis, and the zero and unit tests that select
them analyze it as they would without the hypothesis. -/
def assumedFinite (value : Lean.Expr) : MetaM Bool := do
  if ← isInputValue value then return false
  if let some position ← readPosition? value (getters := true) (certified := true) then
    if ← isInputValue value.getAppArgs[position]! then return false
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let type ← instantiateMVars declaration.type
    let conclusion := type.getForallBody
    unless isFiniteness conclusion do continue
    let some candidate := conclusion.getAppArgs[1]!.getAppArgs.back? | continue
    unless candidate.getAppFn.constName? == value.getAppFn.constName? do continue
    let matched ← withNewMCtxDepth do
      let (_, _, conclusion) ← forallMetaTelescopeReducing type
      let some candidate := conclusion.getAppArgs[1]!.getAppArgs.back? | return false
      withReducible (isDefEq candidate value)
    if matched then return true
  return false

/-- Whether `value`, or the model it decodes to, is an input as stored: a local variable, a data
field of one, or an entry of such a container that a read selecting stored entries takes
(`Read.isCertified`). -/
def isStoredInput (value : Lean.Expr) : MetaM Bool := do
  let value := if value.isAppOf ``ExecFloat.Binary.toModel then value.appArg! else value
  if let some position ← readPosition? value (certified := true) then
    return ← isInputValue value.getAppArgs[position]!
  isInputValue value

/-- The numerical carriers of the analysis: the reals, rationals and dyadics, Lean's floats with
their models in the core library (the packed `Float.Model` and `Float32.Model`, the unpacked
`Float.Model.UnpackedFloat` and the mantissa with rounding bits that its rounding uses), and
FloatLib's executable values, their codes and descriptor models. A value of one can hold a rounded
number. -/
def carrierTypes : Array Name := #[``Real, ``Rat, ``Float, ``Float32, ``Float.Model,
  ``Float32.Model, ``Float.Model.UnpackedFloat, ``Float.Model.UnpackedFloat.ExtendedMantissa,
  ``FloatLib.Numerics.Dyadic, ``FloatLib.Floats.ExecFloat, ``FloatLib.Floats.ExecFloat.Binary,
  ``FloatLib.Numerics.FormatCode, ``FloatLib.Floats.Formats.BinaryInterchange.Model]

/-- `expression` with each local definition it uses replaced by its value, at any depth, so that a
local abbreviation such as `let F := Value → Nat` is read as the type it stands for. -/
def expandLocal (expression : Lean.Expr) : MetaM Lean.Expr := do
  let expression ← instantiateMVars expression
  unless expression.hasFVar && (← getLCtx).any (·.isLet) do return expression
  zetaReduce expression

/-- Whether the constant `name` can hold a numerical value. As a type it does when it is one of
the `carrierTypes`, a definition of any reducibility whose value uses such a constant, or an
inductive type with a field of such a type that is not a proof. As a term (`term`) it also does
when its type does as a type, when its value uses a constant that does as a term, and when it is
an opaque constant or an axiom that is not a proof, whose value cannot be inspected, unless it
belongs to Lean's core library (`coreConstant`). A theorem never does. Every constant of a value
counts, also one that only its proofs use. -/
partial def carries (cache : CarrierCache) (term : Bool) (name : Name) : MetaM Bool := do
  let mode := term.toNat
  -- The constants `name` reads, or `none` when it holds a numerical value outright.
  let uses (name : Name) : MetaM (Option (Array Name)) := do
    if carrierTypes.contains name then return none
    let some info := (← getEnv).find? name | return if term then none else some #[]
    if term && (← info.type.getUsedConstants.anyM (carries cache false)) then return none
    match info with
    | .thmInfo _ => return some #[]
    | .defnInfo definition => return some definition.value.getUsedConstants
    | .opaqueInfo _ | .axiomInfo _ =>
        if term && !(← isProp info.type) && !(← coreConstant name) then return none
        return some #[]
    | .inductInfo type =>
        let mut fields := #[]
        for ctor in type.ctors do
          let some (.ctorInfo ctor) := (← getEnv).find? ctor | continue
          fields := fields ++ (← forallTelescope ctor.type fun arguments _ => do
            let mut used := #[]
            for field in arguments.extract ctor.numParams arguments.size do
              let fieldType ← inferType field
              unless ← isProp fieldType do used := used ++ fieldType.getUsedConstants
            return used)
        return some fields
    | _ => return some #[]
  -- Depth-first search for such a constant. A constant whose search met one still being searched
  -- above it is not cached as holding none: that one may still turn out to hold one.
  let rec visit (pending : NameMap Nat) (depth : Nat) (name : Name) :
      MetaM (Bool × Option Nat) := do
    if let some known := (← cache.get)[(name, mode)]? then return (known, none)
    if let some above := pending.find? name then return (false, some above)
    let pending := pending.insert name depth
    let some next ← uses name | do
      cache.modify (·.insert (name, mode) true)
      return (true, none)
    let mut low : Option Nat := none
    for used in next do
      let (found, reached) ← visit pending (depth + 1) used
      if found then
        cache.modify (·.insert (name, mode) true)
        return (true, none)
      low := match low, reached with
        | some low, some reached => some (min low reached)
        | low, reached => low <|> reached
    if low.all (depth ≤ ·) then cache.modify (·.insert (name, mode) false)
    return (false, low.filter (· < depth))
  return (← visit {} 0 name).1

/-- Whether a value of a type built with the constant `name` can hold a function of any kind: as a
definition its value has a function type in it or uses such a constant, or as an inductive type a
field of a constructor that is not a proof does, or is a type, as in a record that packs a value
with its type. A numerical carrier counts as holding none, being a value, while an opaque type or an
axiom counts as holding one. This only spares the precise search of `holdsNumericalFunction` the
types, such as `Nat` or a list of them, that hold none. -/
partial def mayHoldFunction (cache : CarrierCache) (name : Name) : MetaM Bool := do
  -- Whether a value of `type` is a type or a family of types, not a proposition.
  let typeField (type : Lean.Expr) : MetaM Bool :=
    forallTelescopeReducing type fun _ sort => do
      let sort ← whnfD sort
      return sort.isSort && !sort.isProp
  -- The constants whose answer `name` inherits, or `none` when it holds a function outright.
  let uses (name : Name) : MetaM (Option (Array Name)) := do
    if carrierTypes.contains name then return some #[]
    let some info := (← getEnv).find? name | return none
    match info with
    | .defnInfo definition =>
        if (definition.value.find? (·.isForall)).isSome then return none
        return some definition.value.getUsedConstants
    | .opaqueInfo _ | .axiomInfo _ =>
        return if ← isTypeFormerType info.type then none else some #[]
    | .inductInfo type =>
        let mut used := #[]
        for ctor in type.ctors do
          let some (.ctorInfo ctor) := (← getEnv).find? ctor | continue
          -- The types of the fields that are not proofs, and whether one of them is a type, as in a
          -- record that packs a value with its type.
          let (fields, packs) ← forallTelescope ctor.type fun arguments _ => do
            let mut fields := #[]
            let mut packs := false
            for field in arguments.extract ctor.numParams arguments.size do
              let fieldType ← inferType field
              if ← isProp fieldType then continue
              fields := fields.push fieldType
              packs := packs || (← typeField fieldType)
            return (fields, packs)
          if packs || fields.any (·.find? (·.isForall) |>.isSome) then return none
          used := used ++ fields.flatMap (·.getUsedConstants)
        return some used
    | _ => return some #[]
  -- The same depth-first search as `carries`, with its rule for constants met on a cycle.
  let rec visit (pending : NameMap Nat) (depth : Nat) (name : Name) :
      MetaM (Bool × Option Nat) := do
    if let some known := (← cache.get)[(name, 2)]? then return (known, none)
    if let some above := pending.find? name then return (false, some above)
    let pending := pending.insert name depth
    let some next ← uses name | do
      cache.modify (·.insert (name, 2) true)
      return (true, none)
    let mut low : Option Nat := none
    for used in next do
      let (found, reached) ← visit pending (depth + 1) used
      if found then
        cache.modify (·.insert (name, 2) true)
        return (true, none)
      low := match low, reached with
        | some low, some reached => some (min low reached)
        | low, reached => low <|> reached
    if low.all (depth ≤ ·) then cache.modify (·.insert (name, 2) false)
    return (false, low.filter (· < depth))
  return (← visit {} 0 name).1

/-- Whether a value of `type` can be a type or a family of types, or hold one: `type` ends in a
sort, or at default transparency it is an inductive type with a field that can, as a record with a
field of type `Type` does. A type nested too deeply to finish counts. -/
partial def holdsType (type : Lean.Expr) : MetaM Bool := do
  let rec visit (seen : Array Lean.Expr) (fuel : Nat) (type : Lean.Expr) : MetaM Bool := do
    if ← isProp type then return false
    -- The result of a function, as of `Unit → TypeBox`, is what it gives.
    forallTelescopeReducing type fun _ result => do
      let type ← whnfD result
      if type.isSort then return true
      if seen.contains type then return false
      let fuel + 1 := fuel | return true
      let .const name levels := type.getAppFn | return false
      let some (.inductInfo info) := (← getEnv).find? name | return false
      for constructor in info.ctors do
        let constructorType := (← getConstInfo constructor).instantiateTypeLevelParams levels
        let constructorType ←
          instantiateForall constructorType (type.getAppArgs.extract 0 info.numParams)
        if ← forallTelescope constructorType fun fields _ =>
            fields.anyM fun field => do visit (seen.push type) fuel (← inferType field) then
          return true
      return false
  visit #[] 8 type

/-- Whether the local variable `id` is a type parameter: it has no visible value, is no dictionary
of a class that a read selecting stored entries trusts (`Read.trusts`), and its type can be or hold
a type (`holdsType`), as `β : Type` or a record that packs a type does. A value of a type it gives
can be a numerical value, or a function, once the statement is specialized, so such a type counts
as numerical (`mentionsCarrier`, `carrierHead`, `holdsNumericalFunction`). A type that a trusted
dictionary gives, such as the buffer of a tensor's storage, belongs to the storage it trusts. -/
def isTypeParameter (id : FVarId) (cache? : Option CarrierCache := none) : MetaM Bool := do
  let key := (id.name, 3)
  if let some cache := cache? then
    if let some known := (← cache.get)[key]? then return known
  let some declaration := (← getLCtx).find? id | return false
  let type ← instantiateMVars declaration.type
  let trusted ← match ← isClass? type with
    | some name => pure ((← extension).reads.any fun read =>
        read.isCertified && read.trusts.contains name)
    | none => pure false
  let parameter ← if declaration.isLet || trusted then pure false else holdsType type
  if let some cache := cache? then cache.modify (·.insert key parameter)
  return parameter

/-- Whether `type` mentions a type parameter (`isTypeParameter`). -/
def mentionsTypeParameter (type : Lean.Expr) (cache? : Option CarrierCache := none) :
    MetaM Bool := do
  unless type.hasFVar do return false
  (collectFVars {} type).fvarIds.anyM (isTypeParameter · cache?)

/-- The head that `type` reaches first among its reducible unfoldings, also through local
definitions (`expandLocal`): one of the `carrierTypes` (`false`), as `ExecFloat.Binary` unfolds to
`ExecFloat`, or a type parameter (`isTypeParameter`) or a field of one (`true`), which can be
specialized to a carrier or to a function type, also behind a definition of any reducibility. -/
private def carrierHead? (type : Lean.Expr) (cache? : Option CarrierCache := none) :
    MetaM (Option Bool) := do
  let mut current ← expandLocal type
  for _ in [0:16] do
    if current.getAppFn.constName?.any carrierTypes.contains then return some false
    match current.getAppFn with
    | .fvar id => if ← isTypeParameter id cache? then return some true
    | .proj _ _ record => if ← mentionsTypeParameter record cache? then return some true
    | _ => pure ()
    let some next ← withReducible (unfoldDefinition? current) | break
    current := next.headBeta
  -- A type parameter behind a definition of any reducibility, as `def Alias (α : Type) := α`, which
  -- it is an argument of. The carriers stay folded, so that a definition that stands for one is
  -- still read as before.
  let some name := current.getAppFn.constName? | return none
  unless (← getEnv).find? name matches some (.defnInfo _) do return none
  unless ← mentionsTypeParameter current cache? do return none
  let folded (config : Meta.Config) (info : ConstantInfo) : CoreM Bool :=
    if carrierTypes.contains info.name then pure false else canUnfoldDefault config info
  match (← withCanUnfoldPred folded (whnfD current)).getAppFn with
  | .fvar id => if ← isTypeParameter id cache? then return some true
  | .proj _ _ record => if ← mentionsTypeParameter record cache? then return some true
  | _ => pure ()
  return none

/-- Whether `type` or one of its reducible unfoldings has one of the `carrierTypes` or a type
parameter at its head (`carrierHead?`). -/
def carrierHead (type : Lean.Expr) (cache? : Option CarrierCache := none) : MetaM Bool :=
  return (← carrierHead? type cache?).isSome

/-- Whether `type` mentions a constant that can hold a numerical value as a type (`carries`): one of
the `carrierTypes`, an alias of one such as `Binary32` whatever its reducibility, or a record with a
field of one, also through the local definitions it uses (`expandLocal`). A metavariable that is
still to be assigned and can be or hold a type (`holdsType`) may turn out to give such a type, and
so may a type parameter (`isTypeParameter`) once the statement is specialized, so they count too. -/
def mentionsCarrier (type : Lean.Expr) (cache? : Option CarrierCache := none) : MetaM Bool := do
  let cache ← match cache? with
    | some cache => pure cache
    | none => IO.mkRef {}
  let type ← expandLocal type
  if type.hasExprMVar then
    if ← (← getMVars type).anyM fun id => do holdsType (← id.getType) then return true
  if ← mentionsTypeParameter type cache then return true
  type.getUsedConstants.anyM (carries cache false)

/-- The classes of the comparisons through which index data may read stored values. -/
def orderClasses : Array Name := #[``LT, ``LE, ``BEq, ``Ord, ``Decidable]

/-- FloatLib's dictionaries of `orderClasses` on its configured executable values. `==` and the
orders and their decisions compare the decoded values exactly, as IEEE 754 does: a NaN is unordered
and unequal to itself, and the two zeros are equal. Its `DecidableEq` decides structural equality of
the stored word instead: the two zeros differ, and a NaN equals itself. -/
def orderDictionaries : Array Name := #[``FloatLib.Floats.execFloatBEq,
  ``FloatLib.Floats.ExecFloat.Binary.instLTFamily, ``FloatLib.Floats.ExecFloat.Binary.instLEFamily,
  ``FloatLib.Floats.ExecFloat.Binary.instDecidableLtFamily,
  ``FloatLib.Floats.ExecFloat.Binary.instDecidableLeFamily,
  ``FloatLib.Floats.ExecFloat.Binary.instDecidableEqFamily]

/-- FloatLib's own comparison of configured executable values, which `execFloatBEq` must take. -/
def comparisonDictionaries : Array Name :=
  #[``FloatLib.Floats.ExecFloat.Binary.instComparisonFamily]

/-- The classes that registered reads selecting stored entries (`Read.isCertified`) trust to store and
fetch entries (`Read.trusts`). -/
def storageClasses : CoreM (Array Name) := do
  return (← extension).reads.foldl (init := #[]) fun classes read =>
    if read.isCertified then classes ++ read.trusts else classes

/-- Whether `type`, at default transparency and with its local definitions expanded, is the type of
a function that takes or returns a numerical value. -/
def numericalFunction (type : Lean.Expr) (cache : CarrierCache) : MetaM Bool := do
  let type ← expandLocal type
  return (← whnfD type).isForall && (← mentionsCarrier type cache)

/-- Whether a value of `type` can hold a numerical function (`numericalFunction`): `type` is one, or
at default transparency a type with a type argument or a field that holds one, such as a list, an
option or a pair of numerical functions, a record with one as a field or a record of such records.
The fields of an inductive type are read at its parameters and at the indices of `type`: matching a
constructor's result against `type` specializes its fields, and a type that the match leaves open,
as when an index is not a constructor or the constructor cannot build `type`, may be a numerical one
(`mentionsCarrier`), so a function on it counts, and so does a value of a type that a constructor
leaves open, which can be a function. A function that takes a type, such as `(β : Type) → β → Nat`,
counts too, since it can be applied at a numerical type, and so does a value of a type parameter
(`isTypeParameter`), which can be specialized to a numerical function type. A numerical value holds
none, and neither does a proof; a type nested too deeply to finish counts as holding one. -/
partial def holdsNumericalFunction (type : Lean.Expr) (cache : CarrierCache) : MetaM Bool := do
  let rec visit (seen : Array Lean.Expr) (fuel : Nat) (type : Lean.Expr) : MetaM Bool := do
    let type ← expandLocal type
    if ← isProp type then return false
    -- Most types, such as `Nat` or a list of them, can hold no function at all.
    unless type.hasExprMVar || (type.find? fun term => term.isForall ||
          (term.isSort && !term.isProp)).isSome ||
        (← type.getUsedConstants.anyM (mayHoldFunction cache)) ||
        (← mentionsTypeParameter type cache) do
      return false
    -- A type parameter can be specialized to a numerical function type, also behind an alias; a
    -- numerical value holds none.
    if let some parameter ← carrierHead? type cache then return parameter
    let type ← whnfD type
    if type.isForall then
      if ← mentionsCarrier type cache then return true
      -- A function that takes a type, such as `(β : Type) → β → Nat`, can be applied at a
      -- numerical one; a proposition cannot be one. A function that gives a value that holds a
      -- numerical function holds one too.
      return ← forallTelescopeReducing type fun binders result => do
        for binder in binders do
          if ← forallTelescopeReducing (← inferType binder) fun _ sort => do
              let sort ← whnfD sort
              return sort.isSort && !sort.isProp then
            return true
        visit seen fuel result
    -- A type that a constructor leaves open, such as the type that a dependent record packs with
    -- a value of it, can be a numerical function.
    if let .mvar id := type.getAppFn then
      return ← forallTelescopeReducing (← id.getType) fun _ sort => do
        let sort ← whnfD sort
        return sort.isSort && !sort.isProp
    if seen.contains type then return false
    let fuel + 1 := fuel | return true
    let seen := seen.push type
    -- A type argument, or a family of types such as the second component of a dependent pair.
    for argument in type.getAppArgs do
      let family ← forallTelescopeReducing (← inferType argument) fun binders sort => do
        if (← whnfD sort).isSort then
          return some (← visit seen fuel (mkAppN argument binders).headBeta)
        return none
      if family == some true then return true
    let .const name levels := type.getAppFn | return false
    let some (.inductInfo info) := (← getEnv).find? name | return false
    let parameters := type.getAppArgs.extract 0 info.numParams
    for constructor in info.ctors do
      let constructorType := (← getConstInfo constructor).instantiateTypeLevelParams levels
      let constructorType ← instantiateForall constructorType parameters
      let holds ← withNewMCtxDepth do
        let (fields, _, result) ← forallMetaTelescope constructorType
        discard <| isDefEq result type
        fields.anyM fun field => do visit seen fuel (← instantiateMVars (← inferType field))
      if holds then return true
    return false
  visit #[] 16 type

/-- Whether a hypothesis states the error of the variable `id` against a reference, as the
analysis states it for the accumulator of a loop: `id` then stands for a computed value. -/
def estimated (id : FVarId) : MetaM Bool := do
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let type ← instantiateMVars declaration.type
    let found := type.find? fun term =>
      (term.isAppOfArity ``MixedError 4 && mentions (term.getArg! 0) (· == id)) ||
        (term.isAppOfArity ``LE.le 4 && (term.getArg! 2).isAppOf ``abs &&
          (term.getArg! 2).appArg!.isAppOfArity ``HSub.hSub 6 &&
          mentions ((term.getArg! 2).appArg!.getArg! 4) (· == id))
    if found.isSome then return true
  return false

/-- Whether `argument` is index data, such as a length, start, step, offset or shape that an index
producer reads, an index at which a stored input is read, the integer of an exact cast or a discrete
value that a loop's reference keeps. It may read stored values only to compare, select or store
them, never to compute with them. Proofs, data types, the propositions of `exact` and their
decisions are index data. A dictionary whose type mentions a numerical carrier (`mentionsCarrier`)
must be one of the `orderDictionaries`, `execFloatBEq` only over one of the
`comparisonDictionaries`, a dictionary of a registered read (`Read.dictionaries`) or of one of the
`storageClasses`, or be built by a constant that holds no number, such as `instDecidableEqBool`, and
then pass through its arguments. A variable whose type mentions a carrier must be stored, not one
whose error a hypothesis bounds (`estimated`); a numerical function (`numericalFunction`) takes only
index data whose types hold no number, and fully, however it is produced: a variable, a projection
or a field applied to arguments, or the value of any other constant at the arguments its type names,
such as an entry that a getter reads, applied to the arguments after those; a definition that takes
a value that can hold one (`holdsNumericalFunction`), such as a list of numerical functions or a
record with one, is read through its value and checked use by use, failing closed when that does not
finish, while a function written as `fun` is checked through its body and counts as such a value
only when its result can hold one; a value of a numerical type (`carrierHead`) may pass only to a
parameter whose type is a type variable, which can compare, select or store it, or hand it to the
functions and dictionaries it takes, but not look into it, and no projection may look into it
either. No constant the argument uses may hold a numerical value as a term (`carries`), so a
definition it calls is read through its value and an opaque constant or an axiom outside Lean's core
library is rejected, and each `let`-bound local definition it uses must have index data as its
value, while a variable without a visible value, such as one that a `have` in a tactic proof
introduces, is an input as Lean states it, and a value of a type parameter of the statement
(`isTypeParameter`) counts as numerical, since the statement can be specialized to a numerical type.
The length of a stored list or array, or of a map of one, is index data. A number
computed from a decoded or rounded value, such as the numerator of `toRat? (x * x)` or the number of
indices below `x * x`, is not index data, also when a helper `Nat → Nat` computes it, while
literals, parameters, fields of inputs, arithmetic on them and the position of the largest of stored
values are. -/
partial def indexClosed (argument : Lean.Expr) (exact : Array Lean.Expr := #[])
    (cache? : Option CarrierCache := none) : MetaM Bool := do
  let cache ← match cache? with
    | some cache => pure cache
    | none => IO.mkRef {}
  let closed ← IO.mkRef true
  -- The decisions of the propositions of `exact` met so far.
  let decisions ← IO.mkRef (#[] : Array Lean.Expr)
  let storage ← storageClasses
  let reads := (← extension).reads
  -- The definitions unfolded to see how they use a value that can hold a numerical function.
  let unfolded ← IO.mkRef (0 : Nat)
  -- Whether the dictionary `term` of the class `name` only compares, selects or stores values.
  let trusted (name : Name) (term : Lean.Expr) : MetaM Bool :=
    lambdaTelescope term.headBeta fun _ body => do
      let head := body.consumeMData.headBeta
      if orderClasses.contains name &&
          head.getAppFn.constName?.any orderDictionaries.contains then
        -- `execFloatBEq` compares through the comparison it takes, which must be FloatLib's own.
        return ← head.getAppArgs.allM fun argument => do
          unless (← isClass? (← inferType argument)) ==
              some ``FloatLib.Floats.ExecFloat.Comparison do
            return true
          return argument.getAppFn.constName?.any comparisonDictionaries.contains
      if reads.any fun read => read.isCertified && read.selectsThrough head then return true
      return storage.contains name
  -- Whether `term`, an argument, can hold a numerical function whose uses are not written out
  -- (`holdsNumericalFunction`), as a variable's are not, whether it is one or a container or a
  -- record of them. A function written as `fun` is checked through its body, so it counts only when
  -- its result can hold one, and a dictionary is checked as a dictionary.
  let functionArgument (term : Lean.Expr) : MetaM Bool := do
    let type ← inferType term
    if (← isClass? type).isSome then return false
    if term.consumeMData.isLambda then
      return ← lambdaTelescope term fun _ body => do
        holdsNumericalFunction (← inferType body) cache
    holdsNumericalFunction type cache
  -- How the application `term` applies a function that its head produces: the position of the
  -- first argument that function takes, whether it may be applied, and whether the arguments before
  -- that position are checked here. A variable produces itself and must be stored, a projection or
  -- a structure's field reads a record that must be index data, and any other constant produces its
  -- value at the arguments its type names, as a getter reads a function from a container; those
  -- arguments are checked below like any other.
  let applied (term : Lean.Expr) : MetaM (Option (Nat × Bool × Bool)) := do
    let arguments := term.getAppArgs
    match term.getAppFn.consumeMData with
    | .fvar id => return some (0, (← id.getDecl).value?.isNone && !(← estimated id), true)
    | .proj _ _ record => return some (0, ← indexClosed record exact cache, true)
    | .const name _ =>
        if let some field ← getProjectionFnInfo? name then
          unless field.fromClass do
            if arguments.size ≤ field.numParams + 1 then return none
            return some (field.numParams + 1,
              ← indexClosed arguments[field.numParams]! exact cache, true)
        let arity := (← getConstInfo name).type.getForallArity
        return if arguments.size ≤ arity then none else some (arity, true, false)
    | _ => return none
  discard <| Meta.transform argument (pre := fun term => do
    unless ← closed.get do return .done term
    if exact.contains term || (← decisions.get).contains term then return .done term
    -- A function applied where it is written, as after unfolding a definition, is its body.
    if term.isHeadBetaTarget then return .visit term.headBeta
    let decide := term.isAppOfArity ``Decidable.decide 2
    if term.isAppOfArity ``ite 5 || term.isAppOfArity ``dite 5 || decide then
      let offset := if decide then 0 else 1
      if exact.contains term.getAppArgs[offset]! then
        decisions.modify (·.push term.getAppArgs[offset + 1]!)
    if term.isAppOfArity ``List.length 2 || term.isAppOfArity ``Array.size 2 then
      -- A map keeps the length of its container.
      let mut container := term.appArg!
      while container.isAppOfArity ``List.map 4 || container.isAppOfArity ``Array.map 4 do
        container := container.appArg!
      if ← isInputValue container then return .done term
    let type ← inferType term
    if ← isProp type then return .done term
    let sort ← whnfR type
    if sort.isSort && !sort.isProp then return .done term
    let numerical ← mentionsCarrier type cache
    if numerical then
      if let some name ← isClass? type then
        if ← trusted name term then return .done term
        -- A dictionary that a constant without numbers builds, such as `instDecidableEqBool`, is
        -- checked through its arguments.
        let plain ← match term.headBeta.getAppFn.constName? with
          | some head => do pure !(← carries cache true head)
          | none => pure false
        unless plain do
          closed.set false
          return .done term
    -- A numerical function, whatever produces it, is only the head of a full application to index
    -- data of carrier-free types, or the argument of a definition read through its value below;
    -- one written as `fun` is checked through its body. The arguments from the position that
    -- `applied` names on are such arguments as soon as a prefix of the application that ends at
    -- one of them is a numerical function.
    if let some (start, stored, checked) ← applied term then
      let head := term.getAppFn
      let arguments := term.getAppArgs
      let numerical ← (List.range' start (arguments.size - start)).anyM fun position => do
        numericalFunction (← inferType (mkAppN head (arguments.extract 0 position))) cache
      if numerical then
        let full := !(← whnfD type).isForall
        let indices ← (arguments.extract start arguments.size).allM fun argument => do
          return !(← mentionsCarrier (← inferType argument) cache) &&
            (← indexClosed argument exact cache)
        unless full && stored && indices do
          closed.set false
          return .done term
        if checked then return .done term
    if !term.consumeMData.isLambda && (← numericalFunction type cache) &&
        (← isClass? type).isNone then
      closed.set false
      return .done term
    if let .const name _ := term then
      if ← carries cache true name then closed.set false
      return .done term
    if let .fvar id := term then
      match (← id.getDecl).value? with
      | some value =>
          unless ← indexClosed value exact cache do closed.set false
          return .done term
      | none =>
          if numerical && (← estimated id) then closed.set false
          return .done term
    -- No projection looks into a numerical value, such as the stored bits of a float.
    let record? ← match term with
      | .proj _ _ record => pure (some record)
      | _ => do
          let some name := term.getAppFn.constName? | pure none
          let some field ← getProjectionFnInfo? name | pure none
          pure (if field.fromClass || term.getAppNumArgs != field.numParams + 1 then none
            else some term.appArg!)
    if let some record := record? then
      if ← carrierHead (← inferType record) cache then
        closed.set false
        return .done term
    if !numerical && (← isInputValue term) then return .done term
    -- A definition that takes a numerical function is read through its value, so that each use
    -- of the function is checked.
    if let .const _ _ := term.getAppFn then
      if ← term.getAppArgs.anyM functionArgument then
        if (← unfolded.get) < 64 then
          if let some next ← unfoldDefinition? term then
            unfolded.modify (· + 1)
            return .visit next.headBeta
        closed.set false
        return .done term
    -- A numerical value passes only to a parameter whose type is a type variable.
    if let .const _ _ := term.getAppFn then
      let arguments := term.getAppArgs
      let opened ← arguments.mapM fun argument => do carrierHead (← inferType argument) cache
      if opened.any id then
        let parametric ← forallBoundedTelescope (← inferType term.getAppFn) arguments.size
          fun binders _ => do
            for index in [0:arguments.size] do
              unless opened[index]! do continue
              let some binder := binders[index]? | return false
              let domain ← inferType binder
              unless domain.isFVar && binders.contains domain do return false
            return true
        unless parametric do
          closed.set false
          return .done term
    return .continue)
  closed.get

/-- Whether the entries of `input`, a container that `loop` traverses, have the provenance that
lets an entry be exact data: they are stored inputs or indices. `input` is an input
(`isInputValue`); a traversal of the loop's coordinates or an index computation (`List.range`,
`List.range'`, `List.finRange` and their array and vector forms) whose arguments are index data
(`indexClosed`); or it lists, pairs or numbers the entries of such containers (`Vector.toList`,
`List.zip`, `List.zipIdx` and their array and vector forms) with any number it takes, such as an
offset, index data too. The type of an entry says nothing about where it comes from: a pair of
integers can encode a rounded value, and so can a range whose start is computed from one. -/
partial def storedEntries (loop : Loop) (input : Lean.Expr) (cache? : Option CarrierCache := none) :
    MetaM Bool := do
  let input := input.consumeMData
  if ← isInputValue input then return true
  let some head := input.getAppFn.constName? | return false
  let info ← getFunInfoNArgs input.getAppFn input.getAppNumArgs
  let explicit := (input.getAppArgs.zip info.paramInfo).filterMap fun (argument, parameter) =>
    if parameter.binderInfo.isExplicit then some argument else none
  if loop.coordinates.any (·.1 == head) || #[``List.range, ``List.range', ``List.finRange,
      ``Array.range, ``Array.range', ``Array.finRange, ``Vector.range, ``Vector.finRange].contains
      head then
    return ← explicit.allM (indexClosed · (cache? := cache?))
  unless #[``Array.toList, ``Vector.toList, ``Vector.toArray, ``List.zip, ``Array.zip,
      ``Vector.zip, ``List.zipIdx, ``Array.zipIdx, ``Vector.zipIdx].contains head do
    return false
  -- The containers it reads must have that provenance too, and a number it takes is index data.
  explicit.allM fun argument => do
    let type ← whnfR (← inferType argument)
    if type.isConstOf ``Nat || type.isConstOf ``Int then indexClosed argument (cache? := cache?)
    else storedEntries loop argument cache?

/-- Whether every container observation in `expression` is a coordinate read of a stored input by a
read selecting stored entries (`Read.isCertified`), which the coordinate laws leave as it is. -/
def hasOnlyInputReads (expression : Lean.Expr) : MetaM Bool := do
  let withoutInputs ← Meta.transform expression (pre := fun term => do
    if let some position ← readPosition? term (certified := true) then
      if ← isInputValue term.getAppArgs[position]! then return .done (mkConst ``Unit.unit)
    return .continue)
  return !(← hasObservation withoutInputs)


/-- The natural number or integer that `actual` casts to the reals, when `actual` is such a cast. -/
def castInteger? (actual : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let head := actual.getAppFn.constName?.getD .anonymous
  unless #[``Nat.cast, ``NatCast.natCast, ``Int.cast, ``IntCast.intCast].contains head do
    return none
  let some argument := actual.getAppArgs.back? | return none
  let type ← whnfR (← inferType argument)
  return if type.isConstOf ``Nat || type.isConstOf ``Int then some argument else none

/-- Exact discrete data uses the complete canonical real cast, including its dictionary, of index
data (`indexClosed`) or of a stored rational. Computed rational expressions instead follow their
registered algebra and observation laws, and an integer computed from numerical values, such as the
numerator of a rounded value, is not data. -/
def exactRealData? (actual : Q(ℝ)) (cache? : Option CarrierCache := none) : MetaM Bool := do
  let actual : Q(ℝ) ← instantiateMVars actual
  if actual.hasExprMVar then return false
  let head := actual.getAppFn.constName?.getD .anonymous
  let some argument := actual.getAppArgs.back? | return false
  if head == ``Nat.cast || head == ``NatCast.natCast then
    unless ← withReducible (isDefEq (← inferType argument) q(Nat)) do return false
    unless ← indexClosed argument (cache? := cache?) do return false
    let value : Q(Nat) := argument
    return ← withNewMCtxDepth <| withReducible <| isDefEq actual q(($value : ℝ))
  if head == ``Int.cast || head == ``IntCast.intCast then
    unless ← withReducible (isDefEq (← inferType argument) q(Int)) do return false
    unless ← indexClosed argument (cache? := cache?) do return false
    let value : Q(Int) := argument
    return ← withNewMCtxDepth <| withReducible <| isDefEq actual q(($value : ℝ))
  if head == ``Rat.cast || head == ``RatCast.ratCast then
    unless ← withReducible (isDefEq (← inferType argument) q(Rat)) do return false
    unless ← isInputValue argument do return false
    let value : Q(Rat) := argument
    return ← withNewMCtxDepth <| withReducible <| isDefEq actual q(($value : ℝ))
  return false

/-- Only canonical mathematical real literals are exact data. Constructed floating-point
literals retain their conversion through the selected codec and its numerical law. -/
def literalInput? (actual : Q(ℝ)) (source : Lean.Expr) : MetaM Bool := do
  let source ← instantiateMVars source
  if source.hasExprMVar then return false
  unless ← withReducible (isDefEq (← inferType source) q(ℝ)) do return false
  let head := source.getAppFn.constName?.getD .anonymous
  unless literalHeads.contains head do return false
  if head == ``Real.pi then return actual == source
  let arguments := source.getAppArgs
  let expected? : Option Lean.Expr ←
    if head == ``OfNat.ofNat && arguments.size == 3 then do
      let value : Q(Nat) := arguments[1]!
      let some literal := value.consumeMData.rawNatLit? | return false
      let real : Q(ℝ) := if literal == 0 then q((0 : ℝ))
        else if literal == 1 then q((1 : ℝ)) else q(($value : ℝ))
      pure (some real)
    else if head == ``OfScientific.ofScientific && arguments.size == 5 then do
      let mantissa : Q(Nat) := arguments[2]!
      let negative : Q(Bool) := arguments[3]!
      let exponent : Q(Nat) := arguments[4]!
      unless mantissa.consumeMData.rawNatLit?.isSome &&
          exponent.consumeMData.rawNatLit?.isSome &&
          (negative.isConstOf ``Bool.true || negative.isConstOf ``Bool.false) do return false
      pure (some q((OfScientific.ofScientific $mantissa $negative $exponent : ℝ)))
    else pure none
  let some expected := expected? | return false
  return ← withNewMCtxDepth <| withReducibleAndInstances <| isDefEq source expected

/-- Read a real absolute-error proposition without changing its arithmetic dictionaries. -/
def errorConclusion? (type : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  unless ← isProp type do return none
  let type : Q(Prop) ← pure type
  match type with
  | ~q(|($actual : ℝ) - $reference| ≤ $error) =>
      unless ← isDefEq (← inferType actual) q(ℝ) do return none
      unless ← isDefEq type q(|$actual - $reference| ≤ $error) do return none
      return some (actual, reference, error)
  | _ => return none

/-- Read a mixed-error proposition, returning its actual value, reference and both parts. -/
def mixedConclusion? (type : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let type ← instantiateMVars type
  unless type.isAppOfArity ``MixedError 4 do return none
  let arguments := type.getAppArgs
  return some (arguments[0]!, arguments[1]!, arguments[2]!, arguments[3]!)

/-- Read an absolute or mixed bound as its actual value, reference and `Bound`. -/
def boundConclusion? (type : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr × Bound)) := do
  if let some (actual, reference, error) ← errorConclusion? type then
    return some (actual, reference, .absolute error)
  if let some (actual, reference, relative, absolute) ← mixedConclusion? type then
    return some (actual, reference, .mixed relative absolute)
  return none

/-- Extract the observation and its proposition context without reducing scalar arithmetic. -/
def numericalConclusion? (type : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr × Bool)) := do
  let type : Q(Prop) ← pure type
  if let some (scalar, actual, reference) := type.eq? then
    unless ← isDefEq scalar q(ℝ) do return none
    let reference : Q(ℝ) ← instantiateMVars reference
    return some (← instantiateMVars actual, q(fun value : ℝ => value = $reference), true)
  let some (actual, reference, bound) ← boundConclusion? type | return none
  let reference : Q(ℝ) ← pure reference
  return some (actual, ← withLocalDeclD `value q(ℝ) fun value =>
    mkLambdaFVars #[value] (bound.statement value reference), false)

/-- Abstract the theorem parameters left after specializing its local rounding premise. -/
partial def closeRuleArguments (arguments : Array Lean.Expr) (binders : Array BinderInfo)
    (index : Nat) (opened : Array Lean.Expr) (proof : Lean.Expr) : MetaM Lean.Expr := do
  if index == arguments.size then
    return ← mkLambdaFVars opened (← instantiateMVars proof)
  let argument ← instantiateMVars arguments[index]!
  unless argument.isMVar do
    return ← closeRuleArguments arguments binders (index + 1) opened proof
  let goal := argument.mvarId!
  let declaration ← goal.getDecl
  let type ← instantiateMVars declaration.type
  withLocalDecl declaration.userName binders[index]! type fun value => do
    goal.assign value
    closeRuleArguments arguments binders (index + 1) (opened.push value) proof

/-- A scalar error transformer also describes an exact real operation. Discharge its local
rounding premise with reflexivity, retaining its input-error and domain premises. -/
def specializeLocalError (rule : Lean.Expr) : MetaM Lean.Expr := do
  let (arguments, binders, conclusion) ← forallMetaTelescopeReducing (← ruleType rule)
  let some (actual, _, _) ← errorConclusion? conclusion | return rule
  unless actual.isMVar do return rule
  for argument in arguments do
    let type ← instantiateMVars (← inferType argument)
    let some (value, middle, _) ← errorConclusion? type | continue
    unless value == actual do continue
    let saved ← saveState
    let exactProof ← mkAppM ``exact_error #[middle]
    unless ← isDefEq type (← inferType exactProof) do
      saved.restore
      continue
    argument.mvarId!.assign exactProof
    return ← closeRuleArguments arguments binders 0 #[] (mkAppN rule arguments)
  return rule

/-- Normalize a rule's container reads by an equality proof, retaining its original premises,
reference and budget. Rigid parameters prevent simplification from choosing theorem arguments. -/
def normalizeRule (session : Session) (rule : Lean.Expr) : MetaM Lean.Expr := do
  forallTelescopeReducing (← ruleType rule) fun arguments conclusion => do
    let some (actual, proposition, _) ← numericalConclusion? conclusion | return rule
    unless ← hasObservation actual do return rule
    let (context, procedures) ← coordinateSimpContext session
    let (normalized, _) ← simp actual context procedures
    if normalized.expr == actual then return rule
    let equality ← mkAppM ``congrArg #[proposition, ← normalized.getProof' actual]
    let proof ← mkAppM ``Eq.mp #[equality, mkAppN rule arguments]
    mkLambdaFVars arguments proof

/-- Index complete computation patterns. The tree ignores instance arguments; applying a
candidate still checks its complete statement, including every selected dictionary. -/
partial def numericalPattern (expression : Lean.Expr) (root : Bool := true) :
    MetaM Lean.Expr := do
  let expression ← DiscrTree.reduceDT expression root
  let mut function := expression.getAppFn
  if let .proj name index source := function then
    let source ← if isClass (← getEnv) name then pure (DiscrTree.mkNoindexAnnotation source)
      else numericalPattern source false
    function := .proj name index source
  let arguments := expression.getAppArgs
  let info ← getFunInfoNArgs function arguments.size
  let mut prepared := #[]
  for h : index in [:arguments.size] do
    let argument := arguments[index]
    let ignore := info.paramInfo[index]?.any fun parameter =>
      parameter.isInstance || parameter.isImplicit || parameter.isStrictImplicit
    let argument ← if ignore || (← isType argument) || (← isProof argument) then
        pure (DiscrTree.mkNoindexAnnotation argument)
      else numericalPattern argument false
    prepared := prepared.push argument
  return mkAppN function prepared

/-- `value` as the pair `(value.1, ())` when its type is a pair with a unit second component, such
as the coordinate of a vector, and a pair `(i, u)` of that type as `(i, ())`; `none` when `value`
has another type or is such a pair `(i, ())` already. -/
def unitPair? (value : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let type ← whnf (← inferType value)
  unless type.isAppOfArity ``Prod 2 do return none
  let .const name [level] ← whnf type.appArg! | return none
  unless name == ``PUnit do return none
  let unit := mkConst ``PUnit.unit [level]
  if value.isAppOfArity ``Prod.mk 4 then
    if value.appArg!.isConstOf ``PUnit.unit then return none
    return some (mkApp value.appFn! unit)
  let first ← mkAppM ``Prod.fst #[value]
  return some (← mkAppM ``Prod.mk #[first, unit])

/-- The local variable `id` as `unitPair?` writes it, and as itself otherwise. Each variable's form
is computed once (`Session.unitPairs`). -/
def Session.unitPair (session : Session) (id : FVarId) : MetaM Lean.Expr := do
  if let some pair := (← session.unitPairs.get).get? id then return pair.getD (.fvar id)
  let pair? ← unitPair? (.fvar id)
  session.unitPairs.modify (·.insert id pair?)
  return pair?.getD (.fvar id)

/-- Whether `value` is a pair or projects a component out of one, such as the coordinate `c.2` of
a matrix row. -/
def isPairCoordinate (value : Lean.Expr) : Bool :=
  match value with
  | .proj ``Prod .. => true
  | _ => value.isAppOfArity ``Prod.fst 3 || value.isAppOfArity ``Prod.snd 3 ||
      value.isAppOfArity ``Prod.mk 4

/-- The form under which the rules for `term` are looked up: `term` with the coordinate that ends
its chain of last arguments, such as the coordinate `c` of a read `toReal (get t c)`, written by
`Session.unitPair` when it is a local variable and by `unitPair?` when it is a pair or projects a
component out of one. The forms are definitionally equal, but a rule stated at a coordinate
`(i, ())` is indexed under that pair. -/
partial def Session.indexKey (session : Session) (term : Lean.Expr) :
    MetaM Lean.Expr := do
  let arguments := term.getAppArgs
  let some last := arguments.back? | return term
  let pair? ← if isPairCoordinate last then unitPair? last else pure none
  let next ← match last, pair? with
    | _, some pair => pure pair
    | .fvar id, none => session.unitPair id
    | .app .., none => session.indexKey last
    | _, none => pure last
  if next == last then return term
  return mkAppN term.getAppFn (arguments.set! (arguments.size - 1) next)

/-- The rules of `tree` for `term`: those indexed under its lookup form `key`
(`Session.indexKey`), then, when the two differ, those indexed under `term` as written. -/
def rulesFor (tree : DiscrTree Rule) (term key : Lean.Expr) : MetaM (Array Rule) := do
  let found ← tree.getMatch key
  if key == term then return found
  let written ← tree.getMatch term
  return found ++ written.filter fun rule => !found.any (·.name == rule.name)

/-- A scalar observation has one explicit data input. Implicit data must be parameters of
that input's type, rather than captured container values or additional scalar operands.
Instance arguments remain intact and are checked when a numerical theorem is applied. -/
def isScalarObservation (containerFree : IO.Ref NameSet) (expression : Lean.Expr) :
    MetaM Bool := do
  let head := expression.getAppFn.constName?.getD .anonymous
  if #[``Nat.cast, ``NatCast.natCast, ``Int.cast, ``IntCast.intCast].contains head then return false
  -- Exact rational reductions use their canonical real observation. A different selected
  -- RatCast dictionary must expose its computation instead of becoming a decoder.
  if head == ``Rat.cast || head == ``RatCast.ratCast then
    let some argument := expression.getAppArgs.back? | return false
    unless ← withReducible (isDefEq (← inferType argument) q(Rat)) do return false
    let value : Q(Rat) := argument
    return ← withNewMCtxDepth <| withReducible <| isDefEq expression q(($value : ℝ))
  let arguments := expression.getAppArgs
  let some input := arguments.back? | return false
  let info ← getFunInfoNArgs expression.getAppFn arguments.size
  let mut functionType ← inferType expression.getAppFn
  let mut inputTypes := #[← instantiateMVars (← inferType input)]
  let mut implicitData := #[]
  let mut dataInputs := 0
  let mut finalInput := false
  for h : index in [:arguments.size] do
    let some parameter := info.paramInfo[index]? | return false
    let argument := arguments[index]
    let .forallE _ domain body _ ← withReducible (whnf functionType) | return false
    functionType := body.instantiate1 argument
    if index + 1 == arguments.size then
      inputTypes := inputTypes.push (← instantiateMVars domain)
    if parameter.isInstance then continue
    if (← isType argument) || (← isProof argument) then continue
    if parameter.isImplicit || parameter.isStrictImplicit then
      implicitData := implicitData.push (← instantiateMVars argument)
      continue
    dataInputs := dataInputs + 1
    finalInput := index + 1 == arguments.size
  if dataInputs != 1 || !finalInput then return false
  if ← hasContainer containerFree inputTypes[0]! then return false
  -- Retain the original types: reducing a carrier to its storage type can erase the
  -- descriptor and storage-plan parameters that its observation still needs.
  for type in inputTypes do
    inputTypes := inputTypes.push (← withReducible (whnf type))
  for argument in implicitData do
    if ← hasContainer containerFree (← inferType argument) then return false
    unless inputTypes.any (fun type =>
        (type.find? fun term => term.consumeMData == argument.consumeMData).isSome) do
      return false
  return !(← withReducible (whnf (← inferType input))).isConstOf ``Real

/-- An arithmetic observation law reads smaller operands with the same observer in its
real reference. An echo bound, or a reference that reuses the complete computation, does not
identify a decoder. The complete numerical theorem remains available in every case. -/
def referenceObservesOperands (containerFree : IO.Ref NameSet) (actual reference : Lean.Expr) :
    MetaM Bool := do
  unless ← isScalarObservation containerFree actual do return false
  let some name := actual.getAppFn.constName? | return false
  let some input := actual.getAppArgs.back? | return false
  let input := input.consumeMData
  let found ← IO.mkRef false
  reference.forEach' fun term => do
    if ← found.get then return false
    let term := term.consumeMData
    if term.getAppFn.constName? != some name ||
        term.getAppNumArgs != actual.getAppNumArgs || term.hasLooseBVars then return true
    let some operand := term.getAppArgs.back? | return true
    let operand := operand.consumeMData
    if operand == input ||
        (input.find? fun child => child.consumeMData == operand).isNone then return true
    let matched ← isScalarObservation containerFree term
    found.set matched
    return !matched
  return ← found.get

/-- Dispatch proof search by rigid proposition heads. Unknown and conjunctive conclusions
remain candidates; applying the proof still checks all arguments and selected instances. -/
def conditionHead (type : Expr) (classifiers : Bool := false) : Option Name :=
  let conclusion := type.getForallBody.consumeMData
  if conclusion.isAppOf ``And || conclusion.isAppOf ``Iff || conclusion.isConstOf ``False then
    none
  else if classifiers && conclusion.isAppOfArity ``Eq 3 then
    if conclusion.getAppArgs[0]!.isConstOf ``Bool then
      conclusion.getAppArgs[1]!.getAppFn.constName?
    else none
  else conclusion.getAppFn.constName?

/-- Index the registered numerical rules by their computation patterns. Type arguments are
wildcards even when a format is reconstructed from its widths; a retrieved theorem must still
unify with the original, fully typed computation. -/
def Session.index (session : Session) (mixed : Bool := false) : TacticM Session := do
  let environment ← getEnv
  let exactOperations ← exactOperations
  let mut entries : DiscrTree Rule := {}
  let mut mixedEntries : DiscrTree Rule := {}
  let mut finiteness : DiscrTree Rule := {}
  let mut orders : Array Rule := #[]
  let mut observations : NameSet := {}
  let mut refutations : Array Name := #[]
  -- Index a mixed, exact or finiteness rule by the computation `observed` reads from its
  -- conclusion: the left side of an equality, or the value a bound concerns.
  let insert (tree : DiscrTree Rule) (name : Name) (exact : Bool) (order : Nat)
      (observed : Lean.Expr → Lean.Expr) : MetaM (DiscrTree Rule) := withNewMCtxDepth do
    let rule ← mkConstWithFreshMVarLevels name
    let prepared ← abstractMVars rule
    let (_, _, conclusion) ← forallMetaTelescopeReducing (← ruleType rule)
    let pattern ← withReducible <| withCanUnfoldPred (programCanUnfold session.boundaries false)
      (numericalPattern (observed conclusion))
    withCanUnfoldPred (fun _ _ => pure false)
      (tree.insertIfSpecific pattern { name, exact, prepared, order })
  -- Order facts read containers like the analyzed program, so their reads are normalized once.
  -- `project` selects a part of the conclusion first.
  let normalizeFact (name : Name) (project : Option Name := none) :
      MetaM AbstractMVarsResult := withNewMCtxDepth do
    let fact ← mkConstWithFreshMVarLevels name
    let normalized ← forallTelescopeReducing (← ruleType fact) fun arguments conclusion => do
      let proof ← match project with
        | some part => mkAppM part #[mkAppN fact arguments]
        | none => pure (mkAppN fact arguments)
      let conclusion ← inferType proof
      let (context, procedures) ← coordinateSimpContext session
      let (result, _) ← simp conclusion context procedures
      mkLambdaFVars arguments (← mkAppM ``Eq.mp #[← result.getProof' conclusion, proof])
    abstractMVars normalized
  -- A fact about a sum or a fold is also stated in the traversal form of the analysis, which
  -- premises about computed values can take. `none` when it has no other form.
  let traversalFact (prepared : AbstractMVarsResult) : MetaM (Option AbstractMVarsResult) :=
    withNewMCtxDepth do
      let (_, _, fact) ← openAbstractMVarsResult prepared
      let traversed ← forallTelescopeReducing (← ruleType fact) fun arguments conclusion => do
        let (context, procedures) ← foldSimpContext session
        let (result, _) ← simp conclusion context procedures
        if result.expr == conclusion then return none
        some <$> mkLambdaFVars arguments
          (← mkAppM ``Eq.mp #[← result.getProof' conclusion, mkAppN fact arguments])
      traversed.mapM abstractMVars
  -- Index a prepared rule by the computation `observed` reads from its conclusion.
  let insertPrepared (tree : DiscrTree Rule) (name : Name) (prepared : AbstractMVarsResult)
      (order : Nat) (observed : Lean.Expr → Lean.Expr) : MetaM (DiscrTree Rule) :=
    withNewMCtxDepth do
      let (_, _, rule) ← openAbstractMVarsResult prepared
      let (_, _, conclusion) ← forallMetaTelescopeReducing (← ruleType rule)
      let pattern ← withReducible <|
        withCanUnfoldPred (programCanUnfold session.boundaries false)
          (numericalPattern (observed conclusion))
      withCanUnfoldPred (fun _ _ => pure false)
        (tree.insertIfSpecific pattern { name, exact := false, prepared, order })
  if mixed then
    for h : index in [:exactOperations.size] do
      if environment.contains exactOperations[index] then
        mixedEntries ← insert mixedEntries exactOperations[index] true index (·.appFn!.appArg!)
  let rules := roundoffRules.getState environment
  for h : index in [:rules.size] do
    let name := rules[index]
    let some info := environment.find? name | continue
    if isRefutation info.type then refutations := refutations.push name
    match ruleKind info.type with
    | .mixed =>
        if mixed then
          -- Its container reads are normalized like the analyzed program's.
          let prepared? ← try
              some <$> withNewMCtxDepth (do
                abstractMVars (← normalizeRule session (← mkConstWithFreshMVarLevels name)))
            catch error => do
              trace[roundoff] "rule {name} not indexed: {error.toMessageData}"
              pure none
          if let some prepared := prepared? then
            mixedEntries ← insertPrepared mixedEntries name prepared (exactOperations.size + index)
              (·.getAppArgs[0]!)
        continue
    | .finiteness =>
        if mixed then
          -- A rule about a container read is normalized like the analyzed program.
          if ← hasObservation info.type.getForallBody then
            let prepared? ← try some <$> normalizeFact name catch error => do
              trace[roundoff] "finiteness rule {name} not indexed: {error.toMessageData}"
              pure none
            if let some prepared := prepared? then
              finiteness ← insertPrepared finiteness name prepared index (·.appFn!.appArg!)
          else finiteness ← insert finiteness name false index (·.appFn!.appArg!)
        continue
    | .order =>
        if mixed then
          let prepared? ← try some <$> normalizeFact name catch error => do
            trace[roundoff] "order fact {name} not indexed: {error.toMessageData}"
            pure none
          if let some prepared := prepared? then
            orders := orders.push { name, exact := false, prepared, order := index }
            if let some traversed ← traversalFact prepared then
              orders := orders.push { name, exact := false, prepared := traversed, order := index }
        continue
    | .numerical => pure ()
    -- A generated statement concludes the finiteness of its output and its mixed bound. Both
    -- parts are rules, under the statement's conditions.
    let generated ← withNewMCtxDepth do
      forallTelescopeReducing info.type fun _ conclusion => pure (finiteMixed? conclusion).isSome
    if generated then
      if mixed then
        -- Only the bound's computation is normalized; its reference and budget stay as stated.
        let bound ← withNewMCtxDepth do
          let rule ← mkConstWithFreshMVarLevels name
          let projected ← forallTelescopeReducing (← ruleType rule) fun arguments _ => do
            mkLambdaFVars arguments (← mkAppM ``And.right #[mkAppN rule arguments])
          abstractMVars (← normalizeRule session projected)
        mixedEntries ← insertPrepared mixedEntries name bound (exactOperations.size + index)
          (·.getAppArgs[0]!)
        let finite ← normalizeFact name ``And.left
        finiteness ← insertPrepared finiteness name finite index (·.appFn!.appArg!)
      continue
    let entry? ← withNewMCtxDepth do
      -- Normalization runs once, in the main goal's context, so a hypothesis that only a branch
      -- introduces does not rewrite a registered rule. A theorem that cannot be prepared would
      -- fail at every node, so it is not indexed.
      let rule? ← try
        let rule ← specializeLocalError (← mkConstWithFreshMVarLevels name)
        pure (some (← normalizeRule session rule))
      catch error =>
        trace[roundoff] "rule {name} not indexed: {error.toMessageData}"
        pure none
      let some rule := rule? | return none
      let prepared ← abstractMVars rule
      let (_, _, conclusion) ← forallMetaTelescopeReducing (← ruleType rule)
      let some (actual, _, exact) ← numericalConclusion? conclusion | return none
      let reference? ← if exact then
          pure (conclusion.eq?.map fun (_, _, reference) => reference)
        else do
          pure ((← errorConclusion? conclusion).map fun (_, reference, _) => reference)
      let some reference := reference? | return none
      let reference ← instantiateMVars reference
      let pattern ← withReducible <|
        withCanUnfoldPred (programCanUnfold session.boundaries false) (numericalPattern actual)
      let observation? ← if ← referenceObservesOperands session.containerFree actual reference then
          pure actual.getAppFn.constName?
        else pure none
      let indexed ← withCanUnfoldPred (fun _ _ => pure false)
        (entries.insertIfSpecific pattern { name, exact, prepared })
      pure (some (indexed, observation?))
    if let some (indexed, observation?) := entry? then
      trace[roundoff] "rule {name}: {observation?.getD .anonymous}"
      entries := indexed
      if let some observation := observation? then observations := observations.insert observation
  -- Mixed analysis also proves literal finiteness and the range conditions it generates.
  let mixedHelpers ← if mixed then do
      pure #[(``ExecFloat.Binary.isFinite_one,
          ← `(tactic| (apply ExecFloat.Binary.isFinite_one; assumption))),
        (``Model.unitRoundoffAt_lt_one, ← `(tactic| apply Model.unitRoundoffAt_lt_one)),
        (``Model.toReal_posMaxFinite_nonneg, ← `(tactic| apply Model.toReal_posMaxFinite_nonneg)),
        (``Model.one_le_toReal_posMaxFinite,
          ← `(tactic| exact Model.one_le_toReal_posMaxFinite _)),
        (``Model.isFinite_ofRat, ← `(tactic|
          (refine Model.isFinite_ofRat _ ‹_› (le_trans ?_ (Model.one_le_toReal_posMaxFinite _))
            <;> norm_num))),
        (``ExecFloat.Binary.abs_toReal_le_posMaxFinite_of_isFinite,
          ← `(tactic| (apply ExecFloat.Binary.abs_toReal_le_posMaxFinite_of_isFinite
            <;> solve_by_elim)))]
    else pure #[]
  let helpers ← (#[
      (``ExecFloat.Binary.isFinite_zero, ← `(tactic| apply ExecFloat.Binary.isFinite_zero)),
      (``FloatFormat.supportsSignedZero_eq_true_of_isIEEE,
        ← `(tactic| (apply FloatFormat.supportsSignedZero_eq_true_of_isIEEE; assumption))),
      (``Real.exp_pos, ← `(tactic| apply Real.exp_pos))] ++ mixedHelpers).mapM
    fun (name, tactic) =>
    withNewMCtxDepth do
      let (_, _, conclusion) ← forallMetaTelescopeReducing
        (← inferType (← mkConstWithFreshMVarLevels name))
      let patterns ← withCanUnfoldPred (fun _ _ => pure false) do
        ({} : DiscrTree Unit).insertIfSpecific (← numericalPattern conclusion) ()
      let head := conditionHead conclusion (classifiers := true)
      return { name, tactic, head, patterns : Helper }
  -- The simplification of side conditions is elaborated once; each local context adds its
  -- hypotheses, as `*` does.
  let identities ← (← extension).loops.mapM fun loop =>
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent loop.foldErrorIdentity):ident)
  let simplification ← `(tactic|
    simp (config := { zetaDelta := false, implicitDefEqProofs := false }) only
      [Except.isOk, Except.toBool, Except.toOption, Option.getD, sub_self, abs_zero, zero_add,
      add_zero, zero_mul, mul_zero, zero_div, ExecFloat.Binary.toReal_zero, $identities,*,
      le_refl])
  let simplification ← mkSimpContext simplification (eraseLocal := false)
  let orderShapes ← orders.mapM fun rule => withNewMCtxDepth do
    let (_, _, conclusion) ← forallMetaTelescopeReducing (← ruleType (← rule.instantiate))
    return conclusion
  return { session with
    bounds := entries, observations, helpers, mixed, mixedBounds := mixedEntries, finiteness,
    refutations, orders, orderShapes, base := .ofArray (← getLCtx).getFVarIds,
    dischargeSimp := some (simplification.ctx, simplification.simprocs) }
/-- Whether a helper lemma can apply to the target. Its index decides most targets; the others
are compared by unification that keeps the helper's heads and selected class methods opaque. -/
def Helper.compatible (helper : Helper) (target : Expr) : MetaM Bool :=
  withoutModifyingState <| withNewMCtxDepth do
    if let (some left, some right) := (helper.head, conditionHead target (classifiers := true)) then
      unless left == right do return false
    -- Match the helper's complete computation before unification can evaluate an unrelated
    -- scalar program. Candidate application still checks every selected dictionary.
    if ← withCanUnfoldPred (fun _ _ => pure false) do
        return !(← helper.patterns.getMatch target).isEmpty then return true
    let (_, _, conclusion) ← forallMetaTelescopeReducing
      (← inferType (← mkConstWithFreshMVarLevels helper.name))
    -- Ordinary value aliases may hide a matching literal.
    let protectedNames := conclusion.getUsedConstantsAsSet
    withCanUnfoldPred (fun config info => do
        if protectedNames.contains info.name ||
            (← getProjectionFnInfo? info.name).any (·.fromClass) then return false
        programCanUnfold {} false config info) <| withDefault do
      isDefEq conclusion target

/-- Two relations with the same head whose two sides also have the same heads. A cheap filter
before unification, which could otherwise evaluate floating-point code. -/
def sameRelation (reads : Array Read) (left right : Lean.Expr) : Bool :=
  let left := left.consumeMData
  let right := right.consumeMData
  let sides (relation : Lean.Expr) := (relation.getAppArgs.extract
    (relation.getAppNumArgs - 2) relation.getAppNumArgs).toList
  let sameHead (left right : Lean.Expr) :=
    left.getAppFn.constName? == right.getAppFn.constName? || left.getAppFn.isMVar ||
      right.getAppFn.isMVar
  let decoded? (value : Lean.Expr) : Option Lean.Expr :=
    if value.isAppOf ``ExecFloat.Binary.toReal || value.isAppOf ``ExecFloat.Binary.isFinite then
      value.getAppArgs.back?
    else none
  let container? (read : Lean.Expr) : Option Lean.Expr :=
    (Read.position? reads read (getters := true) (strict := false)).bind (read.getAppArgs[·]?)
  -- A decoded or classified value is compared by the operation that computes it as well, and a
  -- container read by the container it reads.
  let compatible (pair : Lean.Expr × Lean.Expr) :=
    sameHead pair.1 pair.2 &&
      match decoded? pair.1, decoded? pair.2 with
      | some left, some right => sameHead left right &&
          match container? left, container? right with
          | some left, some right => sameHead left right
          | _, _ => true
      | _, _ => true
  left.getAppFn.constName? == right.getAppFn.constName? &&
    left.getAppNumArgs == right.getAppNumArgs && left.getAppNumArgs ≥ 2 &&
    ((sides left).zip (sides right)).all compatible

/-- The value that `isFinite value = b` or `isZero value = b` classifies, on the configured
carrier or on its model. -/
def classified? (type : Lean.Expr) : Option Lean.Expr := do
  let some (_, test, _) := type.consumeMData.eq? | none
  guard (#[``ExecFloat.Binary.isFinite, ``ExecFloat.Binary.isZero, ``Model.isFinite,
    ``Model.isZero].any test.isAppOf)
  let value := test.appArg!
  return if value.isAppOf ``ExecFloat.Binary.toModel then value.appArg! else value

/-- Whether `fact` and `target` classify values computed by different operations, so that `fact`
cannot supply `target`; comparing them by unification would evaluate floating-point code. -/
def otherClassified (fact target : Lean.Expr) : Bool :=
  match classified? fact, classified? target with
  | some left, some right => left.getAppFn != right.getAppFn
  | _, _ => false

/-- The conjuncts of a proposition. -/
partial def conjuncts (proposition : Lean.Expr) : Array Lean.Expr :=
  match proposition.and? with
  | some (left, right) => conjuncts left ++ conjuncts right
  | none => #[proposition]

/-- Read the decoded finiteness `Model.isFinite (toModel v)` of a configured value as its
finiteness `isFinite v`, which is the same by definition. -/
def foldDecodedFinite (proposition : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform proposition (pre := fun term => do
    unless term.isAppOfArity ``Model.isFinite 2 && term.appArg!.isAppOf ``ExecFloat.Binary.toModel
    do return .continue
    return .done (← mkAppM ``ExecFloat.Binary.isFinite #[term.appArg!.appArg!]))


/-- Compare predicate heads without evaluating floating-point classifiers. Ordinary aliases may
expose those heads; dependent propositions and unresolved control flow remain conservative. -/
def assumptionHead (type : Expr) : MetaM (Option Name) := do
  if type.isForall then return none
  let conclusion := type.consumeMData
  let some (scalar, predicate, _) := conclusion.eq? | return conditionHead type true
  unless scalar.isConstOf ``Bool do return none
  let classifier ← withCanUnfoldPred (fun config info => do
      if (← getProjectionFnInfo? info.name).any (·.fromClass) then return false
      programCanUnfold {} false config info) <| withDefault (whnf predicate)
  if classifier.isConstOf ``Bool.true || classifier.isConstOf ``Bool.false then return none
  if let some name := classifier.getAppFn.constName? then
    if (← getMatcherInfo? name).isSome || isAuxRecursor (← getEnv) name ||
        ((← getEnv).find? name).any (fun info => match info with
          | .recInfo _ => true | _ => false) then
      return predicate.getAppFn.constName?
  return classifier.getAppFn.constName?

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
