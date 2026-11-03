/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Loop

/-!
# Loops whose state is a tuple in the `roundoff` analysis

A registered loop whose state is a pair or a nondependent record, such as a running maximum beside a
rescaled sum, is analyzed one component at a time. A component of the observed format is compared
with a real reference under a bound, kept finite and of one sign when the step preserves it; a
component whose type mentions no numerical carrier equals a shadow copy, which is part of the
reference and so starts at index data and is updated to index data. A record is split into its
fields, so a field of a record of binary32 values is a value of that format. The step is analyzed
once for symbolic components, and the loop's relation law (`Loop.relation`) lifts the conjunction of
these facts through the traversal. Only the components the observed one depends on through the step
enter the relation. A component stays exact while the step keeps it exact from exact components, and
a test (`<`, `≤`, `==`, `!=`) of exact finite values that a discrete component reads is the test of
their references, when the conditions, indices and other data in those references are index data.
Another test of the rounded state is the test of the references of its operands under the premise
that the two agree, which the loop's condition carries, so the theorem holds for the executions
whose decisions match the reference's. Both kinds are FloatLib's own tests under the observation
(`ownTest`): the left side of the law that makes a test the test of the decoded values, with the
observation's codec, so a reversed order, the structural equality of the stored word and a test
under a second codec are neither. An agreement test also needs an analysis of each operand whose
reference is a plain real expression (`plainReference`): real variables, numerals, casts of index
data, the decoded values of index data, the four operations, negation, `max`, `min` and branches on
comparisons of such expressions, through the reals' own dictionaries, the ones Mathlib declares
(`realDictionary?`), whatever instances a section declares on the reals. A stored function read at
the rounded state, an entry read at an index computed from rounded values and a contract's model,
which may hide a rounded computation in a definition, are not. Each component of the observed format
that such a reference reads, directly, through another or through the shadow copy of a discrete
component that tests it, keeps a plain reference from its start and through the step, so a component
that holds an entry chosen by rounding cannot enter the references of an agreement test either, not
even through a flag that tests it. A loop analyzed inside another loop's step states no agreement
premise there, since its references could read the enclosing loop's state, whose provenance only
that loop could check; an estimate found outside the step, which reads no such state, is reused as
it is. A real input stands for the value it names. The shadow copy's check (`indexClosed`) admits an
agreement test although its operands are rounded, since the copy never reads it: the copy reads the
test of the references in its place and mentions no rounded component, so a rounded value reaches
the theorem only through the premise, as the decision it states, and not through the reference,
beyond what references keep under the trust assumptions of the roundoff overview: a stored entry
read at an index chosen by rounding.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

namespace Tuple

/-- A leaf of a loop state: its field indices from the state, its type, and whether it is a value
of the observed format. -/
structure Component where
  /-- The field indices from the state to the leaf. -/
  path : Array Nat
  /-- The type of the leaf. -/
  type : Lean.Expr
  /-- Whether the leaf is a value of the observed format. -/
  float : Bool
  deriving Inhabited

/-- What the relation of a loop keeps about a component of the observed format: an exact bound,
its finiteness, and the sign of its reference (`true` for nonnegative). -/
structure Facts where
  /-- Whether the bound of the component is exact. -/
  exact : Bool := false
  /-- Whether the component is finite. -/
  finite : Bool := false
  /-- The sign of the component's reference, `true` for nonnegative. -/
  sign : Option Bool := none
  deriving BEq, Inhabited

/-- The structure name and field types of `type` when it is a structure that is not a class and
whose fields are data that do not depend on earlier fields. -/
def recordFields? (type : Lean.Expr) : MetaM (Option (Name × Array Lean.Expr)) := do
  let type ← whnf type
  let .const name levels := type.getAppFn | return none
  let environment ← getEnv
  unless isStructure environment name do return none
  if isClass environment name then return none
  let ctor := getStructureCtor environment name
  let parameters := type.getAppArgs
  unless parameters.size == ctor.numParams do return none
  let mut rest ← instantiateForall
    ((ConstantInfo.ctorInfo ctor).instantiateTypeLevelParams levels) parameters
  let mut fields := #[]
  for _ in [0:ctor.numFields] do
    let .forallE _ domain body _ := rest | return none
    if body.hasLooseBVars then return none
    if ← isProp domain then return none
    fields := fields.push domain
    rest := body
  return some (name, fields)

/-- The leaves of a loop state of type `type` at `path`, values of the observed format
`floatType` and data whose type mentions no numerical carrier (`mentionsCarrier`), with the
projection functions of the records between them. A record whose fields hold such values, also a
record of one format or a wrapper of such a record, is split into its fields; any other leaf is
rejected. -/
partial def components (floatType type : Lean.Expr) (path : Array Nat := #[]) :
    MetaM (Array Component × Array Lean.Expr) := do
  if ← withNewMCtxDepth (withReducible (isDefEq type floatType)) then
    return (#[{ path, type, float := true }], #[])
  unless ← mentionsCarrier type do return (#[{ path, type, float := false }], #[])
  let fields? ← if ← carrierHead type then pure none else recordFields? type
  let some (name, fields) := fields? |
    throwError "roundoff: the loop state component {type} is neither a value of the observed \
      format {floatType}, data without real or floating-point values, nor a pair or \
      nondependent record of them"
  let names := getStructureFields (← getEnv) name
  let mut leaves := #[]
  let mut functions := #[]
  for index in [0:fields.size] do
    let function ← withLocalDeclD `state type fun state => do
      return (← mkProjection state names[index]!).appFn!
    let (inner, innerFunctions) ← components floatType fields[index]! (path.push index)
    leaves := leaves ++ inner
    functions := (functions.push function) ++ innerFunctions
  return (leaves, functions)

/-- The format whose exponent width `field` is. -/
def fieldFormat? (field : Lean.Expr) : Option Lean.Expr :=
  match field.consumeMData with
  | .proj ``FloatFormat 0 format => some format
  | field => if field.isAppOfArity ``FloatFormat.expWidth 1 then some field.appArg! else none

/-- `term` with each binary descriptor built from the fields of a format written as that format,
and each `ExecFloat.Binary` over such a descriptor written as the configured family. -/
def formatForm (term : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform term (post := fun child => do
    if child.isAppOfArity ``ExecFloat.Binary 10 &&
        (fieldFormat? child.getAppArgs[0]!).isSome then
      if let some unfolded ← unfoldDefinition? child then return .visit unfolded.headBeta
    if child.isAppOfArity ``ExecFloat.Binary.descriptor 8 then
      if let some format := fieldFormat? child.getAppArgs[0]! then
        if ← withNewMCtxDepth (isDefEq child format) then return .done format
    return .continue)

/-- The leaf of `value` at `path`. -/
def project (value : Lean.Expr) (path : Array Nat) : MetaM Lean.Expr := do
  let mut current := value
  for index in path do
    let type ← whnf (← inferType current)
    let .const name _ := type.getAppFn | throwError "roundoff: {current} is not a record"
    let some field := (getStructureFields (← getEnv) name)[index]? |
      throwError "roundoff: {current} has no field {index}"
    current ← mkProjection current field
  return current

/-- The field index and the record of a projection of a record that is not a class instance. -/
def projectionStep? (term : Lean.Expr) : MetaM (Option (Nat × Lean.Expr)) := do
  match term with
  | .proj name index inner =>
      if isClass (← getEnv) name then return none
      return some (index, inner)
  | _ =>
      let some name := term.getAppFn.constName? | return none
      let some info ← getProjectionFnInfo? name | return none
      if info.fromClass || term.getAppNumArgs != info.numParams + 1 then return none
      return some (info.i, term.appArg!)

/-- A leaf read from `term` by record projections: the term it is read from and its path. -/
partial def projection? (term : Lean.Expr) : MetaM (Option (Lean.Expr × Array Nat)) := do
  let some (index, inner) ← projectionStep? term.consumeMData | return none
  let (base, path) := (← projection? inner).getD (inner.consumeMData, #[])
  return some (base, path.push index)

/-- The state of type `type` whose leaf at the path of each of `leaves` is the corresponding entry
of `values`. -/
partial def assemble (leaves : Array Component) (values : Array Lean.Expr) (type : Lean.Expr)
    (path : Array Nat := #[]) : MetaM Lean.Expr := do
  if let some index := leaves.findIdx? (·.path == path) then return values[index]!
  let type ← whnf type
  let .const name levels := type.getAppFn | throwError "roundoff: {type} is not a record"
  let some (_, fields) ← recordFields? type | throwError "roundoff: {type} is not a record"
  let ctor := getStructureCtor (← getEnv) name
  let mut arguments := type.getAppArgs
  for index in [0:fields.size] do
    arguments := arguments.push (← assemble leaves values fields[index]! (path.push index))
  return mkAppN (mkConst ctor.name levels) arguments

/-- The nested pair type of `types`, `Unit` when there are none. -/
def tupleType : List Lean.Expr → MetaM Lean.Expr
  | [] => return mkConst ``Unit
  | [type] => return type
  | type :: rest => do mkAppM ``Prod #[type, ← tupleType rest]

/-- The nested pair of `values`, `()` when there are none. -/
def tupleValue : List Lean.Expr → MetaM Lean.Expr
  | [] => return mkConst ``Unit.unit
  | [value] => return value
  | value :: rest => do mkAppM ``Prod.mk #[value, ← tupleValue rest]

/-- The entry `index` of a nested pair `tuple` of `count` entries. -/
def tupleGet (tuple : Lean.Expr) : Nat → Nat → MetaM Lean.Expr
  | 0, _ | 1, _ => return tuple
  | _ + 2, 0 => mkAppM ``Prod.fst #[tuple]
  | count + 2, index + 1 => do tupleGet (← mkAppM ``Prod.snd #[tuple]) (count + 1) index

/-- The conjunction of `props`, nested to the right. -/
def conjunction : List Lean.Expr → Lean.Expr
  | [] => mkConst ``True
  | [prop] => prop
  | prop :: rest => mkAnd prop (conjunction rest)

/-- A proof of the conjunction of the propositions of `pairs` from their proofs. -/
def conjunctionProof : List (Lean.Expr × Lean.Expr) → Lean.Expr
  | [] => mkConst ``True.intro
  | [(_, proof)] => proof
  | (prop, proof) :: rest =>
      mkApp4 (mkConst ``And.intro) prop (conjunction (rest.map (·.1))) proof
        (conjunctionProof rest)

/-- The proofs of the conjuncts `props` of a proof of their conjunction. -/
def conjunctProofs (proof : Lean.Expr) : List Lean.Expr → Array Lean.Expr
  | [] => #[]
  | [_] => #[proof]
  | prop :: rest =>
      let others := conjunction rest
      #[mkApp3 (mkConst ``And.left) prop others proof] ++
        conjunctProofs (mkApp3 (mkConst ``And.right) prop others proof) rest

/-- The conjuncts of a conjunction of `count` propositions nested to the right. -/
def splitConjunction (prop : Lean.Expr) : Nat → List Lean.Expr
  | 0 => []
  | 1 => [prop]
  | count + 1 => prop.appFn!.appArg! :: splitConjunction prop.appArg! count

/-- A simplification context that moves the projection functions `functions` into branches and
rewrites with the equations `extra`. -/
def componentContext (functions extra : Array Lean.Expr) : MetaM Simp.Context := do
  let mut theorems : SimpTheorems := {}
  let mut index := 0
  for function in functions do
    for law in [``apply_ite, ``apply_dite] do
      let proof ← instantiateMVars (← mkAppOptM law #[none, none, some function])
      theorems ← theorems.add (.other (Name.mkNum law index)) #[] proof
      index := index + 1
  for equation in extra do
    theorems ← theorems.add (.other (Name.mkNum `roundoff.tuple index)) #[] equation
    index := index + 1
  Simp.mkContext { implicitDefEqProofs := false, failIfUnchanged := false } #[theorems]
    (← getSimpCongrTheorems)

/-- `term` with the definitions at its head unfolded until it shows a branch, a constructor, a
match, a class method or a FloatLib operation, and its `let` bindings substituted. -/
partial def exposeStep (term : Lean.Expr) (fuel : Nat := 16) : MetaM Lean.Expr := do
  let term := headZeta term.headBeta
  if fuel == 0 then return term
  let some name := term.getAppFn.constName? | return term
  if name == ``ite || name == ``dite || name == ``cond || name.getRoot == `FloatLib then
    return term
  if ← isMatcher name then return term
  if let some (.ctorInfo _) := (← getEnv).find? name then return term
  if (← getProjectionFnInfo? name).any (·.fromClass) then return term
  let some next ← unfoldDefinition? term | return term
  exposeStep next (fuel - 1)

/-- The leaf of `next` at `path`, simplified in `context` from the form `exposed` of `next`, with
a proof that the leaf of `next` equals it. -/
def normalizedComponent (context : Simp.Context) (exposed next : Lean.Expr)
    (path : Array Nat) : MetaM (Lean.Expr × Lean.Expr) := do
  let leaf ← project exposed path
  let (result, _) ← simp leaf context
  let proof ← result.getProof' leaf
  return (result.expr, ← mkExpectedTypeHint proof (← mkEq (← project next path) result.expr))

/-- The leaves among `leaves` that the leaf `target` depends on through `step` at `value`, itself
included: the closure of the leaves that each leaf of the simplified next state mentions. -/
def relevantLeaves (leaves : Array Component) (functions : Array Lean.Expr)
    (stateType step value : Lean.Expr) (target : Nat) : MetaM (Array Bool) := do
  let declarations := leaves.map fun leaf => (`accumulator, leaf.type)
  withLocalDeclsDND declarations fun actuals => do
    let state ← assemble leaves actuals stateType
    let next := mkAppN step #[state, value]
    let exposed ← exposeStep next
    let context ← componentContext functions #[]
    let mut reads := #[]
    for leaf in leaves do
      let (normalized, _) ← normalizedComponent context exposed next leaf.path
      reads := reads.push ((Array.range leaves.size).filter fun other =>
        mentions normalized (· == actuals[other]!.fvarId!))
    let mut relevant := (Array.replicate leaves.size false).set! target true
    for _ in [0:leaves.size] do
      for index in [0:leaves.size] do
        if relevant[index]! then
          for other in reads[index]! do
            relevant := relevant.set! other true
    return relevant

/-- The proposition that `value` is finite. -/
def finiteness (value : Lean.Expr) : MetaM Lean.Expr := do
  mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[value]) (mkConst ``Bool.true)

/-- The sign of `reference`: nonnegative for `true`, nonpositive for `false`. -/
def signed (nonneg : Bool) (reference : Q(ℝ)) : Q(Prop) :=
  if nonneg then q(0 ≤ $reference) else q($reference ≤ 0)

/-- The finiteness of the left side of `equality`, from the finiteness `proof` of its right side. -/
def transportFinite (equality proof : Lean.Expr) : MetaM Lean.Expr := do
  let some (type, leaf, _) := (← instantiateMVars (← inferType equality)).eq? |
    throwError "roundoff: expected an equality of floating-point values"
  let motive ← withLocalDeclD `value type fun value => do
    mkLambdaFVars #[value] (← finiteness value)
  mkExpectedTypeHint (← mkEqMPR (← mkCongrArg motive equality) proof) (← finiteness leaf)

/-- The estimate of `actual` with its budgets written as the literal zero, when they simplify to
it in the session's budget simplification. -/
def exactly (estimate : Estimate) (actual : Q(ℝ)) : AnalyzeM (Option Estimate) := do
  let session ← read
  let context ← Simp.mkContext { implicitDefEqProofs := false } #[session.budget]
  let zero (budget : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if budget.nat? == some 0 then return some (← mkEqRefl budget)
    let tidied ← session.tidyTerm budget context
    unless tidied.expr.nat? == some 0 do return none
    return some (← tidied.getProof' budget)
  let statement := estimate.bound.statement actual estimate.reference
  let proof ← mkExpectedTypeHint estimate.proof statement
  match estimate.bound with
  | .absolute error =>
      let some equality ← zero error | return none
      let bound : Bound := .absolute q(0)
      let proof ← mkEqMP (← mkCongrArg statement.appFn! equality) proof
      return some { estimate with
        bound := bound
        proof := ← mkExpectedTypeHint proof (bound.statement actual estimate.reference) }
  | .mixed relative absolute =>
      let some relativeZero ← zero relative | return none
      let some absoluteZero ← zero absolute | return none
      let bound : Bound := .mixed q(0) q(0)
      let equality ← mkCongr (← mkCongrArg statement.appFn!.appFn! relativeZero) absoluteZero
      let proof ← mkEqMP equality proof
      return some { estimate with
        bound := bound
        proof := ← mkExpectedTypeHint proof (bound.statement actual estimate.reference) }

/-- The equality `actual = reference` stated by an exact estimate of either mode. -/
def exactValue (estimate : Estimate) : MetaM Lean.Expr := do
  match estimate.bound with
  | .absolute _ => exactEquality (← mkAppM ``MixedError.of_abs_sub_le #[estimate.proof])
  | .mixed _ _ => exactEquality estimate.proof

/-- Whether the choices that `reference`, the reference of an operand of a test of exact values,
makes are index data (`indexClosed`): each proposition in it, such as the condition of a branch,
and each value in it that holds no number, such as an index, enters the shadow copy of the test
with it, as the shadow's own data does. -/
def choicesAtIndexData (reference : Lean.Expr) (cache : CarrierCache) : MetaM Bool := do
  let closed ← IO.mkRef true
  -- Whether a value of `type` is numerical: of a numerical type at default transparency, a function
  -- over numerical values, a dictionary, or a container with a numerical type argument. An index of
  -- a type that only names a number, as `Fin 2` under an alias taking a value, is data.
  let numerical (type : Lean.Expr) : MetaM Bool := do
    if ← carrierHead type then return true
    let type ← whnfD type
    if ← carrierHead type then return true
    if type.isForall then return ← mentionsCarrier type cache
    if (← isClass? type).isSome then return true
    type.getAppArgs.anyM fun argument => do
      return (← isType argument) && (← mentionsCarrier argument cache)
  discard <| Meta.transform reference (pre := fun term => do
    unless ← closed.get do return .done term
    let type ← inferType term
    if ← isProp type then return .done term
    let sort ← whnfR type
    if sort.isSort && !sort.isProp then return .done term
    if sort.isProp || !(← numerical type) then
      unless ← indexClosed term (cache? := cache) do closed.set false
      return .done term
    return .continue)
  closed.get

/-- The tests `a < b`, `a ≤ b`, `a == b` and `a != b` in `term`. -/
partial def comparisons (term : Lean.Expr) (found : Array Lean.Expr := #[]) :
    Array Lean.Expr :=
  let test := term.isAppOfArity ``LT.lt 4 || term.isAppOfArity ``LE.le 4 ||
    term.isAppOfArity ``BEq.beq 4 || term.isAppOfArity ``bne 4
  let found := if test && !term.hasLooseBVars && !found.contains term then found.push term
    else found
  match term with
  | .app function argument => comparisons argument (comparisons function found)
  | .lam _ type body _ | .forallE _ type body _ => comparisons body (comparisons type found)
  | .letE _ type value body _ => comparisons body (comparisons value (comparisons type found))
  | .mdata _ inner | .proj _ _ inner => comparisons inner found
  | _ => found

/-- Whether `comparison`, a test with head `head`, is FloatLib's own test of configured values up
to unfolding, under the observation `observe`: at fresh operands and instance transparency it is the
left side of the law that makes it the test of their real values
(`ExecFloat.Binary.lt_iff_toReal_lt`, `le_iff_toReal_le`, `beq_eq_decide_toReal_eq`; `a != b`
negates `a == b` through the same dictionary), and the law's right side decodes them by `observe`,
so that the law's codec is the observation's. Fresh operands and instance transparency unfold no
comparison and no rounded computation. A test through another dictionary, such as a reversed order
or the structural equality of the stored word, under which the two zeros differ, or through
another codec, is not one. -/
def ownTest (head : Name) (observe comparison : Lean.Expr) : MetaM Bool := do
  let law := if head == ``LT.lt then ``ExecFloat.Binary.lt_iff_toReal_lt
    else if head == ``LE.le then ``ExecFloat.Binary.le_iff_toReal_le
    else ``ExecFloat.Binary.beq_eq_decide_toReal_eq
  let arguments := comparison.getAppArgs
  let levels := comparison.getAppFn.constLevels!
  let function := if head == ``bne then mkConst ``BEq.beq levels else comparison.getAppFn
  withNewMCtxDepth <| withReducibleAndInstances <| withLocalDeclD `left arguments[0]! fun left =>
      withLocalDeclD `right arguments[0]! fun right => do
    let lawType ← inferType (← mkConstWithFreshMVarLevels law)
    let (_, _, statement) ← forallMetaTelescopeReducing lawType
    -- The test and the test of real values that the law equates.
    let some (side, decoded) := match statement.iff?, statement.eq? with
        | some sides, _ => some sides
        | none, some (_, side, decoded) =>
            if decoded.isAppOfArity ``Decidable.decide 2 then some (side, decoded.getArg! 0)
            else none
        | none, none => none
      | return false
    unless side.getAppNumArgs == 4 && decoded.getAppNumArgs ≥ 2 do return false
    unless ← isDefEq side.getAppArgs[2]! left <&&> isDefEq side.getAppArgs[3]! right do
      return false
    unless ← isDefEq side (mkAppN function #[arguments[0]!, arguments[1]!, left, right]) do
      return false
    let decodedArguments := decoded.getAppArgs
    isDefEq decodedArguments[decodedArguments.size - 2]! (mkApp observe left).headBeta <&&>
      isDefEq decodedArguments[decodedArguments.size - 1]! (mkApp observe right).headBeta

/-- The head and the operands of a test that `comparisons` collects, when it is FloatLib's own test
(`ownTest`) of values of type `floatType` under the observation `observe`. -/
def floatTest? (floatType observe comparison : Lean.Expr) :
    MetaM (Option (Name × Lean.Expr × Lean.Expr)) := do
  let some head := comparison.getAppFn.constName? | return none
  let arguments := comparison.getAppArgs
  unless arguments.size == 4 do return none
  unless ← withNewMCtxDepth (withReducible (isDefEq arguments[0]! floatType)) do return none
  unless ← ownTest head observe comparison do return none
  return some (head, arguments[2]!, arguments[3]!)

/-- The reals' own dictionary of the class application `type` on `ℝ`: the order, the four
operations, negation, `max`, `min`, a numeral and the casts of natural numbers and integers, as
Mathlib declares them and this module's elaboration finds them. Instance search is not asked, since
it also finds instances that a section or another module declares on the reals. For a numeral of at
least two, the proof of `Nat.AtLeastTwo` is a metavariable for unification to fill, since a proof
carries no value. -/
def realDictionary? (type : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let type ← instantiateMVars type
  if type.isAppOfArity ``OfNat 2 then
    unless ← withNewMCtxDepth (withReducible (isDefEq type.appFn!.appArg! q(ℝ))) do
      return none
    let some value := type.appArg!.rawNatLit? | return none
    if value == 0 then return some q(@Zero.toOfNat0 ℝ Real.instZero)
    if value == 1 then return some q(@One.toOfNat1 ℝ Real.instOne)
    let atLeastTwo ← mkFreshExprMVar (mkApp (mkConst ``Nat.AtLeastTwo) (mkRawNatLit value))
    return some (mkAppN (mkConst ``instOfNatAtLeastTwo [0])
      #[q(ℝ), mkRawNatLit value, q(Real.instNatCast), atLeastTwo])
  let dictionaries : Array (Lean.Expr × Lean.Expr) := #[
    (q(LT ℝ), q(Real.instLT)), (q(LE ℝ), q(Real.instLE)),
    (q(HAdd ℝ ℝ ℝ), q(@instHAdd ℝ Real.instAdd)), (q(HSub ℝ ℝ ℝ), q(@instHSub ℝ Real.instSub)),
    (q(HMul ℝ ℝ ℝ), q(@instHMul ℝ Real.instMul)),
    (q(HDiv ℝ ℝ ℝ), q(@instHDiv ℝ (@DivInvMonoid.toDiv ℝ Real.instDivInvMonoid))),
    (q(Neg ℝ), q(Real.instNeg)), (q(Max ℝ), q(Real.instMax)), (q(Min ℝ), q(Real.instMin)),
    (q(NatCast ℝ), q(Real.instNatCast)), (q(IntCast ℝ), q(Real.instIntCast))]
  for (application, dictionary) in dictionaries do
    if ← withNewMCtxDepth (withReducible (isDefEq type application)) then
      return some dictionary
  return none

/-- Whether `term`, the real reference of an operand of an agreement test or a part of one, is a
plain real expression: a real variable or a field of one, a real local definition whose value is
plain, a numeral, a cast of index data, the observation `observe` of index data, the four
operations, negation, `max` and `min` with the reals' own dictionaries (`realDictionary?`), and a
branch (`if`, also with its proof) on a comparison of plain expressions or on index data. A
contract's model, a stored entry read at an index computed from rounded values, a helper that hides
a rounded computation and any other function is not. A real variable stands for what it names: an
input, or the reference of a component, whose own references the caller checks. -/
partial def plainReference (observe : Lean.Expr) (cache? : Option CarrierCache) (term : Lean.Expr) :
    MetaM Bool := do
  let term ← instantiateMVars term.consumeMData
  let plain := plainReference observe cache?
  let real (type : Lean.Expr) : MetaM Bool := return (← whnfR type).isConstOf ``Real
  let own (dictionary : Lean.Expr) : MetaM Bool := withNewMCtxDepth do
    let some reals ← realDictionary? (← inferType dictionary) | return false
    withReducibleAndInstances (isDefEq dictionary reals)
  let type ← inferType term
  let arguments := term.getAppArgs
  let head := term.getAppFn.constName?.getD .anonymous
  let arity (name : Name) (count : Nat) : Bool := head == name && arguments.size == count
  if type.isProp then
    if arity ``LT.lt 4 || arity ``LE.le 4 then
      if ← real arguments[0]! then
        return ← own arguments[1]! <&&> plain arguments[2]! <&&> plain arguments[3]!
    if arity ``Eq 3 then
      if ← real arguments[0]! then return ← plain arguments[1]! <&&> plain arguments[2]!
    if arity ``And 2 || arity ``Or 2 then
      return ← plain arguments[0]! <&&> plain arguments[1]!
    if arity ``Not 1 then return ← plain arguments[0]!
    return ← indexClosed term (cache? := cache?)
  unless ← real type do
    if arity ``Decidable.decide 2 then return ← plain arguments[0]!
    if ← mentionsCarrier type cache? then return false
    return ← indexClosed term (cache? := cache?)
  if let .fvar id := term then
    return ← match (← id.getDecl).value? with
      | some value => plain value
      | none => pure true
  -- A field of a real variable, such as a component of a real state.
  let mut record := term
  while record.isProj || record.isAppOfArity ``Prod.fst 3 || record.isAppOfArity ``Prod.snd 3 do
    record := if record.isProj then record.projExpr! else record.appArg!
  if record != term then
    if let .fvar id := record then return (← id.getDecl).value?.isNone
    return false
  if term.isApp then
    if (← instantiateMVars (mkApp observe term.appArg!).headBeta) == term then
      return ← indexClosed term.appArg! (cache? := cache?)
  if arity ``HAdd.hAdd 6 || arity ``HSub.hSub 6 || arity ``HMul.hMul 6 || arity ``HDiv.hDiv 6 then
    return ← real arguments[0]! <&&> real arguments[1]! <&&> own arguments[3]! <&&>
      plain arguments[4]! <&&> plain arguments[5]!
  if arity ``Neg.neg 3 then return ← own arguments[1]! <&&> plain arguments[2]!
  if arity ``Max.max 4 || arity ``Min.min 4 then
    return ← own arguments[1]! <&&> plain arguments[2]! <&&> plain arguments[3]!
  if arity ``OfNat.ofNat 3 then
    return arguments[1]!.rawNatLit?.isSome && (← own arguments[2]!)
  if arity ``Nat.cast 3 || arity ``NatCast.natCast 3 || arity ``Int.cast 3 ||
      arity ``IntCast.intCast 3 then
    return ← own arguments[1]! <&&> indexClosed arguments[2]! (cache? := cache?)
  if arity ``ite 5 then
    return ← plain arguments[1]! <&&> plain arguments[3]! <&&> plain arguments[4]!
  if arity ``dite 5 then
    let branch (body : Lean.Expr) : MetaM Bool := lambdaTelescope body fun _ value => plain value
    return ← plain arguments[1]! <&&> branch arguments[3]! <&&> branch arguments[4]!
  return false

/-- The test with head `head` between the real numbers `left` and `right`: `left < right`,
`left ≤ right`, through the reals' own order (`realDictionary?`), or the decision of their equality
or of its negation. -/
def realTest (head : Name) (left right : Lean.Expr) : MetaM Lean.Expr := do
  if head == ``LT.lt || head == ``LE.le then
    let order := if head == ``LT.lt then ``LT else ``LE
    let some dictionary ← realDictionary? (mkApp (mkConst order [0]) q(ℝ)) |
      throwError "roundoff: no order of the reals for {head}"
    return mkAppN (mkConst head [0]) #[q(ℝ), dictionary, left, right]
  let equal ← mkDecide (← mkEq left right)
  return if head == ``bne then mkApp (mkConst ``not) equal else equal

/-- The equation of a test between finite values with the test of real numbers that their real
values equal, from the finiteness of the operands and these equalities. -/
def exactTest (head : Name) (comparison : Lean.Expr) (finite equalities : Array Lean.Expr) :
    MetaM (Option Lean.Expr) := do
  let some (_, _, left) := (← inferType equalities[0]!).eq? | return none
  let some (_, _, right) := (← inferType equalities[1]!).eq? | return none
  let decoded ← if head == ``LT.lt then
      mkPropExt (← mkAppM ``ExecFloat.Binary.lt_iff_toReal_lt finite)
    else if head == ``LE.le then
      mkPropExt (← mkAppM ``ExecFloat.Binary.le_iff_toReal_le finite)
    else do
      let equal ← mkAppM ``ExecFloat.Binary.beq_eq_decide_toReal_eq finite
      if head == ``bne then mkCongrArg (mkConst ``not) equal else pure equal
  let test ← withLocalDeclD `left q(ℝ) fun x => withLocalDeclD `right q(ℝ) fun y => do
    mkLambdaFVars #[x, y] (← realTest head x y)
  let shifted ← mkCongr (← mkCongrArg test equalities[0]!) equalities[1]!
  return some (← mkExpectedTypeHint (← mkEqTrans decoded shifted)
    (← mkEq comparison (← realTest head left right)))

/-- The analysis of the initial value of one component: its simplified leaf with the equality to
it, and for a value of the observed format its estimate, its exact estimate, its finiteness and
the sign of its reference. -/
structure Start where
  /-- The simplified leaf of the initial state. -/
  value : Lean.Expr
  /-- A proof that the leaf of the initial state equals `value`. -/
  equality : Lean.Expr
  /-- The estimate of the observed leaf. -/
  estimate? : Option Estimate := none
  /-- The estimate of the observed leaf with literal zero budgets, when it is exact. -/
  zero? : Option Estimate := none
  /-- The finiteness of the leaf. -/
  finite? : Option Lean.Expr := none
  /-- The sign of the reference of the leaf, with its proof. -/
  sign? : Option (Bool × Lean.Expr) := none
  deriving Inhabited

/-- The data of a loop whose state is a tuple, shared by the attempts at its relation. -/
structure Setting where
  /-- The registered loop. -/
  loop : Loop
  /-- The observation of a value of the observed format. -/
  observe : Lean.Expr
  /-- The step of the loop. -/
  step : Lean.Expr
  /-- The initial state of the loop. -/
  initial : Lean.Expr
  /-- The input of the loop. -/
  input : Lean.Expr
  /-- The element variable at which the step is analyzed. -/
  value : Lean.Expr
  /-- The type of the loop's state. -/
  stateType : Lean.Expr
  /-- The type of the observed values. -/
  floatType : Lean.Expr
  /-- The leaves of the state that the observed leaf depends on through the step. -/
  leaves : Array Component
  /-- The other leaves of the state, which the relation does not mention. -/
  others : Array Component
  /-- The projection functions of the records in the state. -/
  functions : Array Lean.Expr
  /-- Whether the observation decodes configured values, whose finiteness is tracked. -/
  configured : Bool
  /-- The index of the observed leaf in `leaves`. -/
  target : Nat
  /-- The caller's observation of the leaf of the loop. -/
  actual : Lean.Expr
  /-- The analysis of the initial leaves. -/
  starts : Array Start

/-- The leaf of the actual state, the shadow entry and the budget entries of each component, for
an actual state, a shadow state and budgets of the relation, under `facts` in mode `mixed`. -/
def Setting.slots (setting : Setting) (facts : Array Facts) (mixed : Bool)
    (state realState budgets : Lean.Expr) :
    MetaM (Array (Lean.Expr × Lean.Expr × Array Lean.Expr)) := do
  let count := setting.leaves.size
  let inexact := (setting.leaves.zip facts).filter fun (leaf, fact) => leaf.float && !fact.exact
  let mut result := #[]
  let mut slot := 0
  for index in [0:count] do
    let leaf := setting.leaves[index]!
    let actual ← project state leaf.path
    let shadow ← tupleGet realState count index
    let mut parts := #[]
    if leaf.float && !facts[index]!.exact then
      let entry ← tupleGet budgets inexact.size slot
      slot := slot + 1
      if mixed then parts := #[← mkAppM ``Prod.fst #[entry], ← mkAppM ``Prod.snd #[entry]]
      else parts := #[entry]
    result := result.push (actual, shadow, parts)
  return result

/-- The flat list of the parts of `slots`, in the order of the variables of a step. -/
def flatten (slots : Array (Lean.Expr × Lean.Expr × Array Lean.Expr)) : Array Lean.Expr :=
  slots.foldl (fun parts (actual, shadow, budgets) => (parts.push actual |>.push shadow) ++ budgets)
    #[]

/-- The conjuncts of the relation at `slots`, each with the name of its hypothesis in a step. -/
def Setting.atoms (setting : Setting) (facts : Array Facts) (mixed : Bool)
    (slots : Array (Lean.Expr × Lean.Expr × Array Lean.Expr)) :
    MetaM (Array (Name × Lean.Expr)) := do
  let mut atoms := #[]
  for index in [0:setting.leaves.size] do
    let (actual, shadow, parts) := slots[index]!
    let shadow : Q(ℝ) := shadow
    let fact := facts[index]!
    if setting.leaves[index]!.float then
      let observed : Q(ℝ) := (mkApp setting.observe actual).headBeta
      let bound : Bound := if fact.exact then
          if mixed then .mixed q(0) q(0) else .absolute q(0)
        else if mixed then .mixed parts[0]! parts[1]! else .absolute parts[0]!
      atoms := atoms.push (`accumulator_error, bound.statement observed shadow)
      if fact.finite then atoms := atoms.push (`accumulator_finite, ← finiteness actual)
      if let some nonneg := fact.sign then
        atoms := atoms.push (`reference_sign, signed nonneg shadow)
    else
      atoms := atoms.push (`shadow_eq, ← mkEq actual shadow)
  return atoms

end Tuple

namespace Analyze

open Tuple

/-- One attempt at the relation of a loop whose state is a tuple, under `facts`. The step is
analyzed once for symbolic components; a fact the step does not keep is recorded in `drops`
before the attempt fails, so that the next attempt drops it and analyzes every component again. -/
def tupleAttempt (r : Recursor) (setting : Setting) (facts : Array Facts)
    (drops : IO.Ref (Option (Array Facts))) (fuel : Nat) : AnalyzeM Estimate := do
  let mixed := (← read).mixed
  let nested := (← read).nested
  let leaves := setting.leaves
  let count := leaves.size
  let value := setting.value
  let observe := setting.observe
  let before ← get
  let mut declarations : Array (Name × Lean.Expr) := #[]
  for index in [0:count] do
    let leaf := leaves[index]!
    if leaf.float then
      declarations := declarations.push (`accumulator, setting.floatType) |>.push (`reference, q(ℝ))
      unless facts[index]!.exact do
        declarations := if mixed then
            declarations.push (`relative, q(ℝ)) |>.push (`absolute, q(ℝ))
          else declarations.push (`budget, q(ℝ))
    else
      declarations := declarations.push (`discrete, leaf.type) |>.push (`shadow, leaf.type)
  for leaf in setting.others do
    declarations := declarations.push (if leaf.float then `accumulator else `discrete, leaf.type)
  let (referenceLam, budgetLam, conditionLam, actualLam?, stepLam) ←
    withLocalDeclsDND declarations fun locals => do
    -- The variables of each component.
    let mut slots : Array (Lean.Expr × Lean.Expr × Array Lean.Expr) := #[]
    let mut position := 0
    for index in [0:count] do
      let width := if leaves[index]!.float && !facts[index]!.exact then
          if mixed then 2 else 1
        else 0
      slots := slots.push (locals[position]!, locals[position + 1]!,
        locals.extract (position + 2) (position + 2 + width))
      position := position + 2 + width
    let otherActuals := locals.extract position locals.size
    let actuals := slots.map (·.1)
    let shadows := slots.map (·.2.1)
    let budgetVariables := slots.foldl (fun parts slot => parts ++ slot.2.2) #[]
    let atoms ← setting.atoms facts mixed slots
    -- A loop that the step holds is nested in this one.
    withReader (fun session => { session with nested := true }) do
    withLocalDeclsDND atoms fun hypotheses => do
    -- The hypotheses of each component, in the order of `atoms`.
    let mut owned : Array (Array Lean.Expr) := #[]
    let mut cursor := 0
    for index in [0:count] do
      let fact := facts[index]!
      let width := if leaves[index]!.float then
          1 + (if fact.finite then 1 else 0) + (if fact.sign.isSome then 1 else 0)
        else 1
      owned := owned.push (hypotheses.extract cursor (cursor + width))
      cursor := cursor + width
    let discretes := (Array.range count).filter (!leaves[·]!.float)
    let state ← assemble (leaves ++ setting.others) (actuals ++ otherActuals) setting.stateType
    let next := mkAppN setting.step #[state, value]
    let exposed ← exposeStep next
    let context ← componentContext setting.functions #[]
    let mut dropped := facts
    let mut nextShadows : Array Lean.Expr := #[]
    -- The components that an agreement test reads, of the observed format or discrete.
    let mut agreementReads : Array Nat := #[]
    let mut nextBudgets : Array (Array Lean.Expr) := #[]
    let mut proofs : Array (Array Lean.Expr) := #[]
    for index in [0:count] do
      let leaf := leaves[index]!
      let fact := facts[index]!
      let leafNext ← project next leaf.path
      let (normalized, equality) ← normalizedComponent context exposed next leaf.path
      if leaf.float then
        let observedNext : Q(ℝ) := (mkApp observe leafNext).headBeta
        let estimate ← r.analyze (mkApp observe normalized).headBeta fuel
        let estimate ← estimate.inMode mixed
        let finiteProof? ← if fact.finite then do
            let goal ← mkFreshExprMVar (← finiteness normalized)
            if ← estimate.closeFinite goal.mvarId! <||> r.proveFinite goal.mvarId! fuel then
              pure (some (← transportFinite equality (← instantiateMVars goal)))
            else pure none
          else pure none
        let mut estimate ← rewriteActual estimate (← mkCongrArg observe equality)
        estimate := { estimate with
          proof := ← mkExpectedTypeHint estimate.proof
            (estimate.bound.statement observedNext estimate.reference) }
        if fact.exact then
          if let some exact ← exactly estimate observedNext then estimate := exact
          else dropped := dropped.set! index { dropped[index]! with exact := false }
        -- A reference or budget that reads a discrete component reads its shadow copy instead.
        for other in discretes do
          let (discrete, shadow, _) := slots[other]!
          let copied (copy : Lean.Expr) : Bound × Lean.Expr :=
            let bound : Bound := match estimate.bound with
              | .absolute error => .absolute (error.replaceFVar discrete copy)
              | .mixed relative absolute =>
                  .mixed (relative.replaceFVar discrete copy) (absolute.replaceFVar discrete copy)
            (bound, estimate.reference.replaceFVar discrete copy)
          let read := estimate.reference :: match estimate.bound with
            | .absolute error => [error]
            | .mixed relative absolute => [relative, absolute]
          unless read.any (mentions · (· == discrete.fvarId!)) do continue
          let motive ← withLocalDeclD `copy leaves[other]!.type fun copy => do
            let (bound, reference) := copied copy
            mkLambdaFVars #[copy] (bound.statement observedNext reference)
          let (bound, reference) := copied shadow
          let proof ← mkEqMP (← mkCongrArg motive (owned[other]!)[0]!) estimate.proof
          estimate := { estimate with
            reference := reference
            bound := bound
            proof := ← mkExpectedTypeHint proof (bound.statement observedNext reference) }
        if fact.finite && finiteProof?.isNone then
          dropped := dropped.set! index { dropped[index]! with finite := false }
        let signProof? ← if let some nonneg := fact.sign then do
            let goal ← mkFreshExprMVar (signed nonneg estimate.reference)
            if ← r.proveSign goal.mvarId! fuel signDepth then pure (some (← instantiateMVars goal))
            else
              dropped := dropped.set! index { dropped[index]! with sign := none }
              pure none
          else pure none
        let parts := if fact.exact then #[] else match estimate.bound with
          | .mixed relative absolute => #[relative, absolute]
          | .absolute error => #[error]
        nextShadows := nextShadows.push estimate.reference
        nextBudgets := nextBudgets.push parts
        proofs := proofs.push (#[estimate.proof] ++ finiteProof?.toArray ++ signProof?.toArray)
      else
        -- A test of exact finite values is the test of their references.
        let tested := actuals ++ otherActuals ++ budgetVariables ++ hypotheses
        let mut equations : Array Lean.Expr := #[]
        let mut tests : Array Lean.Expr := #[]
        if setting.configured then
          for comparison in comparisons normalized do
            let some (head, left, right) ← floatTest? setting.floatType observe comparison
              | continue
            let mut equalities := #[]
            let mut finite := #[]
            for operand in #[left, right] do
              let estimate ← (← r.analyze (mkApp observe operand).headBeta fuel).inMode mixed
              let some exact ← exactly estimate (mkApp observe operand).headBeta | break
              let goal ← mkFreshExprMVar (← finiteness operand)
              let given := (actuals.zip owned).findSome? fun (accumulator, facts') =>
                if accumulator == operand && facts'.size > 1 &&
                    leaves[actuals.idxOf accumulator]!.float &&
                    facts[actuals.idxOf accumulator]!.finite then
                  some facts'[1]!
                else none
              if let some proof := given then goal.mvarId!.assign proof
              else unless ← estimate.closeFinite goal.mvarId! <||>
                  r.proveFinite goal.mvarId! fuel do
                if mentions operand (actuals.contains <| .fvar ·) then break
                modify fun state => { state with pending := state.pending.push goal.mvarId! }
              equalities := equalities.push (← exactValue exact)
              finite := finite.push goal
            unless equalities.size == 2 do continue
            let choices ← equalities.allM fun equality => do
              let some (_, _, reference) := (← inferType equality).eq? | return false
              choicesAtIndexData reference (← read).carriers
            unless choices do continue
            if let some equation ← exactTest head comparison finite equalities then
              equations := equations.push equation
              tests := tests.push comparison
        let copies := discretes.map fun other => (owned[other]!)[0]!
        let shadowContext ← componentContext setting.functions (equations ++ copies)
        let (result, _) ← simp normalized shadowContext
        let mut result := result
        -- Another test of the rounded state is the test of the references of its operands, under
        -- the premise that the two agree, which the loop's condition carries.
        if setting.configured && mentions result.expr (tested.contains <| .fvar ·) then
          let mut agreements := #[]
          for comparison in comparisons result.expr do
            unless mentions comparison (tested.contains <| .fvar ·) do continue
            let some (head, left, right) ← floatTest? setting.floatType observe comparison
              | continue
            let some references ← speculate? (#[left, right].mapM fun operand => do
                instantiateMVars (← r.analyze (mkApp observe operand).headBeta fuel).reference)
              | continue
            let references := references.map fun reference =>
              discretes.foldl (init := reference) fun reference other =>
                reference.replaceFVar slots[other]!.1 slots[other]!.2.1
            if references.any fun reference =>
                reference.hasMVar || mentions reference (tested.contains <| .fvar ·) then continue
            -- The copy reads these references, so they must be plain real expressions, and so must
            -- the references of the components of the observed format they read, also through
            -- discrete components (checked after the step). In a loop that another loop's step
            -- holds they could read the enclosing loop's state, which this check cannot follow.
            unless ← references.allM (plainReference observe (← read).carriers ·) do continue
            if nested then
              throwError "roundoff: a test of the rounded state, {comparison}, is in a loop inside \
                another loop's step, whose state the test of the references could read, so it \
                gets no agreement premise"
            for other in [0:count] do
              if references.any (mentions · (· == shadows[other]!.fvarId!)) then
                agreementReads := agreementReads.push other
            let realized ← realTest head references[0]! references[1]!
            let decision := head == ``BEq.beq || head == ``bne
            let premise ← mkFreshExprMVar
              (← if decision then mkEq comparison realized else pure (mkIff comparison realized))
            modify fun state => { state with pending := state.pending.push premise.mvarId! }
            agreements := agreements.push (← if decision then pure premise else mkPropExt premise)
            tests := tests.push comparison
          unless agreements.isEmpty do
            let context ← componentContext setting.functions (agreements ++ copies)
            let (agreed, _) ← simp result.expr context
            result ← result.mkEqTrans agreed
        if mentions result.expr (tested.contains <| .fvar ·) then
          throwError "roundoff: a discrete component of the loop state, {result.expr}, depends \
            on its rounded state, such as through a test of values that have no analysis; decide \
            the branch first or keep the tested values exact"
        -- Its shadow copy is part of the reference, so beside those tests it reads index data only.
        -- An agreement test is admitted although its operands are rounded: the copy reads the test
        -- of their references in its place, which are plain real expressions, and, as checked
        -- above, no rounded component.
        unless ← indexClosed normalized tests (← read).carriers do
          throwError "roundoff: a discrete component of the loop state, {result.expr}, is computed \
            from real or floating-point values other than tests of exact ones, so its shadow copy \
            would keep their rounding"
        let proof ← mkEqTrans equality (← result.getProof' normalized)
        nextShadows := nextShadows.push result.expr
        nextBudgets := nextBudgets.push #[]
        proofs := proofs.push #[proof]
    -- Follow what an agreement test reads through the references of components of the observed
    -- format and the updates of discrete ones, whose shadow copies may read tests of exact
    -- components. Each component of the observed format reached keeps a plain reference from its
    -- start and through the step: otherwise a reference could carry a rounded value into the
    -- copy, such as an entry read at an index chosen by rounding.
    let mut checked : Array Nat := #[]
    for _ in [0:count] do
      let fresh := agreementReads.filter (!checked.contains ·)
      if fresh.isEmpty then break
      for index in fresh do
        checked := checked.push index
        let initial := (setting.starts[index]!.estimate?.map (·.reference)).toArray
        for reference in initial.push nextShadows[index]! do
          if leaves[index]!.float then
            unless ← plainReference observe (← read).carriers reference do
              throwError "roundoff: a test of the rounded state reads a component whose reference \
                {reference} is not a plain real expression, so the test of the references could \
                keep a rounded value"
          for other in [0:count] do
            if mentions reference (· == shadows[other]!.fvarId!) then
              agreementReads := agreementReads.push other
    if dropped != facts then
      drops.set (some dropped)
      throwError "roundoff: the step does not keep the loop invariant {facts.map (·.exact)}"
    let nextSlots ← (Array.range count).mapM fun index => do
      return (← project next leaves[index]!.path, nextShadows[index]!, nextBudgets[index]!)
    let nextAtoms ← setting.atoms facts mixed nextSlots
    let pairs := (nextAtoms.map (·.2)).zip (proofs.foldl (· ++ ·) #[])
    let candidates := (← get).pending.extract before.pending.size (← get).pending.size
    withConditions candidates (← read).comparisons fun condition evidence => do
      for hypothesis in hypotheses do
        if mentions condition (· == hypothesis.fvarId!) then
          throwError "roundoff: a loop condition depends on its proof argument"
      let forbidden := actuals ++ otherActuals ++ budgetVariables ++ hypotheses
      for shadow in nextShadows do
        if mentions shadow (forbidden.contains <| .fvar ·) then
          throwError "roundoff: the loop's real reference depends on its rounded \
            accumulator; establish agreement of its branch conditions first"
      let budgetEntries ← (Array.range count).filterMapM fun index => do
        unless leaves[index]!.float && !facts[index]!.exact do return none
        let parts := nextBudgets[index]!
        if mixed then return some (← mkAppM ``Prod.mk #[parts[0]!, parts[1]!])
        return some parts[0]!
      let steps := flatten slots ++ otherActuals ++ #[value]
      let actualLam? ← if mentions condition ((shadows ++ budgetVariables).contains <| .fvar ·)
        then pure none
        else pure (some (← mkLambdaFVars (actuals ++ otherActuals ++ #[value]) condition))
      let conclusion ← instantiateMVars (conjunctionProof pairs.toList)
      return (← mkLambdaFVars (shadows ++ #[value]) (← tupleValue nextShadows.toList),
        ← mkLambdaFVars steps (← tupleValue budgetEntries.toList),
        ← mkLambdaFVars steps condition, actualLam?,
        ← mkLambdaFVars (steps ++ #[evidence] ++ hypotheses) conclusion)
  set { before with pending := before.pending }
  -- The functions of the relation law.
  let elementType ← inferType value
  let inexact := (Array.range count).filter fun index =>
    leaves[index]!.float && !facts[index]!.exact
  let realType ← tupleType (leaves.toList.map fun leaf => if leaf.float then q(ℝ) else leaf.type)
  let budgetType ← tupleType (inexact.toList.map fun _ =>
    if mixed then q(ℝ × ℝ) else q(ℝ))
  let referenceFunction ← withLocalDeclD `realState realType fun realState =>
    withLocalDeclD `value elementType fun element => do
      let shadows ← (Array.range count).mapM (tupleGet realState count ·)
      mkLambdaFVars #[realState, element] (referenceLam.beta (shadows ++ #[element]))
  checkEntries setting.loop setting.input referenceFunction
  let withState {α : Type} [Inhabited α]
      (k : Lean.Expr → Lean.Expr → Lean.Expr → Array Lean.Expr → AnalyzeM α) : AnalyzeM α :=
    withLocalDeclD `state setting.stateType fun state =>
    withLocalDeclD `realState realType fun realState =>
    withLocalDeclD `budgets budgetType fun budgets => do
      let others ← setting.others.mapM (project state ·.path)
      k state realState budgets
        (flatten (← setting.slots facts mixed state realState budgets) ++ others)
  let budgetFunction ← withState fun state realState budgets arguments =>
    withLocalDeclD `value elementType fun element => do
      mkLambdaFVars #[state, realState, budgets, element]
        (budgetLam.beta (arguments ++ #[element]))
  let conditionFunction ← withState fun state realState budgets arguments =>
    withLocalDeclD `value elementType fun element => do
      mkLambdaFVars #[state, realState, budgets, element]
        (conditionLam.beta (arguments ++ #[element]))
  let relationAt (state realState budgets : Lean.Expr) : MetaM (List Lean.Expr) := do
    let slots ← setting.slots facts mixed state realState budgets
    return ((← setting.atoms facts mixed slots).map (·.2)).toList
  let relationFunction ← withState fun state realState budgets _ => do
    mkLambdaFVars #[state, realState, budgets]
      (conjunction (← relationAt state realState budgets))
  -- The initial relation.
  let mut initialShadows := #[]
  let mut initialBudgets := #[]
  let mut initialProofs := #[]
  for index in [0:count] do
    let start := setting.starts[index]!
    let fact := facts[index]!
    unless leaves[index]!.float do
      initialShadows := initialShadows.push start.value
      initialProofs := initialProofs.push start.equality
      continue
    let some estimate := start.estimate? | throwError "roundoff: missing initial estimate"
    initialShadows := initialShadows.push estimate.reference
    if fact.exact then
      let some exact := start.zero? | throwError "roundoff: missing exact initial estimate"
      initialProofs := initialProofs.push exact.proof
    else
      initialProofs := initialProofs.push estimate.proof
      match estimate.bound, mixed with
      | .mixed relative absolute, true =>
          initialBudgets := initialBudgets.push (← mkAppM ``Prod.mk #[relative, absolute])
      | .absolute error, false => initialBudgets := initialBudgets.push error
      | _, _ => throwError "roundoff: an initial component was analyzed in another mode"
    if fact.finite then
      let some finite := start.finite? | throwError "roundoff: missing initial finiteness"
      initialProofs := initialProofs.push finite
    if fact.sign.isSome then
      let some (_, sign) := start.sign? | throwError "roundoff: missing initial sign"
      initialProofs := initialProofs.push sign
  let shadow ← tupleValue initialShadows.toList
  let budgets ← tupleValue initialBudgets.toList
  let initialAtoms ← relationAt setting.initial shadow budgets
  let hinit ← mkExpectedTypeHint (conjunctionProof (initialAtoms.zip initialProofs.toList))
    (conjunction initialAtoms)
  -- One step keeps the relation.
  let hstep ← withState fun state realState budgets arguments =>
    withLocalDeclD `value elementType fun element => do
      let condition := (conditionFunction.beta #[state, realState, budgets, element]).headBeta
      withLocalDeclD `condition condition fun evidence => do
        let atoms ← relationAt state realState budgets
        withLocalDeclD `relation (conjunction atoms) fun relation => do
          let proof := stepLam.beta
            (arguments ++ #[element, evidence] ++ conjunctProofs relation atoms)
          let nextState := mkAppN setting.step #[state, element]
          let nextShadow := referenceFunction.beta #[realState, element]
          let nextBudget := budgetFunction.beta #[state, realState, budgets, element]
          let expected := conjunction (← relationAt nextState nextShadow nextBudget)
          mkLambdaFVars #[state, realState, budgets, element, evidence, relation]
            (← mkExpectedTypeHint proof expected)
  let some (_, _, law) := setting.loop.relation |
    throwError "roundoff: the loop has no relation law"
  let lifted ← mkAppM law #[setting.step, referenceFunction, budgetFunction, relationFunction,
    conditionFunction, setting.initial, shadow, budgets, setting.input, hinit, hstep]
  let .forallE _ validType _ _ ← whnf (← inferType lifted) |
    throwError "roundoff: unexpected relation law {law}"
  let validType ← instantiateMVars validType
  let valid ← mkFreshExprMVar validType
  if let some actualLam := actualLam? then
    let augmentedType ← inferType (validType.getArg! 4)
    let first ← withLocalDeclD `state augmentedType fun state =>
      mkLambdaFVars #[state] (.proj ``Prod 0 state)
    let actualCondition ← withLocalDeclD `state setting.stateType fun state =>
      withLocalDeclD `value elementType fun element => do
        let actuals ← (leaves ++ setting.others).mapM (project state ·.path)
        mkLambdaFVars #[state, element] (actualLam.beta (actuals ++ #[element]))
    let goals ← valid.mvarId!.apply (← mkAppM setting.loop.allStepsOfMap
      #[validType.getArg! 2, validType.getArg! 3, validType.getArg! 4, setting.input, first,
        setting.step, actualCondition])
    for goal in goals do
      unless ← discharge (← read) goal do
        if let some condition ← (← read).tidy goal then
          modify fun state => { state with pending := state.pending.push condition }
  else
    modify fun state => { state with pending := state.pending.push valid.mvarId! }
  let proof := mkApp lifted valid
  let conclusion := (← instantiateMVars (← inferType proof)).headBeta
  let total := (← relationAt setting.initial shadow budgets).length
  let props := splitConjunction conclusion total
  let parts := conjunctProofs (← mkExpectedTypeHint proof conclusion) props
  let mut offset := 0
  for index in [0:setting.target] do
    let fact := facts[index]!
    offset := offset + if leaves[index]!.float then
        1 + (if fact.finite then 1 else 0) + (if fact.sign.isSome then 1 else 0)
      else 1
  let some (_, reference, bound) ← boundConclusion? props[offset]! |
    throwError "roundoff: unexpected loop relation {props[offset]!}"
  let actual : Q(ℝ) := setting.actual
  let reference : Q(ℝ) := reference
  let finite? ← if facts[setting.target]!.finite then
      pure (some (← mkExpectedTypeHint parts[offset + 1]! (← finiteness actual.appArg!)))
    else pure none
  return {
    reference := reference
    bound := bound
    finite? := finite?
    proof := ← mkExpectedTypeHint parts[offset]! (bound.statement actual reference) }

/-- The analysis of the observed leaf at `path` of the loop `fold`, whose state is a pair or a
nondependent record, through the loop's relation law. Mixed analysis that finds no relation
keeps the absolute one. -/
def tupleFoldIn (r : Recursor) (loop : Loop) (observe fold : Lean.Expr) (path : Array Nat)
    (actual : Q(ℝ)) (fuel : Nat) : AnalyzeM Estimate := do
  let mixed := (← read).mixed
  let arguments := fold.getAppArgs
  let step := arguments[loop.step]!
  let initial := arguments[loop.initial]!
  let input := arguments[loop.input]!
  let elementType := arguments[loop.element]!
  let stateType := arguments[loop.state]!
  let floatType ← inferType (← project fold path)
  let (all, functions) ← components floatType stateType
  let some position := all.findIdx? (·.path == path) |
    throwError "roundoff: {fold} has no leaf at {path}"
  unless all[position]!.float do throwError "roundoff: the observed leaf is not a float"
  let relevant ← withLocalDeclD `value elementType fun value =>
    relevantLeaves all functions stateType step value position
  let leaves := (all.zip relevant).filterMap fun (leaf, keep) => if keep then some leaf else none
  let others := (all.zip relevant).filterMap fun (leaf, keep) => if keep then none else some leaf
  let some target := leaves.findIdx? (·.path == path) |
    throwError "roundoff: {fold} has no leaf at {path}"
  let configured := actual.isAppOf ``ExecFloat.Binary.toReal
  let context ← componentContext functions #[]
  let mut starts := #[]
  let mut facts := #[]
  for leaf in leaves do
    let initialLeaf ← project initial leaf.path
    let (result, _) ← simp initialLeaf context
    let equality ← mkExpectedTypeHint (← result.getProof' initialLeaf)
      (← mkEq initialLeaf result.expr)
    unless leaf.float do
      -- The shadow copy starts at the initial value, which must be index data too.
      unless ← indexClosed result.expr (cache? := (← read).carriers) do
        throwError "roundoff: a discrete component of the loop state starts at {result.expr}, \
          which is computed from real or floating-point values, so its shadow copy would keep \
          their rounding"
      starts := starts.push { value := result.expr, equality := equality }
      facts := facts.push {}
      continue
    let observed : Q(ℝ) := (mkApp observe initialLeaf).headBeta
    let estimate ← (← r.analyze (mkApp observe result.expr).headBeta fuel).inMode mixed
    let finite? ← if configured then do
        let goal ← mkFreshExprMVar (← finiteness result.expr)
        if ← estimate.closeFinite goal.mvarId! <||> r.proveFinite goal.mvarId! fuel then
          pure (some (← transportFinite equality (← instantiateMVars goal)))
        -- The finiteness of an entry of a function the program takes is a premise.
        else if ← isAppliedInput result.expr then
          modify fun state => { state with pending := state.pending.push goal.mvarId! }
          pure (some (← transportFinite equality goal))
        else pure none
      else pure none
    let estimate ← rewriteActual estimate (← mkCongrArg observe equality)
    let estimate := { estimate with
      proof := ← mkExpectedTypeHint estimate.proof
        (estimate.bound.statement observed estimate.reference) }
    let zero? ← exactly estimate observed
    let mut sign? : Option (Bool × Lean.Expr) := none
    for nonneg in [true, false] do
      if sign?.isSome then continue
      let goal ← mkFreshExprMVar (signed nonneg estimate.reference)
      if ← r.proveSign goal.mvarId! fuel signDepth then
        sign? := some (nonneg, ← instantiateMVars goal)
    starts := starts.push {
      value := result.expr
      equality := equality
      estimate? := some estimate
      zero? := zero?
      finite? := finite?
      sign? := sign? }
    facts := facts.push
      { exact := zero?.isSome, finite := finite?.isSome, sign := sign?.map (·.1) }
  withLocalDeclD `value elementType fun value => do
    let mut facts := facts
    let setting : Setting := {
      loop := loop, observe := observe, step := step, initial := initial, input := input
      value := value, stateType := stateType, floatType := floatType, leaves := leaves
      others := others, functions := functions, configured := configured, target := target
      actual := actual, starts := starts }
    for _ in [0:3 * leaves.size + 2] do
      let drops ← IO.mkRef none
      if let some estimate ← speculate? (tupleAttempt r setting facts drops fuel) then
        return estimate
      if let some next ← drops.get then
        facts := next
      else if facts.any (·.sign.isSome) then
        facts := facts.map ({ · with sign := none })
      else if facts.any (·.finite) then
        facts := facts.map ({ · with finite := false })
      else break
    tupleAttempt r setting facts (← IO.mkRef none) fuel

/-- The analysis of the observed leaf at `path` of the loop `fold` whose state is a tuple
(`tupleFoldIn` at `formatForm`), mixed when a relation carries mixed bounds and absolute otherwise.
-/
def tupleFold (r : Recursor) (loop : Loop) (observe fold : Lean.Expr) (path : Array Nat)
    (actual : Q(ℝ)) (fuel : Nat) : AnalyzeM Estimate := do
  let observe ← formatForm observe
  let fold ← formatForm fold
  if (← read).mixed then
    if let some estimate ← speculate? (tupleFoldIn r loop observe fold path actual fuel) then
      return estimate
    let estimate ← withReader ({ · with mixed := false })
      (tupleFoldIn r loop observe fold path actual fuel)
    return ← estimate.inMode true
  tupleFoldIn r loop observe fold path actual fuel

end Analyze

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
