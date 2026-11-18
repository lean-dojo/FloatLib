/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.Roundoff.Backward.Tree

/-!
# Backward error from the implementation

`analyze` reads a computation as `roundoff` does and proves that the computed value is within an
absolute error of the exact computation on perturbed inputs, `x * (1 + δ)` with `|δ|` bounded.
The absolute error is zero unless an operation has one, as a product that may underflow.

Each operation's local rule is the one the forward analysis uses (`registeredBound?`), applied
with its operands taken as exact. Its mixed error `(r, a)` is the standard model
`x = x₀ * c + η` (`MixedError.factor`, `MixedError.offset`), and `round` moves the factor `c`
onto the perturbations of the exact operation (`Tree.scale`).

A loop is analyzed once for a symbolic accumulator (`step`). Its step computes
`G (accumulator * ρ) entry p` for an exact step `G` and the perturbations `p` of the step: one
for the entries that took the same factors, and those of each loop inside the step. Scaling the
step's exact computation by a symbolic factor gives the way each perturbation takes a factor of
the accumulator and the law `G (s * c) v (scale c p) = G s v p * c` that `List.fold_backward`
needs. The perturbations of the step at position `k` of `n` take the factors of the later steps,
so their bounds have the exponent `n - 1 - k`. A step with an absolute error needs its slope in
the accumulator (`Tree.coefficient`); when the slope reads perturbed entries, as in a product of
entries, it is bounded under the bounds of the perturbations (`Tree.magnitude`).

The finiteness that the rules need is derived from the finiteness of the result where it follows
(`reflect`), and a premise that is not proved outright is left to the statement.

Exact data are literals, casts of index data, real variables and real terms built from them
with the functions of Lean's and Mathlib's libraries. A real term that may read a floating-point
value (`readsFloat`), through a variable, a constant or a definition of the program, is never
taken as exact, because its statement would compare it with itself: a definition of the program
is expanded, the cast of a computed integer is refused, and so is a function of FloatLib without
a rule. A literal is read through the conversion that its instance selects, and stays in the
reference as the number that the format stores.

A rounding that the exact operation cannot pass to its inputs, as that of a sum with a literal
or of a product of inputs that take no perturbation, stays on the operation as a whole
(`Tree.unit`). A product around it moves it onto its other factor when that takes it, and a
product, quotient or negation carries it along otherwise (`settle`).

The analysis refuses a computation with no such form and names the obstacle: a rounding that is
still on a computation as a whole where a sum, a branch, a square root, a divisor, the end of a
loop step or the end of the computation meets it (`settled`), a function without a rule, or a
step that is not affine in its accumulator.

For a forward bound (`Config.forward`) the same analysis bounds each read by itself. An exact
constant and an input that every step of a loop reads are then perturbable reads, an exact
function of inputs such as the exponential of an input is read as an input, a rounding that an
exact operation cannot pass on stays on that operation as a whole (`Tree.unit`), and the
correctly rounded primitives are read through their real references, the exponential and the
logarithm (`Tree.apply`).
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

namespace Backward

/-- The input variable that the read `source` reads: its head, through applications, field
projections and registered reads of a container. -/
partial def headVariable? (source : Lean.Expr) : MetaM (Option FVarId) := do
  let source := source.consumeMData
  match source with
  | .fvar id => return some id
  | .proj _ _ record => headVariable? record
  | .app .. =>
    if let some position ← readPosition? source (getters := true) (strict := false) then
      return ← headVariable? source.getAppArgs[position]!
    if let some name := source.getAppFn.constName? then
      if let some field ← getProjectionFnInfo? name then
        if let some record := source.getAppArgs[field.numParams]? then
          return ← headVariable? record
      -- A conversion such as `Array.toList` reads the container it converts.
      if let some last := source.getAppArgs.back? then return ← headVariable? last
      return none
    headVariable? source.getAppFn
  | _ => return none

/-- Whether `source` is a stored input as the forward analysis reads one: a local variable without
a value, a data field of one, a stored function applied to index data, or an entry that a
certified read takes from an input container. -/
def isLeaf (source : Lean.Expr) : BackM Bool := do
  if ← isInputValue source then return true
  if ← isAppliedInput source then
    unless ← source.getAppArgs.allM (indexClosed · (cache? := (← readThe Session).carriers)) do
      throwError "roundoff: {source} reads a stored input at an index computed from numerical \
        values, so the reference would keep them"
    return true
  if let some entry := (← extension).reads.find? fun read =>
      source.isAppOf read.head && read.selects source && read.isCertified then
    if source.getAppNumArgs == entry.arity then
      let container := source.getAppArgs[source.getAppNumArgs - entry.fromEnd]!
      return ← isInputValue container
  return false

/-- The key that names an input read across attempts: the read as printed. -/
def keyName (key : Lean.Expr) : MetaM String :=
  return toString (← ppExpr key)

/-- The decoded floating-point values in the real term `term`, outermost first. -/
partial def decodedValues (term : Lean.Expr) (found : Array Lean.Expr := #[]) : Array Lean.Expr :=
  if term.isAppOf ``ExecFloat.Binary.toReal || term.isAppOf ``Model.toReal then found.push term
  else match term with
    | .app function argument => decodedValues argument (decodedValues function found)
    | .lam _ type body _ | .forallE _ type body _ => decodedValues body (decodedValues type found)
    | .letE _ type value body _ =>
        decodedValues body (decodedValues value (decodedValues type found))
    | .mdata _ inner | .proj _ _ inner => decodedValues inner found
    | _ => found

/-- The libraries whose functions on index data, reals and rationals are exact mathematics. A
function of FloatLib may round, and a definition from anywhere else is part of the program. -/
def mathematicsRoots : Array Name :=
  #[`Init, `Std, `Lean, `Batteries, `Mathlib, `Aesop, `Qq, `Plausible]

/-- The root of the module that declares the constant `name`; anonymous for this file. -/
def moduleRoot (name : Name) : CoreM Name := do
  let environment ← getEnv
  return match environment.getModuleIdxFor? name with
    | some index => environment.header.moduleNames[index.toNat]!.getRoot
    | none => .anonymous

/-- Whether the constant `name` comes from one of the `mathematicsRoots`. -/
def isMathematics (name : Name) : CoreM Bool :=
  return mathematicsRoots.contains (← moduleRoot name)

/-- Whether a value of a type built with the constant `name` can hold a floating-point value:
`name` is a numerical carrier other than the reals and the rationals, a definition whose value
uses such a constant, as `Binary32` does, or an inductive type with a field of such a type that
is not a proof. `seen` has the constants of this search so far. -/
partial def holdsFloat (seen : IO.Ref NameSet) (name : Name) : MetaM Bool := do
  if name == ``Real || name == ``Rat then return false
  if carrierTypes.contains name then return true
  if (← seen.get).contains name then return false
  seen.modify (·.insert name)
  match (← getEnv).find? name with
  | some (.defnInfo definition) => definition.value.getUsedConstants.anyM (holdsFloat seen)
  | some (.inductInfo type) =>
    type.ctors.anyM fun ctor => do
      let some (.ctorInfo ctor) := (← getEnv).find? ctor | return false
      forallTelescope ctor.type fun arguments _ =>
        (arguments.extract ctor.numParams arguments.size).anyM fun field => do
          let fieldType ← inferType field
          if ← isProp fieldType then return false
          fieldType.getUsedConstants.anyM (holdsFloat seen)
  | some (.opaqueInfo _) | some (.axiomInfo _) => return !(← isMathematics name)
  | _ => return false

/-- Whether the real term `term` may read a floating-point value: through a local variable
whose type can hold one or mentions a type parameter, which a statement can specialize to a
floating-point type, through a constant that is such a type or has one in its type, or through a
definition of the program, whose value is not inspected here. The reals and the rationals count
as none. A term that may read one is not exact data, whatever it computes. -/
def readsFloat (term : Lean.Expr) : BackM Bool := do
  let cache := (← readThe Session).carriers
  let floating (type : Lean.Expr) : MetaM Bool := do
    type.getUsedConstants.anyM (holdsFloat (← IO.mkRef {}))
  for id in (collectFVars {} term).fvarIds do
    let type ← instantiateMVars (← id.getType)
    if (← mentionsTypeParameter type cache) || (← floating type) then
      trace[roundoff] "{term} may read a floating-point value through {mkFVar id}"
      return true
  for name in term.getUsedConstants do
    let some info := (← getEnv).find? name | continue
    let former ← forallTelescopeReducing info.type fun _ body => pure body.isSort
    let reads ← if former then holdsFloat (← IO.mkRef {}) name
      else if ← floating info.type then pure true
      else pure !((← isMathematics name) || info matches .thmInfo _)
    if reads then
      trace[roundoff] "{term} may read a floating-point value through {.ofConstName name}"
      return true
  return false

/-- The form of a read of an input: a slot, or a constant when the read takes no perturbation
inside a loop step because it does not depend on the traversed entry. For a forward bound such
a read is a slot too: it may take a different perturbation at each step. -/
def leaf (actual : Q(ℝ)) (source : Lean.Expr) : BackM Form := do
  let proof ← mkAppM ``FloatLib.Numerics.exact_error #[actual]
  let config ← read
  let state ← get
  let mut origin? ← headVariable? source
  let mut blocked? : Option String := none
  if let some accumulator := state.accumulator? then
    -- An input that every step reads would take a different perturbation at each.
    unless config.forward || source.containsFVar accumulator.element.fvarId! do
      return ⟨.const actual false "is read by every step of the loop, so it takes no perturbation",
        q(0), proof⟩
    if origin? == some accumulator.element.fvarId! then origin? := accumulator.origin?
  if let some selected := config.selected? then
    unless origin?.any selected.contains do
      blocked? := some "is not among the inputs chosen with `perturb`"
  if config.excluded.contains (← keyName actual) then
    blocked? := some "is read more than once, with roundings that differ, so it takes no \
      perturbation"
  modify fun state => { state with slots := state.slots.push {
    key := actual, origin?, perturbable := blocked?.isNone, blocked := blocked?.getD "" } }
  return ⟨.slot state.slots.size, q(0), proof⟩

/-- The local rule of the forward analysis for `actual`, with its operands taken as exact: a
mixed bound against the exact operation on the decoded operands, and whether it is the contract
of a correctly rounded function. Finiteness premises stay open, and so does a bound by the
largest finite value that is not proved outright. -/
def localRule? (actual : Q(ℝ)) : BackM (Option (Estimate × Bool)) := do
  let exactInput (value : Q(ℝ)) : AnalyzeM Estimate := exactEstimate true value
  let prove (goal : MVarId) : AnalyzeM Bool := do
    let type ← instantiateMVars (← goal.getType)
    if isFiniteness type then return false
    -- A premise is proved outright or left to the statement: the forward analysis of an operand
    -- would add the range conditions of its own bound.
    let before ← getThe Analysis
    let saved ← (saveState : TacticM _)
    if (← analysis.prove goal 64) && (← getThe Analysis).pending.size == before.pending.size then
      return true
    saved.restore
    set before
    -- A bound by the largest finite value is left to the statement like a finiteness. An
    -- operation in a directed attribute saturates there, so its rule asks for that bound on the
    -- exact result.
    if (type.find? (·.isAppOf ``Model.posMaxFinite)).isSome && !type.hasExprMVar then
      modify fun state => { state with pending := state.pending.push goal }
      return true
    return false
  let result? ← (registeredBound? actual exactInput prove : AnalyzeM _)
  if let some (estimate, _) := result? then return some (estimate, false)
  -- A correctly rounded primitive rounds its real reference once. Only a forward bound reads
  -- that reference, the exponential or the logarithm of the decoded argument.
  if (← read).forward then
    return (← (primitiveBound? actual exactInput prove : AnalyzeM _)).map (·, true)
  return none

/-- What the analysis is asked for, as a refusal names it, and the mode that asks. -/
def wanted : BackM (String × String) := do
  return if (← read).forward then ("closed forward bound", "the closed forward mode")
    else ("backward-error form", "the backward-error mode")

/-- The message that refuses `actual`, whose rounding cannot move onto the inputs. -/
def refusal (actual : Lean.Expr) (reason : MessageData) : MessageData :=
  m!"roundoff: `{actual}` has no backward-error form: its rounding cannot be moved onto the \
    inputs, because {reason}. Use `roundoff mixed theorem` for a forward bound, or choose the \
    perturbed inputs with `(perturb := [...])`."

/-- Apply the local rule `estimate` of `actual` to the form `inner` of its exact operation: an
exact rule keeps the bound, a rule with an absolute error only adds it, and a rounding moves its
factor onto the perturbations of `inner`. With `whole`, for the one rounding of a correctly
rounded function, the factor stays on a reference that is a sum or a difference: spread over the
terms of `exp x - 1`, it would be charged to terms that cancel. -/
def round (actual : Q(ℝ)) (estimate : Estimate) (inner : Form) (whole : Bool := false) :
    BackM Form := do
  let .mixed relative absolute := estimate.bound |
    throwError "roundoff: expected a mixed local rule for {actual}"
  let budget := inner.budget
  if relative.nat? == some 0 && absolute.nat? == some 0 then
    return { inner with
      proof := (← mkAppM ``FloatLib.Numerics.Backward.exact #[estimate.proof, inner.proof]) }
  if relative.nat? == some 0 then
    return ← tidy { inner with
      budget := q($budget + $absolute)
      proof := (← mkAppM ``FloatLib.Numerics.Backward.offset #[estimate.proof, inner.proof]) }
  -- A rounding that the exact operation cannot take stays on it as a whole. A forward bound
  -- keeps it there. A backward statement needs a product to move it onto its other factor, and
  -- is refused with this reason otherwise.
  let inner ← do
    let several := match inner.tree with
      | .add .. | .sub .. => true
      | _ => false
    let obstacle? ← if whole && several then
        pure (some m!"the value of a correctly rounded function takes its rounding as a whole")
      else inner.tree.obstacle
    let some reason := obstacle? | pure inner
    let index := (← get).slots.size
    let pending? := if (← read).forward then none else some (refusal actual reason)
    modify fun state => { state with slots := state.slots.push { key := q(1), pending? } }
    pure { inner with tree := .unit inner.tree index }
  let exact := estimate.reference
  let factor : Q(ℝ) := q(MixedError.factor $actual $exact $relative $absolute)
  let bound ← mkAppM ``FloatLib.Numerics.Backward.abs_sub_one_le_growth
    #[← mkAppM ``MixedError.abs_factor_sub_one_le #[estimate.proof]]
  -- The factor of a rounding with a unit roundoff is nonnegative, so a square can split it.
  let growth : Q(ℝ) := q(1 + $relative)
  let nonneg? ← (← growthLeTwo? growth).mapM fun small =>
    mkAppM ``FloatLib.Numerics.Backward.nonneg_of_abs_sub_one_le #[bound, small]
  let scaled ← inner.tree.scale factor growth bound nonneg?
  tidy { inner with
    budget := q($budget * (1 + $relative) + $absolute)
    proof := (← mkAppM ``FloatLib.Numerics.Backward.round #[estimate.proof, inner.proof, scaled]) }

/-- A proof of `statement`, `∀ s s' v …, |F s v - F s' v| ≤ L v * |s - s'|` for a step `F` that
is affine in its accumulator with slope one (`unit`) or `μ`, where `L v` is `|μ|`. The identity
`F s v - F s' v = μ * (s - s')` is proved by `ring` under the binders, so that the proof may
mention premises that are still open. With `bounded?` the statement is
`∀ s s' v p, B v p → |F s v p - F s' v p| ≤ L v * |s - s'|` for a slope that reads the
perturbations: `bounded?` has the slope as a function of `v` and `p`, and the proof of
`|μ| ≤ L v` as a function of `v`, `p` and the bounds `B v p`. -/
def slopeLaw (statement : Lean.Expr) (unit : Bool)
    (bounded? : Option (Lean.Expr × Lean.Expr) := none) : TacticM Lean.Expr :=
  forallTelescope statement fun binders body => do
    let failure : MessageData :=
      m!"roundoff: could not prove the slope of the loop step in its accumulator: {body}"
    let prove (goal : Lean.Expr) (tactic : Syntax) : TacticM Unit := do
      let remaining ← try Lean.Elab.Tactic.run goal.mvarId! (evalTactic tactic)
        catch error => throwError "{failure}\n{error.toMessageData}"
      unless remaining.isEmpty do throwError failure
    if let some (slope, bound) := bounded? then
      let #[_, _, entry, perturbation, bounds] := binders | throwError failure
      -- `body` is `|D| ≤ L v * |s - s'|`.
      let difference := (body.getArg! 2).appArg!
      let gap := (body.getArg! 3).appArg!.appArg!
      let slope := (mkApp2 slope entry perturbation).headBeta
      let goal ← mkFreshExprMVar (← mkEq difference (← mkAppM ``HMul.hMul #[slope, gap]))
      prove goal (← `(tactic| ((try dsimp only); ring)))
      let proof ← mkAppM ``FloatLib.Numerics.Backward.abs_sub_le_of_eq_mul_le
        #[← instantiateMVars goal, mkApp3 bound entry perturbation bounds]
      unless ← isDefEq (← inferType proof) body do throwError failure
      return ← mkLambdaFVars binders proof
    let slopeLemma := mkIdent (if unit then ``FloatLib.Numerics.Backward.abs_sub_le_of_eq
      else ``FloatLib.Numerics.Backward.abs_sub_le_of_eq_mul)
    let goal ← mkFreshExprMVar body
    prove goal (← `(tactic| ((try dsimp only); refine $slopeLemma ?_; ring)))
    mkLambdaFVars binders (← instantiateMVars goal)

/-- A proof of `∃ x, p x`, the proposition `type`, from a witness and a proof of `p witness`. -/
def existsIntro (type witness proof : Lean.Expr) : MetaM Lean.Expr := do
  let type ← whnfR type
  unless type.isAppOfArity ``Exists 2 do
    throwError "roundoff: expected an existential statement, not {type}"
  return mkApp4 (mkConst ``Exists.intro type.getAppFn.constLevels!) (type.getArg! 0)
    (type.getArg! 1) witness proof

/-- The witness of `proof : ∃ x, p x` and the proof of `p witness`. -/
def choose (proof : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let witness ← mkAppM ``Classical.choose #[proof]
  return (witness, ← mkAppM ``Classical.choose_spec #[proof])

/-- The theorems that a finite result has finite operands, each with the head of the operation it
is about. -/
def finiteOperands : Array (Name × Name) := #[
  (``HAdd.hAdd, ``ExecFloat.Binary.isFinite_of_isFinite_add),
  (``HSub.hSub, ``ExecFloat.Binary.isFinite_of_isFinite_sub),
  (``HMul.hMul, ``ExecFloat.Binary.isFinite_of_isFinite_mul),
  (``HDiv.hDiv, ``ExecFloat.Binary.isFinite_left_of_isFinite_div),
  (``Model.add, ``Model.isFinite_of_isFinite_add),
  (``Model.sub, ``Model.isFinite_of_isFinite_sub),
  (``Model.mul, ``Model.isFinite_of_isFinite_mul),
  (``Model.fma, ``Model.isFinite_of_isFinite_fma),
  (``Model.div, ``Model.isFinite_left_of_isFinite_div),
  (``Model.cast, ``Model.isFinite_of_isFinite_cast)]

/-- The proposition that the floating-point value `value`, which `actual` decodes, is finite. -/
def finiteStatement (actual value : Lean.Expr) : MetaM Lean.Expr := do
  let finite ← if actual.isAppOf ``Model.toReal then mkAppM ``Model.isFinite #[value]
    else mkAppM ``ExecFloat.Binary.isFinite #[value]
  mkEq finite (mkConst ``Bool.true)

/-- The conjuncts of the proposition that `proof` proves, each with its proof. -/
partial def conjunctProofs (proof : Lean.Expr) : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let type ← whnfR (← instantiateMVars (← inferType proof))
  if type.isAppOfArity ``And 2 then
    return (← conjunctProofs (← mkAppM ``And.left #[proof])) ++
      (← conjunctProofs (← mkAppM ``And.right #[proof]))
  return #[(type, proof)]

/-- The finiteness facts that follow from `fact : isFinite value = true`, each with its proof:
the fact itself, those of the operands of `value` by `finiteOperands`, and theirs in turn. A loop
is first written as its registered loop, and a definition is expanded when no theorem applies.
A premise of a theorem other than the fact, such as the IEEE format, must be discharged. -/
partial def reflect (session : Session) (fact : Lean.Expr) (fuel : Nat := 64) :
    TacticM (Array (Lean.Expr × Lean.Expr)) := do
  let type ← instantiateMVars (← inferType fact)
  let found := #[(type, fact)]
  if fuel == 0 || !isFiniteness type then return found
  let observed := type.getArg! 1
  let value := stripHeadMetadata (← instantiateMVars observed.appArg!)
  let restated (next : Lean.Expr) : TacticM (Array (Lean.Expr × Lean.Expr)) := do
    let nextType ← mkEq (mkApp observed.appFn! next) (mkConst ``Bool.true)
    return found ++ (← reflect session (← mkExpectedTypeHint fact nextType) (fuel - 1))
  if value.headBeta != value then return ← restated value.headBeta
  if let .letE _ _ bound body _ := value then return ← restated (body.instantiate1 bound)
  if value.isFVar then
    if let some bound := (← value.fvarId!.getDecl).value? then return ← restated bound
    return found
  -- A loop, also one observed through a component of its state.
  let loopTerm := if value.isAppOfArity ``Prod.fst 3 || value.isAppOfArity ``Prod.snd 3 then
    stripHeadMetadata value.appArg! else value
  if (← isReduction loopTerm) || (← extension).loops.any (loopTerm.isAppOf ·.fold) then
    let (context, procedures) ← foldSimpContext session
    let normalized ← session.normalize `fold type context procedures
    if normalized.expr != type then
      return found ++ (← reflect session (← mkEqMP (← normalized.getProof) fact) (fuel - 1))
    -- A loop written another way, such as over `Fin n`, is written as its registered loop.
    unless (← loopOf? loopTerm).isSome || (← extension).conversions.isEmpty do
      let (converted, _) ← simp type (← conversionSimpContext)
      if converted.expr != type then
        return found ++ (← reflect session (← mkEqMP (← converted.getProof) fact) (fuel - 1))
    return found
  -- Negation keeps finiteness.
  if value.isAppOfArity ``Neg.neg 3 || value.isAppOfArity ``Model.neg 2 then
    for rule in [``ExecFloat.Binary.isFinite_neg, ``Model.isFinite_neg] do
      let derived? ← attempt? 1000 do
        let law ← mkAppM rule #[value.appArg!]
        let some (_, negated, _) := (← inferType law).eq? | return none
        unless ← isDefEq negated observed do return none
        return some (← mkEqTrans (← mkEqSymm law) fact)
      if let some proof := derived? then
        return found ++ (← reflect session proof (fuel - 1))
    return found
  let head := value.getAppFn.constName?.getD .anonymous
  for (operation, rule) in finiteOperands do
    unless operation == head do continue
    let derived? ← attempt? 2000 do
      let law ← mkConstWithFreshMVarLevels rule
      let (arguments, binders, _) ← forallMetaTelescopeReducing (← ruleType law)
      let mut matched := false
      for argument in arguments do
        if matched then break
        let premise ← instantiateMVars (← inferType argument)
        if isFiniteness premise then
          unless ← isDefEq premise type do
            trace[roundoff] "{rule}: {premise} does not match {type}"
            return none
          argument.mvarId!.assign fact
          matched := true
      unless matched do return none
      synthesizeInstances arguments binders
      for argument in arguments do
        let argument ← instantiateMVars argument
        if argument.isMVar && argument != fact then
          unless ← isProp (← argument.mvarId!.getType) do
            trace[roundoff] "{rule}: unassigned {← argument.mvarId!.getType}"
            return none
          unless ← discharge session argument.mvarId! do
            trace[roundoff] "{rule}: open premise {← argument.mvarId!.getType}"
            return none
      return some (← instantiateMVars (mkAppN law arguments))
    if let some proof := derived? then
      let mut all := found
      for (_, part) in ← conjunctProofs proof do
        all := all ++ (← reflect session part (fuel - 1))
      return all
  unless (`FloatLib).isPrefixOf head || (← getProjectionFnInfo? head).isSome do
    if let some unfolded ← unfoldDefinition? value then
      let unfolded := headZeta unfolded
      unless unfolded == value do return ← restated unfolded
  return found

/-- The proof among `facts` of the finiteness statement `type`, up to the spelling of the
format's parameters. -/
def findFact? (facts : Array (Lean.Expr × Lean.Expr)) (type : Lean.Expr) :
    MetaM (Option Lean.Expr) := do
  unless isFiniteness type do return none
  let found? ← facts.findM? fun (stated, _) => do
    if stated == type then return true
    unless isFiniteness stated &&
        (stated.getArg! 1).appArg!.getAppFn == (type.getArg! 1).appArg!.getAppFn do
      return false
    withNewMCtxDepth (withReducibleAndInstances (isDefEq stated type))
  return found?.map (·.2)

/-- Close each finiteness goal of `goals` that `facts` proves, and say whether one was closed. A
fact that was derived from the goal itself does not prove it. -/
def closeFinite (facts : Array (Lean.Expr × Lean.Expr)) (goals : Array MVarId) : MetaM Bool := do
  let mut closed := false
  for goal in goals do
    if ← goal.isAssigned then continue
    let type ← instantiateMVars (← goal.getType)
    let others ← facts.filterM fun (_, proof) => do
      return ((← instantiateMVars proof).findMVar? (· == goal)).isNone
    let some proof ← findFact? others type | continue
    goal.assign (← mkExpectedTypeHint proof type)
    closed := true
  return closed

/-- Close each finiteness goal of `goals` that follows from another of them, as the finiteness
of a sum follows from that of a value computed from the sum, and each that the context proves,
as that of a literal. -/
def closeAmong (session : Session) (goals : Array MVarId) : TacticM Unit := do
  for goal in goals do
    if ← goal.isAssigned then continue
    unless isFiniteness (← instantiateMVars (← goal.getType)) do continue
    discard <| closeFinite (← reflect session (mkMVar goal)) goals
  for goal in goals do
    if ← goal.isAssigned then continue
    unless isFiniteness (← instantiateMVars (← goal.getType)) do continue
    discard <| discharge session goal

/-- One perturbation of a loop step: that of the entries that took the same factors, or one of
those of a loop inside the step. -/
structure Component where
  /-- Its name in the statement. -/
  name : Name
  /-- Its type and its bound in its own step. -/
  shape : Shape
  /-- How it takes a factor of the accumulator. -/
  pattern : Pattern := .whole
  /-- The perturbation itself. -/
  term : Lean.Expr
  /-- A proof of `shape.statement term`. -/
  proof : Lean.Expr
  /-- The input reads it perturbs. -/
  slots : Array Nat := #[]
  /-- For a perturbation of a loop inside the step: the loop, and the position among its
  perturbations. -/
  fold? : Option (Nat × Nat) := none

/-- What the analysis of a loop step gives: the loop lemma applied to the step, up to the initial
accumulator, and the perturbations of one step. -/
structure Step where
  /-- The loop lemma applied to its step premises. -/
  applied : Lean.Expr
  /-- The step's condition, a function of the accumulator and the entry. -/
  condition : Lean.Expr
  /-- The exact step, a function of the scaled accumulator, the entry and its perturbations. -/
  exactStep : Lean.Expr
  /-- The local variable for the entry, which `shape` may read. -/
  binder : Lean.Expr
  /-- The perturbations of one step and their bounds in that step: one shape, or a right-nested
  pair of them. -/
  shape : Shape
  /-- How they take a factor of the accumulator. -/
  pattern : Pattern
  /-- Their names. -/
  names : Array Name
  /-- How they take a factor of the accumulator, as a function `fun c p => …`. -/
  scale : Lean.Expr
  /-- Whether their bounds read the entry. -/
  readsEntry : Bool
  /-- Whether the accumulator took no factor. -/
  fixed : Bool
  /-- Whether the step has no absolute error. -/
  exact : Bool
  /-- The growth of the factor the accumulator takes at each step; one when it takes none. -/
  growth : Lean.Expr
  /-- The slope of the exact step in its accumulator, a function of the entry. -/
  slope : Lean.Expr
  /-- The absolute error of one step, a function of the accumulator and the entry. -/
  absolute : Lean.Expr
  /-- When neither the slope nor the absolute error of a step depends on the step: both, and the
  proof that the growth, the slope and the absolute error are nonnegative under the condition. -/
  closed? : Option (Lean.Expr × Lean.Expr × Lean.Expr) := none
  /-- When finiteness passes from the result of a step to its accumulator: the finiteness
  property, the proof that it passes, and the rest of the step's condition, if any. The
  condition is then the finiteness of the step's result and that rest. -/
  finite? : Option (Lean.Expr × Lean.Expr × Option Lean.Expr) := none
  /-- A proof that scaling the accumulator scales the step (`Fold.homogeneous?`). -/
  homogeneous? : Option Lean.Expr := none
  /-- Whether a perturbation takes the square root of a factor (`Fold.root`). -/
  root : Bool := false
  /-- What the step keeps for a forward bound (`Fold.record?`). -/
  record : Record
  /-- The loops inside the step (`Fold.inner`). -/
  inner : Array Fold

/-- The backward analysis of one step of a loop observed by `observe`, for a symbolic accumulator
and entry. The exact computation of the step reads the scaled accumulator and perturbed entries.
Its perturbations are those of the entries, one for the entries that took the same factors, and
those of the loops inside the step. Scaling the step's exact computation by a symbolic factor
gives the way each of them takes a factor of the accumulator, and the law that the loop lemma
needs. The result applies the form of `List.fold_backward` that fits: without absolute error when
the step has none (`exact`), for an accumulator that takes no factor when the step moves none
onto it (`fixed`), and indexed by `Fin n` for a loop over `List.finRange n` (`overFin`). -/
def step (analyze : Q(ℝ) → Nat → BackM Form)
    (observe stepFunction elementType stateType : Lean.Expr) (scalable overFin : Bool)
    (origin? : Option FVarId) (fuel : Nat) : BackM Step := do
  let outer ← get
  let before ← getThe Analysis
  let session ← readThe Session
  -- The accumulator and the entry under the names of the program's step.
  let (accumulatorName, entryName) := match stepFunction with
    | .lam accumulatorName _ (.lam entryName _ _ _) _ =>
        (accumulatorName.eraseMacroScopes, entryName.eraseMacroScopes)
    | _ => (`accumulator, `value)
  let result ← withLocalDeclD accumulatorName stateType fun accumulator =>
      withLocalDeclD entryName elementType fun value => do
    let decoded : Q(ℝ) := (mkApp observe accumulator).headBeta
    modify fun state => { state with accumulator? := some {
      binder := accumulator, element := value, value := decoded, origin?, scalable } }
    let stepActual : Q(ℝ) := reducePairs
      (mkApp observe (mkAppN stepFunction #[accumulator, value]).headBeta).headBeta
    let form ← withTheReader Session (fun session => { session with nested := true })
      (analyze stepActual fuel)
    let state ← get
    let some scaled := state.accumulator? | throwError "roundoff: no loop accumulator in scope"
    let (treeSlots, treeFolds) := form.tree.leaves
    for index in treeSlots do
      if let some refusal := state.slots[index]!.pending? then throwError refusal
    -- One input must not be read with two perturbations, unless a forward bound is wanted.
    for index in (if (← read).forward then #[] else treeSlots) do
      let slot := state.slots[index]!
      for other in treeSlots do
        let otherSlot := state.slots[other]!
        if otherSlot.key == slot.key && otherSlot.delta? != slot.delta? then
          (← read).conflicts.modify (·.push (← keyName slot.key))
          throwError "roundoff: `{slot.key}` is read twice with different perturbations, so the \
            loop step has no backward-error form in it; choose other inputs with \
            `(perturb := [...])` or use `roundoff mixed theorem` for a forward bound"
    -- The perturbations of the step: one for the entries that took the same factors, and those
    -- of each loop inside the step.
    let mut components : Array Component := #[]
    let mut origins : Array (Array FVarId) := #[]
    for index in treeSlots do
      let slot := state.slots[index]!
      let (some delta, some bound) := (slot.delta?, slot.bound?) | continue
      let known? := components.findIdx? fun component =>
        component.fold?.isNone && component.term == delta
      match known? with
      | some position =>
        components := components.modify position fun component =>
          { component with slots := component.slots.push index }
        if let some origin := slot.origin? then
          unless origins[position]!.contains origin do
            origins := origins.modify position (·.push origin)
      | none =>
        components := components.push {
          name := default, shape := .real slot.growth, term := delta, proof := bound
          slots := #[index] }
        origins := origins.push slot.origin?.toArray
    for position in [0:components.size] do
      let name ← perturbationName origins[position]!
      components := components.modify position ({ · with name })
    for index in treeFolds do
      let witnesses := state.folds[index]!.witnesses
      for witness in witnesses, position in [0:witnesses.size] do
        components := components.push {
          name := witness.name, shape := witness.shape, pattern := witness.pattern
          term := witness.term, proof := witness.proof, fold? := some (index, position) }
    if components.isEmpty then
      unless (← read).forward do
        throwError MessageData.tagged `roundoff.noEntry m!"roundoff: no entry of the loop step \
          takes a perturbation, so the loop has no backward-error form in its entries: each \
          rounding moved onto the accumulator. Use `roundoff mixed theorem` for a forward bound."
      -- For a forward bound the step is given the zero perturbation, which nothing reads.
      components := components.push {
        name := `δ, shape := .real q((1 : ℝ)), pattern := .keep, term := q((0 : ℝ))
        proof := mkConst ``FloatLib.Numerics.Backward.abs_zero_le }
    let count := components.size
    let shape := Shape.nest (components.map (·.shape))
    let type := shape.type
    let stepGrowth := scaled.growth
    let exact := form.isExact
    let fixed := scaled.rho?.isNone
    if stepGrowth.containsFVar value.fvarId! || stepGrowth.containsFVar accumulator.fvarId! then
      throwError "roundoff: the relative error of the loop step depends on its entry"
    -- The step's exact computation at the scaled accumulator `s` and the perturbations `parts`.
    let viewAt (s : Lean.Expr) (parts : Array Lean.Expr) : BackM View := do
      let mut deltas : Array (Nat × Q(ℝ)) := #[]
      for component in components, part in parts do
        for index in component.slots do deltas := deltas.push (index, part)
      let mut folds : Array (Nat × Q(ℝ)) := #[]
      for index in treeFolds do
        let mut terms := #[]
        for component in components, part in parts do
          if component.fold?.any (·.1 == index) then terms := terms.push part
        folds := folds.push (index, ← state.folds[index]!.at terms)
      return { accumulator? := some s, deltas, folds }
    let perturbedSlope : MessageData := m!"roundoff: the loop step has an absolute error and \
      multiplies its accumulator by a perturbed loop of its own or by a quotient with a \
      perturbed divisor, which the backward-error mode does not carry through the loop. Use \
      `roundoff mixed theorem` for a forward bound."
    let (exactStep, slope?, readsEntry, perturbed) ← withLocalDeclD `s q(ℝ) fun s =>
        withLocalDeclD `δ type fun p => do
      let view ← viewAt s (← projections p count)
      let body ← form.tree.render view
      if body.containsFVar accumulator.fvarId! then
        throwError "roundoff: the loop step reads its accumulator where {(← wanted).2} does \
          not follow it: a step must read one numerical component of its state, in sums and \
          products. Use `roundoff mixed theorem` for a forward bound."
      let stated ← shape.statement p
      if stated.containsFVar accumulator.fvarId! then
        throwError "roundoff: the relative error of the loop step depends on its accumulator"
      -- A slope that reads the perturbations gets its bound once theirs are stated.
      let (slope?, perturbed) ← if exact then pure (none, false) else do
        let some slope ← form.tree.slope view |
          throwError "roundoff: the loop step does not read its accumulator"
        if slope.containsFVar p.fvarId! then
          if (← read).forward then
            throwError "roundoff: the loop step multiplies its accumulator by a perturbed entry \
              and has an absolute error, which the closed forward bound does not carry through \
              the loop. Use `roundoff mixed theorem` for a forward bound."
          pure (none, true)
        else pure (some slope, false)
      return (← mkLambdaFVars #[s, value, p] body, slope?, stated.containsFVar value.fvarId!,
        perturbed)
    let unitSlope := slope?.any (·.nat? == some 1)
    -- How the perturbations take a factor of the accumulator, and the law that scaling the
    -- accumulator scales the step: the step's exact computation is scaled by a symbolic factor.
    let symbolic ← withLocalDeclD `c q(ℝ) fun c => do
      let c' : Q(ℝ) := c
      withLocalDeclD `h q(0 ≤ $c') fun nonneg => withLocalDeclD `g q(ℝ) fun g => do
      let g' : Q(ℝ) := g
      withLocalDeclD `hc q(|$c' - 1| ≤ $g' - 1) fun hc => withLocalDeclD `s q(ℝ) fun s =>
      withLocalDeclD `δ type fun p => do
        let parts ← projections p count
        let mut statements : Array (Name × Lean.Expr) := #[]
        for component in components, part in parts do
          statements := statements.push (`hδ, ← component.shape.statement part)
        withLocalDeclsDND statements fun hypotheses => do
          let saved ← get
          let mut slots := saved.slots
          let mut folds := saved.folds
          for component in components, part in parts, hypothesis in hypotheses do
            for index in component.slots do
              slots := slots.modify index
                ({ · with delta? := some part, bound? := some hypothesis })
            if let some (index, position) := component.fold? then
              folds := folds.modify index (·.setWitness position part hypothesis)
          let s' : Q(ℝ) := s
          set { saved with
            slots, folds
            accumulator? := some { scaled with
              value := s', rho? := none, bound? := none, growth := q(1), scalable := true } }
          let outcome? ← try
              let law ← withReader ({ · with followAccumulator := true })
                (form.tree.scale c' g' hc (some nonneg))
              let after ← get
              let mut scaledParts : Array Lean.Expr := #[]
              let mut patterns : Array Pattern := #[]
              for component in components, part in parts do
                let scaledPart ← match component.fold? with
                  | some (index, position) =>
                    let witnesses := after.folds[index]!.witnesses
                    unless witnesses.size == saved.folds[index]!.witnesses.size do
                      throwError "roundoff: a loop inside the step takes its first factor from \
                        the accumulator"
                    pure witnesses[position]!.term
                  | none =>
                    let deltas := component.slots.map fun index => after.slots[index]!.delta?
                    unless deltas.all (some · == deltas[0]?) do
                      throwError "roundoff: an entry of the loop step is read both squared and \
                        not"
                    pure ((deltas[0]?.getD none).getD part)
                let pattern ← if scaledPart == part then pure Pattern.keep
                  else if scaledPart == (← component.shape.scaleTerm component.pattern part c) then
                    pure component.pattern
                  else if scaledPart == (← component.shape.scaleTerm .root part c) then
                    pure Pattern.root
                  else throwError "roundoff: unexpected perturbation {scaledPart}"
                scaledParts := scaledParts.push scaledPart
                patterns := patterns.push pattern
              -- An entry that had no perturbation must not take one from the accumulator.
              for index in treeSlots do
                if state.slots[index]!.delta?.isNone && after.slots[index]!.delta?.isSome then
                  throwError "roundoff: an entry of the loop step takes its first factor from \
                    the accumulator"
              pure (some (law, scaledParts, patterns))
            catch error =>
              trace[roundoff] "the loop step does not scale with its accumulator: \
                {error.toMessageData}"
              pure none
          set saved
          let some (law, scaledParts, patterns) := outcome? | return none
          let scaledTerm ← tuple scaledParts
          let hidden := #[g, hc, s, nonneg] ++ hypotheses
          if hidden.any fun binder => scaledTerm.containsFVar binder.fvarId! then return none
          let scale ← mkLambdaFVars #[c, p] scaledTerm
          let root := law.containsFVar nonneg.fvarId!
          if (#[g, hc] ++ hypotheses).any fun binder => law.containsFVar binder.fvarId! then
            return none
          let s' : Q(ℝ) := s
          let left : Q(ℝ) := (mkApp3 exactStep q($s' * $c') value scaledTerm).headBeta
          let right : Q(ℝ) := (mkApp3 exactStep s value p).headBeta
          let proof ← mkEqSymm law
          let expected : Q(Prop) := q($left = $right * $c')
          unless ← isDefEq (← inferType proof) expected do return none
          let proof ← mkExpectedTypeHint proof expected
          let homogeneous ← mkLambdaFVars (if root then #[c, nonneg, s, value, p]
            else #[c, s, value, p]) proof
          return some (scale, Pattern.nest patterns, homogeneous, root)
    let (scale, pattern, homogeneous?, root) := match symbolic with
      | some (scale, pattern, homogeneous, root) => (scale, pattern, some homogeneous, root)
      | none => (default, Pattern.whole, none, false)
    let small? ← growthLeTwo? stepGrowth
    let unsigned : MessageData := m!"roundoff: the loop step squares a perturbed entry, which \
      takes the square root of the factor of the accumulator, and that factor is not known to \
      be nonnegative; use `roundoff mixed theorem` for a forward bound"
    -- The bounds of the perturbations after `steps` further steps.
    let shapeAfter (steps : Q(ℕ)) : Shape := shape.scaleGrowth pattern q($stepGrowth ^ $steps)
    let bounds : Lean.Expr ← if fixed then
        withLocalDeclD `δ type fun p => do mkLambdaFVars #[value, p] (← shape.statement p)
      else
        withLocalDeclD `steps q(ℕ) fun steps => withLocalDeclD `δ type fun p => do
          mkLambdaFVars #[steps, value, p] (← (shapeAfter steps).statement p)
    -- A slope that reads the perturbations of the step, as a function of the entry and of
    -- them, with its bound and the proof of the bound from the bounds the step states.
    let bounded? ← if !perturbed then pure none else
      withLocalDeclD `s q(ℝ) fun s => withLocalDeclD `δ type fun p => do
        let initial := if fixed then shape else shapeAfter q(0)
        withLocalDeclD `hδ (← initial.statement p) fun hp => do
          let parts ← projections p count
          let proofs ← conjuncts hp count
          let mut facts : Array (Nat × Q(ℝ) × Lean.Expr) := #[]
          for component in components, proof in proofs, position in [0:count] do
            let .real raw _ := component.shape | continue
            let .real grown _ := initial.component position count | continue
            let proof ← if grown == raw then pure proof
              else mkAppM ``FloatLib.Numerics.Backward.slot_stop #[proof]
            for index in component.slots do facts := facts.push (index, raw, proof)
          let some coefficient ← form.tree.coefficient |
            throwError "roundoff: the loop step does not read its accumulator"
          let view ← viewAt s parts
          let slope ← coefficient.render view
          let (bound, proof) ← coefficient.magnitude view p.fvarId! facts perturbedSlope
          if slope.containsFVar s.fvarId! || bound.containsFVar s.fvarId! then
            throwError perturbedSlope
          return some (← mkLambdaFVars #[value, p] slope, (bound : Lean.Expr),
            ← mkLambdaFVars #[value, p, hp] proof)
    let slopeBody : Q(ℝ) := match slope?, bounded? with
      | _, some (_, bound, _) => bound
      | some slope, none => if unitSlope then slope else q(|$slope|)
      | none, none => q(1)
    let slopeFunction ← mkLambdaFVars #[value] slopeBody
    -- Each perturbation that takes the factor of a step has then taken one more.
    let growthLaw? ← if fixed then pure none else do
        let law ← withLocalDeclD `m q(ℕ) fun m => withLocalDeclD `δ type fun p =>
            withLocalDeclD `c q(ℝ) fun c => do
          let m' : Q(ℕ) := m
          let c' : Q(ℝ) := c
          let stepGrowth : Q(ℝ) := stepGrowth
          let before := shapeAfter m'
          withLocalDeclD `hδ (← before.statement p) fun hp =>
              withLocalDeclD `hc q(|$c' - 1| ≤ $stepGrowth - 1) fun hc => do
            let leaf (root : Bool) (delta grown bound : Lean.Expr) :
                BackM (Lean.Expr × Lean.Expr) := do
              let raw : Q(ℝ) := grown.getArg! 4
              let (factor, hfactor) ← if root then do
                  let some small := small? | throwError unsigned
                  let nonneg ←
                    mkAppM ``FloatLib.Numerics.Backward.nonneg_of_abs_sub_one_le #[hc, small]
                  pure ((q(Real.sqrt $c') : Lean.Expr),
                    ← mkAppM ``FloatLib.Numerics.Backward.abs_sqrt_sub_one_le #[nonneg, hc])
                else pure (c, hc)
              return (q($raw * $stepGrowth ^ ($m' + 1)),
                ← mkAppM ``FloatLib.Numerics.Backward.slot_growth
                  #[elementType, raw, stepGrowth, m, value, delta, factor, bound, hfactor])
            let (_, proof) ← before.scaleM pattern p hp c leaf
            mkLambdaFVars #[m, value, p, c, hp, hc] proof
        pure (some law)
    -- The perturbations the step took, and their bounds before any later step.
    let taken ← tuple (components.map (·.term))
    let whole ← conjunction (components.map (·.proof))
    let started ← if fixed then pure whole else do
        let stepGrowth : Q(ℝ) := stepGrowth
        let (_, started) ← shape.restateM pattern taken whole fun _ grown bound => do
          let grown : Q(ℝ) := grown
          return (.real q($grown * $stepGrowth ^ 0),
            ← mkAppM ``FloatLib.Numerics.Backward.slot_start #[bound, stepGrowth])
        pure started
    let absolute ← mkLambdaFVars #[accumulator, value] form.budget
    let lemmaName := match fixed, exact, overFin with
      | false, false, false => ``List.fold_backward
      | false, false, true => ``List.fold_backward_finRange
      | false, true, false => ``List.fold_backward_exact
      | false, true, true => ``List.fold_backward_exact_finRange
      | true, false, false => ``List.fold_backward_fixed
      | true, false, true => ``List.fold_backward_fixed_finRange
      | true, true, false => ``List.fold_backward_fixed_exact
      | true, true, true => ``List.fold_backward_fixed_exact_finRange
    let mut candidates := (← getThe Analysis).pending.extract before.pending.size
      (← getThe Analysis).pending.size
    -- The finiteness that the step's rules need follows from the finiteness of its result. When
    -- that of the accumulator does too, the loop needs the finiteness of its result only.
    let mut passes? : Option (Lean.Expr × Lean.Expr) := none
    if let some stepValue := decodedValue? stepActual then
      let root ← mkFreshExprMVar (← finiteStatement stepActual stepValue)
      let facts ← reflect session root
      let kept ← finiteStatement stepActual ((decodedValue? decoded).getD accumulator)
      trace[roundoff] "finiteness from the step's result: {facts.map (·.1)}"
      if let some keptProof ← findFact? facts kept then
        discard <| closeFinite facts candidates
        let passes ← withLocalDeclD `finite (← inferType root) fun finite => do
          let proof := (← instantiateMVars keptProof).replace fun term =>
            if term == root then some finite else none
          mkLambdaFVars #[accumulator, value, finite] proof
        let property ← mkLambdaFVars #[accumulator] kept
        passes? := some (property, passes)
        candidates := #[root.mvarId!] ++ candidates
    closeAmong session candidates
    let constant := !exact && bounded?.isNone && !slopeBody.containsFVar value.fvarId! &&
      !form.budget.containsFVar value.fvarId! && !form.budget.containsFVar accumulator.fvarId!
    let (applied, condition, rest?, closed?) ← withConditions candidates session.comparisons
        fun stated evidence => do
      let condition ← mkLambdaFVars #[accumulator, value] stated
      let rest? ← if passes?.isSome && stated.isAppOfArity ``And 2 then
          pure (some (← mkLambdaFVars #[accumulator, value] stated.appArg!))
        else pure none
      -- The signs that the closed form of the absolute error needs, at a visited step.
      let closed? ← if !constant then pure none else do
        let unit : Lean.Expr := q((zero_le_one : (0 : ℝ) ≤ 1))
        let growthSign ← match scaled.bound? with
          | some bound => mkAppM ``FloatLib.Numerics.Backward.growth_nonneg #[bound]
          | none => pure unit
        let slopeSign ← match slope? with
          | some slope => (if unitSlope then pure unit else mkAppM ``abs_nonneg #[slope])
          | none => pure unit
        let budgetSign ← mkAppM ``FloatLib.Numerics.Backward.budget_nonneg #[form.proof]
        let signs ← mkAppM ``And.intro
          #[growthSign, ← mkAppM ``And.intro #[slopeSign, budgetSign]]
        pure (some ((slopeBody : Lean.Expr), (form.budget : Lean.Expr),
          ← mkLambdaFVars #[accumulator, value, evidence] signs))
      -- The lemma at this step, and the premises its statement leaves.
      let parameters := match fixed, exact with
        | false, false =>
            #[observe, stepFunction, exactStep, scale, stepGrowth, slopeFunction, bounds, absolute,
              condition]
        | false, true => #[observe, stepFunction, exactStep, scale, stepGrowth, bounds, condition]
        | true, false =>
            #[observe, stepFunction, exactStep, slopeFunction, bounds, absolute, condition]
        | true, true => #[observe, stepFunction, exactStep, bounds, condition]
      unless fixed || homogeneous?.isSome do
        throwError "roundoff: scaling the accumulator of the loop step does not scale the step \
          {exactStep}, so the loop has no backward-error form; use `roundoff mixed theorem` for \
          a forward bound"
      let head ← mkAppM lemmaName parameters
      let mut applied := head
      let mut remaining ← whnfR (← inferType head)
      unless fixed do
        let some homogeneous := homogeneous? | throwError "roundoff: no law for the loop step"
        let premise := remaining.bindingDomain!
        let law ← withLocalDeclD `c q(ℝ) fun c =>
            withLocalDeclD `h (premise.bindingBody!.bindingDomain!.instantiate1 c) fun h => do
          if root then
            let some small := small? | throwError unsigned
            mkLambdaFVars #[c, h] (mkApp2 homogeneous c
              (← mkAppM ``FloatLib.Numerics.Backward.nonneg_of_abs_sub_one_le #[h, small]))
          else mkLambdaFVars #[c, h] (mkApp homogeneous c)
        applied := mkApp applied law
        remaining ← whnfR remaining.bindingBody!
      unless exact do
        applied := mkApp applied (← slopeLaw remaining.bindingDomain! unitSlope
          (bounded?.map fun (slope, _, proof) => (slope, proof)))
        remaining ← whnfR remaining.bindingBody!
      if let some growthLaw := growthLaw? then
        applied := mkApp applied growthLaw
        remaining ← whnfR remaining.bindingBody!
      -- The step's facts, for the factor and the perturbations it took.
      let main ← if exact then mkAppM ``eq_of_abs_sub_nonpos #[form.proof] else pure form.proof
      let conclusion := (← instantiateForall remaining.bindingDomain! #[accumulator, value])
        |>.bindingBody!
      let stepProof ← if fixed then
          existsIntro conclusion taken (← mkAppM ``And.intro #[started, main])
        else do
          let (some rho, some accumulatorBound) := (scaled.rho?, scaled.bound?) |
            throwError "roundoff: the scaled accumulator has no bound"
          let fact ← mkAppM ``And.intro #[accumulatorBound, ← mkAppM ``And.intro #[started, main]]
          let inner := (mkApp ((← whnfR conclusion).getArg! 1) rho).headBeta
          existsIntro conclusion rho (← existsIntro inner taken fact)
      applied := mkApp applied (← mkLambdaFVars #[accumulator, value, evidence] stepProof)
      return (applied, condition, rest?, closed?)
    return ({ applied, condition, exactStep, binder := value, shape, pattern, scale, readsEntry
              names := components.map (·.name), fixed, exact
              growth := if fixed then q((1 : ℝ)) else stepGrowth
              slope := slopeFunction, absolute, closed?, homogeneous?, root
              inner := state.folds
              record := {
                tree := form.tree, slots := state.slots, accumulator := scaled
                parts := components.map fun component => (component.slots, component.fold?)
                binders := #[← accumulator.fvarId!.getDecl, ← value.fvarId!.getDecl] }
              finite? := passes?.map fun (property, passes) => (property, passes, rest?) } : Step)
  set outer
  modifyThe Analysis fun analysis => { analysis with pending := before.pending }
  return result

/-- Where a loop starts. -/
inductive Start where
  /-- From an exact zero, with the proof that the decoded initial value is zero. -/
  | zero (proof : Lean.Expr)
  /-- From an input that may take a perturbation. -/
  | input (origin? : Option FVarId)
  /-- From a value that takes none: an input, or an exact value such as a literal, then with
  the value as the reference states it and the proof that the decoded initial value is it. -/
  | fixed (exact? : Option (Lean.Expr × Lean.Expr) := none)

/-- The backward analysis of a loop `input.foldl stepFunction initial` observed by `observe`. The
step is analyzed once (`step`), and the loop lemma then gives the perturbations: those of each
step, and one of the initial value when the loop starts from an input that takes the factors of
the accumulator. The loop's reference is the exact loop on perturbed entries, and its absolute
error is in closed form when no step's slope or error depends on the step. -/
def fold (analyze : Q(ℝ) → Nat → BackM Form) (actual : Q(ℝ)) (observe source : Lean.Expr)
    (loop : Loop) (fuel : Nat) : BackM Form := do
  unless loop.fold == ``List.foldl do
    throwError "roundoff: {(← wanted).2} has no loop rule for `{.ofConstName loop.fold}`; use \
      `roundoff mixed theorem` for a forward bound"
  let arguments := source.getAppArgs
  let stepFunction := arguments[loop.step]!
  let initial := arguments[loop.initial]!
  let input := arguments[loop.input]!
  let elementType := arguments[loop.element]!
  let stateType := arguments[loop.state]!
  unless ← storedEntries loop input (← readThe Session).carriers do
    throwError "roundoff: the loop reads the entries of the computed container {input} as \
      exact data, so its reference would omit their rounding; write the producer into the step"
  let overFin := input.isAppOfArity ``List.finRange 1
  -- Where the loop starts decides whether its accumulator may take a factor.
  let initialValue : Q(ℝ) := (mkApp observe initial).headBeta
  let computedStart : MessageData := m!"roundoff: the loop starts from the computed value \
    {initial}, which {(← wanted).2} does not follow; start from zero or from an input"
  let initialForm ← analyze initialValue fuel
  unless initialForm.isExact do throwError computedStart
  let start ← match initialForm.tree with
    | .const _ true _ =>
        pure (Start.zero (← mkExpectedTypeHint
          (← mkAppM ``eq_of_abs_sub_nonpos #[initialForm.proof]) q($initialValue = 0)))
    | .slot index =>
        let slot := (← get).slots[index]!
        pure (if slot.perturbable then Start.input slot.origin? else Start.fixed)
    | .const value false _ =>
        let value : Q(ℝ) := value
        if value == initialValue then pure Start.fixed else
          pure (Start.fixed (some (value, ← mkExpectedTypeHint
            (← mkAppM ``eq_of_abs_sub_nonpos #[initialForm.proof]) q($initialValue = $value))))
    | _ => throwError computedStart
  -- A loop inside a step that traverses the outer entry perturbs the outer input.
  let mut origin? ← headVariable? input
  if let some accumulator := (← get).accumulator? then
    if origin? == some accumulator.element.fvarId! then origin? := accumulator.origin?
  let analyzeStep : BackM Step := step analyze observe stepFunction elementType stateType
    (!(start matches .fixed _)) overFin origin? fuel
  let saved ← get
  let pending := (← getThe Analysis).pending
  let result ← try analyzeStep catch error =>
    -- When every rounding moved onto the accumulator, the products of the step give theirs to
    -- their right factors instead.
    if (← read).preferRight || !error.toMessageData.hasTag (· == `roundoff.noEntry) then
      throw error
    set saved
    modifyThe Analysis fun analysis => { analysis with pending }
    withReader ({ · with preferRight := true }) analyzeStep
  let length : Q(ℕ) ← if overFin then pure (input.getArg! 0) else mkAppM ``List.length #[input]
  -- The condition is required at the states the loop visits. When finiteness passes from the
  -- result of a step to its accumulator, it is required of the result of the loop only.
  let require (type : Lean.Expr) : BackM Lean.Expr := do
    let goal ← mkFreshExprMVar type
    modifyThe Analysis fun analysis =>
      { analysis with pending := analysis.pending.push goal.mvarId! }
    return goal
  let valid ← match result.finite? with
    | some (property, passes, rest?) =>
        let final ← require (mkApp property source).headBeta
        let finite ← mkAppOptM ``List.AllSteps.of_foldl #[none, none, some stepFunction,
          some property, some passes, some initial, some input, some final]
        match rest? with
        | some rest =>
            let other ← require (← mkAppM loop.allSteps #[stepFunction, rest, initial, input])
            mkAppM ``List.AllSteps.and #[finite, other]
        | none => pure finite
    | none => require (← mkAppM loop.allSteps #[stepFunction, result.condition, initial, input])
  let proof ← mkAppM' result.applied
    (if overFin then #[initial, valid] else #[initial, input, valid])
  -- The perturbations the lemma gives, each with its bound as the lemma states it.
  let growth : Q(ℝ) := result.growth
  let mut rest := proof
  let mut startWitness? : Option Witness := none
  let mut startDelta? : Option Lean.Expr := none
  unless result.fixed do
    let (startDelta, spec) ← choose rest
    rest ← mkAppM ``And.right #[spec]
    startDelta? := some startDelta
    if let .input startOrigin? := start then
      startWitness? := some {
        name := (← perturbationName startOrigin?.toArray).appendAfter "₀"
        shape := .real q($growth ^ $length), term := startDelta
        proof := ← mkAppM ``And.left #[spec] }
  let (entryTerm, spec) ← choose rest
  let (entryProof, main) ← if overFin then
      pure (← mkAppM ``And.left #[spec], ← mkAppM ``And.right #[spec])
    else do
      let tail ← mkAppM ``And.right #[spec]
      pure (← mkAppM ``And.intro #[← mkAppM ``And.left #[spec], ← mkAppM ``And.left #[tail]],
        ← mkAppM ``And.right #[tail])
  -- The perturbations of the step at position `k` took the factors of the later steps.
  let later (position : Q(ℕ)) (shape : Shape) : Shape :=
    if result.fixed then shape
    else shape.scaleGrowth result.pattern q($growth ^ ($length - 1 - $position))
  let binders : Name × Name := match stepFunction with
    | .lam accumulatorName _ (.lam entryName _ _ _) _ =>
        (accumulatorName.eraseMacroScopes, entryName.eraseMacroScopes)
    | _ => (`s, `j)
  -- The entry at a position of a list, for bounds that read it.
  let entryAt ← withLocalDeclD `k q(ℕ) fun k => do
    let inside ← mkAppM ``LT.lt #[k, length]
    withLocalDeclD `hk inside fun hk => do
      let entry ← if overFin then pure k else listEntry elementType input k hk
      pure fun (position proof : Lean.Expr) => entry.replaceFVars #[k, hk] #[position, proof]
  let entryShape : Shape := if overFin then
      .family elementType (fun j =>
        later (mkApp2 (mkConst ``Fin.val) length j) (result.shape.replaceFVar result.binder j))
        binders.2
    else .list length fun k hk =>
      later k (if result.readsEntry then result.shape.replaceFVar result.binder (entryAt k hk)
        else result.shape)
  let entryStated ← entryShape.statement entryTerm
  unless ← isDefEq entryStated (← inferType entryProof) do
    throwError "roundoff: the perturbations of the loop over `{input}` have the bound \
      {← inferType entryProof}, not {entryStated}"
  let distinct := result.names.foldl (init := #[]) fun found name =>
    if found.contains name then found else found.push name
  let name := match distinct with
    | #[name] => name
    | names => Name.mkSimple
        (names.foldl (init := "δ") fun joined name =>
          joined ++ String.join ((name.toString.toList.drop 1).map toString))
  let entries : Witness := {
    name, shape := entryShape, pattern := .each result.pattern, term := entryTerm
    proof := ← mkExpectedTypeHint entryProof entryStated }
  let loopNode : Fold := {
    overFin, exactStep := result.exactStep, elementType, input, entries, startWitness?
    names := result.names, scale := result.scale
    start? := match start with
      | .zero _ => none
      | .fixed (some (value, _)) => some value
      | _ => some initialValue
    startOrigin? := match start with
      | .input origin? => some origin?
      | _ => none
    homogeneous? := result.homogeneous?, root := result.root, binders
    record? := some result.record, inner := result.inner }
  let budget : Q(ℝ) ← if result.exact then pure q(0) else
    pure ((← whnfR (← instantiateMVars (← inferType main))).getArg! 3)
  let statedAt (startTerm : Lean.Expr) : MetaM Lean.Expr := do
    let loopTerm ← loopNode.loop startTerm entryTerm
    return if result.exact then q($actual = $loopTerm) else q(|$actual - $loopTerm| ≤ $budget)
  -- The start as the lemma states it, and as the reference reads it: zero from an exact zero,
  -- and the value of a literal.
  let lemmaStart : Q(ℝ) := match startDelta? with
    | some startDelta =>
        let startDelta : Q(ℝ) := startDelta
        q($initialValue * (1 + $startDelta))
    | none => initialValue
  let main ← mkExpectedTypeHint main (← statedAt lemmaStart)
  let equality? ← match start, startDelta? with
    | .zero zeroProof, some startDelta =>
        let startDelta : Q(ℝ) := startDelta
        pure (some (← mkExpectedTypeHint
          (← mkAppM ``mul_eq_zero_of_left #[zeroProof, q(1 + $startDelta)]) q($lemmaStart = 0)))
    | .zero zeroProof, none => pure (some zeroProof)
    | .fixed (some (_, equality)), _ => pure (some equality)
    | _, _ => pure none
  let main ← match equality? with
    | some equality =>
        let motive ← withLocalDeclD `start q(ℝ) fun startValue => do
          mkLambdaFVars #[startValue] (← statedAt startValue)
        mkAppM ``Eq.mp #[← mkAppM ``congrArg #[motive, equality], main]
    | none => pure main
  let main ← if result.exact then mkAppM ``FloatLib.Numerics.Backward.of_eq #[main] else pure main
  -- The absolute error in closed form, when no step's slope or absolute error depends on it.
  let (main, budget) ← match result.closed? with
    | some (slope, absolute, signs) =>
        let slopes ← withLocalDeclD `value elementType fun value => do
          mkLambdaFVars #[value] (← mkAppM ``le_refl #[slope])
        let errors ← withLocalDeclD `state stateType fun state =>
          withLocalDeclD `value elementType fun value => do
            mkLambdaFVars #[state, value] (← mkAppM ``le_refl #[absolute])
        let closed ← mkAppM ``List.foldBackwardAbsolute_le_geom #[stepFunction, result.slope,
          result.growth, slope, absolute, result.absolute, result.condition, signs, slopes, errors,
          initial, input, valid]
        let main ← mkAppM ``le_trans #[main, closed]
        let budget : Q(ℝ) := (← whnfR (← instantiateMVars (← inferType main))).getArg! 3
        pure (main, budget)
    | none => pure (main, budget)
  let index := (← get).folds.size
  modify fun state => { state with folds := state.folds.push loopNode }
  tidy ⟨.fold index, budget, main⟩

/-- The backward analysis of the real value `actual`: the exact real operations of a local rule's
reference, exact data, reads of inputs, components of pairs, branches, maxima and minima, loops,
and floating-point operations through their local rules, after the expansion of definitions. -/
partial def analyze (actual : Q(ℝ)) (fuel : Nat) : BackM Form := do
  let actual : Q(ℝ) ← instantiateMVars actual
  let actual : Q(ℝ) := stripHeadMetadata actual
  if actual.headBeta != actual then return ← analyze actual.headBeta fuel
  if fuel == 0 then throwError "roundoff: source expansion exceeded its traversal limit"
  let fuel := fuel - 1
  let name := actual.getAppFn.constName?.getD .anonymous
  let arguments := actual.getAppArgs
  let overReals := arguments[0]?.any (·.isConstOf ``Real)
  let binary := arguments.size == 6 && overReals
  -- The exact real operations of a local rule's reference.
  if binary && name == ``HAdd.hAdd then
    let left ← settled (← analyze arguments[4]! fuel)
    let right ← settled (← analyze arguments[5]! fuel)
    let (a, b) := (left.budget, right.budget)
    return ← tidy ⟨.add left.tree right.tree, q($a + $b),
      ← mkAppM ``FloatLib.Numerics.Backward.add #[left.proof, right.proof]⟩
  if binary && name == ``HSub.hSub then
    let left ← settled (← analyze arguments[4]! fuel)
    let right ← settled (← analyze arguments[5]! fuel)
    let (a, b) := (left.budget, right.budget)
    return ← tidy ⟨.sub left.tree right.tree, q($a + $b),
      ← mkAppM ``FloatLib.Numerics.Backward.sub #[left.proof, right.proof]⟩
  if binary && name == ``HMul.hMul then
    let x : Q(ℝ) := arguments[4]!
    let y : Q(ℝ) := arguments[5]!
    let left ← analyze x fuel
    let right ← analyze y fuel
    let (a, b) := (left.budget, right.budget)
    return ← tidy (← settle ⟨.mul left.tree right.tree, q($a * |$y| + (|$x| + $a) * $b),
      ← mkAppM ``FloatLib.Numerics.Backward.mul #[left.proof, right.proof]⟩)
  if binary && name == ``HDiv.hDiv then
    let y : Q(ℝ) := arguments[5]!
    let left ← analyze arguments[4]! fuel
    let right ← settled (← analyze y fuel)
    -- A quotient by an exact zero is never finite, so the premise of a statement would be false.
    if right.tree matches .const _ true _ then
      throwError "roundoff: a required numerical condition is false: `{actual}` divides by zero"
    unless right.isExact do
      -- For a forward bound a divisor with an absolute error must stay away from zero: a
      -- premise of the statement.
      unless (← read).forward && (← get).accumulator?.isNone do
        throwError refusal actual m!"the divisor `{y}` has an absolute error"
      let x : Q(ℝ) := arguments[4]!
      let (a, b) := (left.budget, right.budget)
      let apart ← mkFreshExprMVar q($b < |$y|)
      modifyThe Analysis fun analysis =>
        { analysis with pending := analysis.pending.push apart.mvarId! }
      return ← tidy ⟨.div left.tree right.tree, q(($a * |$y| + |$x| * $b) / (|$y| * (|$y| - $b))),
        ← mkAppM ``FloatLib.Numerics.Backward.div_of_lt #[left.proof, right.proof, apart]⟩
    let a := left.budget
    return ← tidy (← settle ⟨.div left.tree right.tree, q($a / |$y|),
      ← mkAppM ``FloatLib.Numerics.Backward.div #[left.proof, right.proof]⟩)
  if (name == ``Max.max || name == ``Min.min) && arguments.size == 4 && overReals then
    let left ← settled (← analyze arguments[2]! fuel)
    let right ← settled (← analyze arguments[3]! fuel)
    let (a, b) := (left.budget, right.budget)
    let tree : Tree := .lattice (name == ``Max.max) left.tree right.tree
    let proof ← mkAppM (if name == ``Max.max then ``FloatLib.Numerics.Backward.maximum
      else ``FloatLib.Numerics.Backward.minimum) #[left.proof, right.proof]
    -- The larger of a budget and zero is the budget.
    if right.isExact && !left.isExact then
      return ⟨tree, a, ← mkAppM ``LE.le.trans_eq #[proof, ← mkAppM ``max_eq_left
        #[← mkAppM ``FloatLib.Numerics.Backward.budget_nonneg #[left.proof]]]⟩
    if left.isExact && !right.isExact then
      return ⟨tree, b, ← mkAppM ``LE.le.trans_eq #[proof, ← mkAppM ``max_eq_right
        #[← mkAppM ``FloatLib.Numerics.Backward.budget_nonneg #[right.proof]]]⟩
    return ← tidy ⟨tree, q(max $a $b), proof⟩
  if name == ``Real.sqrt && arguments.size == 1 then
    let operand ← settled (← analyze arguments[0]! fuel)
    let a := operand.budget
    return ← tidy ⟨.sqrt operand.tree, q(Real.sqrt $a),
      ← mkAppM ``FloatLib.Numerics.Backward.sqrt #[operand.proof]⟩
  if name == ``Neg.neg && arguments.size == 3 && overReals then
    let operand ← analyze arguments[2]! fuel
    return ← settle { operand with
      tree := .neg operand.tree
      proof := (← mkAppM ``FloatLib.Numerics.Backward.neg #[operand.proof]) }
  let exactLeaf : BackM Form := do
    let proof ← mkAppM ``FloatLib.Numerics.exact_error #[actual]
    -- For a forward bound an exact value other than zero may take a rounding as an input does.
    if (← read).forward && actual.nat? != some 0 then
      let index := (← get).slots.size
      modify fun state => { state with slots := state.slots.push { key := actual } }
      return ⟨.slot index, q(0), proof⟩
    return ⟨.const actual (actual.nat? == some 0), q(0), proof⟩
  unless name == ``ExecFloat.Binary.toReal || name == ``Model.toReal do
    -- Literals and casts of index data are exact and take no perturbation.
    if literalHeads.contains name || (← exactRealData? actual (← readThe Session).carriers) then
      return ← exactLeaf
    if actual.isFVar then
      if let some value := (← actual.fvarId!.getDecl).value? then return ← analyze value fuel
      return ← exactLeaf
    -- The cast of an integer computed from numerical values would keep them in the reference.
    if let some integer ← castInteger? actual then
      unless ← indexClosed integer (cache? := (← readThe Session).carriers) do
        throwError "roundoff: {actual} casts an integer computed from real or floating-point \
          values, so the reference would keep them; compute it from index data"
    -- So is a real term that reads no floating-point value, such as a power of two, and a
    -- rounded literal, which is the literal as the program stores it.
    unless ← readsFloat actual do return ← exactLeaf
    if let some literal := if actual.isAppOf ``Model.roundAt then arguments[1]? else none then
      unless literal.hasFVar || (← readsFloat literal) do return ← exactLeaf
    if (← read).forward then
      -- An exact function of inputs, such as the exponential of an input, is read as an input:
      -- it reads floating-point values through the decoded inputs only.
      let decoded := decodedValues actual
      let fromInputs ← decoded.allM fun value => do
        if value.hasLooseBVars then return false
        try isLeaf (stripHeadMetadata value.appArg!) catch _ => pure false
      let rest := actual.replace fun term =>
        if decoded.contains term then some q((0 : ℝ)) else none
      if fromInputs && !decoded.isEmpty && !(← readsFloat rest) then return ← exactLeaf
      -- The exponential and the logarithm of a computed value.
      if name == ``Real.exp && arguments.size == 1 then
        let x : Q(ℝ) := arguments[0]!
        let operand ← analyze x fuel
        let a := operand.budget
        return ← tidy ⟨.apply name operand.tree, q((Real.exp $x) * (Real.exp $a - 1)),
          ← mkAppM ``FloatLib.Numerics.Backward.exp #[operand.proof]⟩
      if name == ``Real.log && arguments.size == 1 then
        let x : Q(ℝ) := arguments[0]!
        let operand ← analyze x fuel
        let a := operand.budget
        if operand.isExact then
          return ⟨.apply name operand.tree, q(0),
            ← mkAppM ``FloatLib.Numerics.Backward.log_exact #[operand.proof]⟩
        if (← get).accumulator?.isSome then
          throwError "roundoff: the argument `{x}` of a logarithm has an absolute error inside \
            a loop step, and the closed forward bound does not follow it there. Use `roundoff \
            mixed theorem`."
        -- The absolute error of the argument must stay below it: a premise of the statement.
        let apart ← mkFreshExprMVar q($a < $x)
        modifyThe Analysis fun analysis =>
          { analysis with pending := analysis.pending.push apart.mvarId! }
        return ← tidy ⟨.apply name operand.tree, q($a / ($x - $a)),
          ← mkAppM ``FloatLib.Numerics.Backward.log #[operand.proof, apart]⟩
    -- A definition of the program is expanded; a library's function is not.
    let library := (← isMathematics name) || (← moduleRoot name) == `FloatLib
    unless (library && name != ``id) || (← getProjectionFnInfo? name).isSome do
      if let some unfolded ← unfoldDefinition? actual then
        let unfolded : Q(ℝ) := (headZeta unfolded).headBeta
        unless unfolded == actual do return ← analyze unfolded fuel
    let (form, mode) ← wanted
    throwError "roundoff: `{actual}` has no {form}: {mode} has no rule for `{name}` of a \
      computed value. Use `roundoff mixed theorem` for a forward bound."
  -- A registered import of a value of another carrier is part of the observation: the source is
  -- the value it imports.
  let (observe, source) ← importedSource actual.appFn!
    (stripHeadMetadata (← instantiateMVars actual.appArg!))
  let source := stripHeadMetadata source
  if source.headBeta != source then return ← analyze (mkApp observe source.headBeta) fuel
  if name == ``Model.toReal && source.isAppOf ``ExecFloat.Binary.toModel then
    return ← analyze (← mkAppM ``ExecFloat.Binary.toReal #[source.getAppArgs.back!]) fuel
  if let .letE _ _ value body _ := source then
    return ← analyze (mkApp observe (body.instantiate1 value)) fuel
  if source.isFVar then
    if (← get).accumulator?.any (·.binder == source) then
      return ⟨.acc, q(0), ← mkAppM ``FloatLib.Numerics.exact_error #[actual]⟩
    if let some value := (← source.fvarId!.getDecl).value? then
      return ← analyze (mkApp observe value) fuel
  -- A component of a pair: that of an explicit pair, the accumulator of a loop whose state is a
  -- pair, or such a loop observed through the component.
  if source.isAppOfArity ``Prod.fst 3 || source.isAppOfArity ``Prod.snd 3 then
    let inner := stripHeadMetadata (← instantiateMVars source.appArg!)
    let component (pair : Lean.Expr) : Q(ℝ) := mkApp observe (mkApp source.appFn! pair)
    if inner.headBeta != inner then return ← analyze (component inner.headBeta) fuel
    if let .letE _ _ value body _ := inner then
      return ← analyze (component (body.instantiate1 value)) fuel
    if inner.isAppOfArity ``Prod.mk 4 then
      return ← analyze
        (mkApp observe (inner.getArg! (if source.isAppOf ``Prod.fst then 2 else 3))) fuel
    if (← get).accumulator?.any (·.value == actual) then
      return ⟨.acc, q(0), ← mkAppM ``FloatLib.Numerics.exact_error #[actual]⟩
    if (← isReduction inner) || (← extension).loops.any (inner.isAppOf ·.fold) then
      let session ← readThe Session
      let (context, procedures) ← foldSimpContext session
      let normalized ← session.normalize `fold actual context procedures
      if normalized.expr != actual then
        let next : Q(ℝ) := normalized.expr
        let form ← analyze next fuel
        return ← transport form (← form.tree.render) (← normalized.getProof' actual)
      if let some loop ← loopOf? inner then
        let observed ← withLocalDeclD `state (← inferType inner) fun state =>
          mkLambdaFVars #[state] (component state)
        return ← fold analyze actual observed inner loop fuel
      unless (← extension).conversions.isEmpty do
        let context ← conversionSimpContext
        let (normalized, _) ← simp actual context
        if normalized.expr != actual then
          let next : Q(ℝ) := normalized.expr
          let form ← analyze next fuel
          return ← transport form (← form.tree.render) (← normalized.getProof' actual)
  -- A loop step reads its state through the observed component only.
  if let some accumulator := (← get).accumulator? then
    if (← headVariable? source) == some accumulator.binder.fvarId! then
      throwError "roundoff: the loop step reads `{source}` of its state, and {(← wanted).2} \
        follows one numerical component of the state of a loop. Use `roundoff mixed theorem` \
        for a forward bound."
  if ← isLeaf source then return ← leaf actual source
  -- A branch that a hypothesis decides is the case it selects.
  if source.isAppOfArity ``ite 5 || source.isAppOfArity ``dite 5 then
    if let some (positive, evidence) ← guardHypothesis? (source.getArg! 1) then
      let rule := if source.isAppOfArity ``dite 5 then
          if positive then ``dite_eq_left else ``dite_eq_right
        else if positive then ``ite_eq_left else ``ite_eq_right
      let parts := source.getAppArgs
      let equality ← mkAppOptM rule #[some parts[1]!, some parts[2]!, some evidence,
        some parts[0]!, some parts[3]!, some parts[4]!]
      let some (_, _, selected) := (← inferType equality).eq? |
        throwError "roundoff: conditional reduction did not produce an equality"
      let form ← analyze (mkApp observe selected.headBeta) fuel
      return ← transport form (← form.tree.render) (← mkCongrArg observe equality)
  -- Control flow whose discriminant computes is the case it selects.
  if let some reduced ← reduceControl? (← readThe Session).containerProducers source then
    unless reduced == source do return ← analyze (mkApp observe reduced) fuel
  -- A `match` whose discriminants stay open and a branch that binds the proof of its condition
  -- have one statement for each case, which the caller generates (`Config.split`).
  if (← Cases.matcher? source).isSome || source.isAppOfArity ``dite 5 then
    (← read).split.set (some source)
    let (form, mode) ← wanted
    throwError "roundoff: `{source}` has no {form}: {mode} distinguishes the cases of a `match` \
      or of a branch that binds the proof of its condition only on the inputs of the statement. \
      Use `roundoff mixed theorem` for a forward bound."
  -- A branch: both alternatives, under the condition as the program states it.
  if source.isAppOfArity `ite 5 then
    let condition := source.getArg! 1
    let decidable := source.getArg! 2
    let positive ← settled (← analyze (mkApp observe (source.getArg! 3)) fuel)
    let negative ← settled (← analyze (mkApp observe (source.getArg! 4)) fuel)
    let budget : Q(ℝ) := mkApp5 (mkConst `ite [Level.one]) q(ℝ) condition decidable
      positive.budget negative.budget
    let proof ← mkAppOptM ``FloatLib.Numerics.Backward.branch #[none, none, none, none,
      some condition, some decidable, none, none, some positive.proof, some negative.proof]
    let form ← tidy ⟨.ite condition decidable positive.tree negative.tree, budget, proof⟩
    let equality ← mkAppOptM ``apply_ite #[none, none, some observe, some condition,
      some decidable, some (source.getArg! 3), some (source.getArg! 4)]
    return ← transport form (← form.tree.render) equality
  -- A maximum or minimum of finite values is exact: that of the decoded operands.
  if source.isAppOfArity ``Max.max 4 || source.isAppOfArity ``Min.min 4 then
    let upper := source.isAppOf ``Max.max
    let rule := match upper, name == ``Model.toReal with
      | true, false => ``ExecFloat.Binary.mixedError_toReal_max
      | false, false => ``ExecFloat.Binary.mixedError_toReal_min
      | true, true => ``Model.mixedError_toReal_maximum
      | false, true => ``Model.mixedError_toReal_minimum
    let operand (value : Lean.Expr) : BackM (Q(ℝ) × Lean.Expr × Lean.Expr) := do
      let decoded : Q(ℝ) := mkApp observe value
      let finite ← mkFreshExprMVar (← finiteStatement actual value)
      modifyThe Analysis fun analysis =>
        { analysis with pending := analysis.pending.push finite.mvarId! }
      let exact ← mkAppM ``Iff.mpr #[← mkAppOptM ``FloatLib.Numerics.mixedError_zero_zero_iff
        #[some decoded, some decoded], ← mkEqRefl decoded]
      return (decoded, finite, exact)
    let (x, hx, ex) ← operand (source.getArg! 2)
    let (y, hy, ey) ← operand (source.getArg! 3)
    if let some exactRule ← (try some <$> mkAppM rule #[hx, hy, ex, ey] catch _ => pure none) then
      let reference : Q(ℝ) := if upper then q(max $x $y) else q(min $x $y)
      let inner ← analyze reference fuel
      let budget := inner.budget
      return ← tidy { inner with
        budget := q($budget + max (0 * |$x| + 0) (0 * |$y| + 0))
        proof := ← mkAppM ``FloatLib.Numerics.Backward.offset #[exactRule, inner.proof] }
  -- Loops, after the forward analysis wrote them as registered ones.
  if (← isReduction source) || (← extension).loops.any (source.isAppOf ·.fold) then
    let session ← readThe Session
    let (context, procedures) ← foldSimpContext session
    let normalized ← session.normalize `fold actual context procedures
    if normalized.expr != actual then
      let next : Q(ℝ) := normalized.expr
      let form ← analyze next fuel
      return ← transport form (← form.tree.render) (← normalized.getProof' actual)
    if let some loop ← loopOf? source then
      return ← fold analyze actual observe source loop fuel
    unless (← extension).conversions.isEmpty do
      let context ← conversionSimpContext
      let (normalized, _) ← simp actual context
      if normalized.expr != actual then
        let next : Q(ℝ) := normalized.expr
        let form ← analyze next fuel
        return ← transport form (← form.tree.render) (← normalized.getProof' actual)
  -- One floating-point operation: its local rule, then its exact operation on the operands.
  if let some (estimate, primitive) ← localRule? actual then
    if estimate.reference == actual then
      throwError "roundoff: `{actual}` has no {(← wanted).1}: its rule compares it with \
        itself. Use `roundoff mixed theorem` for a forward bound."
    let inner ← analyze estimate.reference fuel
    return ← round actual estimate inner primitive
  -- A definition is expanded; a FloatLib operation without a rule is refused.
  let sourceName := source.getAppFn.constName?.getD .anonymous
  unless (`FloatLib).isPrefixOf sourceName || sourceName == ``Max.max || sourceName == ``Min.min do
    if let some unfolded ← unfoldDefinition? source then
      let unfolded := headZeta unfolded
      unless unfolded == source do return ← analyze (mkApp observe unfolded) fuel
    -- A method of an instance is the operation that the instance gives, as a literal is the
    -- conversion that its instance selects.
    if source.getAppFn.isProj then
      if let some method ← withReducibleAndInstances (reduceProj? source.getAppFn) then
        return ← analyze (mkApp observe (mkAppN method source.getAppArgs).headBeta) fuel
      let reduced ← whnfR source
      unless reduced == source do return ← analyze (mkApp observe reduced) fuel
  -- The forward analysis decodes the observation of a value such as a converted literal.
  let session ← readThe Session
  let (context, procedures) ← decodingSimpContext session
  let normalized ← session.normalize `decoding actual context procedures
  let next : Q(ℝ) := normalized.expr
  let decoded := next.getAppArgs.back?.all fun value => !value.isAppOf ``ExecFloat.Binary.toModel
  if decoded && next != actual then
    let form ← analyze next fuel
    return ← transport form (← form.tree.render) (← normalized.getProof' actual)
  let (form, mode) ← wanted
  throwError "roundoff: `{source}` has no {form}: {mode} has no rule for it. Use `roundoff \
    mixed theorem` for a forward bound."

end Backward

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
