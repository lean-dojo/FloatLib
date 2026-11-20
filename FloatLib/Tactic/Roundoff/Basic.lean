/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.Roundoff.Extension
public meta import Lean.Compiler.CSimpAttr
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Meta.DiscrTree
public meta import Lean.Meta.Match.MatcherInfo
public meta import Lean.Meta.RecursorInfo
public meta import Mathlib.Util.Qq
public import FloatLib.Tactic.Roundoff.Rules

/-!
# Data of the `roundoff` analysis

An analyzed node yields an `Estimate`: a real reference, an absolute or mixed bound against it and
its proof, and possibly the finiteness of the computed value. A `Session` holds the rules, the
normalizers and the memo tables of one `roundoff` call, and an `Analysis` the results and open
premises of one branch or loop scope. Proof search runs in transactions. A failed one leaves no
assignments, messages or scope state behind, while the session's memo tables, such as
`Session.analysisFailures`, keep what it recorded.

Contracts describe the correctly rounded primitives. Their implementations, the dictionary methods
equal to them, are registered by the modules that define those dictionaries. Registered containers
are recognized from their types and reads. `Recursor` collects the functions of the recursive
analysis, so that its parts can live in different modules.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- The type of a rule with the `autoParam` annotations of its premises removed. The analysis
proves every premise itself, such as the format proof `hformat` of a configured theorem, and reads
it as the proposition it states. -/
def ruleType (rule : Lean.Expr) : MetaM Lean.Expr := do
  return (← inferType rule).replace fun e => if e.isAutoParam then some e.appFn!.appArg! else none

/-- Whether `name` is a private declaration of an imported `module`. A `module` that imports it
cannot unfold it. A plain file loads its body, and there Mathlib's private definitions of the
arithmetic and the order of the reals unfold, so that comparing two real numerals evaluates them
until Lean's recursion limit. -/
def isImportedPrivate (environment : Environment) (name : Name) : Bool :=
  isPrivateName name && (environment.getModuleIdxFor? name).any fun index =>
    environment.header.moduleData[index.toNat]?.any (·.isModule)

/-- `canUnfoldDefault` without the private declarations of imported modules
(`isImportedPrivate`): what a `module` can unfold, in a plain file too. -/
def canUnfoldExported (config : Meta.Config) (info : ConstantInfo) : CoreM Bool := do
  if isImportedPrivate (← getEnv) info.name then return false
  canUnfoldDefault config info

/-- Run the proof search `action` unfolding what a `module` can unfold (`canUnfoldExported`), so
that a side condition is proved or left open alike in a `module` and in a plain file. In a
`module` this is `action` itself. -/
def exported {α : Type} (action : TacticM α) : TacticM α := do
  if (← getEnv).header.isModule then action else withCanUnfoldPred canUnfoldExported action

/-- Abstract the parameters of a theorem that are left after some were assigned: the unassigned
ones among `arguments`, in their order and with their binders, around `proof`. -/
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

/-- `expression` with each instance argument that mentions no variable replaced by the instance
that type class resolution finds for its class, when the two agree by definition: the
dictionaries in which elaboration writes the same term. -/
def canonicalInstances (expression : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform expression (pre := fun term => do
    unless term.isApp && term.getAppFn.isConst do return .continue
    let arguments := term.getAppArgs
    let info ← getFunInfoNArgs term.getAppFn arguments.size
    let mut canonical := arguments
    for h : index in [:arguments.size] do
      let argument := arguments[index]
      unless info.paramInfo[index]?.any (·.isInstance) do continue
      if argument.hasFVar || argument.hasMVar then continue
      let some found ← observing? (synthInstance (← inferType argument)) | continue
      if found != argument && (← withDefault (isDefEq argument found)) then
        canonical := canonical.set! index found
    return .continue (mkAppN term.getAppFn canonical))

/-- `rule` at the reals, when it bounds an absolute error over an open carrier, as `add_error`
does over an ordered ring `K`: the carrier is the reals, its instance parameters are those of the
reals, and the statement is written in the dictionaries of real arithmetic
(`canonicalInstances`), as a theorem stated over the reals is. The analysis then matches it as
one, where the dictionaries of an open carrier would be unfolded at every use. Any other rule,
and one whose carrier lacks an instance at the reals, is returned as it is. -/
def realForm (rule : Lean.Expr) : MetaM Lean.Expr := do
  let saved ← saveState
  let (arguments, binders, conclusion) ← forallMetaTelescopeReducing (← inferType rule)
  let specialized? ← observing? do
    unless conclusion.isAppOfArity ``LE.le 4 && conclusion.getAppArgs[2]!.isAppOf ``abs do
      throwError "roundoff: no absolute error bound"
    let carrier := conclusion.getAppArgs[0]!
    unless carrier.isMVar && arguments.contains carrier do
      throwError "roundoff: a fixed carrier"
    unless ← isDefEq carrier q(ℝ) do throwError "roundoff: the carrier is not a type of reals"
    for argument in arguments, binder in binders do
      unless binder.isInstImplicit && (← instantiateMVars argument).isMVar do continue
      let found ← synthInstance (← instantiateMVars (← inferType argument))
      unless ← isDefEq argument found do throwError "roundoff: another instance"
    let closed ← closeRuleArguments arguments binders 0 #[] (mkAppN rule arguments)
    mkExpectedTypeHint closed (← canonicalInstances (← inferType closed))
  match specialized? with
  | some specialized => return specialized
  | none =>
      saved.restore
      return rule

/-- FloatLib's exact configured operations. Mixed analysis tries them before any rounding rule,
and their selection premises must be proved rather than left to the caller. Registered exact
operations follow. -/
def exactOperations : CoreM (Array Name) := do
  return #[
  ``ExecFloat.Binary.toReal_one, ``ExecFloat.Binary.toReal_sub_self,
  ``ExecFloat.Binary.toReal_add_of_isZero_left, ``ExecFloat.Binary.toReal_add_of_isZero_right,
  ``ExecFloat.Binary.toReal_sub_of_isZero_left, ``ExecFloat.Binary.toReal_sub_of_isZero_right,
  ``ExecFloat.Binary.toReal_mul_of_isZero_left, ``ExecFloat.Binary.toReal_mul_of_isZero_right,
  ``ExecFloat.Binary.toReal_mul_of_abs_toReal_eq_one_left,
  ``ExecFloat.Binary.toReal_mul_of_abs_toReal_eq_one_right,
  ``ExecFloat.Binary.toReal_div_of_abs_toReal_eq_one_right,
  ``ExecFloat.Binary.toReal_sqrt_of_isZero, ``ExecFloat.Binary.toReal_execFloat_sqrt_of_isZero,
  ``ExecFloat.Binary.toReal_ofRat_intCast_of_abs_le,
  ``ExecFloat.Binary.toReal_ofRat_natCast_of_le] ++
  (← extension).exactOperations.map (·.1)

/-- Exact operations and selections paired with the theorem that their result is finite under
the same hypotheses, with no range condition. -/
def exactFiniteness : CoreM (Array (Name × Name)) := do
  return #[
  (``ExecFloat.Binary.toReal_one, ``ExecFloat.Binary.isFinite_one),
  (``ExecFloat.Binary.toReal_sub_self, ``ExecFloat.Binary.isFinite_sub_self),
  (``ExecFloat.Binary.toReal_add_of_isZero_left, ``ExecFloat.Binary.isFinite_add_of_isZero_left),
  (``ExecFloat.Binary.toReal_add_of_isZero_right, ``ExecFloat.Binary.isFinite_add_of_isZero_right),
  (``ExecFloat.Binary.toReal_sub_of_isZero_left, ``ExecFloat.Binary.isFinite_sub_of_isZero_left),
  (``ExecFloat.Binary.toReal_sub_of_isZero_right, ``ExecFloat.Binary.isFinite_sub_of_isZero_right),
  (``ExecFloat.Binary.toReal_mul_of_isZero_left, ``ExecFloat.Binary.isFinite_mul_of_isZero_left),
  (``ExecFloat.Binary.toReal_mul_of_isZero_right, ``ExecFloat.Binary.isFinite_mul_of_isZero_right),
  (``ExecFloat.Binary.toReal_mul_of_abs_toReal_eq_one_left,
    ``ExecFloat.Binary.isFinite_mul_of_abs_toReal_eq_one_left),
  (``ExecFloat.Binary.toReal_mul_of_abs_toReal_eq_one_right,
    ``ExecFloat.Binary.isFinite_mul_of_abs_toReal_eq_one_right),
  (``ExecFloat.Binary.toReal_div_of_abs_toReal_eq_one_right,
    ``ExecFloat.Binary.isFinite_div_of_abs_toReal_eq_one_right),
  (``ExecFloat.Binary.toReal_ite_lt_eq_max, ``ExecFloat.Binary.isFinite_ite),
  (``ExecFloat.Binary.toReal_ite_lt_eq_min, ``ExecFloat.Binary.isFinite_ite),
  (``ExecFloat.Binary.toReal_ite_le_eq_max, ``ExecFloat.Binary.isFinite_ite),
  (``ExecFloat.Binary.toReal_ite_le_eq_min, ``ExecFloat.Binary.isFinite_ite)] ++
  (← extension).exactOperations.filterMap (fun (rule, finite?) => finite?.map (rule, ·))

/-- Configured operations whose finite result is the rounding `Model.roundAt` of an exact real
operation on the decoded operands, or of the rational a conversion reads. Monotone rounding
transfers the sign of that operation. -/
def roundings : Array Name := #[
  ``ExecFloat.Binary.toReal_add_eq_roundAt, ``ExecFloat.Binary.toReal_sub_eq_roundAt,
  ``ExecFloat.Binary.toReal_mul_eq_roundAt, ``ExecFloat.Binary.toReal_div_eq_roundAt,
  ``ExecFloat.Binary.toReal_sqrt_eq_roundAt, ``ExecFloat.Binary.toReal_ofRat_eq_roundAt]

/-- FloatLib's selections between two configured values, such as C's maximum step
`if m < x then x else m`, read as `max` or `min` of their real values. They apply only to a
branch on a loop's rounded accumulator, whose cases the branch rules cannot carry through the loop.
Every other branch keeps its two cases. -/
def selectionRules : Array Name := #[
  ``ExecFloat.Binary.toReal_ite_lt_eq_max, ``ExecFloat.Binary.toReal_ite_lt_eq_min,
  ``ExecFloat.Binary.toReal_ite_le_eq_max, ``ExecFloat.Binary.toReal_ite_le_eq_min]

/-- Whether `term` reads the accumulator of a loop step under analysis. -/
def readsAccumulator (term : Lean.Expr) : MetaM Bool := do
  let context ← getLCtx
  return (term.find? fun child => child.isFVar &&
    (context.find? child.fvarId!).any (·.userName == `accumulator)).isSome

/-- Whether `source` is a selection whose condition is an equality at an inductive type other
than `Bool`, such as an equality of indices. The comparison of configured values that a selection
rule (`selectionRules`) states unfolds to an equality of Booleans, so it cannot match. -/
def isNonBooleanTest (source : Lean.Expr) : MetaM Bool := do
  let source := source.consumeMData
  unless source.isAppOfArity ``ite 5 do return false
  let some (type, _, _) := (← instantiateMVars source.getAppArgs[1]!).consumeMData.eq? |
    return false
  let some name := (← whnfR type).getAppFn.constName? | return false
  if name == ``Bool then return false
  return (← getConstInfo name) matches .inductInfo _

/-- What an estimate proves about the actual real value it describes. -/
inductive Bound where
  /-- `|actual - reference| ≤ error`. -/
  | absolute (error : Q(ℝ))
  /-- `MixedError actual reference relative absolute`. -/
  | mixed (relative absolute : Q(ℝ))

/-- The proposition `bound` states about `actual` and `reference`. -/
def Bound.statement : Bound → Q(ℝ) → Q(ℝ) → Q(Prop)
  | .absolute error, actual, reference => q(|$actual - $reference| ≤ $error)
  | .mixed relativeError absoluteError, actual, reference =>
      q(MixedError $actual $reference $relativeError $absoluteError)

/-- Both parts of a mixed bound, or an absolute bound, are the literal zero. -/
def Bound.isExact : Bound → Bool
  | .absolute error => error.nat? == some 0
  | .mixed relativeError absoluteError =>
      relativeError.nat? == some 0 && absoluteError.nat? == some 0

/-- The result for one analyzed node: a real reference, a proof of `bound` against it, and,
when it is derived, the finiteness of the floating-point value that `actual` decodes. An exact
value is a bound whose parts are the literal zero (`Bound.isExact`). A range rule that needs an
enclosure of `actual` reads it off the bound with `MixedError.abs_le`. The record is only proof
construction data and never replaces the executed container program. -/
structure Estimate where
  /-- The real value the bound compares the actual value with. -/
  reference : Q(ℝ)
  /-- The budgets of the bound, absolute or mixed. -/
  bound : Bound
  /-- A proof of `bound.statement actual reference`. -/
  proof : Lean.Expr
  /-- A proof of `isFinite value = true` for the value `actual` decodes. -/
  finite? : Option Lean.Expr := none

/-- An exact value: no error in either mode. -/
def exactEstimate (mixed : Bool) (actual : Q(ℝ)) : MetaM Estimate :=
  if mixed then return ⟨actual, .mixed q(0) q(0), ← mkAppM ``MixedError.refl #[actual], none⟩
  else return ⟨actual, .absolute q(0), ← mkAppM ``exact_error #[actual], none⟩

/-- The equality `actual = reference` stated by an exact mixed bound. -/
def exactEquality (proof : Lean.Expr) : MetaM Lean.Expr := do
  let statement ← instantiateMVars (← inferType proof)
  let arguments := statement.getAppArgs
  let iff ← mkAppOptM ``mixedError_zero_zero_iff #[some arguments[0]!, some arguments[1]!]
  mkAppM ``Iff.mp #[iff, proof]

/-- In mixed mode, read an absolute bound as a mixed bound without relative part. -/
def Estimate.inMode (estimate : Estimate) (mixed : Bool) : MetaM Estimate := do
  let .absolute error := estimate.bound | return estimate
  unless mixed do return estimate
  return { estimate with
    bound := .mixed q(0) error
    proof := (← mkAppM ``MixedError.of_abs_sub_le #[estimate.proof]) }

/-- The number of errors logged so far for the current command. -/
def errorCount : CoreM Nat :=
  return (← Core.getMessageLog).reportedPlusUnreported.foldl
    (fun count message => if message.severity matches .error then count + 1 else count) 0

/-- The exhausted recursion depths that the transactions of the current analysis caught, once
`Session.prepare` installed the count. -/
initialize caughtDepths : EnvExtension (Option (IO.Ref Nat)) ←
  registerEnvExtension (pure none) (asyncMode := .local)

/-- The exhausted recursion depths caught so far (`caughtDepths`). A memo table keeps a failure only
when none was caught during its computation, since the same computation may succeed when shallower.
-/
def depthsCaught : CoreM Nat := do
  match caughtDepths.getState (← getEnv) with
  | some count => count.get
  | none => pure 0

/-- A failed speculative derivation leaves no assignments or errors behind, while the session's
`IO.Ref` tables keep what it recorded. A derivation fails when it logs an error, and errors of
earlier tactics in the same declaration do not count. Recursive source analysis keeps the
declaration's budget and does not share a local matching budget. -/
def transaction? {α : Type} (action : TacticM (Option α)) (catchLimits : Bool := false) :
    TacticM (Option α) := do
  let saved ← saveState
  let errors ← errorCount
  let (result?, _) ← tryFinally'
    (tryCatchRuntimeEx (do
      let result? ← action
      if (← errorCount) > errors then pure none else pure result?) (fun error => do
        -- An exhausted local recursion depth only rejects this attempt; heartbeats are shared.
        if error.isInterrupt || (!catchLimits && error.isMaxHeartbeat) then throw error
        -- A depth is counted, so that no memo table keeps a failure it caused. An attempt's own
        -- heartbeat budget gives the same failure at every repetition.
        if error.isMaxRecDepth then
          if let some count := caughtDepths.getState (← getEnv) then count.modify (· + 1)
        trace[roundoff] "proof search: {error.toMessageData}"
        pure none))
    (fun result => unless result.any (·.isSome) do saved.restore)
  return result?

/-- Bound local matching and proof search independently of recursive source analysis. -/
def attempt? {α : Type} (heartbeats : Nat) (action : TacticM (Option α)) :
    TacticM (Option α) :=
  transaction? (catchLimits := true) <| withTheReader Core.Context
    (fun c => { c with maxHeartbeats := heartbeats * 1000 }) (withCurrHeartbeats action)

/-- Close a finiteness goal with the finiteness an estimate derived, when it concerns the same
value, possibly up to the unfolding of a definition. -/
def Estimate.closeFinite (estimate : Estimate) (goal : MVarId) : TacticM Bool := do
  let some finite := estimate.finite? | return false
  let type ← instantiateMVars (← goal.getType)
  let given ← instantiateMVars (← inferType finite)
  if given == type then
    goal.assign finite
    return true
  -- Each is a finiteness `test value = true`. That of another carrier, such as of the decoded
  -- model, is not this one, and a proposition of another form, such as the invariant `True` of a
  -- loop whose state decodes no value, proves no finiteness.
  let (some (_, derived, _), some (_, wanted, _)) := (given.eq?, type.eq?) | return false
  unless derived.getAppFn == wanted.getAppFn do return false
  -- Program definitions may be kept folded by the surrounding analysis; unfold them here. Such a
  -- comparison settles quickly when it succeeds.
  let matched? ← attempt? 200 <| withCanUnfoldPred
      (fun _ info => return !isImportedPrivate (← getEnv) info.name) <| withDefault do
    return if ← isDefEq given type then some () else none
  if matched?.isNone then return false
  goal.assign finite
  return true

/-- The heads of canonical real literals, which are exact data. -/
def literalHeads : Array Name :=
  #[``OfNat.ofNat, ``OfScientific.ofScientific, ``Real.pi]

/-- A correctly rounded FloatLib primitive and the theorems that analyze its calls.

* `implementations` equate a dictionary method, with the instance it is stated for, to the
  primitive. They are registered as `Extension.bridges`.
* `rounding` identifies the primitive's result with the nearest-even rounding of its real
  reference, and `finite` proves it finite, both under the domain and range conditions in their
  premises.
* `exact` give the exact result at special inputs, such as a zero. They apply only when
  their premises are proved and are tried before `rounding`.
* `finiteWithoutRange` prove the result finite from a sign of the input or from a zero input
  instead, with no range condition, and are tried before `finite`.
* `signs` are the primitive's theorems on the sign of its result.
* `attribute?` are the rounding and the finiteness for a call that names a rounding attribute,
  for a primitive that takes one. `rounding` and `finite` are those of the default attribute and
  are tried first. -/
structure PrimitiveContract where
  /-- The correctly rounded primitive. -/
  primitive : Name
  /-- Equalities of dictionary methods with the primitive. -/
  implementations : Array Name := #[]
  /-- The rounding of the primitive's real reference. -/
  rounding : Name
  /-- The finiteness of its result under the rounding's conditions. -/
  finite : Name
  /-- Exact results at special inputs. -/
  exact : Array Name := #[]
  /-- Finiteness without a range condition. -/
  finiteWithoutRange : Array Name := #[]
  /-- Signs of the result. -/
  signs : Array Name := #[]
  /-- The rounding of the real reference in the attribute of the call, and the finiteness of
  that result. -/
  attribute? : Option (Name × Name) := none
  /-- The constants that head the dictionary methods of `implementations`, or `none` when one of
  them is not read off its statement. -/
  methods? : Option (Array Name) := some #[]

/-- Whether a theorem of `contract` can observe the call `source`: its head is the primitive or
a dictionary method equal to it. The theorems of a primitive that the program does not call are
then not instantiated. -/
def PrimitiveContract.observes (contract : PrimitiveContract) (source : Lean.Expr) : Bool :=
  match contract.methods?, source.getAppFn.constName? with
  | some methods, some head => head == contract.primitive || methods.contains head
  | some _, none => false
  | none, _ => true

/-- The rounding theorems of a contract, each with the finiteness of its result: those of the
default attribute first. -/
def PrimitiveContract.roundings (contract : PrimitiveContract) : Array (Name × Name) :=
  #[(contract.rounding, contract.finite)] ++ contract.attribute?.toArray

/-- The correctly rounded transcendentals of configured IEEE scalars. -/
def primitives : Array PrimitiveContract := #[
  { primitive := ``ExecFloat.Binary.CorrectlyRounded.exp
    rounding := ``ExecFloat.Binary.CorrectlyRounded.toReal_exp_eq_roundAt
    finite := ``ExecFloat.Binary.CorrectlyRounded.isFinite_exp
    exact := #[``ExecFloat.Binary.CorrectlyRounded.toReal_exp_of_isZero]
    finiteWithoutRange := #[``ExecFloat.Binary.CorrectlyRounded.isFinite_exp_of_isZero,
      ``ExecFloat.Binary.CorrectlyRounded.isFinite_exp_of_nonpos]
    signs := #[``ExecFloat.Binary.CorrectlyRounded.toReal_exp_nonneg,
      ``ExecFloat.Binary.CorrectlyRounded.toReal_exp_pos] },
  { primitive := ``ExecFloat.Binary.CorrectlyRounded.log
    rounding := ``ExecFloat.Binary.CorrectlyRounded.toReal_log_eq_roundAt
    finite := ``ExecFloat.Binary.CorrectlyRounded.isFinite_log },
  { primitive := ``ExecFloat.Binary.CorrectlyRounded.expm1
    rounding := ``ExecFloat.Binary.CorrectlyRounded.toReal_expm1_eq_roundAt
    finite := ``ExecFloat.Binary.CorrectlyRounded.isFinite_expm1
    exact := #[``ExecFloat.Binary.CorrectlyRounded.toReal_expm1_of_isZero]
    finiteWithoutRange := #[``ExecFloat.Binary.CorrectlyRounded.isFinite_expm1_of_isZero,
      ``ExecFloat.Binary.CorrectlyRounded.isFinite_expm1_of_nonpos]
    signs := #[``ExecFloat.Binary.CorrectlyRounded.toReal_expm1_lt_zero,
      ``ExecFloat.Binary.CorrectlyRounded.toReal_expm1_pos] },
  { primitive := ``ExecFloat.Binary.CorrectlyRounded.expm1x
    rounding := ``ExecFloat.Binary.CorrectlyRounded.toReal_expm1x_eq_roundAt
    finite := ``ExecFloat.Binary.CorrectlyRounded.isFinite_expm1x
    exact := #[``ExecFloat.Binary.CorrectlyRounded.toReal_expm1x_of_isZero]
    finiteWithoutRange := #[``ExecFloat.Binary.CorrectlyRounded.isFinite_expm1x_of_isZero]
    signs := #[``ExecFloat.Binary.CorrectlyRounded.toReal_expm1x_nonneg]
    attribute? := some (``ExecFloat.Binary.CorrectlyRounded.toReal_expm1x_eq_roundAt_mode,
      ``ExecFloat.Binary.CorrectlyRounded.isFinite_expm1x_mode) },
  { primitive := ``ExecFloat.Binary.CorrectlyRounded.logp1
    rounding := ``ExecFloat.Binary.CorrectlyRounded.toReal_logp1_eq_roundAt
    finite := ``ExecFloat.Binary.CorrectlyRounded.isFinite_logp1
    exact := #[``ExecFloat.Binary.CorrectlyRounded.toReal_logp1_of_isZero]
    finiteWithoutRange := #[``ExecFloat.Binary.CorrectlyRounded.isFinite_logp1_of_isZero,
      ``ExecFloat.Binary.CorrectlyRounded.isFinite_logp1_of_nonneg]
    signs := #[``ExecFloat.Binary.CorrectlyRounded.toReal_logp1_pos] },
  { primitive := ``ExecFloat.Binary.CorrectlyRounded.expMul
    rounding := ``ExecFloat.Binary.CorrectlyRounded.toReal_expMul_eq_roundAt
    finite := ``ExecFloat.Binary.CorrectlyRounded.isFinite_expMul
    signs := #[``ExecFloat.Binary.CorrectlyRounded.toReal_expMul_nonneg,
      ``ExecFloat.Binary.CorrectlyRounded.toReal_expMul_nonpos,
      ``ExecFloat.Binary.CorrectlyRounded.toReal_expMul_pos,
      ``ExecFloat.Binary.CorrectlyRounded.toReal_expMul_lt_zero] }]

/-- The primitive contracts with the implementation equalities registered for them, and the
heads of the methods these equate with the primitive (`PrimitiveContract.observes`). -/
def primitiveContracts : CoreM (Array PrimitiveContract) := do
  let bridges := (← extension).bridges
  let environment ← getEnv
  return primitives.map fun contract =>
    let implementations := bridges.filterMap fun (primitive, bridge) =>
      if primitive == contract.primitive then some bridge else none
    -- The method is the left side of the equality that the implementation theorem states.
    let methods? := implementations.mapM fun bridge => do
      let info ← environment.find? bridge
      let (_, method, _) ← info.type.getForallBody.consumeMData.eq?
      method.getAppFn.constName?
    { contract with implementations, methods? }

/-- Local proof construction for a loop body, before its accumulator variables are closed. -/
structure StepEstimate where
  /-- The reference after one step, `fun reference value => ...`. -/
  reference : Lean.Expr
  /-- The budget after one step, `fun accumulator reference budget value => ...`. -/
  error : Lean.Expr
  /-- The step's conditions, a function of the same four arguments. -/
  condition : Lean.Expr
  /-- The step's bound under its condition and the incoming accumulator bound. -/
  proof : Lean.Expr
  /-- The condition as a function of the accumulator and the entry alone, when it reads neither
  the reference nor the budget, so that it is stated on the loop's actual states. -/
  actualCondition? : Option Lean.Expr
/-- Recognize program values containing a registered container, such as a container, from their type
definitions. A shared visited set handles recursive datatypes without enumerating graph,
operation-record, or user wrapper types. -/
partial def containsContainer (environment : Environment) (containers : Array Name)
    (type : Lean.Expr) : StateM NameSet Bool := do
  if containers.any type.isAppOf then return true
  match type with
  | .app function argument =>
      if ← containsContainer environment containers argument then return true
      containsContainer environment containers function
  | .forallE _ domain body _ | .lam _ domain body _ =>
      if ← containsContainer environment containers body then return true
      containsContainer environment containers domain
  | .letE _ type value body _ =>
      if ← containsContainer environment containers body then return true
      if ← containsContainer environment containers type then return true
      containsContainer environment containers value
  | .mdata _ value | .proj _ _ value => containsContainer environment containers value
  | .const name _ =>
      if (← get).contains name || (`FloatLib).isPrefixOf name then return false
      modify (·.insert name)
      match environment.find? name with
      | some (.inductInfo info) =>
          for constructor in info.ctors do
            if let some info := environment.find? constructor then
              if ← containsContainer environment containers info.type then return true
          return false
      | some (.defnInfo info) =>
          if info.type.getForallBody.isSort then containsContainer environment containers info.value
          else return false
      | _ => return false
  | _ => return false

/-- Decide `containsContainer`, skipping the constants in `containerFree`. A negative answer adds
every constant the search visited: none of them reaches a container type either. -/
def hasContainer (containerFree : IO.Ref NameSet) (type : Lean.Expr) : CoreM Bool := do
  let containers := (← extension).containers
  let (found, visited) := (containsContainer (← getEnv) containers type).run (← containerFree.get)
  unless found do containerFree.set visited
  return found

/-- Protect the container producers in the applied observation pattern. Generic functions can
return a container here even when their own declaration returns an arbitrary type parameter. -/
partial def containerProducerHeads (containerFree : IO.Ref NameSet) (expression : Lean.Expr)
    (names : NameSet) : MetaM NameSet := do
  let expression ← instantiateMVars expression
  let mut names := names
  if let some name := expression.getAppFn.constName? then
    let type ← inferType expression
    if ← hasContainer containerFree type.getForallBody then
      names := names.insert name
  if let .proj _ _ value := expression then
    return ← containerProducerHeads containerFree value names
  if let .mdata _ value := expression then return ← containerProducerHeads containerFree value names
  let mut type ← inferType expression.getAppFn
  for argument in expression.getAppArgs do
    let .forallE _ _ body info := type | break
    if info == .default && !(← isProof argument) then
      names ← containerProducerHeads containerFree argument names
    type := body.instantiate1 argument
  return names

/-- The position of the container in `value`, a registered read of one entry. Only the
canonical reads count unless `getters`. With `strict` the read must have its registered number of
arguments, and with `certified` it must select stored entries (`Read.isCertified`). A class method
read through another dictionary (`Read.selects`) is no read. -/
def Read.position? (reads : Array Read) (value : Lean.Expr) (getters : Bool := false)
    (strict : Bool := true) (certified : Bool := false) : Option Nat :=
  reads.findSome? fun read =>
    if !getters && !read.canonical then none
    else if certified && !read.isCertified then none
    else if (if strict then value.isAppOfArity read.head read.arity else value.isAppOf read.head) &&
        read.selects value
    then some (value.getAppNumArgs - read.fromEnd)
    else none

/-- `Read.position?` for the registered reads. -/
def readPosition? (value : Lean.Expr) (getters : Bool := false) (strict : Bool := true)
    (certified : Bool := false) : CoreM (Option Nat) :=
  return Read.position? (← extension).reads value getters strict certified

/-- Whether a registered extension shows that `value`, a container, has a shape that is not
literal. -/
def symbolic (value : Lean.Expr) : MetaM Bool := do
  for test in (← extension).symbolic do
    if ← test value then return true
  return false

/-- The first registered restatement of the read `actual`. -/
def restate? (actual : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  for restatement in (← extension).restate do
    if let some result ← restatement actual then return some result
  return none

/-- The skeleton of the shape of the container `value`, from the first registered extension that
knows it (`Extension.skeleton`). -/
def skeleton? (value : Lean.Expr) : MetaM (Option (Nat × Bool)) := do
  for skeleton in (← extension).skeleton do
    if let some result ← skeleton value then return some result
  return none

/-- The registered reads of shape-recursive producers. -/
def readRules : CoreM (Array Name) := do
  let environment ← getEnv
  return (← extension).readRules.foldl (fun rules rule => rules ++ rule environment) #[]

/-- The registered loop whose complete application is `value`. -/
def loopOf? (value : Lean.Expr) : CoreM (Option Loop) :=
  return (← extension).loops.find? fun loop => value.isAppOfArity loop.fold loop.arity

/-- The producer of a container: its head, or for a component of a pair, such as one cotangent
of a pullback returning several, the producer of the pair. A registered read of the component is
keyed by that producer. -/
partial def containerProducer (container : Lean.Expr) : Name :=
  match container with
  | .proj ``Prod _ pair => containerProducer pair
  | _ =>
    if container.isAppOfArity ``Prod.fst 3 || container.isAppOfArity ``Prod.snd 3 then
      containerProducer container.appArg!
    else container.getAppFn.constName?.getD .anonymous

/-- The first component `source` of a registered loop over pairs, as the loop of that component
with the equality between them, when the loop has a projection law and its step computes the
component from the accumulator's first component alone. The flags a checked computation
accumulates beside its value are such a second component. -/
def projectLoop? (source : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let loop? := match source with
    | .proj ``Prod 0 loop => some loop
    | _ => if source.isAppOfArity ``Prod.fst 3 then some source.appArg! else none
  let some value := loop? | return none
  let some loop ← loopOf? value | return none
  let some law := loop.projection | return none
  let arguments := value.getAppArgs
  let (step, initial) := (arguments[loop.step]!, arguments[loop.initial]!)
  let pair ← whnfR (← inferType initial)
  unless pair.isAppOfArity ``Prod 2 do return none
  let component := pair.getArg! 0
  let first? ← withLocalDeclD `state pair fun state =>
    withLocalDeclD `element arguments[loop.element]! fun element => do
      let next := (mkApp2 step state element).headBeta
      let first ← if next.isAppOfArity ``Prod.mk 4 then pure (next.getArg! 2)
        else whnfCore (.proj ``Prod 0 next)
      withLocalDeclD `first component fun head => do
        let body := first.replace fun term => match term with
          | .proj ``Prod 0 (.fvar id) => if id == state.fvarId! then some head else none
          | _ => if term.isAppOfArity ``Prod.fst 3 && term.appArg! == state then some head
              else none
        if body.containsFVar state.fvarId! then return none
        return some (← mkLambdaFVars #[head, element] body)
  let some first := first? | return none
  let start ← whnfCore (.proj ``Prod 0 initial)
  let proof ← withLocalDeclD `state pair fun state =>
    withLocalDeclD `element arguments[loop.element]! fun element => do
      mkLambdaFVars #[state, element] (← mkEqRefl (.proj ``Prod 0 (mkApp2 step state element)))
  let equality ← mkAppM law #[step, first, proof, initial, arguments[loop.input]!]
  let result := mkAppN value.getAppFn
    ((arguments.set! loop.state component).set! loop.step first |>.set! loop.initial start)
  return some (result, ← mkExpectedTypeHint equality (← mkEq source result))

/-- Whether `value` applies a registered reduction, which the fold laws write as a loop: one of
the `reductions` or a sum of configured values. -/
def isReduction (value : Lean.Expr) : CoreM Bool := do
  let extension ← extension
  return extension.reductions.any value.isAppOf ||
    extension.sums.any fun sum => !sum.entries && !sum.exact && value.isAppOf sum.head

/-- Whether `value` applies a registered sum of exact real numbers, such as `Finset.sum`. -/
def isExactSum (value : Lean.Expr) : CoreM Bool :=
  return (← extension).sums.any fun sum => sum.exact && value.isAppOf sum.head

/-- The laws, with their direction, of the registered sums that are not entries of a container,
and the heads of those that have none and are unfolded instead. -/
def sumLaws : CoreM (Array (Name × Bool) × Array Name) := do
  let sums := (← extension).sums.filter (!·.entries)
  return (sums.flatMap (·.laws), (sums.filter (·.laws.isEmpty)).map (·.head))

/-- The kinds of registered rule: numerical bounds and observations, mixed-error bounds,
finiteness theorems, and order facts between real values. -/
inductive RuleKind where
  /-- An absolute-error bound or an exact observation equality. -/
  | numerical
  /-- A mixed-error bound. -/
  | mixed
  /-- A finiteness theorem `isFinite value = true`. -/
  | finiteness
  /-- An order fact `≤` or `<` between real values. -/
  | order

/-- Whether a proposition states that a floating-point value is finite. -/
def isFiniteness (type : Lean.Expr) : Bool :=
  type.isAppOfArity ``Eq 3 && type.getAppArgs[2]!.isConstOf ``Bool.true &&
    (type.getAppArgs[1]!.isAppOf ``ExecFloat.Binary.isFinite ||
      type.getAppArgs[1]!.isAppOf ``Model.isFinite)

/-- Split `isFinite value = true ∧ MixedError actual reference relative absolute`. -/
def finiteMixed? (target : Lean.Expr) : Option (Lean.Expr × Lean.Expr) := do
  let some (finite, bound) := target.consumeMData.and? | none
  guard (isFiniteness finite && bound.isAppOfArity ``MixedError 4)
  return (finite, bound)

/-- Synthesize the instance arguments that unification left open in an instantiated theorem. -/
def synthesizeInstances (arguments : Array Lean.Expr) (binders : Array BinderInfo) :
    MetaM Unit := do
  for h : index in [:arguments.size] do
    let argument ← instantiateMVars arguments[index]
    if argument.isMVar && binders[index]!.isInstImplicit then
      argument.mvarId!.assign (← synthInstance (← argument.mvarId!.getType))

/-- Whether a theorem concludes that a Boolean test is `false`. -/
def isRefutation (type : Lean.Expr) : Bool :=
  let conclusion := type.getForallBody.consumeMData
  conclusion.isAppOfArity ``Eq 3 && conclusion.getAppArgs[0]!.isConstOf ``Bool &&
    conclusion.getAppArgs[2]!.isConstOf ``Bool.false

/-- Classify a registered rule by the head of its stated conclusion. -/
def ruleKind (type : Lean.Expr) : RuleKind :=
  let conclusion := type.getForallBody.consumeMData
  if conclusion.isAppOf ``MixedError then .mixed
  else if isFiniteness conclusion then .finiteness
  -- An absolute-error bound is also an inequality; its left side is the absolute difference.
  else if (conclusion.isAppOfArity ``LE.le 4 || conclusion.isAppOfArity ``LT.lt 4) &&
      conclusion.getAppArgs[0]!.isConstOf ``Real && !conclusion.getAppArgs[2]!.isAppOf ``abs then
    .order
  else .numerical
/-- A registered numerical theorem prepared for matching. Its local rounding premise is
specialized and its container reads are normalized. Universes and remaining metavariables are
abstracted so each use instantiates them afresh. -/
structure Rule where
  /-- The registered theorem, or the hypothesis it comes from. -/
  name : Name
  /-- An exact observation, contributing no error, rather than an error bound. -/
  exact : Bool
  /-- The prepared statement, its universes and remaining metavariables abstracted. -/
  prepared : AbstractMVarsResult
  /-- Position among the candidates for one computation, that of its registration, or among the
  exact operations for one of them. The analysis tries lower first. -/
  order : Nat := 0
  /-- An exact observation that a premise selects (`selects`): it states one case of its
  computation, where one without such a premise restates the computation and always applies. -/
  selective : Bool := false
  /-- A mixed bound stated in ulps of the format (`Model.halfUlpAt`). The constants of the
  standard model are numerals for a format without variables, and arithmetic evaluates them,
  so the other mixed bounds of the computation are tried first there. -/
  ulps : Bool := false

/-- Compare rules by theorem name and `exact` flag, ignoring the prepared statement, so the index
keeps one copy of a theorem registered twice. -/
instance : BEq Rule :=
  ⟨fun left right => left.name == right.name && left.exact == right.exact⟩

/-- A fresh instance of a prepared rule. -/
def Rule.instantiate (rule : Rule) : MetaM Lean.Expr :=
  return (← openAbstractMVarsResult rule.prepared).2.2

/-- What `Session.index` reads off a rule: the path of its computation in a discrimination tree,
its entry there, the heads of the computation and of the value it observes (`Session.ruled`), and
the observation whose operands its reference reads (`Session.observations`). -/
structure IndexedRule where
  /-- The path of the computation (`DiscrTree.mkPath`); empty for a rule that has no entry. -/
  keys : Array DiscrTree.Key
  /-- The entry. -/
  rule : Rule
  /-- The heads of the computation and of the value it observes. -/
  heads : Array Name := #[]
  /-- The observation whose operands the reference reads, for a rule that has one. -/
  observation? : Option Name := none

/-- Insert the entry where `DiscrTree.insertIfSpecific` does: under a path that is more than a
variable or an equation of variables. -/
def IndexedRule.insertInto (entry : IndexedRule) (tree : DiscrTree Rule) : DiscrTree Rule :=
  if entry.keys.isEmpty || entry.keys == #[.star] ||
      entry.keys == #[.const ``Eq 3, .star, .star, .star] then tree
  else tree.insertKeyValue entry.keys entry.rule

/-- Whether the entry is the same in every declaration that has its rule: it has no local
variable and no metavariable, and every constant of its proof but the rule is one of an imported
module. A constant of this file, such as an instance that preparing the rule found, need not
exist in the declaration that reads the entry next. -/
def IndexedRule.portable (entry : IndexedRule) : CoreM Bool := do
  let proof := entry.rule.prepared.expr
  if proof.hasFVar || proof.hasMVar then return false
  let environment ← getEnv
  return proof.getUsedConstants.all fun name =>
    name == entry.rule.name || (environment.getModuleIdxFor? name).isSome

/-- The number of rule sets (`rulesHash`) of which a process keeps what it prepared. An editor
that elaborates a file again after a change to one of its rules prepares a new set. A set beyond
this number replaces the kept ones, which are prepared again where they are used. -/
def keptRuleSets : Nat := 16

/-- The rules indexed in this process, by `rulesHash`, then by name and the tree the entry goes
to. A rule whose statement reads no container is prepared without the goal, so every `roundoff`
of a file after the first finds its entry here: `some none` for a rule that has no entry. `none`
is a rule that every call prepares: its preparation reads the goal, or its entry is not
portable (`IndexedRule.portable`). An entry stays as the first call prepared it: a later change
of the reducibility or of the instances that preparing it read does not change it. -/
initialize indexedRules :
    IO.Ref (Std.HashMap UInt64 (Std.HashMap (Name × Nat) (Option (Option IndexedRule)))) ←
  IO.mkRef {}

/-- A hash of what preparing a rule reads beside the goal: the statement of every registered
rule, in the order of their registration, and whether it is a `@[csimp]` theorem, the
declarations of the registered extensions, and the declarations of this file that these use,
through each other. A declaration of an imported
module stays as it is while the process lives. One of this file changes when an editor
elaborates the file again, so a rule or an extension that uses it gets another hash. A proof is
not read: preparing a rule reads statements and definitions. -/
def rulesHash : CoreM UInt64 := do
  let environment ← getEnv
  let body (info : ConstantInfo) : Option Lean.Expr :=
    if info matches .thmInfo _ then none else info.value?
  let constant (seed : UInt64) (name : Name) (info : ConstantInfo) : UInt64 :=
    mixHash (mixHash seed (hash name)) (mixHash info.type.hash ((body info).map (·.hash) |>.getD 0))
  let mut seed : UInt64 := 7
  let mut queued : NameSet := {}
  let mut pending : Array Name := #[]
  for name in roundoffRules.getState environment ++ (extensions.getState environment).names do
    let some info := environment.find? name | do
      seed := mixHash seed (hash name)
      continue
    seed := constant seed name info
    if Lean.Compiler.hasCSimpAttribute environment name then seed := mixHash seed 11
    if (environment.getModuleIdxFor? name).isNone && !queued.contains name then
      queued := queued.insert name
      pending := pending.push name
  while let some name := pending.back? do
    pending := pending.pop
    let some info := environment.find? name | continue
    for other in info.type.getUsedConstants ++ ((body info).map (·.getUsedConstants) |>.getD #[]) do
      if queued.contains other || (environment.getModuleIdxFor? other).isSome then continue
      let some otherInfo := environment.find? other | continue
      seed := constant seed other otherInfo
      queued := queued.insert other
      pending := pending.push other
  return seed

/-- What the process keeps of rule `name` for the tree `kind` under `seed` (`indexedRules`). -/
def keptRule? (seed : UInt64) (name : Name) (kind : Nat) :
    CoreM (Option (Option (Option IndexedRule))) :=
  return ((← indexedRules.get).get? seed).bind (·.get? (name, kind))

/-- The entry of rule `name` in the tree `kind`: the one kept for `seed` (`indexedRules`), or
the one that `compute` returns. That one is kept unless preparing the rule reads the goal
(`contextual`) or the entry is not portable (`IndexedRule.portable`): then every call prepares
the rule. Nothing is kept once the heartbeat budget is spent: a step may then have failed for
lack of it, and a nested tactic reports that as an ordinary failure. -/
def indexedRule (seed : UInt64) (name : Name) (kind : Nat) (contextual : CoreM Bool)
    (compute : MetaM (Option IndexedRule)) : MetaM (Option IndexedRule) := do
  match ← keptRule? seed name kind with
  | some (some entry?) => return entry?
  | some none => compute
  | none =>
      let entry? ← compute
      let portable ← match entry? with
        | some entry => entry.portable
        | none => pure true
      let value := if portable && !(← contextual) then some entry? else none
      Core.checkSystem "roundoff"
      indexedRules.modify fun sets =>
        (if sets.size ≥ keptRuleSets && !sets.contains seed then {} else sets).alter seed
          fun rules? => some ((rules?.getD {}).insert (name, kind) value)
      return entry?

/-- A lemma tried on simple side conditions: the tactic applying it, and the head and index of
its conclusion. -/
structure Helper where
  /-- The lemma. -/
  name : Name
  /-- The tactic that applies it. -/
  tactic : TSyntax `tactic
  /-- The head of its conclusion, compared with a side condition's before any unification. -/
  head : Option Name
  /-- Its conclusion, indexed for retrieval. -/
  patterns : DiscrTree Unit

/-- Proofs without metavariables, by the proposition they prove, each with the local variables it
uses. Such a proof holds in every local context that has those variables. -/
abbrev Settled := Std.HashMap Lean.Expr (Array (Lean.Expr × Array FVarId))

/-- A settled proof of `type` whose local variables are all in the current context. -/
def Settled.proof? (settled : Settled) (type : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let context ← getLCtx
  return (settled.getD type #[]).findSome? fun (proof, used) =>
    if used.all context.contains then some proof else none

/-- Record `proof` of `type`, unless it has metavariables. -/
def Settled.remember (settled : Settled) (type proof : Lean.Expr) : MetaM Settled := do
  let proof ← instantiateMVars proof
  if proof.hasMVar then return settled
  let used := (collectFVars {} proof).fvarIds
  return settled.insert type ((settled.getD type #[]).push (proof, used))

/-- A costly estimate kept for reuse in other scopes, with the estimates of its parts that its
analysis cached, each with whether it is mixed, and the obligations its analysis left open (their
metavariables, user names and types, in the order they arose), the scope facts of its
computation (`Session.scopeFacts`), the fuel it needs and the local variables it mentions. Its
proofs are instantiated, so they survive the rollback of the attempt that made them. -/
structure Derivation where
  /-- The kept estimate. -/
  estimate : Estimate
  /-- The cached estimates of its parts: whether each is mixed, its computation and its estimate. -/
  parts : Array (Bool × Lean.Expr × Estimate)
  /-- The obligations it left: their metavariables, user names and types. -/
  obligations : Array (MVarId × Name × Lean.Expr)
  /-- The scope facts of its computation (`Session.scopeFacts`). -/
  facts : Array FVarId
  /-- The traversal fuel it needs: one more than the depth of the analyses below it, or the
  fuel it had when one of them ran out. -/
  fuel : Nat
  /-- The local variables its computation, terms and obligations mention, collected when a reuse
  first needs them. -/
  locals : Thunk (Array FVarId)

/-- Whether `term` mentions a local variable satisfying `wanted`, visiting each distinct subterm
once. `Expr.hasAnyFVar` visits a shared subterm once per occurrence. -/
def mentions (term : Lean.Expr) (wanted : FVarId → Bool) : Bool :=
  (term.findExt? fun child =>
    if !child.hasFVar then .done
    else match child with
      | .fvar id => if wanted id then .found else .done
      | _ => .visit).isSome

/-- The observer of a bounded value and the head of the value it observes, under the imports
that value applies, which a hypothesis bound must share with a computation to apply to it. -/
abbrev BoundHeads := Option Name × Option (Option Name)

/-- How a hypothesis bounds a value, read once per local variable: whether it is a proposition,
the producer of the value it concludes finite with a mixed bound when it is stated like a
generated theorem, and the heads of the value its conclusion bounds, and of the value of that
mixed bound. -/
structure Given where
  /-- Whether the hypothesis is a proposition. -/
  proposition : Bool
  /-- The producer of the value it concludes finite with a mixed bound, when it is stated like a
  generated theorem. -/
  producer? : Option Lean.Expr := none
  /-- The heads of the value its conclusion bounds. -/
  heads? : Option BoundHeads := none
  /-- The heads of the value of that generated mixed bound. -/
  generatedHeads? : Option BoundHeads := none

/-- The answers of `carries` during one analysis, by constant and by whether it is read as a type
(`0`) or a term (`1`), and of `mayHoldFunction` (`2`). The environment only grows meanwhile, so an
answer stays right. -/
abbrev CarrierCache := IO.Ref (Std.HashMap (Name × Nat) Bool)

/-- The rules, normalizers and memo tables of one `roundoff` call. The simp sets depend only on
the environment and each normalizer adds its local hypotheses, while `bounds` is normalized under
the main goal's hypotheses and `failures` is keyed by the facts of a scope. Only `Session.prepare`
builds a session, and its fields are the engine's own and change with it. -/
structure Session where
  /-- Producers that program normalization keeps intact. -/
  boundaries : NameSet
  /-- The boundaries returning containers, kept intact even while a discriminant is reduced. -/
  containerProducers : NameSet
  /-- Constants already known not to reach a container type. -/
  containerFree : IO.Ref NameSet
  /-- Closed side conditions that already failed, with the facts of the scope they failed in
  (`Session.scopeFacts`). -/
  failures : IO.Ref (Std.HashMap Lean.Expr (Array (Array FVarId)))
  /-- Closed side conditions already proved. -/
  solved : IO.Ref Settled
  /-- Signs proved with no obligation. Unlike the signs of a scope, they outlive the branch or
  speculative attempt that proved them. -/
  settledSigns : IO.Ref Settled
  /-- Definitional comparisons of premises without metavariables, as `withConditions` found them. -/
  comparisons : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Bool)
  /-- Boolean facts that semantic simplification did not show equivalent, with the local results
  of checked references it rewrote with. -/
  inequivalent : IO.Ref (Std.HashSet (Lean.Expr × Lean.Expr × Array FVarId))
  /-- Computations whose analysis failed, by `Session.mode`, each with the facts of the scopes
  about it (`Session.scopeFacts`), the traversal fuel it had, whether it was part of a loop's step
  (`nested`) and its error. A rolled-back speculative attempt keeps these. -/
  analysisFailures : IO.Ref (Std.HashMap ((Bool × Bool × Bool × Bool) × Lean.Expr)
    (Array (Array FVarId × Nat × Bool × Exception)))
  /-- Whether each constant that a provenance check met can hold a numerical value (`carries`). -/
  carriers : CarrierCache
  /-- Laws that read container observations at their coordinates. -/
  coordinate : SimpTheorems
  /-- Traversal equalities that fuse source maps into loops. -/
  fold : SimpTheorems
  /-- Codec laws that decode a real observation through the selected scalar methods. -/
  decoding : SimpTheorems
  /-- The decoding lemmas, with `false = true` simplified to `False`, for deciding guards. -/
  guards : SimpTheorems
  /-- FloatLib meanings of configured operations, for comparing two computations. -/
  semantic : SimpTheorems
  /-- The semantic lemmas, also decoding Boolean classifiers of fresh propositions. -/
  classifiers : SimpTheorems
  /-- The selection of a branch by its simplified guard (`branchProcedures`), then `programStep`,
  `observeBranch`, `readSum` when a sum is read entrywise, and the registered procedures
  (`Extension.procedures`), which every normalizer except the semantic ones runs. -/
  procedures : Simp.SimprocsArray
  /-- `rulesHash` of the environment the session was prepared in. -/
  seed : UInt64 := 0
  /-- Registered numerical bounds and observations, indexed by their computation pattern. -/
  bounds : DiscrTree Rule := {}
  /-- Whether estimates are mixed bounds rather than absolute ones. -/
  mixed : Bool := false
  /-- Whether this analysis is part of the analysis of a loop's step: of a tuple fold, a mixed or
  absolute fold, or an exact step. A tuple fold analyzed there states no new agreement premise: its
  references could read the enclosing loop's state, whose provenance only that loop could check.
  An estimate established outside the step is reused there as it is, and a failure there is
  replayed only inside a step. -/
  nested : Bool := false
  /-- Exact operations and mixed-error rules, indexed like `bounds`. Only mixed analysis uses
  them, and absolute rules stay its fallback. -/
  mixedBounds : DiscrTree Rule := {}
  /-- Registered theorems concluding that a floating-point value is finite. -/
  finiteness : DiscrTree Rule := {}
  /-- Registered theorems concluding that a Boolean test is `false`, such as a finite value's NaN
  test. They decide branch guards (`refutedGuard?`). -/
  refutations : Array Name := #[]
  /-- Registered order facts, with their container reads normalized like the analyzed program. -/
  orders : Array Rule := #[]
  /-- The conclusion of each of `orders`, at fresh metavariables, to select the facts whose
  relation and sides fit a goal (`sameRelation`) before instantiating them. -/
  orderShapes : Array Lean.Expr := #[]
  /-- Identities of zero and one, and container reads through their producers, that tidy generated
  references, budgets and conditions. -/
  budget : SimpTheorems := {}
  /-- Scalar decoders, whose observed arguments are exact data. -/
  observations : NameSet := {}
  /-- Side-condition lemmas, in the order their tactics are tried. -/
  helpers : Array Helper := #[]
  /-- Whether a call of a correctly rounded primitive is kept as a computed value, its own exact
  reference, rather than analyzed as a rounding of its real function. The signs and finiteness
  of an expression of such calls follow from their contracts and the exact operations. -/
  computedCalls : Bool := false
  /-- Whether the analysis is inside the step of a loop whose state is a container. Inside such a
  step, an Option match that chooses a container is split on its discriminant. -/
  containerLoop : Bool := false
  /-- The producers with a registered read (`Extension.readRules`), each with its read. Zero and
  unit tests run without them. -/
  reads : Array (Name × Name) := #[]
  /-- The registered bounds that are also registered reads (`Extension.readRules`). They apply
  only to an entry of a container whose shape, or the shape of one it is computed from, is not
  literal. -/
  symbolicBounds : NameSet := {}
  /-- The terms and conditions `Session.simplify`, `Session.zeroBudget` and `Session.tidy` already
  tidied with the identities of zero and one, by the variables and local instances of the local
  context (`Session.tidyTerm`). An estimate repeats the tidied references and budgets of its parts,
  so one cache serves every estimate analyzed in a context. -/
  tidied : IO.Ref (Std.HashMap (Array FVarId × Array FVarId) Simp.State)
  /-- The local variables of the goal the analysis began in. Branches, loops and premises about
  every value introduce the others. -/
  base : Std.HashSet FVarId := {}
  /-- The simplification side conditions are tried with, without the local hypotheses: the
  identities of zero and one, the budget identities of the registered loops and the decoding of
  checked results. -/
  dischargeSimp : Option (Simp.Context × Simp.SimprocsArray) := none
  /-- The simplification caches of program normalization, by normalizer, local context and local
  instances. A normalizer sees the local rewrites of its context, which the variables of the context
  fix. -/
  normalized : IO.Ref (Std.HashMap (Name × Array FVarId × Array FVarId) Simp.State)
  /-- Whether `programStep`'s steps are kept for reuse (`memoizeStep`): set by `Session.normalize`
  while it shares its caches, in a local context without metavariables. -/
  memoized : IO.Ref Bool
  /-- The bounds the hypotheses state, by local variable and whether the analysis is mixed
  (`Session.given`). -/
  givens : IO.Ref (Std.HashMap (FVarId × Bool) Given)
  /-- The hypotheses that bound a value, by local context and whether the analysis is mixed
  (`Session.hypothesisBounds`). -/
  givenBounds : IO.Ref (Std.HashMap (Array FVarId × Bool) (Array (LocalDecl × Given)))
  /-- The simplification contexts of the normalizers with the local rewrites of a local context,
  by normalizer and the context's variables (`Session.localContext`). -/
  contexts : IO.Ref (Std.HashMap (Name × Array FVarId) Simp.Context)
  /-- `dischargeSimp` with the hypotheses of a local context, by its variables. -/
  hypothesisSimp : IO.Ref (Std.HashMap (Array FVarId) Simp.Context)
  /-- For each local variable: whether it is a hypothesis other than `True`, and the local
  variables its type, or its value for a local definition, mentions (`Session.describe`). -/
  descriptions : IO.Ref (Std.HashMap FVarId (Bool × Array FVarId))
  /-- The facts of the scopes about a term without metavariables (`Session.scopeFacts`), by the
  variables of the local context and the term. -/
  factsOf : IO.Ref (Std.HashMap (Array FVarId × Lean.Expr) (Array FVarId))
  /-- For each local variable whose type is a pair with a unit second component, its pair of first
  projection and unit (`Session.unitPair`), and `none` for any other variable. -/
  unitPairs : IO.Ref (Std.HashMap FVarId (Option Lean.Expr))
  /-- Sign goals that `positivity` did not prove, with the facts of their scope
  (`Session.scopeFacts`). It uses no other hypothesis. -/
  positivityFailures : IO.Ref (Std.HashMap Lean.Expr (Array (Array FVarId)))
  /-- Orders that linear arithmetic did not derive from the hypotheses (`orderByHypotheses`),
  with the facts of their scope (`Session.scopeFacts`). -/
  orderFailures : IO.Ref (Std.HashMap Lean.Expr (Array (Array FVarId)))
  /-- The lookup keys with their numerical operands exposed (`registeredBound?`), or `none` for
  a key whose exposure ran out of its budget. -/
  exposed : IO.Ref (Std.HashMap Lean.Expr (Option Lean.Expr))
  /-- The constants that head the computation of an indexed rule, or the value it observes. A
  rule reads such a constant as written, so the exposure of a lookup key does not unfold it. -/
  ruled : NameSet := {}
  /-- Sign goals whose search failed, with the local context and the largest depth that failed.
  Unlike the signs of a scope, they outlive a rolled-back attempt. -/
  signFailures : IO.Ref (Std.HashMap (Array FVarId × Lean.Expr) Nat)
  /-- Costly estimates by `Session.mode` and computation, reused where their variables are in
  scope and the facts of their computation are the same. A rolled-back attempt keeps them. -/
  derivations :
    IO.Ref (Std.HashMap ((Bool × Bool × Bool × Bool) × Lean.Expr) (Array Derivation))
  /-- The number of finiteness derivations refused so far because their derivation was in progress
  or too deeply nested (`Session.deriving`). A failed premise search that refused one did not
  settle its premise. -/
  finiteCuts : IO.Ref Nat
  /-- The finiteness propositions whose derivation is in progress, outermost first. A premise
  among them, or below `finiteDepth` of them, is not derived again (`Session.deriving`). -/
  finiteGoals : Array Lean.Expr := #[]
  /-- The least traversal fuel of the analyses since the innermost build began, from which
  `Analyze.analyze` learns the fuel a derivation needs. -/
  leastFuel : IO.Ref Nat

/-- The settings that change what an analysis proves: mixed bounds, the registered reads, which
zero and unit tests drop, computed calls and a container loop step. -/
def Session.mode (session : Session) : Bool × Bool × Bool × Bool :=
  (session.mixed, session.reads.isEmpty, session.computedCalls, session.containerLoop)

/-- The number of finiteness derivations that may be nested. A registered rule whose finiteness
premise is a new proposition each time, such as that of `-x` for `x`, stops there. -/
def finiteDepth : Nat := 64

/-- Whether the finiteness proposition `type` is not derived here: its derivation is in progress
(`Session.finiteGoals`), up to reducible unfolding, or `finiteDepth` derivations are nested. A
derivation that needs its own conclusion, through one rule or several, would repeat without end.
Only goals whose values have the same head are compared by unification. -/
def Session.deriving (session : Session) (type : Lean.Expr) : MetaM Bool := do
  -- A finiteness is an equality `test value = true`. Another proposition, such as the invariant
  -- `True` of a loop whose state decodes no value, is compared as it is.
  let value (finiteness : Lean.Expr) : Lean.Expr :=
    match finiteness.eq? with
    | some (_, test, _) => test.getAppArgs.back?.getD finiteness
    | none => finiteness
  let head := value type
  let refused ← if session.finiteGoals.size ≥ finiteDepth then pure true
    else session.finiteGoals.anyM fun active => do
      if active == type then return true
      let other := value active
      unless other.toHeadIndex == head.toHeadIndex && other.headNumArgs == head.headNumArgs do
        return false
      withNewMCtxDepth <| withReducible <| isDefEq active type
  if refused then session.finiteCuts.modify (· + 1)
  return refused
/-- Node results and open premises of the current branch or loop scope. -/
structure Analysis where
  /-- Results of repeated subexpressions, shared within the scope. -/
  cache : Lean.ExprMap Estimate := {}
  /-- Mixed results of repeated subexpressions, kept apart from the absolute ones. -/
  mixedCache : Lean.ExprMap Estimate := {}
  /-- The computations whose results this scope cached, in the order they were added, each with
  whether its result is mixed. -/
  added : Array (Bool × Lean.Expr) := #[]
  /-- Sign facts already settled in a local context: a proof that left no obligation, or the
  largest search depth that failed. -/
  signs : Std.HashMap (Array FVarId × Lean.Expr) (Option Lean.Expr × Nat) := {}
  /-- Premises left open in this scope, in the order they arose. -/
  pending : Array MVarId := #[]
  /-- Finiteness goals already proved in this scope, each with the local variables its proof uses.
  The proof may use premises of this scope, which are already pending. -/
  finite : Std.HashMap Lean.Expr (Array (MVarId × Array FVarId)) := {}

/-- The analysis monad: the session of the call and the state of the current scope. -/
abbrev AnalyzeM := ReaderT Session (StateRefT Analysis TacticM)

/-- The functions of the recursive analysis, as in `Analyze`. Each part of the analysis takes this
record and reaches the others through it, so that the parts can live in different modules.
`Analyze.recursor` ties them together. -/
structure Recursor where
  /-- The analysis function `Analyze.build`. -/
  build : Q(ℝ) → Nat → AnalyzeM Estimate
  /-- The analysis function `Analyze.prove`. -/
  prove : MVarId → Nat → AnalyzeM Bool
  /-- The analysis function `Analyze.proveNormalized`. -/
  proveNormalized : MVarId → Nat → AnalyzeM Bool
  /-- The analysis function `Analyze.proveForall`. -/
  proveForall : MVarId → Nat → AnalyzeM Bool
  /-- The analysis function `Analyze.proveNonzero`. -/
  proveNonzero : MVarId → Nat → AnalyzeM Bool
  /-- The analysis function `Analyze.enclosedNonzero`. -/
  enclosedNonzero : Q(ℝ) → Nat → AnalyzeM Lean.Expr
  /-- The analysis function `Analyze.proveRange`. -/
  proveRange : MVarId → Nat → AnalyzeM Bool
  /-- The analysis function `Analyze.rangeByBounds`. -/
  rangeByBounds : MVarId → Nat → AnalyzeM Bool
  /-- The analysis function `Analyze.proveFinite`. -/
  proveFinite : MVarId → Nat → AnalyzeM Bool
  /-- The analysis function `Analyze.deriveFinite`. -/
  deriveFinite : MVarId → Nat → AnalyzeM Bool
  /-- The analysis function `Analyze.exactAnalysis`. -/
  exactAnalysis : Q(ℝ) → Nat → AnalyzeM Estimate
  /-- The analysis function `Analyze.proveSelection`. -/
  proveSelection : MVarId → Nat → AnalyzeM Bool
  /-- The analysis function `Analyze.proveSign`. -/
  proveSign : MVarId → Nat → Nat → AnalyzeM Bool
  /-- The analysis function `Analyze.proveSignCore`. -/
  proveSignCore : MVarId → Nat → Nat → AnalyzeM Bool
  /-- The analysis function `Analyze.branchSign`. -/
  branchSign : MVarId → Lean.Expr → Nat → Nat → AnalyzeM (Option Bool)
  /-- The analysis function `Analyze.foldSign`. -/
  foldSign : MVarId → Lean.Expr → Nat → Nat → AnalyzeM (Option Bool)
  /-- The analysis function `Analyze.relativeSign`. -/
  relativeSign : MVarId → Q(ℝ) → Nat → Nat → AnalyzeM Bool
  /-- The analysis function `Analyze.primitiveSign`. -/
  primitiveSign : MVarId → Q(ℝ) → Nat → Nat → AnalyzeM Bool
  /-- The analysis function `Analyze.roundingSign`. -/
  roundingSign : MVarId → Q(ℝ) → Bool → Nat → Nat → AnalyzeM Bool
  /-- The analysis function `Analyze.absoluteFold`. -/
  absoluteFold : Loop → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr →
    Nat →
    AnalyzeM Estimate
  /-- The analysis function `Analyze.containerFold`. -/
  containerFold : Lean.Expr → Lean.Expr → Nat → AnalyzeM Estimate
  /-- The analysis function `Analyze.mixedFold`. -/
  mixedFold : Loop → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → Nat →
    AnalyzeM Estimate
  /-- The analysis function `Analyze.singleFold`. -/
  singleFold : Loop → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → Nat →
    AnalyzeM Estimate
  /-- The analysis function `Analyze.singleFoldAt`. -/
  singleFoldAt : Loop → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → Bool →
    Lean.Expr →
    Lean.Expr → Lean.Expr → Nat → AnalyzeM Estimate
  /-- The analysis function `Analyze.constantFold`. -/
  constantFold : Loop → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr →
    Nat →
    AnalyzeM Estimate
  /-- The analysis function `Analyze.exactStart`. -/
  exactStart : Lean.Expr → Lean.Expr → Lean.Expr → Bool → Option Q(ℝ) → Nat →
    AnalyzeM (Lean.Expr × Q(ℝ))
  /-- The analysis function `Analyze.exactStepCase`. -/
  exactStepCase : Lean.Expr → Lean.Expr → Lean.Expr → Bool → Lean.Expr → Lean.Expr → Q(ℝ) →
    Option Q(ℝ) → Nat → AnalyzeM (Lean.Expr × Q(ℝ))
  /-- The analysis function `Analyze.liftLoopObligations`. -/
  liftLoopObligations : Nat → LocalContext → LocalInstances → Array Lean.Expr → AnalyzeM Unit
  /-- The analysis function `Analyze.analyze`. -/
  analyze : Q(ℝ) → Nat → AnalyzeM Estimate

/-- A record whose every function fails. -/
instance : Inhabited Recursor := ⟨{
  build := fun _ _ => throwError "roundoff: no analysis",
  prove := fun _ _ => throwError "roundoff: no analysis",
  proveNormalized := fun _ _ => throwError "roundoff: no analysis",
  proveForall := fun _ _ => throwError "roundoff: no analysis",
  proveNonzero := fun _ _ => throwError "roundoff: no analysis",
  enclosedNonzero := fun _ _ => throwError "roundoff: no analysis",
  proveRange := fun _ _ => throwError "roundoff: no analysis",
  rangeByBounds := fun _ _ => throwError "roundoff: no analysis",
  proveFinite := fun _ _ => throwError "roundoff: no analysis",
  deriveFinite := fun _ _ => throwError "roundoff: no analysis",
  exactAnalysis := fun _ _ => throwError "roundoff: no analysis",
  proveSelection := fun _ _ => throwError "roundoff: no analysis",
  proveSign := fun _ _ _ => throwError "roundoff: no analysis",
  proveSignCore := fun _ _ _ => throwError "roundoff: no analysis",
  branchSign := fun _ _ _ _ => throwError "roundoff: no analysis",
  foldSign := fun _ _ _ _ => throwError "roundoff: no analysis",
  relativeSign := fun _ _ _ _ => throwError "roundoff: no analysis",
  primitiveSign := fun _ _ _ _ => throwError "roundoff: no analysis",
  roundingSign := fun _ _ _ _ _ => throwError "roundoff: no analysis",
  absoluteFold := fun _ _ _ _ _ _ _ _ => throwError "roundoff: no analysis",
  containerFold := fun _ _ _ => throwError "roundoff: no analysis",
  mixedFold := fun _ _ _ _ _ _ _ _ => throwError "roundoff: no analysis",
  singleFold := fun _ _ _ _ _ _ _ _ => throwError "roundoff: no analysis",
  singleFoldAt := fun _ _ _ _ _ _ _ _ _ _ _ => throwError "roundoff: no analysis",
  constantFold := fun _ _ _ _ _ _ _ _ => throwError "roundoff: no analysis",
  exactStart := fun _ _ _ _ _ _ => throwError "roundoff: no analysis",
  exactStepCase := fun _ _ _ _ _ _ _ _ _ => throwError "roundoff: no analysis",
  liftLoopObligations := fun _ _ _ _ => throwError "roundoff: no analysis",
  analyze := fun _ _ => throwError "roundoff: no analysis" }⟩

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
