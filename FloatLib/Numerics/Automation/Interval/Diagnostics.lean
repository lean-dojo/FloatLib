/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Backends
public import FloatLib.Numerics.Enclosure.Expression.Check
public meta import FloatLib.Numerics.Enclosure.Expression.Backends
public meta import FloatLib.Numerics.Enclosure.Expression.Check
public meta import Lean.Meta.LitValues
public meta import Mathlib.Util.Qq

/-!
# Failure diagnostics for interval proofs

`Tactic.diagnoseFailure` explains a failed binary-grid check without constructing proof evidence.
Algebraic failures follow the checker's subdivision order and use the existing evaluator to locate
the first rejected operation. Registered functions are inspected through their actual quoted
backend. An enclosure that includes a forbidden value is reported as an enclosure obstruction,
not as a claim about the real subexpression.

A diagnostic retry doubles the endpoint precision. It describes only the inspected box; the
tactic must still verify every successful proof with its usual kernel check. All work is
confined to the failure path, and the entry point restores the caller's metavariable state.

The diagnostics explain what the enclosures show. Whether a failure came from a heartbeat or
recursion limit is known only to the caller that caught it, so no message here advises raising a
budget.

The quoted-syntax readers unfold definitions, so they use `partial` with Lean's resource checks.
The obstruction walk below instead recurses structurally over the decoded `Interval.Expr`.
-/

public meta section

open Lean Meta Qq

namespace FloatLib.Numerics.Interval.Tactic

/--
A registered call as the diagnostics name it: the real function it encloses and, when its
registration states one, the argument enclosures that its enclosure accepts.
-/
structure RegisteredCall where
  /-- The real function or constant, such as `Real.log`. -/
  function : Name
  /-- The accepted argument enclosures, as a plural noun phrase, or `none` if not stated. -/
  acceptedDomain? : Option String := none

namespace Diagnostics

/-- Recover a closed natural literal after reducing its quoted expression. -/
private def readNat (e : Q(Nat)) : MetaM Nat := do
  let some n := (← withTransparency .all (whnf e)).rawNatLit?
    | throwError "expected a closed natural number"
  return n

/-- Read a signed integer from Lean’s two literal constructors. -/
private def readInt (e : Q(Int)) : MetaM Int := do
  let e : Q(Int) ← withTransparency .all (whnf e)
  match e with
  | ~q(Int.ofNat $n) => return Int.ofNat (← readNat n)
  | ~q(Int.negSucc $n) => return Int.negSucc (← readNat n)
  | _ => throwError "expected a closed integer"

/-- Decode a quoted rational exactly, retaining its signed numerator. -/
private def readRat (e : Q(ℚ)) : MetaM ℚ := do
  if let some r ← getRatValue? e then return r
  return Rat.divInt (← readInt q(Rat.num $e)) (← readNat q(Rat.den $e))

/-- Read only algebraic syntax; registered functions use the actual quoted backend below. -/
private partial def readExpr (e : Q(Interval.Expr)) : MetaM Interval.Expr :=
  withIncRecDepth do
    checkSystem "interval diagnostics"
    let e : Q(Interval.Expr) ← whnf e
    match e with
    | ~q(Interval.Expr.const $r) => return .const (← readRat r)
    | ~q(Interval.Expr.var $i) => return .var (← readNat i)
    | ~q(Interval.Expr.unary $op $a) =>
      let op : Q(UnaryOp) ← whnf op
      let operation ← match op with
        | ~q(UnaryOp.neg) => pure UnaryOp.neg
        | ~q(UnaryOp.abs) => pure UnaryOp.abs
        | ~q(UnaryOp.inv) => pure UnaryOp.inv
        | ~q(UnaryOp.pow $n) => pure (UnaryOp.pow (← readNat n))
        | _ => throwError "expected an algebraic unary operation"
      return .unary operation (← readExpr a)
    | ~q(Interval.Expr.binary $op $a $b) =>
      let op : Q(BinaryOp) ← whnf op
      let operation ← match op with
        | ~q(BinaryOp.add) => pure BinaryOp.add
        | ~q(BinaryOp.sub) => pure BinaryOp.sub
        | ~q(BinaryOp.mul) => pure BinaryOp.mul
        | ~q(BinaryOp.div) => pure BinaryOp.div
        | ~q(BinaryOp.min) => pure BinaryOp.min
        | ~q(BinaryOp.max) => pure BinaryOp.max
        | _ => throwError "expected a closed binary operation"
      return .binary operation (← readExpr a) (← readExpr b)
    | ~q(Interval.Expr.ternary TernaryOp.fma $a $b $c) =>
      return .ternary .fma (← readExpr a) (← readExpr b) (← readExpr c)
    | _ => throwError "native interval diagnostics require algebraic syntax"

/-- Decode the original rational coordinates in their variable-index order. -/
private partial def readBox (box : Q(Box)) : MetaM Box :=
  withIncRecDepth do
    checkSystem "interval diagnostics"
    let box : Q(Box) ← whnf box
    match box with
    | ~q([]) => return []
    | ~q($head :: $tail) =>
      return ⟨← readRat q(Interval.lo $head), ← readRat q(Interval.hi $head)⟩ ::
        (← readBox tail)
    | _ => throwError "expected a closed rational box"

/-- Display an algebraic binary operation in a failed expression. -/
private def binaryName : BinaryOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .min => "min"
  | .max => "max"

/-- Use the source real term when available, otherwise display its variable index. -/
private def atomMessage (atoms : Array Lean.Expr) (i : Nat) : MessageData :=
  match atoms[i]? with
  | some atom => m!"{atom}"
  | none => m!"x[{i}]"

/-- Bound the displayed syntax so expanded sums do not bury the failed numerical bound. -/
private def exprMessage (atoms : Array Lean.Expr) (e : Interval.Expr) : MessageData :=
  (go e).run' 32
where
  /-- Limit the displayed expression to the remaining node count. -/
  go (e : Interval.Expr) : StateM Nat MessageData := do
    let remaining ← get
    if remaining == 0 then return "…"
    set (remaining - 1)
    match e with
    | .const r => return if r < 0 ∨ r.den ≠ 1 then m!"({r})" else m!"{r}"
    | .var i => return atomMessage atoms i
    | .unary (.pow n) a => return m!"({← go a} ^ {n})"
    | .unary .neg a => return m!"(-{← go a})"
    | .unary .abs a => return m!"abs({← go a})"
    | .unary .inv a => return m!"inverse({← go a})"
    | .unary _ a => return m!"operation({← go a})"
    | .binary op a b => return m!"({← go a} {binaryName op} {← go b})"
    | .ternary .fma a b c => return m!"({← go a} * {← go b} + {← go c})"
    | .call index _ => return m!"registered operation {index}"

/-- Display both exact rational endpoints of an enclosure. -/
private def rangeMessage (I : Interval ℚ) : MessageData :=
  m!"[{I.lo}, {I.hi}]"

/-- Show at most six coordinates so large aggregate goals retain readable diagnostics. -/
private def boxMessage (atoms : Array Lean.Expr) (box : Box) : MessageData :=
  if box.isEmpty then "closed expression"
  else
    let entries := box.take 6 |>.zipIdx |>.map fun (I, i) =>
      m!"{atomMessage atoms i} in {rangeMessage I}"
    let rest := if box.length ≤ 6 then [] else [m!"… ({box.length - 6} more coordinates)"]
    MessageData.joinSep (entries ++ rest) ", "

/-- Interpret integer endpoints on the configured binary grid. -/
private def decodeRange (config : Backend.Config) (I : Interval Int) : Interval ℚ :=
  I.map (BinaryGrid.toRat config.precision)

/-- Check interruption and heartbeat limits before and after advisory evaluation. -/
private def checkedEval (e : Interval.Expr) (B : Backend Int)
    (env : Nat → Option (Interval Int)) : MetaM (Option (Interval Int)) := do
  checkSystem "interval diagnostics"
  let result := e.eval? B env
  checkSystem "interval diagnostics"
  return result

/-- Descend in evaluation order, using `eval?` itself to distinguish rejected children. -/
private def firstObstruction (atoms : Array Lean.Expr) (config : Backend.Config)
    (env : Nat → Option (Interval Int)) (e : Interval.Expr) : MetaM (Interval.Expr × MessageData) :=
  withIncRecDepth do
    checkSystem "interval diagnostics"
    let B := Backend.binaryGrid config
    match e with
    | .const r =>
      return ⟨e, m!"the backend could not enclose the constant {r}"⟩
    | .var i =>
      return ⟨e, m!"no interval is available for {atomMessage atoms i}"⟩
    | .unary op a =>
      let some I ← checkedEval a B env | firstObstruction atoms config env a
      let I := decodeRange config I
      let message := if op == .inv && decide (I.lo ≤ 0 ∧ 0 ≤ I.hi) then
          m!"inverse: {exprMessage atoms a} is enclosed by {rangeMessage I}, which includes \
            zero; the denominator enclosure must exclude zero."
        else m!"the backend returned no enclosure for {exprMessage atoms e}; reason unknown."
      return ⟨e, message⟩
    | .binary op a b =>
      let some _ ← checkedEval a B env | firstObstruction atoms config env a
      let some J ← checkedEval b B env | firstObstruction atoms config env b
      let J := decodeRange config J
      let message := if op == .div && decide (J.lo ≤ 0 ∧ 0 ≤ J.hi) then
          m!"division in {exprMessage atoms e}: denominator {exprMessage atoms b} is enclosed \
            by {rangeMessage J}, which includes zero; \
            the denominator enclosure must exclude zero."
        else m!"the backend returned no enclosure for {exprMessage atoms e}; reason unknown."
      return ⟨e, message⟩
    | .ternary _ a b c =>
      let some _ ← checkedEval a B env | firstObstruction atoms config env a
      let some _ ← checkedEval b B env | firstObstruction atoms config env b
      let some _ ← checkedEval c B env | firstObstruction atoms config env c
      return ⟨e, m!"the backend returned no enclosure for {exprMessage atoms e}; reason unknown."⟩
    | .call index _ =>
      return ⟨e, m!"registered operation {index} returned no enclosure; check its domain \
        conditions or increase the approximation settings."⟩
termination_by structural e

/-- A diagnostic search either certifies its boxes, isolates a failing leaf, or runs out of fuel. -/
private inductive SearchResult where
  | certified
  | leaf (box : Box) (splits : Nat)
  | limited

/--
Mirror `Expr.check`'s short-circuit order with a bounded number of diagnostic box visits.
The numerical decisions and the choice of split remain those of `checkBox` and `bisect?`.
-/
private def findLeaf (e : Interval.Expr) (B : Backend Int) (relation : Relation)
    (box : Box) (depth splits : Nat) : StateRefT Nat MetaM SearchResult :=
  withIncRecDepth do
    checkSystem "interval diagnostics"
    let fuel ← get
    if fuel == 0 then return .limited
    set (fuel - 1)
    let passed := e.checkBox B relation box
    checkSystem "interval diagnostics"
    if passed then return .certified
    match depth with
    | 0 => return .leaf box splits
    | depth + 1 =>
      let some (left, right) := box.bisect? | return .leaf box splits
      match ← findLeaf e B relation left depth (splits + 1) with
      | .certified => findLeaf e B relation right depth (splits + 1)
      | result => return result
termination_by depth

/--
Probe one larger precision without treating a diagnostic retry as a proof.

`readExpr` accepts only algebraic expressions, and the binary-grid backend reads the Taylor degree
only for elementary functions, so a larger degree could not change a diagnosed check.
-/
private def retryMessage (e : Interval.Expr) (obstruction : Option Interval.Expr)
    (box : Box) (relation : Relation) (config : Backend.Config) :
    MetaM (Option MessageData) := do
  -- One bounded probe doubles the precision; a successful leaf is not a proof of the box from
  -- which it was subdivided.
  let candidates :=
    if config.precision < 128 then
      [("precision", max 16 (2 * config.precision),
        { config with precision := max 16 (2 * config.precision) })] else []
  for (setting, value, trial) in candidates do
    checkSystem "interval diagnostics"
    let B := Backend.binaryGrid trial
    let passed := e.checkBox B relation box
    checkSystem "interval diagnostics"
    if passed then
      return some m!"A diagnostic retry passes on this box with {setting} := {value}; \
        retry the tactic with that setting."
    if let some operation := obstruction then
      if let some intervals := box.enclose? B then
        if (← checkedEval operation B (fun i => intervals[i]?)).isSome then
          return some m!"A diagnostic retry encloses this operation with {setting} := {value}; \
            the full inequality still needs checking."
  return none

/-- Explain a failed leaf and distinguish subdivision exhaustion from an unsplittable box. -/
private def leafMessage (atoms : Array Lean.Expr) (e : Interval.Expr) (box : Box)
    (relation : Relation) (config : Backend.Config) (depth splits : Nat) : MetaM MessageData := do
  let B := Backend.binaryGrid config
  let some intervals := box.enclose? B
    | return "interval could not certify: the backend could not enclose the input box."
  let (reason, obstruction) ← match ← checkedEval e B (fun i => intervals[i]?) with
    | none => do
      let failure ← firstObstruction atoms config (fun i => intervals[i]?) e
      pure (failure.2, some failure.1)
    | some I =>
      let required := if relation == .negative then "< 0" else "≤ 0"
      pure (m!"the enclosure of {exprMessage atoms e} is {rangeMessage (decodeRange config I)}; \
        its upper endpoint does not establish {required}.", none)
  let splittable := box.bisect?.isSome
  let budget := if !splittable then
      m!"No input interval can be subdivided."
    else m!"Subdivision depth {depth} exhausted after {splits} splits on this branch."
  let hint ← retryMessage e obstruction box relation config
  let hint := hint.orElse fun _ =>
    if splittable then some "Try tighter input bounds or more subdivision depth." else none
  let message := m!"interval could not certify: {reason}\n\
    Box: {boxMessage atoms box}. {budget}"
  return match hint with
    | some hint => m!"{message}\n{hint}"
    | none => message

/-- Evaluate a quoted subexpression on quoted binary-grid inputs by reduction. -/
private def evalQuoted (backend : Q(Backend Int)) (inputs : Q(List (Interval Int)))
    (e : Q(Interval.Expr)) : MetaM (Option Q(Interval Int)) := do
  checkSystem "interval diagnostics"
  let result : Q(Option (Interval Int)) ← withTransparency .all
    (whnf q(Interval.Expr.eval? $e $backend (fun i => $inputs[i]?)))
  match result with
  | ~q(some $I) => return some I
  | ~q(none) => return none
  | _ => throwError "expected a closed interval evaluation"

/-- Decode a quoted binary-grid enclosure to its exact rational endpoints. -/
private def readRange (precision : Nat) (I : Q(Interval Int)) : MetaM (Interval ℚ) :=
  return ⟨BinaryGrid.toRat precision (← readInt q(Interval.lo $I)),
    BinaryGrid.toRat precision (← readInt q(Interval.hi $I))⟩

/-- Read the elements of a closed quoted list of expressions. -/
private partial def readArguments (args : Q(List Interval.Expr)) :
    MetaM (List Q(Interval.Expr)) := do
  let args : Q(List Interval.Expr) ← whnf args
  match args with
  | ~q([]) => return []
  | ~q($head :: $tail) => return head :: (← readArguments tail)
  | _ => throwError "expected a closed argument list"

/-- An operation that the backend rejected, with the enclosures of the operands it received. -/
private inductive Rejection where
  /-- A registered call, by call index, with its arguments and their enclosures. -/
  | call (index : Nat) (arguments : List (Q(Interval.Expr) × Interval ℚ))
  /-- A division or reciprocal whose denominator enclosure contains zero. -/
  | division (expression denominator : Q(Interval.Expr)) (range : Interval ℚ)
  /-- Another rejected operation, or an input the backend could not enclose. -/
  | other (expression : Q(Interval.Expr))

/-- Find the first operation, in evaluation order, whose enclosure the backend rejects. -/
private partial def findRejection (backend : Q(Backend Int)) (inputs : Q(List (Interval Int)))
    (precision : Nat) (e : Q(Interval.Expr)) : MetaM Rejection :=
  withIncRecDepth do
    let e : Q(Interval.Expr) ← whnf e
    let search := findRejection backend inputs precision
    let evaluate := evalQuoted backend inputs
    let includesZero (I : Interval ℚ) := decide (I.lo ≤ 0) && decide (0 ≤ I.hi)
    match e with
    | ~q(Interval.Expr.unary $op $a) =>
      let some I ← evaluate a | search a
      let I ← readRange precision I
      let op : Q(UnaryOp) ← whnf op
      match op with
      | ~q(UnaryOp.inv) => return if includesZero I then .division e a I else .other e
      | _ => return .other e
    | ~q(Interval.Expr.binary $op $a $b) =>
      let some _ ← evaluate a | search a
      let some J ← evaluate b | search b
      let J ← readRange precision J
      let op : Q(BinaryOp) ← whnf op
      match op with
      | ~q(BinaryOp.div) => return if includesZero J then .division e b J else .other e
      | _ => return .other e
    | ~q(Interval.Expr.ternary TernaryOp.fma $a $b $c) =>
      let some _ ← evaluate a | search a
      let some _ ← evaluate b | search b
      let some _ ← evaluate c | search c
      return .other e
    | ~q(Interval.Expr.call $index $args) =>
      let mut arguments := #[]
      for arg in ← readArguments args do
        let some I ← evaluate arg | return (← search arg)
        arguments := arguments.push (arg, ← readRange precision I)
      return .call (← readNat index) arguments.toList
    | _ => return .other e

/-- A quoted operand as source syntax, or `none` when it is not algebraic, such as a call. -/
private def operandText? (atoms : Array Lean.Expr) (e : Q(Interval.Expr)) :
    MetaM (Option MessageData) := do
  try
    return some (exprMessage atoms (← readExpr e))
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return none

/-- Show a quoted operand as source syntax when it is algebraic, otherwise by its role. -/
private def operandMessage (atoms : Array Lean.Expr) (role : MessageData)
    (e : Q(Interval.Expr)) : MetaM MessageData :=
  return (← operandText? atoms e).getD role

/--
Name argument `k` of a call with `count` arguments, then its source syntax when that is algebraic,
and its enclosure: `its argument x in [0, 1]`, or `its second argument in [0, 1]` for an argument
that is itself a registered call.
-/
private def argumentMessage (atoms : Array Lean.Expr) (count k : Nat) (arg : Q(Interval.Expr))
    (range : Interval ℚ) : MetaM MessageData := do
  let role := if count == 1 then "its argument" else match k with
    | 0 => "its first argument"
    | 1 => "its second argument"
    | 2 => "its third argument"
    | _ => s!"its argument {k + 1}"
  return match ← operandText? atoms arg with
    | some text => m!"{role} {text} in {rangeMessage range}"
    | none => m!"{role} in {rangeMessage range}"

/-- Explain a rejected operation, quoting the accepted domain that its registration states. -/
private def rejectionMessage (atoms : Array Lean.Expr) (calls : Array RegisteredCall) :
    Rejection → MetaM MessageData
  | .call index arguments => do
    let call? := calls[index]?
    let function := match call? with
      | some call => m!"the {MessageData.ofConstName call.function} enclosure"
      | none => m!"registered operation {index}"
    let operands ← arguments.zipIdx.mapM fun ((arg, range), k) =>
      argumentMessage atoms arguments.length k arg range
    let rejected := match operands with
      | [] => m!"{function} returned no bounds"
      | _ => m!"{function} rejected {MessageData.joinSep operands " and "}"
    return match call?.bind (·.acceptedDomain?) with
      | some domain => m!"{rejected}. It accepts only {domain}."
      | none => m!"{rejected}."
  | .division expression denominator range => do
    let operation ← operandMessage atoms "a division" expression
    let denominator ← operandMessage atoms "its denominator" denominator
    return m!"in {operation}, {denominator} is enclosed by {rangeMessage range}, which \
      includes zero; the denominator enclosure must exclude zero."
  | .other expression => do
    let operation ← operandMessage atoms "an operation" expression
    return m!"the backend returned no enclosure for {operation}."

/-- Explain why the backend could not evaluate the expression on the original box. -/
private def rejectedOnBox (atoms : Array Lean.Expr) (calls : Array RegisteredCall)
    (backend : Q(Backend Int)) (inputs : Q(List (Interval Int))) (precision : Nat)
    (expression : Q(Interval.Expr)) (boxText : MessageData) : MetaM MessageData := do
  let reason ← rejectionMessage atoms calls (← findRejection backend inputs precision expression)
  return m!"interval could not certify: on the original box, {reason}\nBox: {boxText}."

end Diagnostics

/-- Inspect the actual registered backend by reduction, within the caller's diagnostic budget.
The displayed enclosure belongs to the original box; subdivision may have narrower children.
When the backend rejects an operation on that box, the message names it and, for a registered
call, quotes the accepted domain from `calls`, the registered calls in call-index order.
The relation is reduced as in `diagnoseFailure`, and a term that is neither relation is an error. -/
def diagnoseRegisteredFailure (expression : Q(Interval.Expr)) (backend : Q(Backend Int))
    (box : Q(Box)) (config : Q(Backend.Config)) (relation : Q(Relation)) (depth : Q(Nat))
    (atoms : Array Lean.Expr := #[]) (calls : Array RegisteredCall := #[]) :
    MetaM MessageData := withoutModifyingState do
  let bounds ← Diagnostics.readBox box
  let boxText := Diagnostics.boxMessage atoms bounds
  let intervals : Q(Option (List (Interval Int))) ←
    withTransparency .all (whnf q(Box.enclose? $box $backend))
  let ~q(some $inputs) := intervals
    | return m!"interval could not enclose the original input box: {boxText}."
  let precision ← Diagnostics.readNat q(Backend.Config.precision $config)
  let some I ← Diagnostics.evalQuoted backend inputs expression
    | Diagnostics.rejectedOnBox atoms calls backend inputs precision expression boxText
  let range ← Diagnostics.readRange precision I
  let relation : Q(Relation) ← whnf relation
  let strict ← match relation with
    | ~q(Relation.negative) => pure true
    | ~q(Relation.nonpositive) => pure false
    | _ => throwError "expected a closed interval relation"
  let required := if strict then "< 0" else "≤ 0"
  if (if strict then range.hi < 0 else range.hi ≤ 0) then
    return m!"interval could not certify: the enclosure on the original box establishes \
      {required}, but kernel verification failed."
  let depth ← Diagnostics.readNat depth
  return m!"interval could not certify: on the original box, the expression is enclosed by \
    {Diagnostics.rangeMessage range}; its upper endpoint does not establish {required}.\n\
    Box: {boxText}. Verification used subdivision depth {depth}. Try tighter input bounds, \
    more subdivision, or higher approximation settings."

/-- Inspect the executable checker before kernel verification. A failed leaf can reject the
attempt early; this advisory result never supplies evidence for a successful proof. -/
def preflightCheck (expression : Q(Interval.Expr)) (box : Q(Box))
    (config : Q(Backend.Config)) (relation : Q(Relation)) (depth : Q(Nat)) :
    MetaM (Option Bool) := withoutModifyingState do
  let e ← Diagnostics.readExpr expression
  let box ← Diagnostics.readBox box
  let config : Backend.Config :=
    ⟨← Diagnostics.readNat q(Backend.Config.precision $config),
      ← Diagnostics.readNat q(Backend.Config.degree $config)⟩
  let relation : Q(Relation) ← whnf relation
  let relation ← match relation with
    | ~q(Relation.nonpositive) => pure Relation.nonpositive
    | ~q(Relation.negative) => pure Relation.negative
    | _ => throwError "expected a closed interval relation"
  let depth ← Diagnostics.readNat depth
  let (result, _) ←
    (Diagnostics.findLeaf e (Backend.binaryGrid config) relation box depth 0).run 512
  return match result with
    | .certified => some true
    | .leaf _ _ => some false
    | .limited => none

/--
Explain a failed `Expr.check` using its quoted expression, box, binary-grid configuration, relation,
and subdivision depth. The optional `atoms` array supplies the original real terms in variable
index order; otherwise variables are displayed as `x[i]`.

Call only after the kernel verification fails. This function returns advisory text, never proof
evidence. It restores Meta state even on exceptions and propagates interrupts, heartbeat exhaustion,
and recursion limits. Unknown inspection failures receive a generic diagnostic. A bounded search
can report that its own diagnostic budget ran out, without claiming subdivision was exhausted.
-/
def diagnoseFailure (expression : Q(Interval.Expr)) (box : Q(Box))
    (config : Q(Backend.Config)) (relation : Q(Relation)) (depth : Q(Nat))
    (atoms : Array Lean.Expr := #[]) : MetaM MessageData := withoutModifyingState do
  try
    checkSystem "interval diagnostics"
    for input in [expression, box, config, relation, depth] do
      let input ← instantiateMVars input
      if input.hasFVar || input.hasMVar then
        throwError "diagnostics require closed checker inputs"
    let e ← Diagnostics.readExpr expression
    let box ← Diagnostics.readBox box
    let config : Backend.Config :=
      ⟨← Diagnostics.readNat q(Backend.Config.precision $config),
        ← Diagnostics.readNat q(Backend.Config.degree $config)⟩
    let relation : Q(Relation) ← whnf relation
    let relation ← match relation with
      | ~q(Relation.nonpositive) => pure Relation.nonpositive
      | ~q(Relation.negative) => pure Relation.negative
      | _ => throwError "expected a closed interval relation"
    let depth ← Diagnostics.readNat depth
    let (result, _) ←
      (Diagnostics.findLeaf e (Backend.binaryGrid config) relation box depth 0).run 512
    let message ← match result with
    | .certified =>
      return "interval could not certify: the executable checker accepts this goal, but kernel \
        verification failed."
    | .limited =>
      return m!"interval could not certify: the diagnostic budget of 512 boxes was exhausted \
        before a failing leaf was isolated (subdivision depth {depth})."
    | .leaf box splits => Diagnostics.leafMessage atoms e box relation config depth splits
    checkSystem "interval diagnostics"
    return message
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return "interval could not certify this inequality; diagnostics could not inspect the \
      checker inputs or backend failure."

end FloatLib.Numerics.Interval.Tactic
