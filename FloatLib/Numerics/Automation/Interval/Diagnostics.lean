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

Diagnostic retries change one accuracy setting at a time. They describe only the inspected box;
the tactic must still verify every successful proof with its usual kernel check. All work is
confined to the failure path, and the entry point restores the caller's metavariable state.
-/

public meta section

open Lean Meta Qq

namespace FloatLib.Numerics.Interval.Tactic

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
private partial def firstObstruction (atoms : Array Lean.Expr) (config : Backend.Config)
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

/-- Probe one larger precision or degree without treating a diagnostic retry as a proof. -/
private def retryMessage (e : Interval.Expr) (obstruction : Option Interval.Expr)
    (box : Box) (relation : Relation) (config : Backend.Config) :
    MetaM (Option MessageData) := do
  -- Two bounded probes change one setting at a time; a successful leaf is not a proof of the box
  -- from which it was subdivided.
  let candidates :=
    (if config.precision < 128 then
      [("precision", max 16 (2 * config.precision),
        { config with precision := max 16 (2 * config.precision) })] else []) ++
    (if config.degree < 32 then
      [("degree", max 8 (2 * config.degree),
        { config with degree := max 8 (2 * config.degree) })] else [])
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

end Diagnostics

/-- Inspect the actual registered backend by reduction, within the caller's diagnostic budget.
The displayed enclosure belongs to the original box; subdivision may have narrower children. -/
def diagnoseRegisteredFailure (expression : Q(Interval.Expr)) (backend : Q(Backend Int))
    (box : Q(Box)) (config : Q(Backend.Config)) (relation : Q(Relation)) (depth : Q(Nat))
    (atoms : Array Lean.Expr := #[]) : MetaM MessageData := withoutModifyingState do
  let bounds ← Diagnostics.readBox box
  let boxText := Diagnostics.boxMessage atoms bounds
  let intervals : Q(Option (List (Interval Int))) ←
    withTransparency .all (whnf q(Box.enclose? $box $backend))
  let ~q(some $inputs) := intervals
    | return m!"interval could not enclose the original input box: {boxText}."
  let result : Q(Option (Interval Int)) ← withTransparency .all
    (whnf q(Interval.Expr.eval? $expression $backend (fun i => $inputs[i]?)))
  let ~q(some $I) := result
    | return m!"interval could not enclose a registered operation on the original box: \
      {boxText}. Check its accepted domain and approximation settings."
  let precision ← Diagnostics.readNat q(Backend.Config.precision $config)
  let lo ← Diagnostics.readInt q(Interval.lo $I)
  let hi ← Diagnostics.readInt q(Interval.hi $I)
  let range : Interval ℚ := ⟨BinaryGrid.toRat precision lo, BinaryGrid.toRat precision hi⟩
  let strict := relation.isAppOf ``Relation.negative
  let required := if strict then "< 0" else "≤ 0"
  if (if strict then range.hi < 0 else range.hi ≤ 0) then
    return m!"The original-box enclosure establishes {required}, but kernel verification \
      did not complete. A larger finite `(maxHeartbeats := ...)` may be needed."
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
      return "interval could not certify: diagnostic evaluation passed, but kernel verification \
        failed for an unknown reason."
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
