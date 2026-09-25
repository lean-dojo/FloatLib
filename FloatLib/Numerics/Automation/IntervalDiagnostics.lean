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
It follows the checker's subdivision order and uses the existing evaluator and backend operations
to locate the first rejected operation on a failing leaf. An enclosure that includes a forbidden
value is reported as an enclosure obstruction, not as a claim about the real subexpression.

Diagnostic retries change one accuracy setting at a time. They describe only the inspected box;
the tactic must still verify every successful proof with its usual kernel check. All work is
confined to the failure path, and the entry point restores the caller's metavariable state.
-/

public meta section

open Lean Meta Qq

namespace FloatLib.Numerics.Interval.Tactic

namespace Diagnostics

private def readNat (e : Q(Nat)) : MetaM Nat := do
  let some n := (← withTransparency .all (whnf e)).rawNatLit?
    | throwError "expected a closed natural number"
  return n

private def readInt (e : Q(Int)) : MetaM Int := do
  let e : Q(Int) ← withTransparency .all (whnf e)
  match e with
  | ~q(Int.ofNat $n) => return Int.ofNat (← readNat n)
  | ~q(Int.negSucc $n) => return Int.negSucc (← readNat n)
  | _ => throwError "expected a closed integer"

private def readRat (e : Q(ℚ)) : MetaM ℚ := do
  if let some r ← getRatValue? e then return r
  return Rat.divInt (← readInt q(Rat.num $e)) (← readNat q(Rat.den $e))

private def readUnary (e : Q(UnaryOp)) : MetaM UnaryOp := do
  let e : Q(UnaryOp) ← whnf e
  match e with
  | ~q(UnaryOp.neg) => return .neg
  | ~q(UnaryOp.abs) => return .abs
  | ~q(UnaryOp.inv) => return .inv
  | ~q(UnaryOp.pow $n) => return .pow (← readNat n)
  | ~q(UnaryOp.exp) => return .exp
  | ~q(UnaryOp.log) => return .log
  | ~q(UnaryOp.sin) => return .sin
  | ~q(UnaryOp.cos) => return .cos
  | ~q(UnaryOp.tan) => return .tan
  | ~q(UnaryOp.asin) => return .asin
  | ~q(UnaryOp.acos) => return .acos
  | ~q(UnaryOp.atan) => return .atan
  | ~q(UnaryOp.sinh) => return .sinh
  | ~q(UnaryOp.cosh) => return .cosh
  | ~q(UnaryOp.tanh) => return .tanh
  | ~q(UnaryOp.sqrt) => return .sqrt
  | _ => throwError "expected a closed unary operation"

private def readBinary (e : Q(BinaryOp)) : MetaM BinaryOp := do
  let e : Q(BinaryOp) ← whnf e
  match e with
  | ~q(BinaryOp.add) => return .add
  | ~q(BinaryOp.sub) => return .sub
  | ~q(BinaryOp.mul) => return .mul
  | ~q(BinaryOp.div) => return .div
  | ~q(BinaryOp.min) => return .min
  | ~q(BinaryOp.max) => return .max
  | _ => throwError "expected a closed binary operation"

private partial def readExpr (e : Q(Interval.Expr)) : MetaM Interval.Expr :=
  withIncRecDepth do
    checkSystem "interval diagnostics"
    let e : Q(Interval.Expr) ← whnf e
    match e with
    | ~q(Interval.Expr.const $r) => return .const (← readRat r)
    | ~q(Interval.Expr.var $i) => return .var (← readNat i)
    | ~q(Interval.Expr.unary $op $a) => return .unary (← readUnary op) (← readExpr a)
    | ~q(Interval.Expr.binary $op $a $b) =>
      return .binary (← readBinary op) (← readExpr a) (← readExpr b)
    | ~q(Interval.Expr.ternary TernaryOp.fma $a $b $c) =>
      return .ternary .fma (← readExpr a) (← readExpr b) (← readExpr c)
    | _ => throwError "expected a closed interval expression"

private partial def readBox (box : Q(Box)) : MetaM Box :=
  withIncRecDepth do
    let box : Q(Box) ← whnf box
    match box with
    | ~q([]) => return []
    | ~q($head :: $tail) =>
      return ⟨← readRat q(Interval.lo $head), ← readRat q(Interval.hi $head)⟩ ::
        (← readBox tail)
    | _ => throwError "expected a closed rational box"

private def unaryName : UnaryOp → String
  | .neg => "negation"
  | .abs => "abs"
  | .inv => "inverse"
  | .pow _ => "power"
  | .exp => "exp"
  | .log => "log"
  | .sin => "sin"
  | .cos => "cos"
  | .tan => "tan"
  | .asin => "arcsin"
  | .acos => "arccos"
  | .atan => "arctan"
  | .sinh => "sinh"
  | .cosh => "cosh"
  | .tanh => "tanh"
  | .sqrt => "sqrt"

private def binaryName : BinaryOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .min => "min"
  | .max => "max"

private def atomMessage (atoms : Array Lean.Expr) (i : Nat) : MessageData :=
  match atoms[i]? with
  | some atom => m!"{atom}"
  | none => m!"x[{i}]"

/-- Bound the displayed syntax so expanded sums do not bury the failed numerical bound. -/
private def exprMessage (atoms : Array Lean.Expr) (e : Interval.Expr) : MessageData :=
  (go e).run' 32
where
  go (e : Interval.Expr) : StateM Nat MessageData := do
    let remaining ← get
    if remaining == 0 then return "…"
    set (remaining - 1)
    match e with
    | .const r => return if r < 0 ∨ r.den ≠ 1 then m!"({r})" else m!"{r}"
    | .var i => return atomMessage atoms i
    | .unary (.pow n) a => return m!"({← go a} ^ {n})"
    | .unary .neg a => return m!"(-{← go a})"
    | .unary op a => return m!"{unaryName op}({← go a})"
    | .binary op a b => return m!"({← go a} {binaryName op} {← go b})"
    | .ternary .fma a b c => return m!"({← go a} * {← go b} + {← go c})"

private def rangeMessage (I : Interval ℚ) : MessageData :=
  m!"[{I.lo}, {I.hi}]"

private def boxMessage (atoms : Array Lean.Expr) (box : Box) : MessageData :=
  if box.isEmpty then "closed expression"
  else
    let entries := box.take 6 |>.zipIdx |>.map fun (I, i) =>
      m!"{atomMessage atoms i} in {rangeMessage I}"
    let rest := if box.length ≤ 6 then [] else [m!"… ({box.length - 6} more coordinates)"]
    MessageData.joinSep (entries ++ rest) ", "

private def decodeRange (config : Backend.Config) (I : Interval Int) : Interval ℚ :=
  I.map (BinaryGrid.toRat config.precision)

private def checkedEval (e : Interval.Expr) (B : Backend Int)
    (env : Nat → Option (Interval Int)) : MetaM (Option (Interval Int)) := do
  checkSystem "interval diagnostics"
  let result := e.eval? B env
  checkSystem "interval diagnostics"
  return result

private structure Obstruction where
  expression : Interval.Expr
  message : MessageData

private def unaryObstruction (atoms : Array Lean.Expr) (config : Backend.Config)
    (op : UnaryOp) (a : Interval.Expr) (I : Interval ℚ) : MessageData :=
  let argument := m!"{exprMessage atoms a} is enclosed by {rangeMessage I}"
  let context := m!"{unaryName op}: {argument}"
  match op with
  | .inv =>
    if I.lo ≤ 0 ∧ 0 ≤ I.hi then
      m!"{context}, which includes zero; the denominator enclosure must exclude zero."
    else m!"{context}; the backend returned no enclosure for an unknown reason."
  | .log =>
    if I.lo ≤ 0 then
      m!"{context}; the log backend requires a strictly positive lower endpoint."
    else m!"{context}; the backend returned no enclosure for an unknown reason."
  | .sqrt =>
    if I.lo < 0 then
      m!"{context}; the sqrt backend requires a nonnegative lower endpoint."
    else m!"{context}; the backend returned no enclosure for an unknown reason."
  | .asin | .acos =>
    if I.lo < -1 ∨ 1 < I.hi then
      m!"{context}; the backend requires an enclosing range contained in [-1, 1]."
    else if I.hi < I.lo then
      m!"{context}; the backend rejects reversed interval endpoints."
    else
      let coarse := [I.lo, I.hi].findSome? fun x =>
        if -1 < x ∧ x < 1 ∧ x ≠ 0 then
          let J := sqrtPointBounds (1 - x ^ 2) config.precision
          if J.lo ≤ 0 then some (x, J) else none
        else none
      match coarse with
      | some (x, J) =>
        m!"{context}, within [-1, 1], but the internal sqrt(1 - t^2) enclosure at \
          t = {x} is {rangeMessage J} and cannot separate the denominator from zero. \
          Increase precision."
      | none => m!"{context}; the backend returned no enclosure for an unknown reason."
  | .tan =>
    let cosine := cosBounds I config.degree
    if cosine.lo ≤ 0 ∧ 0 ≤ cosine.hi then
      m!"{context}; its cosine enclosure {rangeMessage cosine} includes zero. \
        This does not establish that the argument reaches a pole."
    else m!"{context}; the backend returned no enclosure for an unknown reason."
  | _ => m!"{context}; the backend returned no enclosure for an unknown reason."

/-- Descend in evaluation order, using `eval?` itself to distinguish rejected children. -/
private partial def firstObstruction (atoms : Array Lean.Expr) (config : Backend.Config)
    (env : Nat → Option (Interval Int)) (e : Interval.Expr) : MetaM Obstruction :=
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
      return ⟨e, unaryObstruction atoms config op a (decodeRange config I)⟩
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

private def leafMessage (atoms : Array Lean.Expr) (e : Interval.Expr) (box : Box)
    (relation : Relation) (config : Backend.Config) (depth splits : Nat) : MetaM MessageData := do
  let B := Backend.binaryGrid config
  let some intervals := box.enclose? B
    | return "interval could not certify: the backend could not enclose the input box."
  let (reason, obstruction) ← match ← checkedEval e B (fun i => intervals[i]?) with
    | none => do
      let failure ← firstObstruction atoms config (fun i => intervals[i]?) e
      pure (failure.message, some failure.expression)
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
