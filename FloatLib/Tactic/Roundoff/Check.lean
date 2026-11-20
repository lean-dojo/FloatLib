/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public meta import Lean.Meta.Eval
public import FloatLib.Tactic.Roundoff.Backward

/-!
# Is a generated bound useful at an input?

A bound `|computed - reference| ≤ relative * |reference| + absolute` holds for every input that
meets its premises, and still says nothing where it is as large as the reference: there the
theorem does not even fix the sign of the result. That happens where the computation cancels, as
`1 / (1 + s) - 1` does for a small `s`, or a sum of terms `p * (log p - log q)` for `p` close to
`q`.

`#roundoff_check` evaluates a generated statement at inputs: those the command is given, and
sampled ones for the arguments it is not given. It runs the program on them, evaluates the
reference and the budgets of the statement, and reports the error, the bound and their ratio. It
warns where the bound is at least the magnitude of the reference.

The evaluation is exact in the rationals as long as the statement uses field operations, and
uses rational enclosures for square roots, exponentials and logarithms. It is a report: the
values are computed by this module's own arithmetic and by running the program, the command
proves nothing, and no generated theorem depends on it.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Command Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

namespace Check

/-! ## Rational enclosures -/

/-- The fractional bits that an endpoint keeps once it is rounded. -/
def gridBits : Nat := 320

/-- The largest multiple of `2 ^ -bits` that is at most `q`. -/
def floorTo (q : ℚ) (bits : Nat := gridBits) : ℚ :=
  mkRat (Int.fdiv (q.num * (2 : Int) ^ bits) q.den) (2 ^ bits)

/-- The least multiple of `2 ^ -bits` that is at least `q`. -/
def ceilTo (q : ℚ) (bits : Nat := gridBits) : ℚ :=
  -floorTo (-q) bits

/-- A rational enclosure `[lower, upper]` of a real number. -/
structure Range where
  /-- A lower bound. -/
  lower : ℚ
  /-- An upper bound. -/
  upper : ℚ
  deriving Inhabited

namespace Range

/-- The enclosure of a rational number by itself. -/
def point (q : ℚ) : Range := ⟨q, q⟩

/-- Whether the enclosure is one point, so that the value is known exactly. -/
def isPoint (range : Range) : Bool := range.lower == range.upper

/-- The enclosure with endpoints rounded outward once they are long, so that a long evaluation
keeps short endpoints. An exact value with a short denominator stays exact. -/
def trim (range : Range) : Range :=
  if range.lower.den.log2 ≤ 2 * gridBits && range.upper.den.log2 ≤ 2 * gridBits then range
  else ⟨floorTo range.lower, ceilTo range.upper⟩

/-- The sum of two enclosures. -/
def add (a b : Range) : Range := trim ⟨a.lower + b.lower, a.upper + b.upper⟩

/-- The negation of an enclosure. -/
def neg (a : Range) : Range := ⟨-a.upper, -a.lower⟩

/-- The difference of two enclosures. -/
def sub (a b : Range) : Range := a.add b.neg

/-- The product of two enclosures. -/
def mul (a b : Range) : Range :=
  let products := [a.lower * b.upper, a.upper * b.lower, a.upper * b.upper]
  let first := a.lower * b.lower
  trim ⟨products.foldl min first, products.foldl max first⟩

/-- The reciprocal of an enclosure that excludes zero. -/
def inv? (a : Range) : Option Range :=
  if 0 < a.lower || a.upper < 0 then some (trim ⟨a.upper⁻¹, a.lower⁻¹⟩) else none

/-- The magnitude of an enclosure. -/
def abs (a : Range) : Range :=
  if 0 ≤ a.lower then a else if a.upper ≤ 0 then a.neg else ⟨0, max (-a.lower) a.upper⟩

/-- The larger of two enclosures. -/
def max (a b : Range) : Range := ⟨Max.max a.lower b.lower, Max.max a.upper b.upper⟩

/-- The smaller of two enclosures. -/
def min (a b : Range) : Range := ⟨Min.min a.lower b.lower, Min.min a.upper b.upper⟩

/-- A natural power of an enclosure. -/
def pow (a : Range) : Nat → Range
  | 0 => point 1
  | n + 1 => (pow a n).mul a

/-- The integer square root: the largest `r` with `r * r ≤ n`. -/
def natSqrt (n : Nat) : Nat := Id.run do
  if n < 2 then return n
  -- Newton's iteration from above the root.
  let mut r := 2 ^ ((n.log2 + 2) / 2)
  for _ in [0:n.log2 + 8] do
    let next := (r + n / r) / 2
    if next ≥ r then break
    r := next
  return r

/-- An enclosure of the square root, which is zero below zero as `Real.sqrt` is. -/
def sqrt (a : Range) : Range :=
  let root (q : ℚ) (up : Bool) : ℚ :=
    if q ≤ 0 then 0 else
      let scaled := Int.toNat (Int.fdiv (q.num * (4 : Int) ^ gridBits) q.den)
      let r := natSqrt scaled
      -- An exact root of an exact square stays exact.
      if r * r == scaled && mkRat (r * r) (4 ^ gridBits) == q then mkRat r (2 ^ gridBits)
      else mkRat (if up then r + 1 else r) (2 ^ gridBits)
  ⟨root a.lower false, root a.upper true⟩

/-- An enclosure of `exp q` for `|q| ≤ 1 / 2`: the Taylor polynomial of degree 40 and its
remainder, at most `2 * |q| ^ 41 / 41!`. -/
def expSmall (q : ℚ) : Range := Id.run do
  let mut term : ℚ := 1
  let mut sum : ℚ := 1
  for index in [1:41] do
    term := term * q / index
    sum := sum + term
  let remainder := 2 * (if term < 0 then -term else term) * (if q < 0 then -q else q) / 41
  return ⟨floorTo (sum - remainder), ceilTo (sum + remainder)⟩

/-- An enclosure of `exp q`: `exp (q / 2 ^ m)` squared `m` times. -/
def expPoint (q : ℚ) : Range := Id.run do
  let magnitude := if q < 0 then -q else q
  let halvings := if magnitude ≤ 1 / 2 then 0 else (magnitude.num.toNat / magnitude.den).log2 + 2
  let mut range := expSmall (q / (2 : ℚ) ^ halvings)
  for _ in [0:halvings] do
    range := ⟨floorTo (range.lower * range.lower), ceilTo (range.upper * range.upper)⟩
  return range

/-- An enclosure of the exponential of an enclosure. -/
def exp (a : Range) : Range := ⟨(expPoint a.lower).lower, (expPoint a.upper).upper⟩

/-- An enclosure of `2 * artanh z` for `|z| ≤ 1 / 3`: sixty terms of its series and the
remainder, at most `|z| ^ 123`. -/
def twoArtanh (z : ℚ) : Range := Id.run do
  let square := z * z
  let mut power := z
  let mut sum : ℚ := 0
  for index in [0:61] do
    sum := sum + power / (2 * index + 1)
    power := floorTo (power * square) (2 * gridBits)
  let remainder := (if z < 0 then -z else z) ^ 123 + mkRat 1 (2 ^ gridBits)
  return ⟨floorTo (2 * (sum - remainder)), ceilTo (2 * (sum + remainder))⟩

/-- An enclosure of `log q` for `0 < q`: with `q = t * 2 ^ e` and `t` in `[2/3, 4/3]`,
`log q = e * log 2 + 2 * artanh ((t - 1) / (t + 1))`, and `log 2 = 2 * artanh (1 / 3)`. -/
def logPoint (q : ℚ) : Range := Id.run do
  let mut exponent : Int := (q.num.toNat.log2 : Int) - (q.den.log2 : Int)
  let scaled (e : Int) : ℚ := if e ≥ 0 then q / (2 : ℚ) ^ e.toNat else q * (2 : ℚ) ^ (-e).toNat
  if scaled exponent > 4 / 3 then exponent := exponent + 1
  if scaled exponent < 2 / 3 then exponent := exponent - 1
  let t := scaled exponent
  let two := twoArtanh (1 / 3)
  let part := twoArtanh ((t - 1) / (t + 1))
  let shift : Range := (Range.point exponent).mul two
  return shift.add part

/-- An enclosure of the logarithm of an enclosure above zero. -/
def log? (a : Range) : Option Range :=
  if 0 < a.lower then some ⟨(logPoint a.lower).lower, (logPoint a.upper).upper⟩ else none

end Range

/-- `q` in scientific notation with `digits` significant digits, rounded to nearest. -/
def format (q : ℚ) (digits : Nat := 4) : String := Id.run do
  if q == 0 then return "0"
  let negative := q < 0
  let magnitude := if negative then -q else q
  -- The decimal exponent `e` with `10 ^ e ≤ magnitude < 10 ^ (e + 1)`.
  let mut exponent : Int :=
    (toString magnitude.num.toNat).length - (toString magnitude.den).length
  let power (e : Int) : ℚ := if e ≥ 0 then (10 : ℚ) ^ e.toNat else 1 / (10 : ℚ) ^ (-e).toNat
  if power exponent > magnitude then exponent := exponent - 1
  if power (exponent + 1) ≤ magnitude then exponent := exponent + 1
  let scaled := magnitude / power exponent * (10 : ℚ) ^ (digits - 1)
  let mut mantissa := (Int.fdiv (2 * scaled.num + scaled.den) (2 * scaled.den)).toNat
  if mantissa ≥ 10 ^ digits then
    mantissa := mantissa / 10
    exponent := exponent + 1
  let text := toString mantissa
  let body := if digits ≤ 1 then text else s!"{text.take 1}.{text.drop 1}"
  let sign := if negative then "-" else ""
  return if exponent == 0 then s!"{sign}{body}" else s!"{sign}{body}e{exponent}"

/-! ## Evaluating a statement -/

/-- What the evaluation of one statement has computed: the rational values of the decoded
floating-point terms it ran, and the enclosures of the real values it has named (`named`). -/
structure Memo where
  /-- The rational value of each term that was run, `none` when it is not finite. -/
  values : Std.HashMap Lean.Expr (Option ℚ) := {}
  /-- The enclosures of the named real values, by number. -/
  ranges : Array Range := #[]
  /-- The scalars sampled for the statement (`scalars`), in their order. -/
  sampled : Array Lean.Expr := #[]
  /-- The programs that the command has compiled (`program`), by the function each one runs. A
  command that samples one input compiles none. -/
  programs? : Option (IO.Ref (Std.HashMap Lean.Expr Name)) := none

/-- The evaluation of one statement. -/
abbrev EvalM := StateRefT Memo MetaM

/-- The key under which a real term carries the number of its known enclosure. -/
def rangeKey : Name := `roundoffCheckRange

/-- A real term that stands for a value with the enclosure `range`: the state of a loop is
evaluated once and then read through such terms, however often the next step reads it. -/
def named (range : Range) : EvalM Lean.Expr := do
  let index := (← get).ranges.size
  modify fun memo => { memo with ranges := memo.ranges.push range }
  return .mdata (KVMap.empty.insert rangeKey (.ofNat index)) q((0 : ℝ))

/-- The enclosure that `term` stands for, when `named` made it. -/
def named? (term : Lean.Expr) : EvalM (Option Range) := do
  let .mdata data _ := term | return none
  let some (.ofNat index) := data.find rangeKey | return none
  return (← get).ranges[index]?

/-- The scalars that `sampleScalar` wrote in `term`, after those of `found`: the literals
`OfScientific.ofScientific _ _ _` and their negations, each once, in the order of the term. -/
partial def scalars (term : Lean.Expr) (found : Array Lean.Expr := #[]) : Array Lean.Expr :=
  let literal (term : Lean.Expr) : Bool := term.isAppOfArity ``OfScientific.ofScientific 5
  if literal term || (term.isAppOfArity ``Neg.neg 3 && literal term.appArg!) then
    if found.contains term then found else found.push term
  else match term with
    | .app function argument => scalars argument (scalars function found)
    | .lam _ domain body _ | .forallE _ domain body _ => scalars body (scalars domain found)
    | .letE _ type value body _ => scalars body (scalars value (scalars type found))
    | .mdata _ inner | .proj _ _ inner => scalars inner found
    | _ => found

/-- `term` as a function of the sampled scalars that occur in it, with those scalars: the terms
that two inputs give are then one function at two lists of scalars. A negated literal is replaced
before the literal inside it. `none` when no sampled scalar occurs. -/
def function? (term : Lean.Expr) (sampled : Array Lean.Expr) :
    MetaM (Option (Lean.Expr × Array Lean.Expr)) := do
  let used := sampled.filter fun scalar => (term.find? (· == scalar)).isSome
  if used.isEmpty then return none
  let binders ← used.mapM fun _ => return mkFVar (← mkFreshFVarId)
  let mut body := term
  for negated in [true, false] do
    let mut places : Std.HashMap Lean.Expr Lean.Expr := {}
    for scalar in used, binder in binders do
      if scalar.isAppOf ``Neg.neg == negated then places := places.insert scalar binder
    body := body.replace places.get?
  let mut function := body.abstract binders
  for index in (List.range used.size).reverse do
    function := .lam ((`scalar).appendIndexAfter index) (← inferType used[index]!) function .default
  if function.hasFVar || function.hasMVar || function.hasLevelParam then return none
  return some (function, used)

/-- The closed term that `run` evaluates for `term`. When the command samples several inputs and
`term` reads sampled scalars, it is the program compiled for the function of those scalars that
`term` is (`function?`), at these scalars: the command compiles that function at its first input
and runs it at the others. The program is an ordinary definition, which the kernel checks. A
function that is not well typed, as one whose proofs read a scalar, or that the kernel does not
accept as a definition is not compiled, and `term` is evaluated as it is. -/
def program (term : Lean.Expr) : EvalM Lean.Expr := do
  let memo ← get
  let some programs := memo.programs? | return term
  let some (function, used) ← function? term memo.sampled | return term
  if let some name := (← programs.get).get? function then return mkAppN (mkConst name) used
  try
    unless ← Meta.isTypeCorrect function do return term
    let name := mkPrivateName (← getEnv) (← mkFreshUserName `_roundoffCheck)
    let declaration := Declaration.defnDecl {
      name, levelParams := [], type := ← inferType function, value := function
      hints := ReducibilityHints.opaque, safety := .safe }
    modifyEnv (markMeta · name)
    withOptions (fun options => ((options.setBool `Elab.async false).setBool
        `compiler.postponeCompile false).setBool `compiler.relaxedMetaCheck true) do
      addAndCompile declaration
    programs.modify (·.insert function name)
    return mkAppN (mkConst name) used
  catch _ => return term

/-- Run the closed term `term`, of type `Option (Int × Nat)`, in the interpreter. Compiling the
program at its inputs is not counted against the heartbeats of the command. The compiled code of
an imported definition must be there to run: a file of the module system has it for the modules
it imports with `meta import`, and the error says so. -/
def run (term : Lean.Expr) : MetaM (Option (Int × Nat)) := do
  if term.hasFVar || term.hasMVar then
    throwError "roundoff_check: `{term}` is not determined by the inputs"
  try
    withTheReader Core.Context ({ · with maxHeartbeats := 0 }) do
      unsafe evalExpr (Option (Int × Nat)) q(Option (Int × Nat)) term (safety := .unsafe)
  catch error =>
    let reason ← error.toMessageData.toString
    let hint := if (reason.splitOn "Could not find native implementation").length > 1 then
        "\nThe compiled code of that definition is not available here. In a file that starts \
          with `module`, import its module with `meta import` as well."
      else ""
    throwError "roundoff_check: could not evaluate `{term}`: {reason}{hint}"

/-- `run` on the program of `term` (`program`), and on `term` itself when the command compiles no
program for it or the program does not evaluate. -/
def runProgram (term : Lean.Expr) : EvalM (Option (Int × Nat)) := do
  if term.hasFVar || term.hasMVar then return ← run term
  let shared ← withTheReader Core.Context ({ · with maxHeartbeats := 0 }) (program term)
  if shared == term then run term else
    try run shared catch _ => run term

/-- The closed natural number `term` as a literal, when a bounded reduction finds one. Such a
number, like the half units in the last place of a rounding attribute, needs no compiled code. -/
def literal? (term : Lean.Expr) : MetaM (Option Nat) := do
  if term.hasFVar || term.hasMVar then return none
  tryCatchRuntimeEx
    (withTheReader Core.Context ({ · with maxHeartbeats := 2000 * 1000 }) <|
      withCurrHeartbeats do
        let reduced ← whnfD term
        return reduced.rawNatLit? <|> reduced.nat?)
    fun _ => return none

/-- The rational value of the closed term `value`, computed by running `decode value`, a term of
type `Option ℚ`: `none` for a value that is not finite. Each term is run once. -/
def rational (value decode : Lean.Expr) : EvalM (Option ℚ) := do
  if let some known := (← get).values.get? value then return known
  let pair ← mkAppM ``Option.map #[q(fun q : ℚ => (q.num, q.den)), decode]
  let result := (← runProgram pair).map fun (numerator, denominator) => mkRat numerator denominator
  modify fun memo => { memo with values := memo.values.insert value result }
  return result

/-- The truth of the closed proposition `condition`, decided by `decidable`, by running it. -/
def decide (condition decidable : Lean.Expr) : MetaM Bool := do
  let test := mkApp5 (mkConst ``ite [Level.one]) q(Option (Int × Nat)) condition decidable
    q(some ((1 : Int), (1 : Nat))) q((none : Option (Int × Nat)))
  return (← run test).isSome

/-- A proof placeholder for the proposition `type`: the evaluation runs programs and reads no
proof. -/
def assumed (type : Lean.Expr) : Lean.Expr := mkApp (mkConst ``lcProof) type

/-- The entries of the closed list `list`, in order. -/
partial def entries (list : Lean.Expr) (found : Array Lean.Expr := #[]) :
    MetaM (Array Lean.Expr) := do
  let list ← whnf list
  if list.isAppOfArity ``List.cons 3 then
    return ← entries (list.getArg! 2) (found.push (list.getArg! 1))
  if list.isAppOfArity ``List.nil 1 then return found
  throwError "roundoff_check: `{list}` is not a list of known entries"

mutual

/-- `term`, a pair, as an explicit pair: a component of a pair, the state of a loop after its
steps, or a definition of these. -/
partial def pair (term : Lean.Expr) : EvalM Lean.Expr := do
  let term ← whnfCore (← instantiateMVars term)
  if term.isAppOfArity ``Prod.mk 4 then return term
  if term.isAppOfArity ``Prod.fst 3 then return ← pair ((← pair term.appArg!).getArg! 2)
  if term.isAppOfArity ``Prod.snd 3 then return ← pair ((← pair term.appArg!).getArg! 3)
  if let .proj ``Prod index inner := term then
    return ← pair ((← pair inner).getArg! (index + 2))
  if term.isAppOfArity ``List.foldl 5 then return ← pair (← fold term)
  let some next ← unfoldDefinition? term |
    throwError "roundoff_check: no value for `{term}` at these inputs"
  pair next

/-- `term` with each real part of it evaluated and named (`named`): a real term, or a pair of
such terms. A part of another type, such as the accumulator of the program, stays as it is. -/
partial def freeze (term : Lean.Expr) : EvalM Lean.Expr := do
  let type ← whnfR (← inferType term)
  if type.isConstOf ``Real then return ← named (← real term)
  if type.isAppOfArity ``Prod 2 then
    let explicit ← pair term
    return mkAppN explicit.getAppFn #[type.getArg! 0, type.getArg! 1,
      ← freeze (explicit.getArg! 2), ← freeze (explicit.getArg! 3)]
  return term

/-- The state of the loop `List.foldl step initial list` after its steps, with the real parts
of each state evaluated before the next step reads them. -/
partial def fold (term : Lean.Expr) : EvalM Lean.Expr := do
  let step := term.getArg! 2
  let mut state ← freeze (term.getArg! 3)
  for entry in ← entries (term.getArg! 4) do
    state ← freeze (mkApp2 step state entry).headBeta
  return state

/-- An enclosure of the closed real term `term`: field operations exactly, square roots,
exponentials and logarithms by enclosures, a decoded floating-point value by running the program
that computes it, a loop step by step, and any other term through its definition. -/
partial def real (term : Lean.Expr) : EvalM Range := do
  let term ← instantiateMVars term
  if let some known ← named? term then return known
  let term := term.consumeMData.headBeta
  if let .letE _ _ value body _ := term then return ← real (body.instantiate1 value)
  let arguments := term.getAppArgs
  let fail {α : Type} : EvalM α :=
    throwError "roundoff_check: no value for `{term}` at these inputs"
  let closed (value decode : Lean.Expr) : EvalM Range := do
    let some q ← rational value decode |
      throwError "roundoff_check: `{value}` is not finite at these inputs"
    return .point q
  match term.getAppFn.constName?, arguments.size with
  | some ``HAdd.hAdd, 6 => return (← real arguments[4]!).add (← real arguments[5]!)
  | some ``HSub.hSub, 6 => return (← real arguments[4]!).sub (← real arguments[5]!)
  | some ``HMul.hMul, 6 => return (← real arguments[4]!).mul (← real arguments[5]!)
  | some ``HDiv.hDiv, 6 =>
      let divisor ← real arguments[5]!
      -- Lean's division by zero is zero.
      if divisor.isPoint && divisor.lower == 0 then return .point 0
      let some inverse := divisor.inv? |
        throwError "roundoff_check: the divisor `{arguments[5]!}` is not separated from zero"
      return (← real arguments[4]!).mul inverse
  | some ``Neg.neg, 3 => return (← real arguments[2]!).neg
  | some ``Inv.inv, 3 =>
      let value ← real arguments[2]!
      if value.isPoint && value.lower == 0 then return .point 0
      let some inverse := value.inv? |
        throwError "roundoff_check: `{arguments[2]!}` is not separated from zero"
      return inverse
  | some ``abs, 4 => return (← real arguments[3]!).abs
  | some ``Max.max, 4 => return (← real arguments[2]!).max (← real arguments[3]!)
  | some ``Min.min, 4 => return (← real arguments[2]!).min (← real arguments[3]!)
  | some ``Real.sqrt, 1 => return (← real arguments[0]!).sqrt
  | some ``Real.exp, 1 => return (← real arguments[0]!).exp
  | some ``Real.log, 1 =>
      let some result := (← real arguments[0]!).log? |
        throwError "roundoff_check: the argument `{arguments[0]!}` of a logarithm is not above zero"
      return result
  | some ``HPow.hPow, 6 =>
      let base ← real arguments[4]!
      let exponentType ← whnfR arguments[1]!
      let exponent ← if exponentType.isConstOf ``Nat then do
          let some (n, _) ← run (← mkAppM ``some
            #[← mkAppM ``Prod.mk #[← mkAppM ``Int.ofNat #[arguments[5]!], q((1 : Nat))]]) | fail
          pure n
        else if exponentType.isConstOf ``Int then do
          let some (n, _) ← run (← mkAppM ``some
            #[← mkAppM ``Prod.mk #[arguments[5]!, q((1 : Nat))]]) | fail
          pure n
        else do
          let value ← real arguments[5]!
          unless value.isPoint && value.lower.den == 1 do fail
          pure value.lower.num
      if exponent ≥ 0 then return base.pow exponent.toNat
      let some inverse := (base.pow (-exponent).toNat).inv? | fail
      return inverse
  | some ``OfNat.ofNat, 3 =>
      let some n := arguments[1]!.rawNatLit? <|> arguments[1]!.nat? | fail
      return .point n
  | some ``OfScientific.ofScientific, 5 =>
      closed term (← mkAppM ``some #[← mkAppOptM ``OfScientific.ofScientific
        #[q(ℚ), none, arguments[2]!, arguments[3]!, arguments[4]!]])
  | some ``Nat.cast, 3 | some ``NatCast.natCast, 3 =>
      if let some n ← literal? arguments[2]! then return .point n
      closed term (← mkAppM ``some #[← mkAppOptM ``Nat.cast #[q(ℚ), none, arguments[2]!]])
  | some ``Int.cast, 3 | some ``IntCast.intCast, 3 =>
      closed term (← mkAppM ``some #[← mkAppOptM ``Int.cast #[q(ℚ), none, arguments[2]!]])
  | some ``Rat.cast, 3 | some ``RatCast.ratCast, 3 =>
      closed term (← mkAppM ``some #[arguments[2]!])
  | some ``ExecFloat.Binary.toReal, _ =>
      closed term (← mkAppM ``ExecFloat.Binary.toRat? #[arguments.back!])
  | some ``Model.toReal, _ => closed term (← mkAppM ``Model.toRat? #[arguments.back!])
  | some ``ite, 5 =>
      return ← real arguments[if ← decide arguments[1]! arguments[2]! then 3 else 4]!
  | some ``dite, 5 =>
      if ← decide arguments[1]! arguments[2]! then
        return ← real (mkApp arguments[3]! (assumed arguments[1]!))
      return ← real (mkApp arguments[4]! (assumed (mkNot arguments[1]!)))
  | some ``Finset.sum, 5 =>
      -- A sum over every index of `Fin n`, or over `Finset.range n`.
      let domain ← whnfR arguments[0]!
      let terms ← if arguments[3]!.isAppOf ``Finset.univ && domain.isAppOfArity ``Fin 1 then do
          let some (n, _) ← run (← mkAppM ``some
            #[← mkAppM ``Prod.mk #[← mkAppM ``Int.ofNat #[domain.appArg!], q((1 : Nat))]]) | fail
          (List.range n.toNat).mapM fun index => do
            let bound := assumed (← mkAppM ``LT.lt #[mkNatLit index, domain.appArg!])
            mkAppM ``Fin.mk #[mkNatLit index, bound]
        else if arguments[3]!.isAppOfArity ``Finset.range 1 then do
          let some (n, _) ← run (← mkAppM ``some #[← mkAppM ``Prod.mk
            #[← mkAppM ``Int.ofNat #[arguments[3]!.appArg!], q((1 : Nat))]]) | fail
          pure ((List.range n.toNat).map mkNatLit)
        else fail
      let mut total := Range.point 0
      for index in terms do
        total := total.add (← real (mkApp arguments[4]! index))
      return total
  | some ``List.foldl, 5 => return ← real (← fold term)
  | some ``Prod.fst, 3 => return ← real ((← pair arguments[2]!).getArg! 2)
  | some ``Prod.snd, 3 => return ← real ((← pair arguments[2]!).getArg! 3)
  | _, _ =>
      if let .proj ``Prod index inner := term then
        return ← real ((← pair inner).getArg! (index + 2))
      -- Any other term is read through one step of its definition.
      let next ← whnfCore term
      if next != term then return ← real next
      let some unfolded ← unfoldDefinition? term | fail
      real unfolded

end

/-- Whether the premise `premise` holds at the inputs: `some` when the evaluation settles it. A
finiteness, a comparison of real values with separated enclosures, a conjunction of these or a
decidable proposition about data is settled. A condition on every step of a loop is not. -/
partial def premise (premise : Lean.Expr) : EvalM (Option Bool) := do
  let premise ← whnfCore (← instantiateMVars premise)
  if premise.isConstOf ``True then return some true
  if let some (left, right) := premise.and? then
    return match ← Check.premise left, ← Check.premise right with
      | some false, _ | _, some false => some false
      | some true, some true => some true
      | _, _ => none
  let strict := premise.isAppOfArity ``LT.lt 4
  if (strict || premise.isAppOfArity ``LE.le 4) &&
      (← whnfR (premise.getArg! 0)).isConstOf ``Real then
    try
      let left ← real (premise.getArg! 2)
      let right ← real (premise.getArg! 3)
      if left.upper < right.lower || (!strict && left.upper ≤ right.lower) then return some true
      if left.lower > right.upper || (strict && left.lower ≥ right.upper) then return some false
      return none
    catch _ => return none
  if (premise.find? fun term => term.isConstOf ``Real).isSome || premise.isForall then return none
  let some decidable ← synthInstance? (← mkAppM ``Decidable #[premise]) | return none
  try return some (← decide premise decidable) catch _ => return none

/-- What a generated statement bounds at one input. -/
structure Outcome where
  /-- The computed value, or `none` when it is not finite. -/
  computed : Option ℚ
  /-- The reference. -/
  reference : Range
  /-- The bound: `relative * |reference| + absolute`, or the absolute error. -/
  bound : Range
  /-- The premises that hold, that do not hold, and that the evaluation does not settle. -/
  premises : Nat × Nat × Nat
  /-- A premise that does not hold. -/
  failed? : Option Lean.Expr := none

/-- The magnitude that the reference has at least. -/
def Outcome.magnitude (outcome : Outcome) : ℚ := outcome.reference.abs.lower

/-- The error of the computed value against the reference, at most. -/
def Outcome.error? (outcome : Outcome) : Option ℚ :=
  outcome.computed.map fun value =>
    ((Range.point value).sub outcome.reference).abs.upper

/-- Whether the bound is at least the magnitude of the reference: the statement does not fix the
sign of the result at this input. -/
def Outcome.cancels (outcome : Outcome) : Bool := outcome.bound.upper ≥ outcome.magnitude

/-- Evaluate the statement `statement` of a generated theorem at closed inputs: its premises, the
case of a `match` or branch that the inputs select, and the bound it concludes. -/
partial def outcome (statement : Lean.Expr) (assumptions : List Lean.Expr := [])
    (premises : Nat × Nat × Nat := (0, 0, 0)) (failed? : Option Lean.Expr := none) :
    EvalM Outcome := do
  let count (verdict : Option Bool) : Nat × Nat × Nat := match verdict with
    | some true => (premises.1 + 1, premises.2.1, premises.2.2)
    | some false => (premises.1, premises.2.1 + 1, premises.2.2)
    | none => (premises.1, premises.2.1, premises.2.2 + 1)
  if let first :: rest := assumptions then
    let verdict ← premise first
    let failed? := if verdict == some false then failed? <|> some first else failed?
    return ← outcome statement rest (count verdict) failed?
  let statement ← whnfCore (← zetaReduce (← instantiateMVars statement))
  if let .forallE _ domain body _ := statement then
    unless ← isProp domain do
      throwError "roundoff_check: the statement still takes an argument of type `{domain}`"
    let verdict ← premise domain
    let failed? := if verdict == some false then failed? <|> some domain else failed?
    return ← outcome (body.instantiate1 (assumed domain)) [] (count verdict) failed?
  if let some (left, right) := statement.and? then
    -- The finiteness of the output beside its bound, or the two cases of a branch.
    if isFiniteness left then return ← outcome right [] premises failed?
    for side in [left, right] do
      let side ← whnfCore side
      let applies ← match side with
        | .forallE _ domain _ _ => pure ((← premise domain) != some false)
        | _ => pure true
      if applies then return ← outcome side [] premises failed?
    throwError "roundoff_check: no case of `{statement}` applies at these inputs"
  let computedOf (actual : Lean.Expr) : EvalM (Option ℚ) := do
    let value := actual.getAppArgs.back?.getD actual
    if actual.isAppOf ``ExecFloat.Binary.toReal then
      rational actual (← mkAppM ``ExecFloat.Binary.toRat? #[value])
    else if actual.isAppOf ``Model.toReal then
      rational actual (← mkAppM ``Model.toRat? #[value])
    else
      let range ← real actual
      pure (if range.isPoint then some range.lower else none)
  if statement.isAppOfArity ``MixedError 4 then
    let reference ← real (statement.getArg! 1)
    let relative ← real (statement.getArg! 2)
    let absolute ← real (statement.getArg! 3)
    return { computed := ← computedOf (statement.getArg! 0), reference, premises, failed?
             bound := (relative.mul reference.abs).add absolute }
  if statement.isAppOfArity ``LE.le 4 && (statement.getArg! 2).isAppOf ``abs &&
      (statement.getArg! 2).appArg!.isAppOfArity ``HSub.hSub 6 then
    let difference := (statement.getArg! 2).appArg!
    return { computed := ← computedOf (difference.getArg! 4), premises, failed?
             reference := ← real (difference.getArg! 5), bound := ← real (statement.getArg! 3) }
  if statement.isAppOf ``Exists then
    throwError "roundoff_check: a backward-error statement bounds perturbations of the inputs, \
      not the result; check the mixed or the closed theorem of the computation"
  throwError "roundoff_check: `{statement}` states no bound"

/-! ## Inputs -/

/-- A sampled input as the report shows it: a decimal for a scalar, the entries for a function
on `Fin n`, a list or an array. -/
partial def display (value : Lean.Expr) : MessageData :=
  let value := value.consumeMData
  if value.isAppOfArity ``Neg.neg 3 then m!"-{display value.appArg!}"
  else if value.isAppOfArity ``OfScientific.ofScientific 5 then
    match (value.getArg! 2).nat?, (value.getArg! 4).nat? with
    | some mantissa, some exponent => m!"{mantissa}e-{exponent}"
    | _, _ => m!"{value}"
  else if value.isAppOfArity ``List.cons 3 || value.isAppOfArity ``List.nil 1 then
    let rec items (list : Lean.Expr) : List MessageData :=
      if list.isAppOfArity ``List.cons 3 then
        display (list.getArg! 1) :: items (list.getArg! 2)
      else []
    m!"[{MessageData.joinSep (items value) ", "}]"
  else if value.isAppOfArity ``List.toArray 2 then display value.appArg!
  else match value with
    | .lam _ _ body _ =>
        if body.isAppOfArity ``List.getD 4 then display (body.getArg! 1) else m!"{value}"
    | _ => m!"{value}"

/-- What the command samples. -/
structure Sampling where
  /-- The size given to every natural-number argument, and the length of a sampled list. -/
  size : Nat := 4
  /-- The floating-point type that a statement about any format is checked at. -/
  carrier : Lean.Expr

/-- A sampled value of the floating-point type `type`: a seven-digit decimal of magnitude between
`1e-4` and `1e3`, of either sign, as the literal the type reads. -/
def sampleScalar (type : Lean.Expr) : StateT StdGen MetaM Lean.Expr := do
  let draw (low high : Nat) : StateT StdGen MetaM Nat := do
    let (value, next) := randNat (← get) low high
    set next
    pure value
  let mantissa ← draw 1000000 9999999
  let exponent ← draw 4 10
  let negative ← draw 0 1
  let literal ← mkAppOptM ``OfScientific.ofScientific
    #[some type, none, some (mkNatLit mantissa), some (toExpr true), some (mkNatLit exponent)]
  if negative == 0 then return literal
  mkAppM ``Neg.neg #[literal]

/-- A sampled value of `type`: a natural number is the size, a function on `Fin n`, a list, an
array or a vector has sampled entries, and any other type is sampled as a scalar. -/
partial def sample (sampling : Sampling) (type : Lean.Expr) : StateT StdGen MetaM Lean.Expr := do
  let type ← whnfR (← instantiateMVars type)
  if type.isConstOf ``Nat then return mkNatLit sampling.size
  let entries (entry : Lean.Expr) (count : Nat) : StateT StdGen MetaM Lean.Expr := do
    let values ← (List.range count).mapM fun _ => sample sampling entry
    mkListLit entry values
  if let .forallE _ domain codomain _ := type then
    let domain ← whnfR domain
    if domain.isAppOfArity ``Fin 1 && !codomain.hasLooseBVars then
      let some count := (← whnfD domain.appArg!).nat? <|> (← whnfD domain.appArg!).rawNatLit? |
        throwError "roundoff_check: the size `{domain.appArg!}` is not a numeral"
      if count == 0 then
        return ← withLocalDeclD `i domain fun index => do
          mkLambdaFVars #[index] (← mkAppOptM ``Fin.elim0 #[some codomain, some index])
      let list ← entries codomain count
      let fallback ← sample sampling codomain
      return ← withLocalDeclD `i domain fun index => do
        mkLambdaFVars #[index] (← mkAppM ``List.getD #[list, ← mkAppM ``Fin.val #[index], fallback])
  if type.isAppOfArity ``List 1 then return ← entries type.appArg! sampling.size
  if type.isAppOfArity ``Array 1 then
    return ← mkAppM ``List.toArray #[← entries type.appArg! sampling.size]
  sampleScalar type

/-- The statement of a theorem of type `type` at arguments for its remaining binders: a sampled
value for data, a placeholder for a premise, an instance by synthesis, and for a type, a format or
another parameter the value that makes the floating-point types of the data `sampling.carrier`.
Returns the conclusion at those inputs, the premises in order and the sampled values by name. -/
def instantiate (sampling : Sampling) (type : Lean.Expr) :
    StateT StdGen MetaM (Lean.Expr × Array Lean.Expr × Array (Name × Lean.Expr)) := do
  let mut type ← whnfCore (← instantiateMVars type)
  let mut sampled := #[]
  let mut premises := #[]
  let mut parameters := #[]
  let mut instances := #[]
  while true do
    let .forallE name domain body info := type | break
    let domain ← instantiateMVars domain
    let kind ← whnfR domain
    let argument ← if ← isProp domain then do
        premises := premises.push domain
        pure (assumed domain)
      else if info.isInstImplicit then do
        let inferred ← mkFreshExprMVar domain .synthetic
        instances := instances.push inferred
        pure inferred
      else if kind.isSort || kind.isConstOf ``FloatFormat ||
          (kind.getAppFn.constName?.any fun head =>
            (`FloatLib.Floats.Formats.BinaryInterchange.Configured).isPrefixOf head) then do
        let parameter ← mkFreshExprMVar domain
        parameters := parameters.push (name, parameter)
        pure parameter
      else do
        -- The floating-point types that the datum mentions are the carrier.
        let open? := domain.find? fun term =>
          term.isAppOf ``FloatLib.Floats.ExecFloat && term.hasExprMVar
        if let some carrier := open? then
          unless ← isDefEq carrier sampling.carrier do
            throwError "roundoff_check: `{carrier}` is not the carrier `{sampling.carrier}`"
        let value ← sample sampling (← instantiateMVars domain)
        sampled := sampled.push (name, value)
        pure value
    type ← whnfCore (← instantiateMVars (body.instantiate1 argument))
  for inferred in instances do
    let goal := inferred.mvarId!
    unless ← goal.isAssigned do
      goal.assign (← synthInstance (← instantiateMVars (← goal.getType)))
  for (name, parameter) in parameters do
    if (← instantiateMVars parameter).hasExprMVar then
      throwError "roundoff_check: the argument `{name}` is not determined; apply the theorem to it"
  return (← instantiateMVars type, ← premises.mapM instantiateMVars, sampled)

end Check

/-- `#roundoff_check theorem` evaluates the bound of a generated theorem at inputs and reports
whether it is useful there.

The theorem is a term: a generated theorem, or one applied to some of its arguments, as in
`#roundoff_check dot_mixed x₀ y₀`. Arguments that are not given are sampled, twenty times unless
`(samples := k)` says otherwise, from `(seed := s)`; a sampled input that misses a premise the
command can evaluate is left out. A floating-point argument is a seven-digit
decimal between `1e-4` and `1e3` in magnitude, of either sign, a natural number is `(size := n)`,
four by default, and a function on `Fin n`, a list or an array has sampled entries. A statement
about every format is checked in `(carrier := T)`, binary32 by default.

At each input the command runs the program, evaluates the reference and the budgets of the
statement, and reports the error, the bound and the bound over the magnitude of the reference. It
warns when the bound is at least that magnitude: there the theorem does not fix the sign of the
result, which is what cancellation does to a bound. Premises are assumed, and the report says
which of them hold at the input.

The values are exact rationals as long as the statement uses field operations, and enclosures for
square roots, exponentials and logarithms. The command reports. It proves nothing, and nothing
depends on it. -/
syntax (name := roundoffCheck) "#roundoff_check"
  (atomic(" (" &"samples") " := " num ")")? (atomic(" (" &"seed") " := " num ")")?
  (atomic(" (" &"size") " := " num ")")? (atomic(" (" &"carrier") " := " term ")")?
  ppSpace term : command

@[command_elab roundoffCheck, inherit_doc roundoffCheck]
def elabRoundoffCheck : CommandElab := fun stx => do
  let applied : Term := ⟨stx[5]⟩
  let option (index : Nat) : Option Syntax :=
    if stx[index].isNone then none else some stx[index][3]
  let samples? := (option 1).bind (·.isNatLit?)
  let seed := ((option 2).bind (·.isNatLit?)).getD 20261116
  let size := ((option 3).bind (·.isNatLit?)).getD 4
  liftTermElabM do
    let carrier ← match option 4 with
      | some carrier => Term.elabType carrier
      | none => pure (mkConst ``FloatLib.Floats.Binary32)
    -- A theorem alone keeps all its arguments; an applied one fixes its implicit ones.
    let term ← if applied.raw.isIdent then `(@$applied) else pure applied
    let proof ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars (← inferType proof)
    let bounds (term : Lean.Expr) : Bool := term.isAppOfArity ``MixedError 4 ||
      (term.isAppOfArity ``LE.le 4 && (term.getArg! 2).isAppOf ``abs)
    if (type.find? bounds).isNone then
      throwError "roundoff_check: `{applied}` states no bound. The command reads a conclusion \
        `|value - reference| ≤ bound` or `MixedError value reference relative absolute`, as \
        `roundoff theorem`, `roundoff mixed theorem` and `roundoff closed theorem` generate."
    let sampling : Check.Sampling := { size, carrier }
    -- Whether an argument is left to sample decides the number of inputs.
    let ((_, _, first), _) ← withoutModifyingState
      ((Check.instantiate sampling type).run (mkStdGen seed))
    let count := if first.isEmpty then 1 else samples?.getD 20
    let mut generator := mkStdGen seed
    let mut cancelling := 0
    let mut evaluated := 0
    let mut worst? : Option (ℚ × Check.Outcome × Array (Name × Lean.Expr)) := none
    let mut errors := #[]
    let mut missed := 0
    let mut excluded? : Option (Check.Outcome × Array (Name × Lean.Expr)) := none
    -- The programs compiled at one input stay in the environment for the inputs after it.
    let initial ← getEnv
    let programs? ← if count == 1 then pure none else some <$> IO.mkRef {}
    let restore (saved : Term.SavedState) : TermElabM Unit := do
      let environment ← getEnv
      saved.restore
      setEnv environment
    try
      for _ in [0:count] do
        let saved ← saveState
        -- Each input has the heartbeats of a command to itself.
        let ((statement, premises, inputs), next) ← withCurrHeartbeats
          ((Check.instantiate sampling type).run generator)
        generator := next
        try
          let mut sampled := #[]
          for (_, value) in inputs do sampled := Check.scalars (← instantiateMVars value) sampled
          let outcome ← withCurrHeartbeats
            ((Check.outcome statement premises.toList).run' { sampled, programs? })
          -- A sampled input that misses a premise is not an input of the theorem.
          if outcome.failed?.isSome && !inputs.isEmpty then
            missed := missed + 1
            if excluded?.isNone then excluded? := some (outcome, inputs)
            restore saved
            continue
          evaluated := evaluated + 1
          if outcome.cancels then cancelling := cancelling + 1
          -- The input with the largest bound over magnitude is reported.
          let weight := if outcome.magnitude == 0 then outcome.bound.upper + 10 ^ 30
            else outcome.bound.upper / outcome.magnitude
          if worst?.all (·.1 < weight) then
            worst? := some (weight, outcome, ← inputs.mapM fun (name, value) =>
              return (name, ← instantiateMVars value))
        catch error =>
          errors := errors.push (← error.toMessageData.toString)
        restore saved
    finally
      setEnv initial
    let some (_, outcome, inputs) := worst? | do
      if let some (outcome, _) := excluded? then
        throwError "roundoff_check: none of the {missed} sampled inputs meets the premises of \
          the theorem, such as{indentExpr (outcome.failed?.getD default)}\ngive inputs that do"
      throwError "roundoff_check: no input could be evaluated: {errors[0]?.getD ""}"
    let mut report := m!"evaluated at {evaluated} input{if evaluated == 1 then "" else "s"}"
    unless missed == 0 do
      report := report ++ m!" ({missed} more sampled inputs miss a premise)"
    unless errors.isEmpty do
      report := report ++ m!" ({errors.size} more failed: {errors[0]!})"
    unless inputs.isEmpty do
      report := report ++ m!"; the largest bound over magnitude is at"
      for (name, value) in inputs do
        report := report ++ m!"\n  {name} := {Check.display value}"
    let computed := match outcome.computed with
      | some value => Check.format value 8
      | none => "not finite"
    let exactness := if outcome.reference.isPoint then "exact" else "enclosed"
    report := report ++ m!"\n  computed value  {computed}\
      \n  reference       {Check.format outcome.reference.lower 8} ({exactness})"
    match outcome.error? with
    | some error =>
        report := report ++ m!"\n  error           {Check.format error}"
        if error != 0 then
          report := report ++ m!"\n  bound           {Check.format outcome.bound.upper} \
            (bound / error = {Check.format (outcome.bound.upper / error) 3})"
        else report := report ++ m!"\n  bound           {Check.format outcome.bound.upper}"
    | none => report := report ++ m!"\n  bound           {Check.format outcome.bound.upper}"
    let (hold, fail, unsettled) := outcome.premises
    report := report ++
      m!"\n  premises        {hold} hold, {fail} do not, {unsettled} not evaluated"
    if let some failed := outcome.failed? then
      report := report ++ m!"\n  this premise does not hold, so the theorem says nothing \
        here:{indentExpr failed}"
    let note := "This is a report at the inputs above, not a proof."
    if outcome.cancels then
      let magnitude := Check.format outcome.magnitude
      let extent := if count == 1 then "" else s!" at {cancelling} of {evaluated} inputs"
      logWarning m!"{report}\n  The bound is at least the magnitude {magnitude} of the \
        reference{extent}: there the theorem does not fix the sign of the result. The \
        computation cancels, or the bound is not relative to its result.\n  {note}"
    else
      let ratio := Check.format (outcome.bound.upper / outcome.magnitude) 3
      let extent := if count == 1 then "" else " at every input"
      logInfo m!"{report}\n  bound / |reference| = {ratio}: the bound fixes the sign of the \
        result{extent}.\n  {note}"

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
