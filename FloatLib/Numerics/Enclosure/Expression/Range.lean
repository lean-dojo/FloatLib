/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Constraint

/-!
# Enclosures with infinite ends

A `Range` is an interval of real numbers whose ends may be infinite: a missing lower end is `-∞`
and a missing upper end is `+∞`. `Expr.range` evaluates an expression on such intervals. It is
total: where an operation has no better enclosure, the result is the whole line, which every real
number is in. So a variable with a bound on one side only, or with none, still gives its
expression a range, and often a useful one: `Real.exp x` is in `[0, 1]` for every `x ≤ 0`, and
`1 / (1 + x ^ 2)` is in `[0, 1]` for every `x`.

On an interval with two rational ends an operation is the one of a backend with rational
endpoints, when that backend encloses it. Otherwise the rules here apply: the ends of sums,
products, quotients and powers by their signs, and the ends of the monotone functions (the
exponential, the logarithm, the square root, the arctangent and the hyperbolic functions) from
the backend's enclosure at the one end that is rational. A product with a factor that is exactly
zero is zero whatever the other factor is. A registered call has these rules when a table names
the unary operation that it is, which is how the `interval` tactic states the elementary
functions.

`Constraint.failsOn` evaluates the atoms of a constraint once on a box of ranges and says whether
the constraint has no point there. `RangeProof` proves `Expr.contains_range` and
`Constraint.not_holds_of_failsOn`.

## Main definitions

* `Range`, `Range.Contains`: an interval with ends that may be infinite, and its real members.
* `Range.unary`, `Range.binary`, `Range.ternary`, `Range.call`: the operations.
* `Expr.range`: the evaluation of an expression on ranges.
* `Constraint.failsOn`: whether a constraint fails on a whole box of ranges.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- An interval of real numbers whose ends may be infinite: the lower end `none` is `-∞` and the
upper end `none` is `+∞`. -/
abbrev Range := Interval (Option ℚ)

namespace Range

/-- The whole real line. -/
def whole : Range := ⟨none, none⟩

/-- The range with the two rational ends of an interval. -/
def ofInterval (I : Interval ℚ) : Range := ⟨some I.lo, some I.hi⟩

/-- The interval of a range whose two ends are rational. -/
def interval? (R : Range) : Option (Interval ℚ) :=
  match R.lo, R.hi with
  | some lo, some hi => some ⟨lo, hi⟩
  | _, _ => none

/-- Whether a range is the point zero. -/
def isZero (R : Range) : Bool :=
  match R.lo, R.hi with
  | some lo, some hi => Kernel.Q.beq lo 0 && Kernel.Q.beq hi 0
  | _, _ => false

/-- The sum of two ends of the same side, infinite when either is. -/
def addEnd : Option ℚ → Option ℚ → Option ℚ
  | some a, some b => some (Kernel.Q.add a b)
  | _, _ => none

/-- The negatives of the members of a range. -/
def neg (R : Range) : Range := ⟨R.hi.map Kernel.Q.neg, R.lo.map Kernel.Q.neg⟩

/-- The sums of the members of two ranges. -/
def add (R S : Range) : Range := ⟨addEnd R.lo S.lo, addEnd R.hi S.hi⟩

/--
An upper end of the products `x * y` for `x` in `R` and `y` in `S`, when `R` has a nonnegative
lower end `a` and `S` an upper end `d`: `a * d` when `d ≤ 0`, and `b * d` for the upper end `b`
of `R` otherwise.
-/
def mulHiOfNonneg (R S : Range) : Option ℚ :=
  match R.lo, S.hi with
  | some a, some d =>
    if Kernel.Q.le 0 a then
      if Kernel.Q.le d 0 then some (Kernel.Q.mul a d) else R.hi.map (Kernel.Q.mul · d)
    else none
  | _, _ => none

/-- An upper end of the products of the members of two ranges: the rule of `mulHiOfNonneg` for
either factor, and for their negatives. -/
def mulHi (R S : Range) : Option ℚ :=
  (mulHiOfNonneg R S).or <| (mulHiOfNonneg S R).or <|
    (mulHiOfNonneg (neg R) (neg S)).or (mulHiOfNonneg (neg S) (neg R))

/-- The products of the members of two ranges. A factor that is exactly zero gives zero. -/
def mul (R S : Range) : Range :=
  if isZero R || isZero S then ⟨some 0, some 0⟩
  else ⟨(mulHi (neg R) S).map Kernel.Q.neg, mulHi R S⟩

/-- The inverses of the members of a range that lies on one side of zero, and the whole line
otherwise. An infinite end gives the end zero. -/
def inv (R : Range) : Range :=
  match R.lo, R.hi with
  | some a, hi =>
    if Kernel.Q.lt 0 a then ⟨some ((hi.map Kernel.Q.inv).getD 0), some (Kernel.Q.inv a)⟩
    else match hi with
      | some b => if Kernel.Q.lt b 0 then ⟨some (Kernel.Q.inv b), some (Kernel.Q.inv a)⟩ else whole
      | none => whole
  | none, some b => if Kernel.Q.lt b 0 then ⟨some (Kernel.Q.inv b), some 0⟩ else whole
  | none, none => whole

/-- The absolute values of the members of a range. -/
def abs (R : Range) : Range :=
  match R.lo, R.hi with
  | some a, some b =>
    if Kernel.Q.le 0 a then R
    else if Kernel.Q.le b 0 then neg R
    else ⟨some 0, some (Kernel.Q.max (Kernel.Q.neg a) b)⟩
  | some a, none => if Kernel.Q.le 0 a then R else ⟨some 0, none⟩
  | none, some b => if Kernel.Q.le b 0 then neg R else ⟨some 0, none⟩
  | none, none => ⟨some 0, none⟩

/-- The powers with a natural exponent of the members of a range: an even power is a power of
the absolute value, and an odd power keeps the order of the ends. -/
def pow (R : Range) (n : Nat) : Range :=
  if n = 0 then ⟨some 1, some 1⟩
  else if n % 2 = 0 then
    ⟨(abs R).lo.map (Kernel.Q.pow · n), (abs R).hi.map (Kernel.Q.pow · n)⟩
  else ⟨R.lo.map (Kernel.Q.pow · n), R.hi.map (Kernel.Q.pow · n)⟩

/-- The smaller of a member of each of two ranges. -/
def min (R S : Range) : Range :=
  ⟨match R.lo, S.lo with
    | some a, some c => some (Kernel.Q.min a c)
    | _, _ => none,
   match R.hi, S.hi with
    | some b, some d => some (Kernel.Q.min b d)
    | some b, none => some b
    | none, d => d⟩

/-- The larger of a member of each of two ranges. -/
def max (R S : Range) : Range := neg (min (neg R) (neg S))

section Backend

variable (B : Backend ℚ)

/-- The lower end of the backend's enclosure of a unary operation at a rational point. -/
def lowerAt (op : UnaryOp) (q : ℚ) : Option ℚ := (B.unary? op ⟨q, q⟩).map (·.lo)

/-- The upper end of the backend's enclosure of a unary operation at a rational point. -/
def upperAt (op : UnaryOp) (q : ℚ) : Option ℚ := (B.unary? op ⟨q, q⟩).map (·.hi)

/-- A rational number that is at least `π / 2`: the upper end of the backend's enclosure of
`Real.arccos 0`, or `2`. -/
def halfPi : ℚ := (upperAt B .acos 0).getD 2

/--
The values of a unary operation on a range, where the backend gives no enclosure: by the signs
of the ends for the negation, the absolute value, the inverse and the powers, by the backend's
enclosure at each rational end for the monotone functions, and by the range of the function for
the sine, the cosine, the inverse sine and the inverse cosine. The tangent has the whole line.
-/
def tail (op : UnaryOp) (R : Range) : Range :=
  match op with
  | .neg => neg R
  | .abs => abs R
  | .inv => inv R
  | .pow n => pow R n
  | .exp => ⟨some ((R.lo.bind (lowerAt B .exp)).getD 0), R.hi.bind (upperAt B .exp)⟩
  | .log =>
    match R.lo with
    | some a => if Kernel.Q.lt 0 a then ⟨lowerAt B .log a, R.hi.bind (upperAt B .log)⟩ else whole
    | none => whole
  | .sin => ⟨some (-1), some 1⟩
  | .cos => ⟨some (-1), some 1⟩
  | .tan => whole
  | .asin => ⟨some (Kernel.Q.neg (halfPi B)), some (halfPi B)⟩
  | .acos => ⟨some 0, some (Kernel.Q.mul 2 (halfPi B))⟩
  | .atan =>
    ⟨some ((R.lo.bind (lowerAt B .atan)).getD (Kernel.Q.neg (halfPi B))),
      some ((R.hi.bind (upperAt B .atan)).getD (halfPi B))⟩
  | .sinh => ⟨R.lo.bind (lowerAt B .sinh), R.hi.bind (upperAt B .sinh)⟩
  | .cosh =>
    ⟨some (((abs R).lo.bind (lowerAt B .cosh)).getD 1), (abs R).hi.bind (upperAt B .cosh)⟩
  | .tanh =>
    ⟨some ((R.lo.bind (lowerAt B .tanh)).getD (-1)), some ((R.hi.bind (upperAt B .tanh)).getD 1)⟩
  | .sqrt =>
    ⟨some ((R.lo.bind fun a => if Kernel.Q.le 0 a then lowerAt B .sqrt a else none).getD 0),
      R.hi.bind fun b => if Kernel.Q.lt b 0 then some 0 else upperAt B .sqrt b⟩

/-- The values of a unary operation on a range: the backend's enclosure on an interval with two
rational ends, and `tail` where it gives none. -/
def unary (op : UnaryOp) (R : Range) : Range :=
  match R.interval? with
  | some I =>
    match B.unary? op I with
    | some J => ofInterval J
    | none => tail B op R
  | none => tail B op R

/-- The values of a binary operation on two ranges, where the backend gives no enclosure. A
quotient is a product with the inverse, so a quotient by a range that contains zero has the
whole line, unless its numerator is exactly zero. -/
def pair (op : BinaryOp) (R S : Range) : Range :=
  match op with
  | .add => add R S
  | .sub => add R (neg S)
  | .mul => mul R S
  | .div => mul R (inv S)
  | .min => min R S
  | .max => max R S

/-- The values of a binary operation on two ranges: the backend's enclosure on intervals with
two rational ends, and `pair` where it gives none. -/
def binary (op : BinaryOp) (R S : Range) : Range :=
  match R.interval?, S.interval? with
  | some I, some J =>
    match B.binary? op I J with
    | some K => ofInterval K
    | none => pair op R S
  | _, _ => pair op R S

/-- The values of a three-input operation on three ranges: the backend's enclosure on intervals
with two rational ends, and the product and the sum of ranges otherwise. -/
def ternary (op : TernaryOp) (R S T : Range) : Range :=
  match R.interval?, S.interval?, T.interval? with
  | some I, some J, some K =>
    match B.ternary? op I J K with
    | some L => ofInterval L
    | none => match op with | .fma => add (mul R S) T
  | _, _, _ => match op with | .fma => add (mul R S) T

/-- The values of a registered operation. A call that the table `names` knows as a unary
operation of the expression language is that operation (`unary`), with its rules for infinite
ends. Any other call has the backend's enclosure when every argument has two rational ends, and
the whole line otherwise. -/
def call (names : List (Option UnaryOp)) (index : Nat) (args : List Range) : Range :=
  match Kernel.Seq.nth? names index, args with
  | some (some op), [R] => unary B op R
  | _, _ =>
    match args.mapM interval? with
    | some inputs =>
      match B.call? index inputs with
      | some output => ofInterval output
      | none => whole
    | none => whole

/-- The range of a rational constant. -/
def const (q : ℚ) : Range :=
  match B.const? q with
  | some I => ofInterval I
  | none => whole

end Backend

/-- The range of each variable of a box of ranges: the whole line for a variable that the box
does not have. -/
def env (box : List Range) (i : Nat) : Range :=
  match Kernel.Seq.nth? box i with
  | some R => R
  | none => whole

end Range

mutual
/-- The range of an expression on ranges of its variables, with the operations of a backend on
rational endpoints where they apply. `names` says which registered calls are unary operations of
the expression language (`Range.call`). The range is total: an operation without an enclosure
has the whole line (`Expr.contains_range`). -/
def Expr.range (e : Expr) (B : Backend ℚ) (names : List (Option UnaryOp))
    (env : Nat → Range) : Range :=
  match e with
  | .const q => Range.const B q
  | .var i => env i
  | .unary op a => Range.unary B op (Expr.range a B names env)
  | .binary op a b => Range.binary B op (Expr.range a B names env) (Expr.range b B names env)
  | .ternary op a b c =>
    Range.ternary B op (Expr.range a B names env) (Expr.range b B names env)
      (Expr.range c B names env)
  | .call index args => Range.call B names index (Expr.rangeArgs args B names env)
termination_by structural e

/-- The ranges of the arguments of a registered call. -/
def Expr.rangeArgs (args : List Expr) (B : Backend ℚ) (names : List (Option UnaryOp))
    (env : Nat → Range) : List Range :=
  match args with
  | [] => []
  | arg :: args => Expr.range arg B names env :: Expr.rangeArgs args B names env
termination_by structural args
end

/--
Whether a constraint has no point in a box of ranges, by one evaluation of its atoms: an atom
fails when the upper end of its range passes the test of its relation, a conjunction when one
part fails, and a disjunction when both do. A form atom is never decided here.
-/
def Constraint.failsOn (B : Backend ℚ) (names : List (Option UnaryOp)) (env : Nat → Range) :
    Constraint → Bool
  | .fails relation e =>
    match (e.range B names env).hi with
    | some hi => relation.check hi
    | none => false
  | .form _ _ => false
  | .and a b => Constraint.failsOn B names env a || Constraint.failsOn B names env b
  | .or a b => Constraint.failsOn B names env a && Constraint.failsOn B names env b

end FloatLib.Numerics.Interval
