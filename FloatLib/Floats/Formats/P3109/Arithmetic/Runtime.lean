/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Rational.Runtime

/-!
# Exact rational arithmetic for P3109

The closed operations in `Arithmetic` evaluate finite operands in `Rat`, retaining infinities
and the report's single NaN. In particular, division by zero returns NaN, including infinity
divided by zero. FMA and fused add-add form the complete exact expression before projection.

The `ExecFloat.P3109.*To` operations accept independent source and destination descriptors and
an explicit projection policy. Same-format operations use FloatLib's nearest-even,
no-saturation policy by default. No IEEE exception flags or floating-point environment are used.

Exact rational intermediates can require large integers when the descriptor has a wide exponent
range. This implementation does not promise a fixed workspace bound for arbitrary descriptors.

## Reference

IEEE Working Group P3109, *Interim Report on Arithmetic Formats for Machine Learning*,
version 4.0.3 (1 September 2026), §§4.10.1–4.10.8, revision `34f5964`.
This is an unapproved working-group report, not an approved IEEE standard.
<https://github.com/P3109/Public/tree/34f5964d9bb2382b2665d15467fc3517b990b308>.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic

/-- The report's single exceptional datum. -/
def nan : NumericalValue Rat := .exceptional (.nan)

/-- Exact rational observation of a decoded binary datum. -/
def toRat : NumericalValue FloatLib.Numerics.Dyadic → NumericalValue Rat
  | .finite value => .finite value.toRat
  | .infinity negative => .infinity negative
  | .exceptional _ => nan

/-- Negation in the report's closed extended domain. -/
def neg : NumericalValue Rat → NumericalValue Rat
  | .finite value => .finite (-value)
  | .infinity negative => .infinity (!negative)
  | .exceptional _ => nan

/-- Absolute value in the report's closed extended domain. -/
def abs : NumericalValue Rat → NumericalValue Rat
  | .finite value => .finite (if value < 0 then -value else value)
  | .infinity _ => .infinity false
  | .exceptional _ => nan

/-- Copying a sign treats zero as nonnegative and propagates either NaN operand. -/
def copySign (value sign : NumericalValue Rat) : NumericalValue Rat :=
  match sign with
  | .exceptional _ => nan
  | .infinity negative => if negative then neg (abs value) else abs value
  | .finite sign => if sign < 0 then neg (abs value) else abs value

/-- Exact addition; opposite infinities have the indeterminate result NaN. -/
def add : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | .infinity left, .infinity right =>
      if left == right then .infinity left else nan
  | .infinity negative, .finite _ | .finite _, .infinity negative => .infinity negative
  | .finite left, .finite right => .finite (left + right)

/-- Exact subtraction, with no projection of the negated operand. -/
def sub (left right : NumericalValue Rat) : NumericalValue Rat :=
  add left (neg right)

/-- Exact multiplication; zero times infinity is NaN. -/
def mul : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | .infinity left, .infinity right => .infinity (left != right)
  | .infinity negative, .finite value | .finite value, .infinity negative =>
      if value == 0 then nan else .infinity (negative != decide (value < 0))
  | .finite left, .finite right => .finite (left * right)

/-- Exact division; every zero denominator and infinity divided by infinity yield NaN. -/
def div : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | .infinity _, .infinity _ => nan
  | .finite _, .infinity _ => .finite 0
  | .infinity negative, .finite value =>
      if value == 0 then nan else .infinity (negative != decide (value < 0))
  | .finite left, .finite right =>
      if right == 0 then nan else .finite (left / right)

/-- Exact reciprocal, before the sole destination projection. -/
def recip (value : NumericalValue Rat) : NumericalValue Rat :=
  div (.finite 1) value

/-- Exact fused multiply-add, with no intermediate rounding or saturation. -/
def fma (left right addend : NumericalValue Rat) : NumericalValue Rat :=
  add (mul left right) addend

/-- Exact fused add-add, with no intermediate rounding or saturation. -/
def faa (left middle right : NumericalValue Rat) : NumericalValue Rat :=
  add (add left middle) right

end FloatLib.Floats.Formats.P3109.Arithmetic

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {source leftFormat rightFormat thirdFormat format : Format}

/-- Exact closed rational value of a P3109 operand. -/
@[inline] def toClosedRat (value : ExecFloat.P3109 source) : NumericalValue Rat :=
  Arithmetic.toRat value.decode

/-- Project an exact unary closed operation into an independently chosen destination. -/
@[inline] def unaryTo (destination : Format) (policy : ProjectionPolicy)
    (operation : NumericalValue Rat → NumericalValue Rat)
    (value : ExecFloat.P3109 source) : ExecFloat.P3109 destination :=
  projectRat policy (operation value.toClosedRat)

/-- Project an exact binary closed operation once, after evaluating both operands. -/
@[inline] def binaryTo (destination : Format) (policy : ProjectionPolicy)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (left : ExecFloat.P3109 leftFormat) (right : ExecFloat.P3109 rightFormat) :
    ExecFloat.P3109 destination :=
  projectRat policy (operation left.toClosedRat right.toClosedRat)

/-- Project an exact ternary closed operation once, after the complete expression. -/
@[inline] def ternaryTo (destination : Format) (policy : ProjectionPolicy)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat →
      NumericalValue Rat)
    (left : ExecFloat.P3109 leftFormat) (right : ExecFloat.P3109 rightFormat)
    (third : ExecFloat.P3109 thirdFormat) : ExecFloat.P3109 destination :=
  projectRat policy (operation left.toClosedRat right.toClosedRat third.toClosedRat)

/-- Negate and project into the requested destination. -/
@[inline] def negTo (destination : Format) (policy : ProjectionPolicy) :
    ExecFloat.P3109 source → ExecFloat.P3109 destination :=
  unaryTo (source := source) destination policy Arithmetic.neg

/-- Take absolute value and project into the requested destination. -/
@[inline] def absTo (destination : Format) (policy : ProjectionPolicy) :
    ExecFloat.P3109 source → ExecFloat.P3109 destination :=
  unaryTo (source := source) destination policy Arithmetic.abs

/-- Copy the sign, propagating either NaN, and project once. -/
@[inline] def copySignTo (destination : Format) (policy : ProjectionPolicy) :
    ExecFloat.P3109 leftFormat → ExecFloat.P3109 rightFormat → ExecFloat.P3109 destination :=
  binaryTo (leftFormat := leftFormat) (rightFormat := rightFormat)
    destination policy Arithmetic.copySign

/-- Add exact decoded operands and project once. -/
@[inline] def addTo (destination : Format) (policy : ProjectionPolicy) :
    ExecFloat.P3109 leftFormat → ExecFloat.P3109 rightFormat → ExecFloat.P3109 destination :=
  binaryTo (leftFormat := leftFormat) (rightFormat := rightFormat)
    destination policy Arithmetic.add

/-- Subtract exact decoded operands and project once. -/
@[inline] def subTo (destination : Format) (policy : ProjectionPolicy) :
    ExecFloat.P3109 leftFormat → ExecFloat.P3109 rightFormat → ExecFloat.P3109 destination :=
  binaryTo (leftFormat := leftFormat) (rightFormat := rightFormat)
    destination policy Arithmetic.sub

/-- Multiply exact decoded operands and project once. -/
@[inline] def mulTo (destination : Format) (policy : ProjectionPolicy) :
    ExecFloat.P3109 leftFormat → ExecFloat.P3109 rightFormat → ExecFloat.P3109 destination :=
  binaryTo (leftFormat := leftFormat) (rightFormat := rightFormat)
    destination policy Arithmetic.mul

/-- Divide exact decoded operands, returning NaN for a zero denominator, and project once. -/
@[inline] def divTo (destination : Format) (policy : ProjectionPolicy) :
    ExecFloat.P3109 leftFormat → ExecFloat.P3109 rightFormat → ExecFloat.P3109 destination :=
  binaryTo (leftFormat := leftFormat) (rightFormat := rightFormat)
    destination policy Arithmetic.div

/-- Take the exact reciprocal and project once. -/
@[inline] def recipTo (destination : Format) (policy : ProjectionPolicy) :
    ExecFloat.P3109 source → ExecFloat.P3109 destination :=
  unaryTo (source := source) destination policy Arithmetic.recip

/-- Fused multiply-add across independently chosen source and destination formats. -/
@[inline] def fmaTo (destination : Format) (policy : ProjectionPolicy) :
    ExecFloat.P3109 leftFormat → ExecFloat.P3109 rightFormat → ExecFloat.P3109 thirdFormat →
      ExecFloat.P3109 destination :=
  ternaryTo (leftFormat := leftFormat) (rightFormat := rightFormat)
    (thirdFormat := thirdFormat) destination policy Arithmetic.fma

/-- Fused add-add across independently chosen source and destination formats. -/
@[inline] def faaTo (destination : Format) (policy : ProjectionPolicy) :
    ExecFloat.P3109 leftFormat → ExecFloat.P3109 rightFormat → ExecFloat.P3109 thirdFormat →
      ExecFloat.P3109 destination :=
  ternaryTo (leftFormat := leftFormat) (rightFormat := rightFormat)
    (thirdFormat := thirdFormat) destination policy Arithmetic.faa

/-- Same-format negation followed by the supplied projection. -/
@[inline] def neg (value : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  negTo format policy value

/-- Same-format absolute value followed by the supplied projection. -/
@[inline] def abs (value : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  absTo format policy value

/-- Same-format sign copying followed by the supplied projection. -/
@[inline] def copySign (value sign : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  copySignTo format policy value sign

/-- Same-format addition with one final projection. -/
@[inline] def add (left right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  addTo format policy left right

/-- Same-format subtraction with one final projection. -/
@[inline] def sub (left right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  subTo format policy left right

/-- Same-format multiplication with one final projection. -/
@[inline] def mul (left right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  mulTo format policy left right

/-- Same-format division with one final projection; a zero denominator yields NaN. -/
@[inline] def div (left right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  divTo format policy left right

/-- Same-format reciprocal with one final projection. -/
@[inline] def recip (value : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  recipTo format policy value

/-- Same-format fused multiply-add with one final projection. -/
@[inline] def fma (left right addend : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  fmaTo format policy left right addend

/-- Same-format fused add-add with one final projection. -/
@[inline] def faa (left middle right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  faaTo format policy left middle right

end FloatLib.Floats.ExecFloat.P3109
