/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Dyadic.Basic
public import FloatLib.Numerics.Core.Value

/-!
# Closed extended-rational arithmetic

The operations compute exactly on finite rationals, retain signed infinities, and collapse
exceptional values to NaN. Opposite infinities in addition, zero times infinity, and division by
zero are indeterminate. No encoding, destination format, or rounding policy occurs here.

P3109 arithmetic and stored block dot products share these operations. The `P3109.Arithmetic`
namespace is retained for the public API; the definitions themselves are format independent.
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
def Negate : NumericalValue Rat → NumericalValue Rat
  | .finite value => .finite (-value)
  | .infinity negative => .infinity (!negative)
  | .exceptional _ => nan

/-- Absolute value in the report's closed extended domain. -/
def Abs : NumericalValue Rat → NumericalValue Rat
  | .finite value => .finite (if value < 0 then -value else value)
  | .infinity _ => .infinity false
  | .exceptional _ => nan

/-- Copying a sign treats zero as nonnegative and propagates either NaN operand. -/
def CopySign (value sign : NumericalValue Rat) : NumericalValue Rat :=
  match sign with
  | .exceptional _ => nan
  | .infinity negative => if negative then Negate (Abs value) else Abs value
  | .finite sign => if sign < 0 then Negate (Abs value) else Abs value

/-- Exact addition, with the indeterminate result NaN for opposite infinities. -/
def Add : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | .infinity left, .infinity right =>
      if left == right then .infinity left else nan
  | .infinity negative, .finite _ | .finite _, .infinity negative => .infinity negative
  | .finite left, .finite right => .finite (left + right)

/-- Exact subtraction, with no projection of the negated operand. -/
def Subtract (left right : NumericalValue Rat) : NumericalValue Rat :=
  Add left (Negate right)

/-- Exact multiplication, with NaN for zero times infinity. -/
def Multiply : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | .infinity left, .infinity right => .infinity (left != right)
  | .infinity negative, .finite value | .finite value, .infinity negative =>
      if value == 0 then nan else .infinity (negative != decide (value < 0))
  | .finite left, .finite right => .finite (left * right)

/-- Exact division, with NaN for every zero denominator and for infinity over infinity. -/
def Divide : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | .infinity _, .infinity _ => nan
  | .finite _, .infinity _ => .finite 0
  | .infinity negative, .finite value =>
      if value == 0 then nan else .infinity (negative != decide (value < 0))
  | .finite left, .finite right =>
      if right == 0 then nan else .finite (left / right)

/-- Exact reciprocal, before the sole destination projection. -/
def Recip (value : NumericalValue Rat) : NumericalValue Rat :=
  Divide (.finite 1) value

/-- Exact fused multiply-add, with no intermediate rounding or saturation. -/
def FMA (left right addend : NumericalValue Rat) : NumericalValue Rat :=
  Add (Multiply left right) addend

/-- Exact fused add-add, with no intermediate rounding or saturation. -/
def FAA (left middle right : NumericalValue Rat) : NumericalValue Rat :=
  Add (Add left middle) right

end FloatLib.Floats.Formats.P3109.Arithmetic
