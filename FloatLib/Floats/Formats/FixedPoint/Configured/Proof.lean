/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Configured.Runtime
public import FloatLib.Floats.Formats.FixedPoint.Exact.Proof

/-!
# Correctness of configured exact fixed-point operations

Wrapping is an equivalence with the complete code, and each arithmetic operation agrees with its
exact rational interpretation.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.FixedPoint

open FloatLib.Numerics

variable {radix : Radix} {fractionalDigits p q : Nat}

/-- Unwrapping a freshly wrapped exact fixed-point code returns the original code. -/
@[simp, grind =] theorem toCode_ofCode
    (code : Formats.FixedPoint.Code radix fractionalDigits) :
    toCode (ofCode code) = code :=
  rfl

/-- Rewrapping the code of an exact fixed-point value returns the original value. -/
@[simp, grind =] theorem ofCode_toCode
    (value : ExecFloat.FixedPoint radix fractionalDigits) :
    ofCode value.toCode = value :=
  ExecFloat.ofRaw_raw value

/-- Constructing from a coefficient stores that coefficient exactly. -/
@[simp, grind =] theorem coefficient_ofCoefficient (stored : Int) :
    coefficient (ofCoefficient stored :
      ExecFloat.FixedPoint radix fractionalDigits) = stored :=
  rfl

/-- `roundRat` stores the ties-to-even rounded grid coefficient. -/
@[simp, grind =] theorem coefficient_roundRat (value : Rat) :
    coefficient (roundRat value :
      ExecFloat.FixedPoint radix fractionalDigits) =
        roundRatEven (value * scale radix fractionalDigits) :=
  rfl

/-- Exact same-scale addition agrees with addition of the decoded rationals. -/
@[simp, grind =] theorem toRat_add
    (left right : ExecFloat.FixedPoint radix fractionalDigits) :
    toRat (add left right) = toRat left + toRat right :=
  Formats.FixedPoint.Code.toRat_add left.toCode right.toCode

/-- Exact fixed-point negation agrees with negation of the decoded rational. -/
@[simp, grind =] theorem toRat_neg
    (value : ExecFloat.FixedPoint radix fractionalDigits) :
    toRat (neg value) = -toRat value :=
  Formats.FixedPoint.Code.toRat_neg value.toCode

/-- Exact same-scale subtraction agrees with subtraction of the decoded rationals. -/
@[simp, grind =] theorem toRat_sub
    (left right : ExecFloat.FixedPoint radix fractionalDigits) :
    toRat (sub left right) = toRat left - toRat right :=
  Formats.FixedPoint.Code.toRat_sub left.toCode right.toCode

/-- Scale-composing multiplication agrees with multiplication of the decoded rationals. -/
@[simp, grind =] theorem toRat_mul
    (left : ExecFloat.FixedPoint radix p)
    (right : ExecFloat.FixedPoint radix q) :
    toRat (mul left right) = toRat left * toRat right :=
  Formats.FixedPoint.Code.toRat_mul left.toCode right.toCode

end FloatLib.Floats.ExecFloat.FixedPoint
