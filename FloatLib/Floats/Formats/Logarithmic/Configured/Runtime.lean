/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Logarithmic.Configured.Core

/-!
# Executable exact logarithmic operations

These are the executable operations on configured logarithmic values, each of which is zero or a
signed integral power of the radix. Multiplication is the one arithmetic operation. It's closed and
exact, since the signs xor and the exponents add. Addition and conversion from arbitrary reals are
left out because they would need rounding, as integral powers of the radix aren't closed under
addition. Division by a nonzero value could subtract exponents, but there's no division operation
and no policy for a zero divisor.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Logarithmic

open FloatLib.Numerics

variable {radix : Radix}

/-- Wrap a complete logarithmic code without conversion. -/
@[inline] def ofCode (code : Formats.Logarithmic.Code radix) :
    ExecFloat.Logarithmic radix :=
  ExecFloat.ofRaw code

/-- Recover the complete logarithmic code without conversion. -/
@[inline] def toCode (value : ExecFloat.Logarithmic radix) :
    Formats.Logarithmic.Code radix :=
  value.raw

/-- Construct the unique zero code. -/
@[inline] def zero : ExecFloat.Logarithmic radix :=
  ofCode .zero

/--
Construct the exact value `radix ^ exponent`, positive by default. `(negative := true)` gives
`-radix ^ exponent`.
-/
@[inline] def ofExponent (exponent : Int) (negative : Bool := false) :
    ExecFloat.Logarithmic radix :=
  ofCode (.value negative exponent)

/-- Decode a configured logarithmic value to its exact real meaning. -/
@[inline] noncomputable def toReal (value : ExecFloat.Logarithmic radix) : ℝ :=
  value.toCode.toReal

/--
Exact rational value of a configured logarithmic value, zero or `±radix^exponent`.

Every value is finite, so the reading is total.
-/
@[inline] def toRat (value : ExecFloat.Logarithmic radix) : Rat :=
  value.toCode.toRat

/-- Exact multiplication of configured logarithmic values. -/
@[inline] def mul (left right : ExecFloat.Logarithmic radix) :
    ExecFloat.Logarithmic radix :=
  ofCode (Formats.Logarithmic.Code.mul left.toCode right.toCode)

end FloatLib.Floats.ExecFloat.Logarithmic
