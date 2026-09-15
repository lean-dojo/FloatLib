/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Logarithmic.Configured.Core

/-!
# Executable exact logarithmic operations

Every value is zero or a signed integral power of the radix. Multiplication is the only
arithmetic operation supplied; it is closed and exact because signs xor and exponents add.
Addition and arbitrary real conversion would require rounding because integral powers of the
radix are not closed under addition. Division by a nonzero value could subtract exponents
exactly, but no division operation or zero-divisor policy is supplied.
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

/-- Construct the exact value `(-1)^negative * radix^exponent`. -/
@[inline] def ofSignExponent (negative : Bool) (exponent : Int) :
    ExecFloat.Logarithmic radix :=
  ofCode (.value negative exponent)

/-- Decode a configured logarithmic value to its exact real meaning. -/
@[inline] noncomputable def toReal (value : ExecFloat.Logarithmic radix) : ℝ :=
  value.toCode.toReal

/-- Exact multiplication of configured logarithmic values. -/
@[inline] def mul (left right : ExecFloat.Logarithmic radix) :
    ExecFloat.Logarithmic radix :=
  ofCode (Formats.Logarithmic.Code.mul left.toCode right.toCode)

end FloatLib.Floats.ExecFloat.Logarithmic
