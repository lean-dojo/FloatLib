/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Logarithmic.Configured.Runtime
public import FloatLib.Floats.Formats.Logarithmic.Exact.Proof

/-!
# Correctness of configured exact logarithmic operations

Wrapping is an equivalence with the complete code, zero denotes real zero, and multiplication
agrees exactly with multiplication of decoded real values.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Logarithmic

open FloatLib.Numerics

variable {radix : Radix}

/-- Unwrapping a freshly wrapped logarithmic code returns the original code. -/
@[simp, grind =] theorem toCode_ofCode (code : Formats.Logarithmic.Code radix) :
    toCode (ofCode code) = code :=
  rfl

/-- Rewrapping the code of a logarithmic value returns the original value. -/
@[simp, grind =] theorem ofCode_toCode (value : ExecFloat.Logarithmic radix) :
    ofCode value.toCode = value :=
  ExecFloat.ofRaw_raw value

/-- The distinguished logarithmic zero code denotes real zero. -/
@[simp, grind =] theorem toReal_zero :
    toReal (zero : ExecFloat.Logarithmic radix) = 0 :=
  Formats.Logarithmic.Code.toReal_zero radix

/-- Logarithmic multiplication agrees exactly with multiplication of decoded real values. -/
@[simp, grind =] theorem toReal_mul (left right : ExecFloat.Logarithmic radix) :
    toReal (mul left right) = toReal left * toReal right :=
  Formats.Logarithmic.Code.toReal_mul left.toCode right.toCode

end FloatLib.Floats.ExecFloat.Logarithmic
