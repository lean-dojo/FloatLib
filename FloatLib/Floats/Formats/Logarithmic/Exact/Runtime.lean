/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Capabilities.Radix

/-!
# Exact logarithmic representation and execution

A code is zero or a sign with an unbounded integer exponent at a fixed radix. This module keeps
that representation, its executable rational decoder, and multiplication together. Multiplication
handles zero, xors the signs, and adds the exponents; it introduces no rounding or overflow.

`Exact.Proof` supplies the real numerical system, erased proof views, and theorems connecting the
rational decoder and multiplication kernel to their real semantics.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Logarithmic

open FloatLib.Numerics

/-- Exact logarithmic code at radix `radix`. -/
inductive Code (radix : Radix) where
  | zero
  | value (negative : Bool) (exponent : Int)
  deriving DecidableEq, Repr

end FloatLib.Floats.Formats.Logarithmic

/-! ## Executable operations -/

namespace FloatLib.Floats.Formats.Logarithmic.Code

open FloatLib.Numerics

/-- Exact rational value of a logarithmic code. -/
def toRat {radix : Radix} : Code radix → Rat
  | .zero => 0
  | .value negative exponent =>
      let magnitude := (radix.base : Rat) ^ exponent
      if negative then -magnitude else magnitude

/-- Exact logarithmic multiplication. -/
def mul {radix : Radix} : Code radix → Code radix → Code radix
  | .zero, _ | _, .zero => .zero
  | .value leftSign leftExponent, .value rightSign rightExponent =>
      .value (Bool.xor leftSign rightSign) (leftExponent + rightExponent)

end FloatLib.Floats.Formats.Logarithmic.Code
