/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Dyadic

/-!
# Executable normalization for directed dyadic rounding

These helpers scale a positive mantissa to a requested leading-bit position. Downward
normalization discards low bits; upward normalization rounds them toward positive infinity and
may carry into the next bit.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Floor a positive mantissa while moving its leading bit to `leadingBit`. -/
def roundMantissaToLeadingBitDown (mantissa leadingBit : Nat) : Nat :=
  if leadingBit ≤ mantissa.log2 then
    Nat.shiftRight mantissa (mantissa.log2 - leadingBit)
  else
    Nat.shiftLeft mantissa (leadingBit - mantissa.log2)

/-- Scale a positive mantissa to `leadingBit` and round up, possibly carrying into the next bit. -/
def roundMantissaToLeadingBitUp (mantissa leadingBit : Nat) : Nat :=
  if leadingBit ≤ mantissa.log2 then
    shiftRightCeilPow2 mantissa (mantissa.log2 - leadingBit)
  else
    Nat.shiftLeft mantissa (leadingBit - mantissa.log2)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
