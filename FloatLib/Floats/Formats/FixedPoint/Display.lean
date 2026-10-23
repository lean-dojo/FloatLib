/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Core
public import FloatLib.Floats.Formats.FixedPoint.Configured.Core
public import FloatLib.Numerics.Exact.DecimalText.Notation

/-!
# Value display of fixed-point formats

Fixed-point values print their exact value in fixed notation. Decimal grids keep their scale, so
3.5 with three fractional digits prints as `3.500`. Other radices print the exact decimal value
without trailing zeros when it terminates, as for binary grids, and otherwise a reduced fraction
such as `1/3`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint

open FloatLib.Numerics

/-- Text of the coefficient `coefficient` on the grid `radix^(-fractionalDigits)`. -/
def display (radix : Radix) (fractionalDigits : Nat) (coefficient : Int) : String :=
  if radix.base = 10 then
    String.ofList
      (DecimalText.Decimal.fixedCharacters
        ⟨coefficient < 0, coefficient.natAbs, -(fractionalDigits : Int)⟩)
  else
    let value : Rat := coefficient / (scale radix fractionalDigits : Nat)
    match DecimalText.ofRat? value with
    | some exact => String.ofList exact.trimTrailingZeros.fixedCharacters
    | none => toString value

end FloatLib.Floats.Formats.FixedPoint

namespace FloatLib.Floats.ExecFloat

/-- Exact fixed-point values print their value on their grid. -/
instance (radix : FloatLib.Numerics.Radix) (fractionalDigits : Nat) :
    FormatDisplay (FixedPoint.Family radix fractionalDigits) where
  format code := Formats.FixedPoint.display radix fractionalDigits code.coefficient

/-- Bounded fixed-point values print their value on their grid. -/
instance (radix : FloatLib.Numerics.Radix) (fractionalDigits width : Nat) :
    FormatDisplay (BoundedFixedPoint.Family radix fractionalDigits width) where
  format code :=
    Formats.FixedPoint.display radix fractionalDigits (Formats.FixedPoint.Bounded.coefficient code)

end FloatLib.Floats.ExecFloat
