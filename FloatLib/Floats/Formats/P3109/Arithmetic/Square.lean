/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Proof

/-!
# Once-projected P3109 squares

Squaring reuses exact multiplication and projects once into the requested destination.
The source and destination may have different widths, precisions, signedness, and domains.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {format : Format}

/--
Square the exact decoded operand and project once into `target`, by default the operand's format,
with multiplication's NaN and infinity behavior.
-/
@[inline] def square (value : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  mul value value target mode saturation

/-- Squaring is multiplication of the operand by itself, for every projection option. -/
theorem square_eq_mul (value : ExecFloat.P3109 format) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    square value target mode saturation = mul value value target mode saturation :=
  rfl

/-- A finite square is projected from the exact rational square with no intermediate rounding. -/
theorem decode_square_finite (value : ExecFloat.P3109 format) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) (q : Rat)
    (hvalue : value.toClosedRat = .finite q) :
    Format.SameDatum (decode (square value target mode saturation))
      (target.projectRatValue { rounding := mode, saturation } (.finite (q * q))) := by
  simpa [square, mul, hvalue, Arithmetic.mul] using
    decode_binary Arithmetic.mul value value target mode saturation

end FloatLib.Floats.ExecFloat.P3109
