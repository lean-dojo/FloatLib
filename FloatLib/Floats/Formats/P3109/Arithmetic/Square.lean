/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Proof

/-!
# Once-projected P3109 squares

Squaring reuses exact multiplication and projects once into the requested destination, so `x * x`
is rounded a single time. Source and destination may differ in width, precision, signedness, and
domain.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.10.4.
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
  Multiply value value target mode saturation

/-- Squaring is multiplication of the operand by itself, for every projection option. -/
theorem square_eq_mul (value : ExecFloat.P3109 format) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    square value target mode saturation = Multiply value value target mode saturation :=
  rfl

/-- A finite square is projected from the exact rational square with no intermediate rounding. -/
theorem decode_square_finite (value : ExecFloat.P3109 format) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) (q : Rat)
    (hvalue : value.toClosedRat = .finite q) :
    Format.SameDatum (decode (square value target mode saturation))
      (target.projectRatValue { rounding := mode, saturation } (.finite (q * q))) := by
  simpa [square, Multiply, hvalue, Arithmetic.Multiply] using
    decode_binary Arithmetic.Multiply value value target mode saturation

end FloatLib.Floats.ExecFloat.P3109
