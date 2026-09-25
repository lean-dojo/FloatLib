/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Proof

/-!
# Once-projected P3109 squares

Squaring uses the existing exact multiplication and projects once into the requested destination.
The source and destination may have different widths, precisions, signedness, and domains.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {source format : Format}

/-- Square an exact decoded operand and project once into the destination format. -/
@[inline] def squareTo (destination : Format) (policy : ProjectionPolicy)
    (value : ExecFloat.P3109 source) : ExecFloat.P3109 destination :=
  mulTo destination policy value value

/-- Same-format square with one projection and multiplication's NaN and infinity behavior. -/
@[inline] def square (value : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  squareTo format policy value

/-- Squaring preserves the complete encoded multiplication result for every projection policy. -/
theorem square_eq_mul (value : ExecFloat.P3109 format) (policy : ProjectionPolicy) :
    square value policy = mul value value policy :=
  rfl

/-- A finite square is projected from the exact rational square with no intermediate rounding. -/
theorem decode_squareTo_finite (destination : Format) (policy : ProjectionPolicy)
    (value : ExecFloat.P3109 source) (q : Rat) (hvalue : value.toClosedRat = .finite q) :
    Format.SameDatum (decode (squareTo destination policy value))
      (destination.projectRatValue policy (.finite (q * q))) := by
  simpa [squareTo, mulTo, hvalue, Arithmetic.mul] using
    decode_binaryTo destination policy Arithmetic.mul value value

end FloatLib.Floats.ExecFloat.P3109
