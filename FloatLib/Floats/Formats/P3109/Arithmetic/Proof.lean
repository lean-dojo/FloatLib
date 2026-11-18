/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.ExtendedRat.Algebra
public import FloatLib.Floats.Formats.P3109.Arithmetic.Runtime
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Proof

/-!
# Mathematical semantics of P3109 rational arithmetic

On finite values, P3109 arithmetic is exact rational arithmetic, and embedding the rationals into
the reals preserves the complete expression. The algebraic results here describe arithmetic
before any rounding. Then the decoding theorems connect each public executable operation to one
report projection of that exact result.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7.3 and 4.10.3–4.10.7.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {source leftFormat rightFormat thirdFormat : Format}

/-- The executable unary operation decodes to one projection of its exact closed result. -/
theorem decode_unary (operation : NumericalValue Rat → NumericalValue Rat)
    (value : ExecFloat.P3109 source) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    Format.SameDatum (decode (unary operation value target mode saturation))
      (target.projectRatValue { rounding := mode, saturation } (operation value.toClosedRat)) :=
  decode_projectRat _ mode saturation

/-- The executable binary operation decodes to one projection of its exact closed result. -/
theorem decode_binary
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (left : ExecFloat.P3109 leftFormat) (right : ExecFloat.P3109 rightFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum (decode (binary operation left right target mode saturation))
      (target.projectRatValue { rounding := mode, saturation }
        (operation left.toClosedRat right.toClosedRat)) :=
  decode_projectRat _ mode saturation

/-- The executable fused operation decodes to one projection of the whole exact expression. -/
theorem decode_ternary
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat →
      NumericalValue Rat)
    (left : ExecFloat.P3109 leftFormat) (right : ExecFloat.P3109 rightFormat)
    (third : ExecFloat.P3109 thirdFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    Format.SameDatum (decode (ternary operation left right third target mode saturation))
      (target.projectRatValue { rounding := mode, saturation }
        (operation left.toClosedRat right.toClosedRat third.toClosedRat)) :=
  decode_projectRat _ mode saturation

/-- Finite FMA is one projection of the exact rational product plus addend. -/
theorem decode_fma_finite {format : Format}
    (left right addend : ExecFloat.P3109 format) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) (x y z : Rat)
    (hleft : left.toClosedRat = .finite x) (hright : right.toClosedRat = .finite y)
    (haddend : addend.toClosedRat = .finite z) :
    Format.SameDatum (decode (FMA left right addend target mode saturation))
      (target.projectRatValue { rounding := mode, saturation } (.finite (x * y + z))) := by
  simpa [FMA, hleft, hright, haddend] using
    decode_ternary Arithmetic.FMA left right addend target mode saturation

end FloatLib.Floats.ExecFloat.P3109
