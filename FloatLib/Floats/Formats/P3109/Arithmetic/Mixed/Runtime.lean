/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Executable.Conversion.Runtime
public import FloatLib.Floats.Formats.P3109.Arithmetic.Runtime
public import FloatLib.Floats.Formats.P3109.Conversion.Runtime

/-!
# Mixed-format P3109 arithmetic

One expression can mix a configured IEEE accumulator, a P3109 operand, and an exact rational. Each
source type selects an exact decoder, and finite values are embedded into `Rat`. In that domain
IEEE negative zero loses its sign, as §4.8.1 requires, and every exceptional observation becomes
the report's one NaN.

`Destination` supplies the final report projection, and `Destination.p3109` selects any P3109
descriptor. External destinations live in `Arithmetic.External`, so importing this module
installs no alternative IEEE arithmetic or conversion instances. The operation always evaluates
the whole closed expression before projecting, fused add-add and scaled arithmetic included.

Reference: P3109 unapproved interim report v4.1 (14 September 2026),
revision `2d45cf2`, §§4.5, 4.8–4.10 and 5.8.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic

/-- Canonicalize exceptions to the report's sole NaN datum. -/
def canonical : NumericalValue Rat → NumericalValue Rat
  | .exceptional _ => nan
  | value => value

/-- A final report projection, kept apart from ordinary destination conversion. -/
structure Destination (Result : Type) where
  /-- Round, saturate, and encode one complete exact result under the supplied policy. -/
  project : ProjectionPolicy → NumericalValue Rat → Result

namespace Destination

/-- A P3109 result format with its complete report projection policy.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.9.1, 4.10 and 5.8.
-/
def p3109 (format : Format) : Destination (ExecFloat.P3109 format) :=
  ⟨fun policy value => ExecFloat.P3109.projectRat value policy.rounding policy.saturation⟩

end Destination

namespace Mixed

open ExecFloat

variable {Source SourceExact Left LeftExact Right RightExact Third ThirdExact Result : Type}
variable [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
variable [ExactDecoder Left LeftExact] [ExactMap LeftExact Rat]
variable [ExactDecoder Right RightExact] [ExactMap RightExact Rat]
variable [ExactDecoder Third ThirdExact] [ExactMap ThirdExact Rat]

/-- Decode through the source's exact interface and discard IEEE zero signs and NaN metadata. -/
@[inline] def decode (value : Source) : NumericalValue Rat :=
  canonical (ExactDecoder.decodeTo value)

/--
Conversion from an independently typed source through one destination projection, rounding in
`mode` (nearest-even by default) before `saturation` (none by default) applies.
P3109 interim report v4.1 (14 September 2026), §4.9.1; unapproved draft.
-/
@[inline] def Convert (destination : Destination Result) (value : Source)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  destination.project { rounding := mode, saturation } (decode value)

/-- Apply a closed unary operation before the destination projection. -/
@[inline] def unary (destination : Destination Result)
    (operation : NumericalValue Rat → NumericalValue Rat) (value : Source)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  destination.project { rounding := mode, saturation } (operation (decode value))

/-- Apply a closed binary operation to independently typed operands, then project once. -/
@[inline] def binary (destination : Destination Result)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (left : Left) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  destination.project { rounding := mode, saturation } (operation (decode left) (decode right))

/-- Evaluate a complete ternary closed expression before the sole destination projection. -/
@[inline] def ternary (destination : Destination Result)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat →
      NumericalValue Rat)
    (left : Left) (right : Right) (third : Third)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  destination.project { rounding := mode, saturation }
    (operation (decode left) (decode right) (decode third))

/-- Mixed reciprocal, with zero mapped to NaN before projection.

P3109 interim report v4.1 (14 September 2026), §4.10.8; unapproved draft.
-/
@[inline] def Recip (destination : Destination Result) (value : Source)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  unary destination Arithmetic.Recip value mode saturation

/-- Mixed addition, retaining closed-domain infinities and NaN.

P3109 interim report v4.1 (14 September 2026), §4.10.3; unapproved draft.
-/
@[inline] def Add (destination : Destination Result) (left : Left) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  binary destination Arithmetic.Add left right mode saturation

/-- Mixed subtraction with no intermediate rounding.

P3109 interim report v4.1 (14 September 2026), §4.10.3; unapproved draft.
-/
@[inline] def Subtract (destination : Destination Result) (left : Left) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  binary destination Arithmetic.Subtract left right mode saturation

/-- Mixed multiplication with no intermediate rounding.

P3109 interim report v4.1 (14 September 2026), §4.10.4; unapproved draft.
-/
@[inline] def Multiply (destination : Destination Result) (left : Left) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  binary destination Arithmetic.Multiply left right mode saturation

/-- Mixed division with the report's zero-denominator rule.

P3109 interim report v4.1 (14 September 2026), §4.10.5; unapproved draft.
-/
@[inline] def Divide (destination : Destination Result) (left : Left) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  binary destination Arithmetic.Divide left right mode saturation

/-- Mixed fused multiply-add, including an independently typed accumulator.

P3109 interim report v4.1 (14 September 2026), §4.10.6; unapproved draft.
-/
@[inline] def FMA (destination : Destination Result) (left : Left) (right : Right)
    (addend : Third) (mode : RoundingMode := .nearest)
    (saturation : SaturationMode := .none) : Result :=
  ternary destination Arithmetic.FMA left right addend mode saturation

/-- Mixed fused add-add, with neither addition rounded before the result projection.

P3109 interim report v4.1 (14 September 2026), §4.10.7; unapproved draft.
-/
@[inline] def FAA (destination : Destination Result) (left : Left) (middle : Right)
    (right : Third) (mode : RoundingMode := .nearest)
    (saturation : SaturationMode := .none) : Result :=
  ternary destination Arithmetic.FAA left middle right mode saturation

variable {LeftScale LeftScaleExact RightScale RightScaleExact : Type}
variable [ExactDecoder LeftScale LeftScaleExact] [ExactMap LeftScaleExact Rat]
variable [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]

/--
Scaled binary operation from §5.8, with an implicit exact result scale of one: `operation` is
applied to `leftScale * left` and `rightScale * right`, and the exact result is projected once into
`destination` with rounding `mode` and overflow policy `saturation`.

Input scaling is closed multiplication, so a zero scale times infinity is NaN, and a NaN scale
propagates even when its element is zero. Dividing by the result scale one would only turn
exceptional results into the canonical NaN, so the division is left out, and
`Mixed.scaledBinary_eq_project_div_one` proves that nothing changes for addition, subtraction,
multiplication and every other operation with canonical results.
-/
@[inline] def scaledBinary (destination : Destination Result)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (leftScale : LeftScale) (left : Left) (rightScale : RightScale) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  destination.project { rounding := mode, saturation }
    (operation (Arithmetic.Multiply (decode leftScale) (decode left))
      (Arithmetic.Multiply (decode rightScale) (decode right)))

/-- P3109 interim report v4.1 (unapproved), §5.8: add exact scaled operands, then project once. -/
@[inline] def ScaledAdd (destination : Destination Result)
    (leftScale : LeftScale) (left : Left) (rightScale : RightScale) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  scaledBinary destination Arithmetic.Add leftScale left rightScale right mode saturation

/-- P3109 interim report v4.1 (unapproved), §5.8: subtract exact scaled operands, then project
    once. -/
@[inline] def ScaledSubtract (destination : Destination Result)
    (leftScale : LeftScale) (left : Left) (rightScale : RightScale) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  scaledBinary destination Arithmetic.Subtract leftScale left rightScale right mode saturation

/-- P3109 interim report v4.1 (unapproved), §5.8: multiply exact scaled operands, then project
    once. -/
@[inline] def ScaledMultiply (destination : Destination Result)
    (leftScale : LeftScale) (left : Left) (rightScale : RightScale) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  scaledBinary destination Arithmetic.Multiply leftScale left rightScale right mode saturation

end Mixed
end FloatLib.Floats.Formats.P3109.Arithmetic
