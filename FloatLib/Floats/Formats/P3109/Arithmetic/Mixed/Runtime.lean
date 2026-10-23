/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Runtime
public import FloatLib.Floats.Formats.P3109.Conversion.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Runtime

/-!
# Mixed-format P3109 arithmetic

The source types select exact decoders and finite values are embedded into `Rat`, so a configured
IEEE accumulator, a P3109 operand, and an exact rational can occur in one expression. IEEE negative
zero loses its sign in this domain, as required by §4.8.1. Every exceptional observation becomes
the report's one NaN.

`Destination` supplies the final report projection. `Destination.p3109` selects any P3109
descriptor. External destinations live in `Arithmetic.External`, so importing this module
installs no alternative IEEE arithmetic or conversion instances. The operation always evaluates
the whole closed expression before projecting, including fused add-add and scaled arithmetic.

Reference: P3109 unapproved interim report 4.0.3, revision `34f5964`, §§4.5, 4.8–4.10 and 5.8.
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

/-- A P3109 result format with its complete report projection policy. -/
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
-/
@[inline] def convert (destination : Destination Result) (value : Source)
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

/-- Mixed reciprocal, with zero mapped to NaN before projection. -/
@[inline] def recip (destination : Destination Result) (value : Source)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  unary destination Arithmetic.recip value mode saturation

/-- Mixed addition, retaining closed-domain infinities and NaN. -/
@[inline] def add (destination : Destination Result) (left : Left) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  binary destination Arithmetic.add left right mode saturation

/-- Mixed subtraction with no intermediate rounding. -/
@[inline] def sub (destination : Destination Result) (left : Left) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  binary destination Arithmetic.sub left right mode saturation

/-- Mixed multiplication with no intermediate rounding. -/
@[inline] def mul (destination : Destination Result) (left : Left) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  binary destination Arithmetic.mul left right mode saturation

/-- Mixed division with the report's zero-denominator rule. -/
@[inline] def div (destination : Destination Result) (left : Left) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  binary destination Arithmetic.div left right mode saturation

/-- Mixed fused multiply-add, including an independently typed accumulator. -/
@[inline] def fma (destination : Destination Result) (left : Left) (right : Right)
    (addend : Third) (mode : RoundingMode := .nearest)
    (saturation : SaturationMode := .none) : Result :=
  ternary destination Arithmetic.fma left right addend mode saturation

/-- Mixed fused add-add, with neither addition rounded before the result projection. -/
@[inline] def faa (destination : Destination Result) (left : Left) (middle : Right)
    (right : Third) (mode : RoundingMode := .nearest)
    (saturation : SaturationMode := .none) : Result :=
  ternary destination Arithmetic.faa left middle right mode saturation

variable {LeftScale LeftScaleExact RightScale RightScaleExact : Type}
variable [ExactDecoder LeftScale LeftScaleExact] [ExactMap LeftScaleExact Rat]
variable [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]

/--
Scaled binary operation from §5.8, with an implicit exact result scale of one.

Input scaling is closed multiplication: a zero scale times infinity is NaN, and a NaN scale
propagates even when its element is zero. The complete scaled expression is projected once.
-/
@[inline] def scaledBinary (destination : Destination Result)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (leftScale : LeftScale) (left : Left) (rightScale : RightScale) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  destination.project { rounding := mode, saturation }
    (operation (Arithmetic.mul (decode leftScale) (decode left))
      (Arithmetic.mul (decode rightScale) (decode right)))

/-- Add two exactly scaled operands and project once. -/
@[inline] def scaledAdd (destination : Destination Result)
    (leftScale : LeftScale) (left : Left) (rightScale : RightScale) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  scaledBinary destination Arithmetic.add leftScale left rightScale right mode saturation

/-- Subtract two exactly scaled operands and project once. -/
@[inline] def scaledSub (destination : Destination Result)
    (leftScale : LeftScale) (left : Left) (rightScale : RightScale) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  scaledBinary destination Arithmetic.sub leftScale left rightScale right mode saturation

/-- Multiply two exactly scaled operands and project once. -/
@[inline] def scaledMul (destination : Destination Result)
    (leftScale : LeftScale) (left : Left) (rightScale : RightScale) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  scaledBinary destination Arithmetic.mul leftScale left rightScale right mode saturation

end Mixed
end FloatLib.Floats.Formats.P3109.Arithmetic
