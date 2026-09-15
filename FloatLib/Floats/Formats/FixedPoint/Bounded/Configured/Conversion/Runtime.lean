/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Core

/-!
# Bounded fixed-point conversion runtime

Bounded fixed point offers three overflow policies. `reject` returns `outOfRange`,
`wrap` reduces the rounded coefficient modulo `2 ^ width`, and `saturate` clamps it
to the signed range. `Conversion.Instances` installs checked conversion as the
context-free default.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat.BoundedFixedPoint
namespace Conversion

/-- Overflow policy for conversion into bounded fixed point. -/
inductive OverflowPolicy where
  /-- Reject a rounded coefficient outside the signed destination range. -/
  | reject
  /-- Reduce the rounded coefficient modulo `2 ^ width`. -/
  | wrap
  /-- Clamp the rounded coefficient to the signed destination range. -/
  | saturate
  deriving DecidableEq, Repr

variable {radix : Radix} {fractionalDigits width : Nat}

/-- Whether the ties-to-even rounded coefficient fits the signed destination width. -/
@[inline] def coefficientInRange (exact : Rat) : Bool :=
  decide <|
    FloatLib.Numerics.Representations.FixedInt.InRange width
      (Formats.FixedPoint.Bounded.coefficientOf radix fractionalDigits exact)

/-- Status for a delivered bounded fixed-point conversion. -/
@[inline] def finiteStatus (policy : OverflowPolicy) (exact : Rat)
    (rounded : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    FloatLib.Floats.ExecFloat.ConversionStatus :=
  let overflow := !coefficientInRange (radix := radix)
    (fractionalDigits := fractionalDigits) (width := width) exact
  { inexact := ExecFloat.BoundedFixedPoint.toRat rounded != exact
    overflow
    saturated := overflow && policy == .saturate
    wrapped := overflow && policy == .wrap }

/-- Quantize one finite rational according to the named bounded-overflow policy. -/
@[inline] def quantizeFinite (policy : OverflowPolicy) (exact : Rat) :
    FloatLib.Floats.ExecFloat.ConversionOutcome
      (ExecFloat.BoundedFixedPoint radix fractionalDigits width) :=
  match policy with
  | .reject =>
      match ExecFloat.BoundedFixedPoint.ofRat? exact with
      | some rounded => .success rounded (finiteStatus policy exact rounded)
      | none => .failure .outOfRange
  | .wrap =>
      let rounded : ExecFloat.BoundedFixedPoint radix fractionalDigits width :=
        ExecFloat.BoundedFixedPoint.ofRatWrapping exact
      .success rounded (finiteStatus policy exact rounded)
  | .saturate =>
      let rounded : ExecFloat.BoundedFixedPoint radix fractionalDigits width :=
        ExecFloat.BoundedFixedPoint.ofRatSaturating exact
      .success rounded (finiteStatus policy exact rounded)

/-- Convert a complete rational observation under an explicit bounded-overflow policy. -/
@[inline] def run (policy : OverflowPolicy) :
    NumericalValue Rat →
      FloatLib.Floats.ExecFloat.ConversionOutcome
        (ExecFloat.BoundedFixedPoint radix fractionalDigits width)
  | .finite exact => quantizeFinite policy exact
  | .infinity negative => .failure (.infinity .source negative)
  | .exceptional exceptional => .failure (.exceptional .source exceptional)

/--
The signed output coefficient after nearest-even rounding and the selected overflow policy.

The wrapping relation uses centered integer reduction, and saturation uses the signed range
endpoints. Neither clause refers to a fixed-width encoding kernel.
-/
def coefficientSpec (policy : OverflowPolicy) (exact : Rat) (stored : Int) : Prop :=
  let nearest := roundRatEven (exact * Formats.FixedPoint.scale radix fractionalDigits)
  match policy with
  | .reject =>
      Representations.FixedInt.InRange width nearest ∧ stored = nearest
  | .wrap => stored = nearest.bmod (2 ^ width)
  | .saturate => stored = Representations.FixedInt.clamp width nearest

/--
Conversion relates the delivered coefficient to integer rounding, range, wrap, and clamp.

The status is retained in full. Rejection of a finite input occurs exactly when the nearest-even
coefficient is out of range under `reject`; the other policies always deliver a value.
-/
def spec :
    Quantization.Spec OverflowPolicy (NumericalValue Rat)
      (FloatLib.Floats.ExecFloat.ConversionOutcome
        (ExecFloat.BoundedFixedPoint radix fractionalDigits width)) :=
  fun policy input outcome =>
    match input, outcome with
    | .finite exact, .success rounded indicators =>
        coefficientSpec (radix := radix) (fractionalDigits := fractionalDigits) (width := width)
            policy exact (coefficient rounded) ∧
          indicators = finiteStatus policy exact rounded
    | .finite exact, .failure reason =>
        policy = .reject ∧
          ¬Representations.FixedInt.InRange width
            (roundRatEven (exact * Formats.FixedPoint.scale radix fractionalDigits)) ∧
          reason = .outOfRange
    | .infinity negative, .failure reason =>
        reason = .infinity .source negative
    | .exceptional exceptional, .failure reason =>
        reason = .exceptional .source exceptional
    | _, _ => False

/-- Bounded fixed-point values decode canonically to their exact stored rational. -/
instance exactDecoder :
    FloatLib.Floats.ExecFloat.ExactDecoder
      (ExecFloat.BoundedFixedPoint radix fractionalDigits width) Rat where
  decode value := .finite (ExecFloat.BoundedFixedPoint.toRat value)

end Conversion
end ExecFloat.BoundedFixedPoint
end FloatLib.Floats
