/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Rational.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Core

/-!
# Conversion into P3109 formats

P3109 destinations use `Rat` as their canonical exact scalar domain. This lets integers, exact
dyadics, configured binary floats, configured posits, and other rationally decoded sources use the
ordinary `convert`, `cast`, and destination-driven mixed-operation APIs without first passing
through a host float.

The conversion context is exactly `ProjectionPolicy`: the P3109 rounding mode and saturation mode
are not duplicated in a second policy type. Every policy produces a P3109 datum, so conversion
returns success for finite, infinite, and exceptional observations. Changes to an input
infinity or exceptional observation are reported through `mappedSpecial`; endpoint clamping
is reported through `saturated`.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats
namespace ExecFloat.P3109
namespace Conversion

variable {format : Formats.P3109.Format}

/-- Decode a P3109 value in the common exact-rational scalar domain. -/
@[inline] def decodeRat (value : ExecFloat.P3109 format) :
    NumericalValue Rat :=
  (ExecFloat.P3109.decode value).map Numerics.Dyadic.toRat

/--
Whether an exact rational lies strictly outside the closed interval `[minFinite, maxFinite]`.

This is a property of the exact input alone. It is not the overflow indicator: an input slightly
above `maxFinite` that rounds back to `maxFinite` satisfies this predicate but does not overflow.
-/
@[inline] def exceedsFiniteRange
    (format : Formats.P3109.Format) (exact : Rat) : Bool :=
  let below :=
    Numerics.RationalBinary.compareDyadic?
      (exact.num < 0) exact.num.natAbs exact.den format.minFinite
  let above :=
    Numerics.RationalBinary.compareDyadic?
      (exact.num < 0) exact.num.natAbs exact.den format.maxFinite
  below == some .lt || above == some .gt

/--
Whether the precision-rounded value of an exact rational lies strictly outside
`[minFinite, maxFinite]`.

Rounding is `roundFiniteRatToPrecision` in the requested mode, before any saturation. This is the
after-rounding range condition of P3109 §4.7.3: an input that rounds to `maxFinite` is
in range even when its exact magnitude exceeds `maxFinite`. Because the endpoints lie on the
precision grid, no rounding mode moves an in-range input past them, so this condition is stronger
than `exceedsFiniteRange`. The theorem
`roundedExceedsFiniteRange_implies_exceedsFiniteRange` in `Conversion.Range` proves this
implication for every mode and every supplied stochastic word.
-/
@[inline] def roundedExceedsFiniteRange
    (format : Formats.P3109.Format) (mode : Formats.P3109.RoundingMode)
    (exact : Rat) : Bool :=
  let rounded := format.roundFiniteRatToPrecision mode exact
  Numerics.Dyadic.Internal.compareScalable rounded format.minFinite == .lt ||
    Numerics.Dyadic.Internal.compareScalable format.maxFinite rounded == .lt

/--
Whether a nonzero exact magnitude is strictly smaller than the least positive finite P3109 datum.

The comparison is sign-independent and scales by binary position before cross multiplication, so
large exponent ranges do not create an enormous temporary rational. This threshold is the least
positive datum (the smallest subnormal when the descriptor has subnormals), not the least normal
datum used by IEEE 754 tininess.
-/
@[inline] def belowMinPositive
    (format : Formats.P3109.Format) (exact : Rat) : Bool :=
  exact != 0 &&
    Numerics.RationalBinary.compareDyadic?
        false exact.num.natAbs exact.den (format.decodePositiveFinite 1) ==
      some .lt

/-- Whether a projected datum is one of the descriptor's finite endpoints. -/
@[inline] def isFiniteEndpoint
    (format : Formats.P3109.Format) :
    NumericalValue Numerics.Dyadic → Bool
  | .finite value =>
      Numerics.Dyadic.Internal.compareScalable value format.minFinite == .eq ||
        Numerics.Dyadic.Internal.compareScalable value format.maxFinite == .eq
  | .infinity _ | .exceptional _ => false

/-- Whether projection deliberately changed a source special-value class or infinity sign. -/
@[inline] def mappedSpecial :
    NumericalValue Rat → NumericalValue Numerics.Dyadic → Bool
  | .finite _, _ => false
  | .infinity sourceSign, .infinity resultSign => sourceSign != resultSign
  | .exceptional (.nan ..), .exceptional (.nan ..) => false
  | .infinity _, _ | .exceptional _, _ => true

/-- Whether projection changes the exact rational input or produces a nonfinite datum. -/
@[inline] def finiteInexact
    (exact : Rat) : NumericalValue Numerics.Dyadic → Bool
  | .finite value => value.toRat != exact
  | .infinity _ | .exceptional _ => true

/--
Conversion indicators for one completed P3109 projection.

The report defines no status flags, so these are FloatLib's conversion indicators:

* `overflow` is `roundedExceedsFiniteRange`: the value rounded to the descriptor's precision in the
  requested mode lies outside `[minFinite, maxFinite]`. It does not depend on the saturation mode,
  and an input that rounds to an endpoint does not overflow (Section 4.7.3, NOTE 1).
* `underflow` is `belowMinPositive`: a nonzero exact input strictly smaller in magnitude than the
  least positive datum. A subnormal-range input that is at least the least positive datum does not
  raise it, so this is narrower than IEEE 754 tininess.
* `saturated` is raised only when saturation changed the rounding result and the delivered datum
  is a finite endpoint.
* `invalid` is raised for a signaling NaN source, as for binary destinations.
-/
@[inline] def status
    (format : Formats.P3109.Format)
    (policy : Formats.P3109.ProjectionPolicy)
    (input : NumericalValue Rat) :
    FloatLib.Floats.ExecFloat.ConversionStatus :=
  let rounded := format.roundRatToPrecision policy.rounding input
  let projected := format.projectRatValue policy input
  match input with
  | .finite exact =>
      {
        inexact := finiteInexact exact projected
        overflow := roundedExceedsFiniteRange format policy.rounding exact
        underflow := belowMinPositive format exact
        saturated :=
          !Formats.P3109.Format.datumEqual rounded projected &&
            isFiniteEndpoint format projected
      }
  | .infinity _ =>
      {
        saturated := isFiniteEndpoint format projected
        mappedSpecial := mappedSpecial input projected
      }
  | .exceptional exceptional =>
      {
        saturated := isFiniteEndpoint format projected
        mappedSpecial := mappedSpecial input projected
        invalid := exceptional.isSignalingNaN
      }

/-- Quantize one complete exact-rational observation according to its P3109 projection policy. -/
@[inline] def run
    (policy : Formats.P3109.ProjectionPolicy)
    (input : NumericalValue Rat) :
    FloatLib.Floats.ExecFloat.ConversionOutcome
      (ExecFloat.P3109 format) :=
  .success (ExecFloat.P3109.projectRat policy input)
    (status format policy input)

/--
Conversion preserves the selected word and status and denotes the round-then-saturate datum.

`SameDatum` compares finite values numerically and identifies NaN payloads. The word equality is
retained separately so that this semantic clause does not discard complete output information.
-/
def spec :
    Quantization.Spec Formats.P3109.ProjectionPolicy
      (NumericalValue Rat)
      (FloatLib.Floats.ExecFloat.ConversionOutcome
        (ExecFloat.P3109 format)) :=
  fun policy input outcome =>
    match outcome with
    | .success value indicators =>
        value = ExecFloat.P3109.projectRat policy input ∧
          indicators = status format policy input ∧
          Formats.P3109.Format.SameDatum
            (ExecFloat.P3109.decode value) (format.projectRatValue policy input)
    | .failure _ => False

/--
P3109 decoding selects the common exact-rational scalar domain.

The elevated priority refines the carrier's generic codebook decoder, whose finite domain is
`Dyadic`. Importing the generic codebook API together with P3109 therefore still leaves one
canonical source domain for ordinary scalar conversion.
-/
instance (priority := 2000) exactDecoder :
    FloatLib.Floats.ExecFloat.ExactDecoder
      (ExecFloat.P3109 format) Rat where
  decode := decodeRat

end Conversion
end ExecFloat.P3109
end FloatLib.Floats
