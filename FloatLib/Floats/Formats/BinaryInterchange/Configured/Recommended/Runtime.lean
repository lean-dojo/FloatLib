/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Reduction.Runtime
public meta import FloatLib.Tactic.IeeeRecommended
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MagnitudeExtrema.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Payload.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Augmented.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Magnitude.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.ScaledProduct.Runtime

/-!
# Recommended operations of IEEE 754-2019 clause 9 for configured binary values

The operations of IEEE 754-2019 §9.4 to §9.7 that the descriptor model defines, on the
`ExecFloat.Binary` carrier of every format and storage plan:

* §9.6: `minimumMagnitude`, `maximumMagnitude`, `minimumMagnitudeNumber` and
  `maximumMagnitudeNumber`, the four instances of `magnitudeExtremum`;
* §9.7: `getPayload`, `setPayload` and `setPayloadSignaling`;
* §9.5: `augmentedAddition`, `augmentedSubtraction` and `augmentedMultiplication`;
* §9.4: `sumAbs`, `sumSquare`, `scaledProd`, `scaledProdSum` and `scaledProdDiff`.

They add no arithmetic. Each one decodes its operands, runs the model operation of
`Operations.MagnitudeExtrema`, `Operations.Payload`, `Operations.Augmented`,
`Reduction.Magnitude` or `Reduction.ScaledProduct`, where the special cases and the sources for
each clause are documented, and packs the result. `Configured.Recommended.Proof` states that
decoding a result gives the model operation on the decoded operands.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

/-! ## Minimum and maximum by magnitude (§9.6) -/

/--
A selection by magnitude on configured values: `Model.magnitudeExtremum larger base` through the
storage codec. With `status := true` the result also carries the `invalid` indicator of a
signaling NaN operand.
-/
@[macro_inline] def magnitudeExtremum (larger : Bool)
    (base : Model format → Model format → Model format) (left right : Value)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.magnitudeExtremum larger base (ExecFloat.Binary.toModel left)
          (ExecFloat.Binary.toModel right) (status := true)
  | false =>
      ModelCodec.liftBinary (Model := Model format) (plan := plan)
        (fun x y => Model.magnitudeExtremum larger base x y) left right


/--
IEEE 754-2019 §9.6 `minimumMagnitude` (C23 `fminimum_mag`, N3220 7.12.12.7): the operand of
smaller magnitude, and `minimum left right` when the magnitudes are equal or an operand is a NaN.
With `status := true` the result also carries the `invalid` indicator of a signaling NaN.
-/
magnitude_extremum minimumMagnitude := false, Model.minimum

/--
IEEE 754-2019 §9.6 `maximumMagnitude` (C23 `fmaximum_mag`, N3220 7.12.12.6): the operand of
larger magnitude, and `maximum left right` when the magnitudes are equal or an operand is a NaN.
With `status := true` the result also carries the `invalid` indicator of a signaling NaN.
-/
magnitude_extremum maximumMagnitude := true, Model.maximum

/--
IEEE 754-2019 §9.6 `minimumMagnitudeNumber` (C23 `fminimum_mag_num`, N3220 7.12.12.11): the
operand of smaller magnitude, and `minimumNumber left right` when the magnitudes are equal or an
operand is a NaN, so a number is preferred to a NaN. With `status := true` the result also
carries the `invalid` indicator of a signaling NaN.
-/
magnitude_extremum minimumMagnitudeNumber := false, Model.minimumNumber

/--
IEEE 754-2019 §9.6 `maximumMagnitudeNumber` (C23 `fmaximum_mag_num`, N3220 7.12.12.10): the
operand of larger magnitude, and `maximumNumber left right` when the magnitudes are equal or an
operand is a NaN, so a number is preferred to a NaN. With `status := true` the result also
carries the `invalid` indicator of a signaling NaN.
-/
magnitude_extremum maximumMagnitudeNumber := true, Model.maximumNumber

/-! ## NaN payloads (§9.7) -/

/--
IEEE 754-2019 §9.7 `getPayload` (C23 `getpayload`, N3220 F.10.13.2): the payload of a NaN as a
nonnegative integral value of the format, and `-1` for an operand that is not a NaN. No flag is
raised, also for a signaling NaN.
-/
@[inline] def getPayload (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) (fun x => Model.getPayload x) value

/--
IEEE 754-2019 §9.7 `setPayload` (C23 `setpayload`, N3220 F.10.13.3): the quiet NaN with the
payload that the operand names, and `+0` when the operand is not a nonnegative integral value
below the payload bound of the format.
-/
@[inline] def setPayload (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) (fun x => Model.setPayload x) value

/--
IEEE 754-2019 §9.7 `setPayloadSignaling` (C23 `setpayloadsig`, N3220 F.10.13.4): the signaling
NaN with the payload that the operand names, and `+0` when the operand names no payload of a
signaling NaN of the format.
-/
@[inline] def setPayloadSignaling (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan)
    (fun x => Model.setPayloadSignaling x) value

/-! ## Augmented arithmetic (§9.5) -/

/--
IEEE 754-2019 §9.5 `augmentedAddition`: the sum rounded to nearest with ties toward zero as the
head, and the error of that rounding as the tail, with the flags of the operation.
-/
@[inline] def augmentedAddition (left right : Value) : AugmentedOutcome Value :=
  (Model.augmentedAddition (ExecFloat.Binary.toModel left)
    (ExecFloat.Binary.toModel right)).map ExecFloat.Binary.ofModel

/-- IEEE 754-2019 §9.5 `augmentedSubtraction`: `augmentedAddition` of `left` and `-right`. -/
@[inline] def augmentedSubtraction (left right : Value) : AugmentedOutcome Value :=
  (Model.augmentedSubtraction (ExecFloat.Binary.toModel left)
    (ExecFloat.Binary.toModel right)).map ExecFloat.Binary.ofModel

/--
IEEE 754-2019 §9.5 `augmentedMultiplication`: the product rounded to nearest with ties toward
zero as the head, and the error of that rounding, rounded the same way, as the tail, with the
flags of the operation.
-/
@[inline] def augmentedMultiplication (left right : Value) : AugmentedOutcome Value :=
  (Model.augmentedMultiplication (ExecFloat.Binary.toModel left)
    (ExecFloat.Binary.toModel right)).map ExecFloat.Binary.ofModel

/-! ## Reductions (§9.4) -/


/--
IEEE 754-2019 §9.4 `sumAbs` (C `reduc_sumabs`, N1797 7.12.13a.2): the sum of the absolute values
of an array, formed without error and rounded once in `mode` (nearest-even by default). With
`status := true` the result also carries the flags and the ternary value of that rounding.
-/
magnitude_reduction sumAbs := Model.sumAbs

/--
IEEE 754-2019 §9.4 `sumSquare` (C `reduc_sumsq`, N1797 7.12.13a.3): the sum of the squares of an
array, formed without error and rounded once in `mode` (nearest-even by default). With
`status := true` the result also carries the flags and the ternary value of that rounding.
-/
magnitude_reduction sumSquare := Model.sumSquare

/--
IEEE 754-2019 §9.4 `scaledProd` (C `scaled_prod`, N1797 7.12.13a.5): a scaled product `pr` and a
scale factor `sf` with `pr × 2 ^ sf` the product of an array, formed without error and rounded
once in `mode` (nearest-even by default).
-/
@[inline] def scaledProd (values : Array Value) (mode : Model.IEEERoundingMode := .nearest) :
    ScaledProduct Value :=
  (Model.scaledProd format (values.map ExecFloat.Binary.toModel) mode).map
    ExecFloat.Binary.ofModel

/--
IEEE 754-2019 §9.4 `scaledProdSum` (C `scaled_prodsum`, N1797 7.12.13a.6): the scaled product of
the sums of the corresponding members of two arrays. Unequal lengths are an error.
-/
@[inline] def scaledProdSum (left right : Array Value)
    (mode : Model.IEEERoundingMode := .nearest) :
    Except Numerics.ReductionError (ScaledProduct Value) :=
  (Model.scaledProdSum format (left.map ExecFloat.Binary.toModel)
    (right.map ExecFloat.Binary.toModel) mode).map (ScaledProduct.map ExecFloat.Binary.ofModel)

/--
IEEE 754-2019 §9.4 `scaledProdDiff` (C `scaled_proddiff`, N1797 7.12.13a.7): the scaled product
of the differences of the corresponding members of two arrays. Unequal lengths are an error.
-/
@[inline] def scaledProdDiff (left right : Array Value)
    (mode : Model.IEEERoundingMode := .nearest) :
    Except Numerics.ReductionError (ScaledProduct Value) :=
  (Model.scaledProdDiff format (left.map ExecFloat.Binary.toModel)
    (right.map ExecFloat.Binary.toModel) mode).map (ScaledProduct.map ExecFloat.Binary.ofModel)

end FloatLib.Floats.ExecFloat.Binary
