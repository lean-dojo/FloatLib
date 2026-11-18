/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Recommended.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Reduction.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MagnitudeExtrema.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Payload.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Augmented.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Magnitude.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.ScaledProduct.Proof

/-!
# Packing correctness of the recommended operations on configured values

Decoding the result of a configured operation of `Configured.Recommended.Runtime` gives the
descriptor-model operation on the decoded operands, for every format and storage plan:

* `toModel_magnitudeExtremum`, `IEEEOutcome.toModel_magnitudeExtremum` and
  `value_magnitudeExtremum` for the selections by magnitude. `minimumMagnitude`,
  `maximumMagnitude`, `minimumMagnitudeNumber` and `maximumMagnitudeNumber` unfold to
  `magnitudeExtremum`, so these three theorems cover all four.
* `toModel_getPayload`, `toModel_setPayload`, `toModel_setPayloadSignaling`.
* `map_toModel_augmentedAddition`, `map_toModel_augmentedSubtraction`,
  `map_toModel_augmentedMultiplication`: head, tail and flags.
* `toModel_sumAbs`, `toModel_sumSquare` and their `IEEEOutcome` forms, `map_toModel_scaledProd`,
  `map_toModel_scaledProdSum`, `map_toModel_scaledProdDiff`.

The contracts of the model operations carry over through these equations.
`toReal_augmentedAddition_add` does it for the error-free transformation of §9.5: with a finite
head, head and tail of a configured `augmentedAddition` add up to the exact sum.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-! ## Minimum and maximum by magnitude -/

/-- Decoding a configured selection by magnitude gives the selection of the model. -/
@[simp, grind =] theorem toModel_magnitudeExtremum (larger : Bool)
    (base : Model format → Model format → Model format) (left right : Value) :
    toModel (magnitudeExtremum larger base left right) =
      Model.magnitudeExtremum larger base (toModel left) (toModel right) := by
  simp [magnitudeExtremum, toModel, Configured.Family.toModel]

/-- A configured selection by magnitude with `status := true` keeps the model value and flags. -/
@[simp, grind =] theorem IEEEOutcome.toModel_magnitudeExtremum (larger : Bool)
    (base : Model format → Model format → Model format) (left right : Value) :
    IEEEOutcome.toModel (magnitudeExtremum larger base left right (status := true)) =
      Model.magnitudeExtremum larger base (ExecFloat.Binary.toModel left)
        (ExecFloat.Binary.toModel right) (status := true) := by
  simp [magnitudeExtremum]

/-- A configured selection by magnitude with `status := true` delivers the value without it. -/
@[simp] theorem value_magnitudeExtremum (larger : Bool)
    (base : Model format → Model format → Model format) (left right : Value) :
    (magnitudeExtremum larger base left right (status := true)).value =
      magnitudeExtremum larger base left right := by
  rw [← ofModel_toModel (magnitudeExtremum larger base left right), toModel_magnitudeExtremum,
    ← Model.value_magnitudeExtremum]
  rfl

/-! ## NaN payloads -/

/-- Decoding configured `getPayload` gives `getPayload` of the model. -/
@[simp, grind =] theorem toModel_getPayload (value : Value) :
    toModel (getPayload value) = Model.getPayload (toModel value) := by
  simp [getPayload, toModel, Configured.Family.toModel]

/-- Decoding configured `setPayload` gives `setPayload` of the model. -/
@[simp, grind =] theorem toModel_setPayload (value : Value) :
    toModel (setPayload value) = Model.setPayload (toModel value) := by
  simp [setPayload, toModel, Configured.Family.toModel]

/-- Decoding configured `setPayloadSignaling` gives `setPayloadSignaling` of the model. -/
@[simp, grind =] theorem toModel_setPayloadSignaling (value : Value) :
    toModel (setPayloadSignaling value) = Model.setPayloadSignaling (toModel value) := by
  simp [setPayloadSignaling, toModel, Configured.Family.toModel]

/-! ## Augmented arithmetic -/

/-- Packing and decoding head and tail of an augmented result is the identity. -/
private theorem map_toModel_map_ofModel
    (outcome : AugmentedOutcome (Model format)) :
    (outcome.map (ExecFloat.Binary.ofModel (plan := plan) (code := code))).map
      ExecFloat.Binary.toModel = outcome := by
  cases outcome
  simp [AugmentedOutcome.map]

/-- Decoding configured `augmentedAddition` gives head, tail and flags of the model. -/
@[simp] theorem map_toModel_augmentedAddition (left right : Value) :
    (augmentedAddition left right).map ExecFloat.Binary.toModel =
      Model.augmentedAddition (toModel left) (toModel right) :=
  map_toModel_map_ofModel _

/-- Decoding configured `augmentedSubtraction` gives head, tail and flags of the model. -/
@[simp] theorem map_toModel_augmentedSubtraction (left right : Value) :
    (augmentedSubtraction left right).map ExecFloat.Binary.toModel =
      Model.augmentedSubtraction (toModel left) (toModel right) :=
  map_toModel_map_ofModel _

/-- Decoding configured `augmentedMultiplication` gives head, tail and flags of the model. -/
@[simp] theorem map_toModel_augmentedMultiplication (left right : Value) :
    (augmentedMultiplication left right).map ExecFloat.Binary.toModel =
      Model.augmentedMultiplication (toModel left) (toModel right) :=
  map_toModel_map_ofModel _

/--
The error-free transformation of IEEE 754-2019 §9.5 on configured values of a conventional IEEE
format: when the head of `augmentedAddition` is finite, head and tail add up to the exact sum
of the operands.
-/
theorem toReal_augmentedAddition_add (hfmt : format.isIEEE = true) (left right : Value)
    (hfinite : isFinite (augmentedAddition left right).head = true) :
    toReal (augmentedAddition left right).head + toReal (augmentedAddition left right).tail =
      toReal left + toReal right := by
  have hhead : Model.isFinite (Model.augmentedAddition (toModel left) (toModel right)).head =
      true := by
    simpa [augmentedAddition, AugmentedOutcome.map, isFinite] using hfinite
  simpa [augmentedAddition, AugmentedOutcome.map, toReal] using
    (Model.toReal_augmentedAddition_add hfmt (toModel left) (toModel right) hhead).1

/-! ## Reductions -/

/-- Decoding the value-only configured `sumAbs` gives `sumAbs` of the model. -/
@[simp, grind =] theorem toModel_sumAbs (values : Array Value) (mode : Model.IEEERoundingMode) :
    ExecFloat.Binary.toModel (sumAbs values mode) =
      Model.sumAbs format (values.map ExecFloat.Binary.toModel) mode :=
  ExecFloat.Binary.toModel_ofModel _

/-- Decoding configured `sumAbs` with `status := true` gives the model outcome, flags included. -/
theorem IEEEOutcome.toModel_sumAbs (values : Array Value) (mode : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (sumAbs values mode (status := true)) =
      Model.sumAbs format (values.map ExecFloat.Binary.toModel) mode (status := true) :=
  IEEEOutcome.toModel_ofModel (plan := plan) (code := code) _

/-- Decoding the value-only configured `sumSquare` gives `sumSquare` of the model. -/
@[simp, grind =] theorem toModel_sumSquare (values : Array Value)
    (mode : Model.IEEERoundingMode) :
    ExecFloat.Binary.toModel (sumSquare values mode) =
      Model.sumSquare format (values.map ExecFloat.Binary.toModel) mode :=
  ExecFloat.Binary.toModel_ofModel _

/-- Decoding configured `sumSquare` with `status := true` gives the model outcome, flags
included. -/
theorem IEEEOutcome.toModel_sumSquare (values : Array Value) (mode : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (sumSquare values mode (status := true)) =
      Model.sumSquare format (values.map ExecFloat.Binary.toModel) mode (status := true) :=
  IEEEOutcome.toModel_ofModel (plan := plan) (code := code) _

/-- Packing and decoding a scaled product is the identity. -/
private theorem scaledProduct_map_toModel_map_ofModel
    (outcome : ScaledProduct (Model format)) :
    (outcome.map (ExecFloat.Binary.ofModel (plan := plan) (code := code))).map
      ExecFloat.Binary.toModel = outcome := by
  cases outcome
  simp [ScaledProduct.map]

/-- Decoding configured `scaledProd` gives product, scale factor and flags of the model. -/
@[simp] theorem map_toModel_scaledProd (values : Array Value) (mode : Model.IEEERoundingMode) :
    (scaledProd values mode).map ExecFloat.Binary.toModel =
      Model.scaledProd format (values.map ExecFloat.Binary.toModel) mode :=
  scaledProduct_map_toModel_map_ofModel _

/-- Decoding configured `scaledProdSum` gives the model result, a length error included. -/
@[simp] theorem map_toModel_scaledProdSum (left right : Array Value)
    (mode : Model.IEEERoundingMode) :
    (scaledProdSum left right mode).map (ScaledProduct.map ExecFloat.Binary.toModel) =
      Model.scaledProdSum format (left.map ExecFloat.Binary.toModel)
        (right.map ExecFloat.Binary.toModel) mode := by
  unfold scaledProdSum
  cases Model.scaledProdSum format (left.map ExecFloat.Binary.toModel)
      (right.map ExecFloat.Binary.toModel) mode with
  | error e => rfl
  | ok outcome => exact congrArg Except.ok (scaledProduct_map_toModel_map_ofModel outcome)

/-- Decoding configured `scaledProdDiff` gives the model result, a length error included. -/
@[simp] theorem map_toModel_scaledProdDiff (left right : Array Value)
    (mode : Model.IEEERoundingMode) :
    (scaledProdDiff left right mode).map (ScaledProduct.map ExecFloat.Binary.toModel) =
      Model.scaledProdDiff format (left.map ExecFloat.Binary.toModel)
        (right.map ExecFloat.Binary.toModel) mode := by
  unfold scaledProdDiff
  cases Model.scaledProdDiff format (left.map ExecFloat.Binary.toModel)
      (right.map ExecFloat.Binary.toModel) mode with
  | error e => rfl
  | ok outcome => exact congrArg Except.ok (scaledProduct_map_toModel_map_ofModel outcome)

end FloatLib.Floats.ExecFloat.Binary
