/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Operations.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof

/-!
# Packing correctness for configured standard operations

Every decoding theorem states that decoding a configured result recovers the single
descriptor-model operation used to compute it. Results with `status := true` keep all five
indicators, and the projection theorems `value_remainder` through `value_maximumNumber` state
that their value is the configured operation without status.

We prove the arithmetic properties for the descriptor-model operations. These theorems transport
those results through the storage codec, giving the same equations for values and exception flags
with every storage plan.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- Decoding configured IEEE remainder gives the descriptor-model remainder. -/
@[simp, grind =] theorem toModel_remainder (dividend divisor : Value) :
    toModel (remainder dividend divisor) =
      Model.remainder (toModel dividend) (toModel divisor) := by
  simp [remainder, toModel, Configured.Family.toModel]

/-- Decoding configured remainder preserves its value, status indicators, and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_remainder
    (dividend divisor : Value) :
    IEEEOutcome.toModel (remainder dividend divisor (status := true)) =
      Model.remainder
        (ExecFloat.Binary.toModel dividend)
        (ExecFloat.Binary.toModel divisor) (status := true) := by
  simp [remainder]

/-- Decoding configured integral rounding gives integral rounding in the descriptor model. -/
@[simp, grind =] theorem toModel_roundToIntegral
    (value : Value) (mode : Model.IEEERoundingMode) :
    toModel (roundToIntegral value mode) =
      Model.roundToIntegral (toModel value) mode := by
  simp [roundToIntegral, toModel, Configured.Family.toModel]

/-- Configured integral rounding preserves the model value, status, and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_roundToIntegral
    (value : Value) (mode : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (roundToIntegral value mode (status := true)) =
      Model.roundToIntegral (ExecFloat.Binary.toModel value) mode (status := true) := by
  simp [roundToIntegral]

/-- Decoding configured power-of-two scaling gives descriptor-model scaling. -/
@[simp, grind =] theorem toModel_scale
    (value : Value) (n : Int) (mode : Model.IEEERoundingMode) :
    toModel (scale value n mode) =
      Model.scale (toModel value) n mode := by
  simp [scale, toModel, Configured.Family.toModel]

/-- Configured power-of-two scaling preserves the model value, status, and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_scale
    (value : Value) (n : Int) (mode : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (scale value n mode (status := true)) =
      Model.scale (ExecFloat.Binary.toModel value) n mode (status := true) := by
  simp [scale]

/-- The integer exponent query is the descriptor-model query on the decoded value. -/
@[simp, grind =] theorem binaryExponentInt_eq (value : Value) :
    binaryExponentInt value = Model.binaryExponentInt (toModel value) :=
  rfl

/-- Decoding configured `binaryExponent` gives the descriptor-model leading binary exponent. -/
@[simp, grind =] theorem toModel_binaryExponent (value : Value) :
    toModel (binaryExponent value) = Model.binaryExponent (toModel value) := by
  simp [binaryExponent, toModel, Configured.Family.toModel]

/-- Configured `binaryExponent` preserves the model value, status, and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_binaryExponent (value : Value) :
    IEEEOutcome.toModel (binaryExponent value (status := true)) =
      Model.binaryExponent (ExecFloat.Binary.toModel value) (status := true) := by
  simp [binaryExponent]

/-- Decoding configured sign copying gives descriptor-model sign copying. -/
@[simp, grind =] theorem toModel_copySign (magnitude signSource : Value) :
    toModel (copySign magnitude signSource) =
      Model.copySign (toModel magnitude) (toModel signSource) := by
  simp [copySign, toModel, Configured.Family.toModel]

/-- Decoding configured absolute value gives descriptor-model absolute value. -/
@[simp, grind =] theorem toModel_abs (value : Value) :
    toModel (abs value) = Model.abs (toModel value) := by
  simp [abs, toModel, Configured.Family.toModel]

/-- Absolute value keeps finiteness. -/
theorem isFinite_abs_of_isFinite {value : Value} (hvalue : isFinite value = true) :
    isFinite (abs value) = true := by
  unfold isFinite
  rw [toModel_abs, Model.isFinite_abs]
  exact hvalue

/-- Decoding the configured upward neighbor gives the descriptor-model upward neighbor. -/
@[simp, grind =] theorem toModel_nextUp (value : Value) :
    toModel (nextUp value) = Model.nextUp (toModel value) := by
  simp [nextUp, toModel, Configured.Family.toModel]

/-- The configured upward neighbor preserves the model value, status, and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_nextUp (value : Value) :
    IEEEOutcome.toModel (nextUp value (status := true)) =
      Model.nextUp (ExecFloat.Binary.toModel value) (status := true) := by
  simp [nextUp]

/-- Decoding the configured downward neighbor gives the descriptor-model downward neighbor. -/
@[simp, grind =] theorem toModel_nextDown (value : Value) :
    toModel (nextDown value) = Model.nextDown (toModel value) := by
  simp [nextDown, toModel, Configured.Family.toModel]

/-- The configured downward neighbor preserves the model value, status, and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_nextDown (value : Value) :
    IEEEOutcome.toModel (nextDown value (status := true)) =
      Model.nextDown (ExecFloat.Binary.toModel value) (status := true) := by
  simp [nextDown]

/-- Decoding configured IEEE `minimum` gives descriptor-model IEEE `minimum`. -/
@[simp, grind =] theorem toModel_minimum (left right : Value) :
    toModel (minimum left right) = Model.minimum (toModel left) (toModel right) := by
  simp [minimum, toModel, Configured.Family.toModel]

/-- Configured `minimum` with `status := true` keeps the model value, status, and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_minimum (left right : Value) :
    IEEEOutcome.toModel (minimum left right (status := true)) =
      Model.minimum (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
        (status := true) := by
  simp [minimum]

/-- Decoding configured IEEE `maximum` gives descriptor-model IEEE `maximum`. -/
@[simp, grind =] theorem toModel_maximum (left right : Value) :
    toModel (maximum left right) = Model.maximum (toModel left) (toModel right) := by
  simp [maximum, toModel, Configured.Family.toModel]

/-- Configured `maximum` with `status := true` keeps the model value, status, and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_maximum (left right : Value) :
    IEEEOutcome.toModel (maximum left right (status := true)) =
      Model.maximum (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
        (status := true) := by
  simp [maximum]

/-- Decoding configured `minimumNumber` gives descriptor-model `minimumNumber`. -/
@[simp, grind =] theorem toModel_minimumNumber (left right : Value) :
    toModel (minimumNumber left right) = Model.minimumNumber (toModel left) (toModel right) := by
  simp [minimumNumber, toModel, Configured.Family.toModel]

/-- Configured `minimumNumber` with `status := true` keeps the model value, status, and ternary. -/
@[simp, grind =] theorem IEEEOutcome.toModel_minimumNumber (left right : Value) :
    IEEEOutcome.toModel (minimumNumber left right (status := true)) =
      Model.minimumNumber (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
        (status := true) := by
  simp [minimumNumber]

/-- Decoding configured `maximumNumber` gives descriptor-model `maximumNumber`. -/
@[simp, grind =] theorem toModel_maximumNumber (left right : Value) :
    toModel (maximumNumber left right) = Model.maximumNumber (toModel left) (toModel right) := by
  simp [maximumNumber, toModel, Configured.Family.toModel]

/-- Configured `maximumNumber` with `status := true` keeps the model value, status, and ternary. -/
@[simp, grind =] theorem IEEEOutcome.toModel_maximumNumber (left right : Value) :
    IEEEOutcome.toModel (maximumNumber left right (status := true)) =
      Model.maximumNumber (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
        (status := true) := by
  simp [maximumNumber]

/-- `min` runs configured IEEE `minimum`. -/
theorem min_eq_minimum (left right : Value) : min left right = minimum left right := rfl

/-- `max` runs configured IEEE `maximum`. -/
theorem max_eq_maximum (left right : Value) : max left right = maximum left right := rfl

/-- Configured remainder with `status := true` delivers the value of configured remainder. -/
@[simp] theorem value_remainder (dividend divisor : Value) :
    (remainder dividend divisor (status := true)).value = remainder dividend divisor := by
  rw [← ofModel_toModel (remainder dividend divisor), toModel_remainder,
    ← Model.value_remainder]
  rfl

/--
Configured integral rounding with `status := true` delivers the value of configured integral
rounding.
-/
@[simp] theorem value_roundToIntegral (value : Value) (mode : Model.IEEERoundingMode) :
    (roundToIntegral value mode (status := true)).value = roundToIntegral value mode := by
  rw [← ofModel_toModel (roundToIntegral value mode), toModel_roundToIntegral,
    ← Model.value_roundToIntegral]
  rfl

/-- Configured scaling with `status := true` delivers the value of configured scaling. -/
@[simp] theorem value_scale (value : Value) (n : Int) (mode : Model.IEEERoundingMode) :
    (scale value n mode (status := true)).value = scale value n mode := by
  rw [← ofModel_toModel (scale value n mode), toModel_scale, ← Model.value_scale]
  rfl

/--
Configured `binaryExponent` with `status := true` delivers the value of configured
`binaryExponent`.
-/
@[simp] theorem value_binaryExponent (value : Value) :
    (binaryExponent value (status := true)).value = binaryExponent value := by
  rw [← ofModel_toModel (binaryExponent value), toModel_binaryExponent,
    ← Model.value_binaryExponent]
  rfl

/-- The configured upward neighbor with `status := true` delivers the upward neighbor. -/
@[simp] theorem value_nextUp (value : Value) :
    (nextUp value (status := true)).value = nextUp value := by
  rw [← ofModel_toModel (nextUp value), toModel_nextUp, ← Model.value_nextUp]
  rfl

/-- The configured downward neighbor with `status := true` delivers the downward neighbor. -/
@[simp] theorem value_nextDown (value : Value) :
    (nextDown value (status := true)).value = nextDown value := by
  rw [← ofModel_toModel (nextDown value), toModel_nextDown, ← Model.value_nextDown]
  rfl

/-- Configured `minimum` with `status := true` delivers the value of configured `minimum`. -/
@[simp] theorem value_minimum (left right : Value) :
    (minimum left right (status := true)).value = minimum left right := by
  rw [← ofModel_toModel (minimum left right), toModel_minimum, ← Model.value_minimum]
  rfl

/-- Configured `maximum` with `status := true` delivers the value of configured `maximum`. -/
@[simp] theorem value_maximum (left right : Value) :
    (maximum left right (status := true)).value = maximum left right := by
  rw [← ofModel_toModel (maximum left right), toModel_maximum, ← Model.value_maximum]
  rfl

/-- Configured `minimumNumber` with `status := true` delivers the value of `minimumNumber`. -/
@[simp] theorem value_minimumNumber (left right : Value) :
    (minimumNumber left right (status := true)).value = minimumNumber left right := by
  rw [← ofModel_toModel (minimumNumber left right), toModel_minimumNumber,
    ← Model.value_minimumNumber]
  rfl

/-- Configured `maximumNumber` with `status := true` delivers the value of `maximumNumber`. -/
@[simp] theorem value_maximumNumber (left right : Value) :
    (maximumNumber left right (status := true)).value = maximumNumber left right := by
  rw [← ofModel_toModel (maximumNumber left right), toModel_maximumNumber,
    ← Model.value_maximumNumber]
  rfl

/-- The integer value is absent if and only if the value is not finite. -/
@[simp] theorem toInt?_eq_none_iff (value : Value) (mode : Model.IEEERoundingMode) :
    toInt? value mode = none ↔ isFinite value = false := by
  have hdecode := Model.toDyadic?_isSome_eq_isFinite (toModel value)
  unfold toInt? isFinite
  cases hd : Model.toDyadic? (toModel value) <;> simp_all

/-- Integral rounding of a finite value is finite when the exponent range reaches the precision,
as it does for the IEEE interchange formats. -/
theorem isFinite_roundToIntegral {value : Value} {mode : Model.IEEERoundingMode}
    (hrange : (format.fracWidth : Int) ≤ format.maxNormalExponent) (hvalue : isFinite value = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (roundToIntegral value mode) = true := by
  unfold isFinite
  rw [toModel_roundToIntegral]
  exact Model.isFinite_roundToIntegral hformat hrange _ mode hvalue

end FloatLib.Floats.ExecFloat.Binary
