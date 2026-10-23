/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Operations.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof
import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Classification
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof

/-!
# Packing correctness for configured standard operations

Every decoding theorem states that decoding a configured result recovers the single
descriptor-model operation used to compute it. Results with `status := true` keep all five
indicators, and the projection theorems `value_remainder` through `value_nextDown` state that
their value is the configured operation without status.

The arithmetic properties are proved for the descriptor-model operations. These theorems
transport their results through the storage codec, giving the same equations for values and
exception flags with every storage plan.
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

/-- Decoding configured `minNum` gives descriptor-model `minNum`. -/
@[simp, grind =] theorem toModel_minNum (left right : Value) :
    toModel (minNum left right) = Model.minNum (toModel left) (toModel right) := by
  simp [minNum, toModel, Configured.Family.toModel]

/-- Decoding configured `maxNum` gives descriptor-model `maxNum`. -/
@[simp, grind =] theorem toModel_maxNum (left right : Value) :
    toModel (maxNum left right) = Model.maxNum (toModel left) (toModel right) := by
  simp [maxNum, toModel, Configured.Family.toModel]

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

/-- The integer value is absent exactly for the values that are not finite. -/
@[simp] theorem toInt?_eq_none_iff (value : Value) (mode : Model.IEEERoundingMode) :
    toInt? value mode = none ↔ isFinite value = false := by
  have hdecode := Model.toDyadic?_isSome_eq_isFinite (toModel value)
  unfold toInt? isFinite
  cases hd : Model.toDyadic? (toModel value) <;> simp_all

end FloatLib.Floats.ExecFloat.Binary
