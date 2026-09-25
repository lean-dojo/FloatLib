/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Operations.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof

/-!
# Packing correctness for configured standard operations

Every theorem states that decoding a configured result recovers the single descriptor-model
operation used to compute it. Status-bearing operations preserve all five indicators exactly.

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

/-- Decoding configured remainder preserves both its value and all IEEE status indicators. -/
@[simp, grind =] theorem IEEEOutcome.toModel_remainderWithStatus
    (dividend divisor : Value) :
    IEEEOutcome.toModel (remainderWithStatus dividend divisor) =
      Model.remainderWithStatus
        (ExecFloat.Binary.toModel dividend)
        (ExecFloat.Binary.toModel divisor) := by
  simp [remainderWithStatus]

/-- Decoding configured integral rounding gives integral rounding in the descriptor model. -/
@[simp, grind =] theorem toModel_roundToIntegral
    (value : Value) (rounding : Model.IEEERoundingMode) :
    toModel (roundToIntegral value rounding) =
      Model.roundToIntegral (toModel value) rounding := by
  simp [roundToIntegral, toModel, Configured.Family.toModel]

/-- Configured integral rounding preserves the descriptor-model value and IEEE status. -/
@[simp, grind =] theorem IEEEOutcome.toModel_roundToIntegralExactWithStatus
    (value : Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (roundToIntegralExactWithStatus value rounding) =
      Model.roundToIntegralExactWithStatus (ExecFloat.Binary.toModel value) rounding := by
  simp [roundToIntegralExactWithStatus]

/-- Decoding configured power-of-two scaling gives descriptor-model scaling. -/
@[simp, grind =] theorem toModel_scale
    (value : Value) (n : Int) (rounding : Model.IEEERoundingMode) :
    toModel (scale value n rounding) =
      Model.scale (toModel value) n rounding := by
  simp [scale, toModel, Configured.Family.toModel]

/-- Configured power-of-two scaling preserves the descriptor-model value and IEEE status. -/
@[simp, grind =] theorem IEEEOutcome.toModel_scaleWithStatus
    (value : Value) (n : Int) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (scaleWithStatus value n rounding) =
      Model.scaleWithStatus (ExecFloat.Binary.toModel value) n rounding := by
  simp [scaleWithStatus]

/-- Decoding configured `binaryExponent` gives the descriptor-model leading binary exponent. -/
@[simp, grind =] theorem toModel_binaryExponent (value : Value) :
    toModel (binaryExponent value) = Model.binaryExponent (toModel value) := by
  simp [binaryExponent, toModel, Configured.Family.toModel]

/-- Configured `binaryExponent` preserves the descriptor-model value and IEEE status. -/
@[simp, grind =] theorem IEEEOutcome.toModel_binaryExponentWithStatus (value : Value) :
    IEEEOutcome.toModel (binaryExponentWithStatus value) =
      Model.binaryExponentWithStatus (ExecFloat.Binary.toModel value) := by
  simp [binaryExponentWithStatus]

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

/-- Decoding the configured downward neighbor gives the descriptor-model downward neighbor. -/
@[simp, grind =] theorem toModel_nextDown (value : Value) :
    toModel (nextDown value) = Model.nextDown (toModel value) := by
  simp [nextDown, toModel, Configured.Family.toModel]

/-- Decoding configured `minNum` gives descriptor-model `minNum`. -/
@[simp, grind =] theorem toModel_minNum (left right : Value) :
    toModel (minNum left right) = Model.minNum (toModel left) (toModel right) := by
  simp [minNum, toModel, Configured.Family.toModel]

/-- Decoding configured `maxNum` gives descriptor-model `maxNum`. -/
@[simp, grind =] theorem toModel_maxNum (left right : Value) :
    toModel (maxNum left right) = Model.maxNum (toModel left) (toModel right) := by
  simp [maxNum, toModel, Configured.Family.toModel]

end FloatLib.Floats.ExecFloat.Binary
