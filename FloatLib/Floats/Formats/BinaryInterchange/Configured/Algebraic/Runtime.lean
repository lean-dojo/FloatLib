/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Runtime

/-!
# Single-round algebraic operations on configured binary values

Each operation evaluates the descriptor-model operation through the storage codec. The packed,
word and limb carriers share its exact arithmetic, exceptional-value policies and final rounding.
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

/-- Reciprocal square root, with one final nearest-even rounding. -/
@[inline] def rsqrt (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.rsqrt value

/-- Euclidean norm, rounded once from the exact sum of squares. -/
@[inline] def hypot (left right : Value) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan) Model.hypot left right

/-- Exact integer-exponent power followed by one rounding. -/
@[inline] def powInt (value : Value) (exponent : Int) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) (Model.powInt · exponent) value

/-- Signed integer root, including reciprocal roots for negative degrees. -/
@[inline] def rootN (value : Value) (degree : Int) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) (Model.rootN · degree) value

end FloatLib.Floats.ExecFloat.Binary
