/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Block.Functions.Runtime
public import FloatLib.Floats.Formats.P3109.Block.Proof
public import FloatLib.Floats.Formats.P3109.Functions.Proof

/-!
# P3109 block function normalization and projection proofs

The §5.4.2 case equations cover all result scales. The §5.7 lane theorem
then applies the same real-function projection certificate to every block
length and independently decoded operand type.
-/

public section

namespace FloatLib.Floats.Formats.P3109

open FloatLib.Numerics FloatLib.Floats.ExecFloat

namespace FunctionBlock

/-- The rational sign witness agrees with the exact real expression at all finite arguments. -/
theorem signWitness_eq_real (expression : FunctionExpr) :
    (signWitness expression : ℝ) =
      if expression.toReal = 0 then 0 else if expression.toReal < 0 then -1 else 1 := by
  unfold signWitness
  rw [expression.prepare_eq_real]
  by_cases hzero : expression.toReal = 0
  · simp [hzero, cmp, cmpUsing]
  · by_cases hnegative : expression.toReal < 0
    · simp [hzero, hnegative, cmp, cmpUsing]
    · have hpositive : 0 < expression.toReal := lt_of_le_of_ne (not_lt.mp hnegative) (Ne.symm hzero)
      simp [hzero, hnegative, hpositive, cmp, cmpUsing]

/-- A finite nonzero result scale divides the exact real value without an intermediate rounding. -/
theorem normalize_finite_real (scale : Rat) (expression : FunctionExpr) (hscale : scale ≠ 0) :
    (normalize (.finite scale) (.finite expression)).map FunctionExpr.toReal =
      .finite (expression.toReal / (scale : ℝ)) := by
  simp [normalize, hscale, NumericalValue.map, FunctionExpr.toReal, div_eq_mul_inv, mul_comm]

/-- NaN takes precedence over every result scale, including zero. -/
theorem normalize_exceptional (scale : NumericalValue Rat) (category : ExceptionalValue) :
    normalize scale (.exceptional category) = .exceptional .nan := by
  simp [normalize, Block.normalize_exceptional, NumericalValue.map, Arithmetic.nan]

/-- A NaN result scale makes every function lane NaN. -/
theorem normalize_exceptional_scale (category : ExceptionalValue)
    (value : NumericalValue FunctionExpr) :
    normalize (.exceptional category) value = .exceptional .nan := by
  cases value <;> rfl

/-- Zero result scale maps every non-NaN lane to exact zero. -/
theorem normalize_zero (value : NumericalValue FunctionExpr)
    (hvalue : ∀ category, value ≠ .exceptional category) :
    normalize (.finite 0) value = .finite (.rational 0) := by
  cases value <;> simp_all [normalize, Block.normalize, NumericalValue.map]

/-- Infinite result scales produce the product of the exact value's sign and the scale's sign. -/
theorem normalize_infinite_finite_real (negative : Bool) (expression : FunctionExpr) :
    (normalize (.infinity negative) (.finite expression)).map FunctionExpr.toReal =
      .finite ((if negative then (-1 : ℝ) else 1) *
        (if expression.toReal = 0 then 0 else if expression.toReal < 0 then -1 else 1)) := by
  have hcompare := expression.prepare_eq_real 8 0
  simp only [Rat.cast_zero] at hcompare
  simp only [normalize, signWitness]
  rw [hcompare]
  rcases lt_trichotomy expression.toReal 0 with hnegative | hzero | hpositive
  · cases negative <;> simp [hnegative, ne_of_lt hnegative, cmp, cmpUsing,
      Block.normalize, Block.signum, Arithmetic.Negate, NumericalValue.map, FunctionExpr.toReal]
  · cases negative <;> simp [hzero, cmp, cmpUsing, Block.normalize, Block.signum,
      Arithmetic.Negate, NumericalValue.map, FunctionExpr.toReal]
  · cases negative <;> simp [hpositive, ne_of_gt hpositive, not_lt.mpr (le_of_lt hpositive),
      cmp, cmpUsing, Block.normalize, Block.signum, Arithmetic.Negate, NumericalValue.map,
      FunctionExpr.toReal] <;> norm_num

end FunctionBlock

namespace Block

variable {length : ℕ+}
variable {Scale ScaleExact Source SourceExact ResultScale ResultScaleExact : Type}
variable [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
variable [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
variable [ExactDecoder ResultScale ResultScaleExact] [ExactMap ResultScaleExact Rat]

/-- Every projected function lane refines its normalized real-function reference (§5.4.2). -/
theorem decode_projectFunctions_lane (format : Format) (policy : BlockPolicy length)
    (scale : ResultScale) (expressions : Vector (NumericalValue FunctionExpr) length)
    (lane : Fin (length : Nat)) :
    Format.SameDatum
      (ExecFloat.P3109.decode (projectFunctions format policy scale expressions).values[lane.val])
      (Functions.referenceValue format (policy.at lane)
        (FunctionBlock.normalize (Arithmetic.Mixed.decode scale) expressions[lane.val])) := by
  simp only [projectFunctions, Vector.getElem_ofFn]
  exact ExecFloat.P3109.decode_projectFunction _ _ _

/-- All unary block functions share exact lane decoding, normalization and projection (§5.7). -/
theorem decode_unaryFunction_lane (format : Format) (policy : BlockPolicy length)
    (operation : Functions.Unary) (block : Block Scale Source length)
    (resultScale : ResultScale) (lane : Fin (length : Nat)) :
    Format.SameDatum
      (ExecFloat.P3109.decode
        (unaryFunction format policy operation block resultScale).values[lane.val])
      (Functions.referenceValue format (policy.at lane)
        (FunctionBlock.normalize (Arithmetic.Mixed.decode resultScale)
          (Functions.unary operation (decode block)[lane.val]))) := by
  simpa only [unaryFunction, Vector.getElem_map] using
    decode_projectFunctions_lane format policy resultScale
      ((decode block).map (Functions.unary operation)) lane

variable {RightScale RightScaleExact Right RightExact : Type}
variable [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
variable [ExactDecoder Right RightExact] [ExactMap RightExact Rat]

/-- Both block inverse-tangent forms use independent exact operands before normalization (§5.7). -/
theorem decode_angleFunction_lane (format : Format) (policy : BlockPolicy length) (piScaled : Bool)
    (y : Block Scale Source length) (x : Block RightScale Right length)
    (resultScale : ResultScale) (lane : Fin (length : Nat)) :
    Format.SameDatum
      (ExecFloat.P3109.decode
        (angleFunction format policy piScaled y x resultScale).values[lane.val])
      (Functions.referenceValue format (policy.at lane)
        (FunctionBlock.normalize (Arithmetic.Mixed.decode resultScale)
          (Functions.arcTan2 piScaled (decode y)[lane.val] (decode x)[lane.val]))) := by
  simpa only [angleFunction, Vector.getElem_ofFn] using
    decode_projectFunctions_lane format policy resultScale
      (Vector.ofFn fun i : Fin (length : Nat) =>
        Functions.arcTan2 piScaled (decode y)[i.val] (decode x)[i.val]) lane

end Block
end FloatLib.Floats.Formats.P3109
