/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.External.Runtime
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Direction

/-!
# Report precision rounding for external binary formats

The external adapter uses its own declared precision and bias in the report formula.
Its precision is always greater than one, so lower-code parity is integer significand parity.
The rational selection theorem covers every deterministic mode and every supplied stochastic
word. These statements concern precision rounding; saturation and encoding are treated separately.

Reference: P3109 unapproved interim report 4.0.3, revision `34f5964`, §§4.7.4 and 4.8.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic.External

open BinaryInterchange

/-- External binary descriptors always have precision greater than one. -/
theorem precisionOf_gt_one (format : FloatFormat) : 1 < precisionOf format := by
  have h := format.fracWidth_pos
  simp only [precisionOf]
  omega

/-- External code parity is the ordinary parity of the integer significand. -/
theorem codeEven_eq (format : FloatFormat) (quantum : Int) (lower : Nat) :
    RationalRounding.codeEven (precisionOf format) (exponentBiasOf format) quantum lower =
      (lower % 2 == 0) := by
  simp only [RationalRounding.codeEven, precisionOf_gt_one, if_pos]
  rfl

/-- The selected external quantum uses the declared bias, including custom exponent biases. -/
theorem quantum_eq (format : FloatFormat) (value : Rat) :
    max (RationalBinary.floorLog2 value.num.natAbs value.den) format.minNormalExponent -
        (format.fracWidth : Int) =
      RationalRounding.quantum (precisionOf format) (exponentBiasOf format) value := by
  simp only [RationalRounding.quantum, precisionOf, exponentBiasOf,
    FloatFormat.minNormalExponent, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
  omega

/-- External precision rounding implements the report formula for every mode and rational input. -/
theorem roundFinite_toRat (format : FloatFormat) (mode : RoundingMode) (value : Rat) :
    (roundFinite format mode value).toRat =
      RationalRounding.round (precisionOf format) (exponentBiasOf format) mode value := by
  by_cases hz : value = 0
  · simp [hz, roundFinite, RationalRounding.round]
  have hn : value.num.natAbs ≠ 0 := by
    simpa only [Int.natAbs_ne_zero] using Rat.num_ne_zero.mpr hz
  simp only [roundFinite, beq_iff_eq, hn, if_false]
  rw [RationalRounding.normalized_toRat]
  rw [RationalRounding.select_eq_roundedInteger mode value _
    (fun lower => lower % 2 == 0)]
  have hp :
      (fun lower => lower % 2 == 0) =
        RationalRounding.codeEven (precisionOf format) (exponentBiasOf format)
          (RationalRounding.quantum (precisionOf format) (exponentBiasOf format) value) :=
    funext fun lower => (codeEven_eq format _ lower).symm
  simp only [RationalRounding.round, RationalRounding.roundAt, Int.ofNat_eq_natCast,
    quantum_eq, hp]

/-- External nearest-even precision rounding stays within half its own quantum. -/
theorem roundFinite_nearestTiesToEven_error (format : FloatFormat) (value : Rat) :
    |(roundFinite format .nearestTiesToEven value).toRat - value| ≤
      (2 : Rat) ^
        RationalRounding.quantum (precisionOf format) (exponentBiasOf format) value / 2 := by
  rw [roundFinite_toRat]
  exact RationalRounding.roundAt_nearestTiesToEven_error _ _ _

/-- Every external mode stays within its own quantum, including each stochastic word. -/
theorem roundFinite_error_lt_quantum (format : FloatFormat) (mode : RoundingMode) (value : Rat) :
    |(roundFinite format mode value).toRat - value| <
      (2 : Rat) ^ RationalRounding.quantum (precisionOf format) (exponentBiasOf format) value := by
  rw [roundFinite_toRat]
  exact RationalRounding.roundAt_error_lt_quantum _ _ _ _

/-- External upward rounding brackets the input from above before saturation. -/
theorem roundFinite_towardPositive (format : FloatFormat) (value : Rat) :
    value ≤ (roundFinite format .towardPositive value).toRat ∧
      (roundFinite format .towardPositive value).toRat < value +
        (2 : Rat) ^
          RationalRounding.quantum (precisionOf format) (exponentBiasOf format) value := by
  rw [roundFinite_toRat]
  exact RationalRounding.roundAt_towardPositive _ _ _

/-- External downward rounding brackets the input from below before saturation. -/
theorem roundFinite_towardNegative (format : FloatFormat) (value : Rat) :
    (roundFinite format .towardNegative value).toRat ≤ value ∧
      value < (roundFinite format .towardNegative value).toRat +
        (2 : Rat) ^
          RationalRounding.quantum (precisionOf format) (exponentBiasOf format) value := by
  rw [roundFinite_toRat]
  exact RationalRounding.roundAt_towardNegative _ _ _

end FloatLib.Floats.Formats.P3109.Arithmetic.External
