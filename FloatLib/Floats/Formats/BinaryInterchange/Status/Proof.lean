/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.DyadicOrder
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Logarithm
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime
public import FloatLib.Numerics.IEEEStatus.Proof

/-!
# Correctness of IEEE exception status

The executable status kernels in `Status.Runtime` satisfy cross-flag invariants and
operation-level specifications. Import `BinaryInterchange.Status` for the combined public
interface.

The rounding-status classifiers compare an exact dyadic or scaled rational with the supplied
rounded value. Operation wrappers compute that exact witness alongside the value-only operation.
This file proves cross-flag invariants, preservation of the ordinary result, real-order tininess
boundaries, and operation-specific invalid and divide-by-zero conditions.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats.Formats.Flocq

/-! ## Constructors and rounding-status invariants -/

/-- The direct result classifier recognizes exactly finite zero and subnormal encodings. -/
@[simp] theorem isTinyAfterRounding_eq_true_iff {fmt : FloatFormat}
    (rounded : Model fmt) :
    isTinyAfterRounding rounded = true ↔
      isFinite rounded = true ∧ expField rounded = 0 := by
  simp [isTinyAfterRounding]

/--
The underflow midpoint is exactly halfway between the unbounded-grid predecessor and the smallest
normal value.

Both gaps are one `2^(minSubnormalExponent - 2)` step. Besides documenting the quarter-subnormal
offset used by nearest-even, the equalities rule out an off-by-one significand or exponent in the
three executable boundary constants.
-/
theorem underflow_boundary_gaps (fmt : FloatFormat) :
    (underflowMidpoint fmt).toReal -
        (underflowPredecessor fmt).toReal =
      FloatLib.Floats.Formats.Flocq.bpow
        Numerics.binaryRadix (fmt.minSubnormalExponent - 2) ∧
    (minNormalDyadic fmt).toReal -
        (underflowMidpoint fmt).toReal =
      FloatLib.Floats.Formats.Flocq.bpow
        Numerics.binaryRadix (fmt.minSubnormalExponent - 2) := by
  let scale :=
    FloatLib.Floats.Formats.Flocq.bpow
      Numerics.binaryRadix (fmt.minSubnormalExponent - 2)
  have hpredecessorScale :
      FloatLib.Floats.Formats.Flocq.bpow
          Numerics.binaryRadix (fmt.minSubnormalExponent - 1) =
        scale * 2 := by
    calc
      FloatLib.Floats.Formats.Flocq.bpow
          Numerics.binaryRadix (fmt.minSubnormalExponent - 1) =
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            ((fmt.minSubnormalExponent - 2) + 1) := by
        congr 1
        omega
      _ = scale *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix 1 := by
        simp only [scale, FloatLib.Floats.Formats.Flocq.bpow.add_exp]
      _ = scale * 2 := by
        norm_num [FloatLib.Floats.Formats.Flocq.bpow,
          Numerics.binaryRadix, Numerics.Radix.toReal]
  have hnormalScale :
      FloatLib.Floats.Formats.Flocq.bpow
          Numerics.binaryRadix fmt.minSubnormalExponent =
        scale * 4 := by
    calc
      FloatLib.Floats.Formats.Flocq.bpow
          Numerics.binaryRadix fmt.minSubnormalExponent =
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            ((fmt.minSubnormalExponent - 2) + 2) := by
        congr 1
        omega
      _ = scale *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix 2 := by
        simp only [scale, FloatLib.Floats.Formats.Flocq.bpow.add_exp]
      _ = scale * 4 := by
        norm_num [FloatLib.Floats.Formats.Flocq.bpow,
          Numerics.binaryRadix, Numerics.Radix.toReal]
  have htwo :
      1 ≤ 2 * pow2 fmt.fracWidth := by
    have : 0 < pow2 fmt.fracWidth := by
      simp [pow2, Nat.shiftLeft_eq]
    omega
  have hfour :
      1 ≤ 4 * pow2 fmt.fracWidth := by
    have : 0 < pow2 fmt.fracWidth := by
      simp [pow2, Nat.shiftLeft_eq]
    omega
  change (2 : ℝ) ^ (fmt.minSubnormalExponent - 1) = scale * 2 at hpredecessorScale
  change (2 : ℝ) ^ fmt.minSubnormalExponent = scale * 4 at hnormalScale
  constructor <;>
    simp [underflowMidpoint, underflowPredecessor, minNormalDyadic,
      Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
      hpredecessorScale, hnormalScale, Nat.cast_sub htwo,
      Nat.cast_sub hfour, scale] <;>
    dsimp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] <;>
    ring

/--
Real-order specification of after-rounding dyadic tininess.

An already tiny encoding is accepted immediately. Otherwise nearest-even uses the underflow
midpoint, rounding toward zero uses the smallest normal, and a directed mode uses either the
unbounded-grid predecessor or the smallest normal according to whether it rounds this sign away
from zero. This theorem is the semantic boundary for the executable comparisons in
`dyadicIsTinyAfterRounding`.
-/
theorem dyadicIsTinyAfterRounding_eq_true_iff
    (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (rounded : Model fmt) :
    dyadicIsTinyAfterRounding fmt mode exact rounded = true ↔
      isTinyAfterRounding rounded = true ∨
        (isTinyAfterRounding rounded = false ∧
          match mode with
          | .nearestEven =>
              ({ exact with negative := false } : Numerics.Dyadic).toReal <
                (underflowMidpoint fmt).toReal
          | .towardZero =>
              ({ exact with negative := false } : Numerics.Dyadic).toReal <
                (minNormalDyadic fmt).toReal
          | .towardPositiveInfinity | .towardNegativeInfinity =>
              if roundsAwayFromZero mode exact.negative then
                ({ exact with negative := false } : Numerics.Dyadic).toReal ≤
                  (underflowPredecessor fmt).toReal
              else
                ({ exact with negative := false } : Numerics.Dyadic).toReal <
                  (minNormalDyadic fmt).toReal) := by
  cases hrounded : isTinyAfterRounding rounded with
  | false =>
      cases mode <;> cases hnegative : exact.negative <;>
        simp [dyadicIsTinyAfterRounding, hrounded, roundsAwayFromZero,
          hnegative, cmpDyadic_lt_iff, cmpDyadic_gt_iff]
  | true =>
      simp [dyadicIsTinyAfterRounding, hrounded]

/--
Real-order specification of after-rounding tininess for scaled rationals.

The denominator premise excludes the malformed representation for which the executable comparator
returns `none`. For every valid rational, the optimized leading-exponent comparison has the same
mode-sensitive boundaries as the dyadic classifier above.
-/
theorem rationalIsTinyAfterRoundingScaled_eq_true_iff
    (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (rounded : Model fmt)
    (hdenominator : denominator ≠ 0) :
    rationalIsTinyAfterRoundingScaled
        fmt mode sign numerator denominator exponent rounded = true ↔
      isTinyAfterRounding rounded = true ∨
        (isTinyAfterRounding rounded = false ∧
          match mode with
          | .nearestEven =>
              scaledRatToReal numerator denominator exponent <
                (underflowMidpoint fmt).toReal
          | .towardZero =>
              scaledRatToReal numerator denominator exponent <
                (minNormalDyadic fmt).toReal
          | .towardPositiveInfinity | .towardNegativeInfinity =>
              if roundsAwayFromZero mode sign then
                scaledRatToReal numerator denominator exponent ≤
                  (underflowPredecessor fmt).toReal
              else
                scaledRatToReal numerator denominator exponent <
                  (minNormalDyadic fmt).toReal) := by
  have hpow : 0 < pow2 fmt.fracWidth := by
    simp [pow2, Nat.shiftLeft_eq]
  have hmidpoint :
      (underflowMidpoint fmt).significand ≠ 0 := by
    simp only [underflowMidpoint]
    omega
  have hnormal :
      (minNormalDyadic fmt).significand ≠ 0 := by
    simpa [minNormalDyadic] using hpow.ne'
  have hpredecessor :
      (underflowPredecessor fmt).significand ≠ 0 := by
    simp only [underflowPredecessor]
    omega
  have hmidpointComparison := compareDyadicScaled?_false_eq_compare
    numerator denominator exponent (underflowMidpoint fmt)
      hdenominator (by simp [underflowMidpoint]) hmidpoint
  have hnormalComparison := compareDyadicScaled?_false_eq_compare
    numerator denominator exponent (minNormalDyadic fmt)
      hdenominator (by simp [minNormalDyadic]) hnormal
  have hpredecessorComparison := compareDyadicScaled?_false_eq_compare
    numerator denominator exponent (underflowPredecessor fmt)
      hdenominator (by simp [underflowPredecessor]) hpredecessor
  cases hrounded : isTinyAfterRounding rounded with
  | false =>
      cases mode with
      | nearestEven =>
          simp [rationalIsTinyAfterRoundingScaled, hrounded, roundsAwayFromZero]
          rw [hmidpointComparison]
          cases hcomparison : compare
              (scaledRatToReal numerator denominator exponent)
              (underflowMidpoint fmt).toReal <;>
            simp_all [compare_lt_iff_lt, compare_gt_iff_gt, le_of_lt]
      | towardZero =>
          simp [rationalIsTinyAfterRoundingScaled, hrounded, roundsAwayFromZero]
          rw [hnormalComparison]
          cases hcomparison : compare
              (scaledRatToReal numerator denominator exponent)
              (minNormalDyadic fmt).toReal <;>
            simp_all [compare_lt_iff_lt, compare_gt_iff_gt, le_of_lt]
      | towardPositiveInfinity =>
          cases sign with
          | false =>
              simp [rationalIsTinyAfterRoundingScaled, hrounded, roundsAwayFromZero]
              rw [hpredecessorComparison]
              cases hcomparison : compare
                  (scaledRatToReal numerator denominator exponent)
                  (underflowPredecessor fmt).toReal <;>
                simp_all [compare_lt_iff_lt, compare_gt_iff_gt, le_of_lt]
          | true =>
              simp [rationalIsTinyAfterRoundingScaled, hrounded, roundsAwayFromZero]
              rw [hnormalComparison]
              cases hcomparison : compare
                  (scaledRatToReal numerator denominator exponent)
                  (minNormalDyadic fmt).toReal <;>
                simp_all [compare_lt_iff_lt, compare_gt_iff_gt, le_of_lt]
      | towardNegativeInfinity =>
          cases sign with
          | false =>
              simp [rationalIsTinyAfterRoundingScaled, hrounded, roundsAwayFromZero]
              rw [hnormalComparison]
              cases hcomparison : compare
                  (scaledRatToReal numerator denominator exponent)
                  (minNormalDyadic fmt).toReal <;>
                simp_all [compare_lt_iff_lt, compare_gt_iff_gt, le_of_lt]
          | true =>
              simp [rationalIsTinyAfterRoundingScaled, hrounded, roundsAwayFromZero]
              rw [hpredecessorComparison]
              cases hcomparison : compare
                  (scaledRatToReal numerator denominator exponent)
                  (underflowPredecessor fmt).toReal <;>
                simp_all [compare_lt_iff_lt, compare_gt_iff_gt, le_of_lt]
  | true =>
      simp [rationalIsTinyAfterRoundingScaled, hrounded]

/--
The dyadic and scaled-rational tininess classifiers agree when the rational has denominator one.

This bridge lets operation proofs choose the representation natural to their exact arithmetic
without creating two notions of IEEE underflow.
-/
theorem rationalIsTinyAfterRoundingScaled_eq_dyadic
    (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (rounded : Model fmt) :
    rationalIsTinyAfterRoundingScaled fmt mode exact.negative
        exact.significand 1 exact.exponent rounded =
      dyadicIsTinyAfterRounding fmt mode exact rounded := by
  apply Bool.eq_iff_iff.mpr
  rw [rationalIsTinyAfterRoundingScaled_eq_true_iff
    fmt mode exact.negative exact.significand 1 exact.exponent rounded (by simp)]
  rw [dyadicIsTinyAfterRounding_eq_true_iff]
  simp [scaledRatToReal, Numerics.Dyadic.toReal,
    Numerics.Dyadic.signedSignificand, bpow,
    FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/-- `outcomeWithInvalid` preserves its supplied floating-point value. -/
@[simp] theorem outcomeWithInvalid_value {fmt : FloatFormat}
    (value : Model fmt) (invalid : Bool) :
    (outcomeWithInvalid value invalid).value = value := rfl

/-- `outcomeWithInvalid` records exactly its supplied invalid-operation condition. -/
@[simp] theorem outcomeWithInvalid_invalid {fmt : FloatFormat}
    (value : Model fmt) (invalid : Bool) :
    (outcomeWithInvalid value invalid).status.invalid = invalid := by
  cases invalid <;> rfl

/-- `outcomeWithInvalid` never raises divide-by-zero. -/
@[simp] theorem outcomeWithInvalid_divideByZero {fmt : FloatFormat}
    (value : Model fmt) (invalid : Bool) :
    (outcomeWithInvalid value invalid).status.divideByZero = false := by
  cases invalid <;> rfl

/-- After-rounding dyadic underflow implies inexactness. -/
theorem dyadicRoundingStatus_inexact_of_underflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {exact : Numerics.Dyadic} {rounded : Model fmt}
    (h : (dyadicRoundingStatus fmt mode exact rounded).underflow = true) :
    (dyadicRoundingStatus fmt mode exact rounded).inexact = true := by
  unfold dyadicRoundingStatus at h ⊢
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/--
Dyadic rounding reports overflow when rounding crosses the format's overflow threshold or when the
supplied rounded result is an infinity.
-/
@[simp] theorem dyadicRoundingStatus_overflow {fmt : FloatFormat}
    (mode : IEEERoundingMode) (exact : Numerics.Dyadic) (rounded : Model fmt) :
    (dyadicRoundingStatus fmt mode exact rounded).overflow =
      (dyadicRoundingOverflows fmt mode exact ||
        (!isFinite rounded && isInf rounded)) := by
  unfold dyadicRoundingStatus
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- For a finite result, dyadic overflow is exactly the exact-value overflow classification. -/
theorem dyadicRoundingStatus_overflow_of_isFinite {fmt : FloatFormat}
    (mode : IEEERoundingMode) (exact : Numerics.Dyadic) (rounded : Model fmt)
    (hfinite : isFinite rounded = true) :
    (dyadicRoundingStatus fmt mode exact rounded).overflow =
      dyadicRoundingOverflows fmt mode exact := by
  rw [dyadicRoundingStatus_overflow]
  simp [hfinite]

/-- Dyadic rounding overflow always raises inexact. -/
theorem dyadicRoundingStatus_inexact_of_overflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {exact : Numerics.Dyadic} {rounded : Model fmt}
    (h : (dyadicRoundingStatus fmt mode exact rounded).overflow = true) :
    (dyadicRoundingStatus fmt mode exact rounded).inexact = true := by
  unfold dyadicRoundingStatus at h ⊢
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- A dyadic rounding result cannot simultaneously signal overflow and underflow. -/
theorem dyadicRoundingStatus_not_underflow_of_overflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {exact : Numerics.Dyadic} {rounded : Model fmt}
    (h : (dyadicRoundingStatus fmt mode exact rounded).overflow = true) :
    (dyadicRoundingStatus fmt mode exact rounded).underflow = false := by
  unfold dyadicRoundingStatus at h ⊢
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- After-rounding scaled rational underflow implies inexactness. -/
theorem rationalRoundingStatusScaled_inexact_of_underflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {sign : Bool} {numerator denominator : Nat}
    {exponent : Int} {rounded : Model fmt}
    (h : (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).underflow = true) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).inexact = true := by
  unfold rationalRoundingStatusScaled at h ⊢
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/--
Scaled rational rounding reports overflow when rounding crosses the format's overflow threshold or
when the supplied rounded result is an infinity.
-/
@[simp] theorem rationalRoundingStatusScaled_overflow {fmt : FloatFormat}
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (rounded : Model fmt) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent rounded).overflow =
      (rationalRoundingOverflowsScaled fmt mode sign numerator denominator exponent ||
        (!isFinite rounded && isInf rounded)) := by
  unfold rationalRoundingStatusScaled
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/--
For a finite result, scaled rational overflow is exactly the exact-value overflow classification.
-/
theorem rationalRoundingStatusScaled_overflow_of_isFinite {fmt : FloatFormat}
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (rounded : Model fmt) (hfinite : isFinite rounded = true) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent rounded).overflow =
      rationalRoundingOverflowsScaled fmt mode sign numerator denominator exponent := by
  rw [rationalRoundingStatusScaled_overflow]
  simp [hfinite]

/-- Scaled rational overflow always raises inexact. -/
theorem rationalRoundingStatusScaled_inexact_of_overflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {sign : Bool} {numerator denominator : Nat}
    {exponent : Int} {rounded : Model fmt}
    (h : (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).overflow = true) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).inexact = true := by
  unfold rationalRoundingStatusScaled at h ⊢
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Scaled rational rounding cannot signal overflow and underflow together. -/
theorem rationalRoundingStatusScaled_not_underflow_of_overflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {sign : Bool} {numerator denominator : Nat}
    {exponent : Int} {rounded : Model fmt}
    (h : (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).overflow = true) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).underflow = false := by
  unfold rationalRoundingStatusScaled at h ⊢
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- After-rounding rational underflow implies inexactness. -/
theorem rationalRoundingStatus_inexact_of_underflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {sign : Bool} {numerator denominator : Nat}
    {rounded : Model fmt}
    (h : (rationalRoundingStatus fmt mode sign numerator denominator rounded).underflow = true) :
    (rationalRoundingStatus fmt mode sign numerator denominator rounded).inexact = true :=
  rationalRoundingStatusScaled_inexact_of_underflow h

/--
Rational rounding reports overflow when rounding crosses the format's overflow threshold or when
the supplied rounded result is an infinity.
-/
@[simp] theorem rationalRoundingStatus_overflow {fmt : FloatFormat}
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat)
    (rounded : Model fmt) :
    (rationalRoundingStatus fmt mode sign numerator denominator rounded).overflow =
      (rationalRoundingOverflows fmt mode sign numerator denominator ||
        (!isFinite rounded && isInf rounded)) :=
  rationalRoundingStatusScaled_overflow mode sign numerator denominator 0 rounded

/-- For a finite result, rational overflow is exactly the exact-value overflow classification. -/
theorem rationalRoundingStatus_overflow_of_isFinite {fmt : FloatFormat}
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat)
    (rounded : Model fmt) (hfinite : isFinite rounded = true) :
    (rationalRoundingStatus fmt mode sign numerator denominator rounded).overflow =
      rationalRoundingOverflows fmt mode sign numerator denominator :=
  rationalRoundingStatusScaled_overflow_of_isFinite
    mode sign numerator denominator 0 rounded hfinite

/-- Rational overflow always raises inexact. -/
theorem rationalRoundingStatus_inexact_of_overflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {sign : Bool} {numerator denominator : Nat}
    {rounded : Model fmt}
    (h : (rationalRoundingStatus fmt mode sign numerator denominator rounded).overflow = true) :
    (rationalRoundingStatus fmt mode sign numerator denominator rounded).inexact = true :=
  rationalRoundingStatusScaled_inexact_of_overflow h

/-- Rational rounding cannot signal overflow and underflow together. -/
theorem rationalRoundingStatus_not_underflow_of_overflow {fmt : FloatFormat}
    {mode : IEEERoundingMode} {sign : Bool} {numerator denominator : Nat}
    {rounded : Model fmt}
    (h : (rationalRoundingStatus fmt mode sign numerator denominator rounded).overflow = true) :
    (rationalRoundingStatus fmt mode sign numerator denominator rounded).underflow = false :=
  rationalRoundingStatusScaled_not_underflow_of_overflow h

/-- Dyadic rounding is invalid exactly for an unclassified non-finite, non-infinite result. -/
@[simp] theorem dyadicRoundingStatus_invalid
    (fmt : FloatFormat) (mode : IEEERoundingMode) (exact : Numerics.Dyadic)
    (rounded : Model fmt) :
    (dyadicRoundingStatus fmt mode exact rounded).invalid =
      (!dyadicRoundingOverflows fmt mode exact &&
        !isFinite rounded && !isInf rounded) := by
  unfold dyadicRoundingStatus
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- A finite dyadic rounding result cannot raise invalid. -/
theorem dyadicRoundingStatus_invalid_false_of_isFinite
    (fmt : FloatFormat) (mode : IEEERoundingMode) (exact : Numerics.Dyadic)
    (rounded : Model fmt) (hfinite : isFinite rounded = true) :
    (dyadicRoundingStatus fmt mode exact rounded).invalid = false := by
  rw [dyadicRoundingStatus_invalid]
  simp [hfinite]

/-- Rounding an exact dyadic never raises `divideByZero`. -/
@[simp] theorem dyadicRoundingStatus_divideByZero_false
    (fmt : FloatFormat) (mode : IEEERoundingMode) (exact : Numerics.Dyadic)
    (rounded : Model fmt) :
    (dyadicRoundingStatus fmt mode exact rounded).divideByZero = false := by
  unfold dyadicRoundingStatus
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/--
Scaled rational rounding is invalid exactly for an unclassified non-finite, non-infinite result.
-/
@[simp] theorem rationalRoundingStatusScaled_invalid
    (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (rounded : Model fmt) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).invalid =
        (!rationalRoundingOverflowsScaled fmt mode sign numerator denominator exponent &&
          !isFinite rounded && !isInf rounded) := by
  unfold rationalRoundingStatusScaled
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- A finite scaled rational rounding result cannot raise invalid. -/
theorem rationalRoundingStatusScaled_invalid_false_of_isFinite
    (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (rounded : Model fmt)
    (hfinite : isFinite rounded = true) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).invalid = false := by
  rw [rationalRoundingStatusScaled_invalid]
  simp [hfinite]

/-- Rounding an exact scaled rational never raises `divideByZero`. -/
@[simp] theorem rationalRoundingStatusScaled_divideByZero_false
    (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (rounded : Model fmt) :
    (rationalRoundingStatusScaled fmt mode sign numerator denominator exponent
      rounded).divideByZero = false := by
  unfold rationalRoundingStatusScaled
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-! ## Result projection -/

/-- Status-bearing addition returns the same value as value-only directed addition. -/
theorem addWithStatus_value {fmt : FloatFormat}
    (x y : Model fmt) (mode : IEEERoundingMode) :
    (addWithStatus x y mode).value = addWithRounding mode x y := by
  unfold addWithStatus
  split <;> simp

/-- Status-bearing subtraction returns the same value as value-only directed subtraction. -/
theorem subWithStatus_value {fmt : FloatFormat}
    (x y : Model fmt) (mode : IEEERoundingMode) :
    (subWithStatus x y mode).value = subWithRounding mode x y := by
  rw [subWithStatus, subWithRounding, addWithStatus_value]

/-- Status-bearing multiplication returns the same value as value-only directed multiplication. -/
theorem mulWithStatus_value {fmt : FloatFormat}
    (x y : Model fmt) (mode : IEEERoundingMode) :
    (mulWithStatus x y mode).value = mulWithRounding mode x y := by
  unfold mulWithStatus
  split <;> simp

/-- Status-bearing division returns the same value as value-only directed division. -/
theorem divWithStatus_value {fmt : FloatFormat}
    (x y : Model fmt) (mode : IEEERoundingMode) :
    (divWithStatus x y mode).value = divWithRounding mode x y := by
  cases mode <;> unfold divWithStatus divWithRounding
  · split
    · rename_i dx dy hx hy
      simp [Proof.div_eq_spec, Spec.div, hx, hy, roundRatWithRoundingScaled]
      by_cases hdy : dy.significand = 0 <;>
        by_cases hdx : dx.significand = 0 <;>
          simp [hdy, hdx]
    · simp
  all_goals
    split
    · rename_i dx dy hx hy
      have hxNaN := isNaN_eq_false_of_toDyadic?_some hx
      have hyNaN := isNaN_eq_false_of_toDyadic?_some hy
      have hchoose : chooseNaN2 x y = none :=
        (chooseNaN2_eq_none_iff x y).2 ⟨hxNaN, hyNaN⟩
      have hxInf := isInf_eq_false_of_toDyadic?_some hx
      have hyInf := isInf_eq_false_of_toDyadic?_some hy
      have hxFinite :=
        isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hxNaN hxInf
      have hyFinite :=
        isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hyNaN hyInf
      have hxExact := finiteDyadic_eq_of_toDyadic hxFinite hx
      have hyExact := finiteDyadic_eq_of_toDyadic hyFinite hy
      have hxZero := isZero_eq_beq_zero_of_toDyadic?_some hx
      have hyZero := isZero_eq_beq_zero_of_toDyadic?_some hy
      have hxSign := sign_eq_signBit_of_toDyadic?_some hx
      have hySign := sign_eq_signBit_of_toDyadic?_some hy
      have hsign :
          Bool.xor dx.negative dy.negative = (dx.negative != dy.negative) := by
        cases dx.negative <;> cases dy.negative <;> rfl
      simp [hchoose, hxInf, hyInf, hxExact, hyExact, hxZero, hyZero,
        ← hxSign, ← hySign]
      by_cases hdy : dy.significand = 0 <;>
        by_cases hdx : dx.significand = 0 <;>
          simp [hdy, hdx, hsign]
    · simp

/-- Status-bearing FMA returns the same value as value-only directed FMA. -/
theorem fmaWithStatus_value {fmt : FloatFormat}
    (x y z : Model fmt) (mode : IEEERoundingMode) :
    (fmaWithStatus x y z mode).value = fmaWithRounding mode x y z := by
  unfold fmaWithStatus
  split <;> simp

/-- Status-bearing square root returns the same value as value-only directed square root. -/
theorem sqrtWithStatus_value {fmt : FloatFormat}
    (x : Model fmt) (mode : IEEERoundingMode) :
    (sqrtWithStatus x mode).value = sqrtWithRounding mode x := by
  unfold sqrtWithStatus
  dsimp only
  split
  · simp [outcomeWithInvalid]
  · split
    · simp [outcomeWithInvalid]
    · split
      · simp [outcomeWithInvalid]
      · split
        · simp [outcomeWithInvalid]
        · rfl

/-! ## Operation-specific exceptional status -/

/-- Finite addition exposes exactly its dyadic rounding status. -/
theorem addWithStatus_of_toDyadic
    {fmt : FloatFormat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (mode : IEEERoundingMode)
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy) :
    addWithStatus x y mode =
      let exact := addDyadic dx dy
      let value := addWithRounding mode x y
      { value, status := dyadicRoundingStatus fmt mode exact value } := by
  simp [addWithStatus, hx, hy]

/--
Complete invalid-status classification for addition.

Finite operands expose the rounded result's classification directly. Exceptional operands raise
invalid exactly for a signaling NaN or opposite-signed infinities when no NaN was supplied.
-/
theorem addWithStatus_invalid
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    (addWithStatus x y mode).status.invalid =
      match toDyadic? x, toDyadic? y with
      | some dx, some dy =>
          let exact := addDyadic dx dy
          let value := addWithRounding mode x y
          !dyadicRoundingOverflows fmt mode exact &&
            !isFinite value && !isInf value
      | _, _ =>
          isSNaN x || isSNaN y ||
            (!(isNaN x || isNaN y) &&
              (isInf x && isInf y && signBit x != signBit y)) := by
  cases hx : toDyadic? x <;> cases hy : toDyadic? y <;>
    simp [addWithStatus, hx, hy]

/-- Finite multiplication exposes exactly its dyadic rounding status. -/
theorem mulWithStatus_of_toDyadic
    {fmt : FloatFormat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (mode : IEEERoundingMode)
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy) :
    mulWithStatus x y mode =
      let exact : Numerics.Dyadic :=
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      let value := mulWithRounding mode x y
      { value, status := dyadicRoundingStatus fmt mode exact value } := by
  simp [mulWithStatus, hx, hy]

/--
Complete invalid-status classification for multiplication.

Finite operands expose the rounded result's classification directly. Exceptional operands raise
invalid exactly for a signaling NaN or an infinity-times-zero operation without an input NaN.
-/
theorem mulWithStatus_invalid
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    (mulWithStatus x y mode).status.invalid =
      match toDyadic? x, toDyadic? y with
      | some dx, some dy =>
          let exact : Numerics.Dyadic :=
            { negative := Bool.xor dx.negative dy.negative
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent }
          let value := mulWithRounding mode x y
          !dyadicRoundingOverflows fmt mode exact &&
            !isFinite value && !isInf value
      | _, _ =>
          isSNaN x || isSNaN y ||
            (!(isNaN x || isNaN y) &&
              ((isInf x && isZero y) || (isInf y && isZero x))) := by
  cases hx : toDyadic? x <;> cases hy : toDyadic? y <;>
    simp [mulWithStatus, hx, hy]

/-- Finite FMA exposes exactly its dyadic rounding status. -/
theorem fmaWithStatus_of_toDyadic
    {fmt : FloatFormat} {x y z : Model fmt} {dx dy dz : Numerics.Dyadic}
    (mode : IEEERoundingMode)
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hz : toDyadic? z = some dz) :
    fmaWithStatus x y z mode =
      let product : Numerics.Dyadic :=
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      let exact := addDyadic product dz
      let value := fmaWithRounding mode x y z
      { value, status := dyadicRoundingStatus fmt mode exact value } := by
  simp [fmaWithStatus, hx, hy, hz]

/--
Complete invalid-status classification for fused multiply-add.

Finite operands expose the singly rounded result's classification directly. Exceptional operands
use the IEEE signaling-NaN, infinity-times-zero, and opposite-infinity rules. For the
implementation-defined quiet-NaN case, this library raises invalid for infinity times zero even
when the addend is a quiet NaN; an input NaN suppresses the opposite-infinity condition.
-/
theorem fmaWithStatus_invalid
    {fmt : FloatFormat} (x y z : Model fmt) (mode : IEEERoundingMode) :
    (fmaWithStatus x y z mode).status.invalid =
      match toDyadic? x, toDyadic? y, toDyadic? z with
      | some dx, some dy, some dz =>
          let product : Numerics.Dyadic :=
            { negative := Bool.xor dx.negative dy.negative
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent }
          let exact := addDyadic product dz
          let value := fmaWithRounding mode x y z
          !dyadicRoundingOverflows fmt mode exact &&
            !isFinite value && !isInf value
      | _, _, _ =>
          let hasNaN := isNaN x || isNaN y || isNaN z
          let invalidProduct := (isInf x || isInf y) && (isZero x || isZero y)
          let productIsInf := (isInf x || isInf y) && !(isZero x || isZero y)
          let oppositeInfiniteAddend :=
            productIsInf && isInf z &&
              signBit z != Bool.xor (signBit x) (signBit y)
          isSNaN x || isSNaN y || isSNaN z ||
            invalidProduct || (!hasNaN && oppositeInfiniteAddend) := by
  cases hx : toDyadic? x <;> cases hy : toDyadic? y <;>
    cases hz : toDyadic? z <;> simp [fmaWithStatus, hx, hy, hz]

/-- Finite nonzero division exposes exactly its scaled-rational rounding status. -/
theorem divWithStatus_of_toDyadic_nonzero
    {fmt : FloatFormat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (mode : IEEERoundingMode)
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hxnonzero : dx.significand ≠ 0) (hynonzero : dy.significand ≠ 0) :
    divWithStatus x y mode =
      let sign := Bool.xor dx.negative dy.negative
      let exponentDifference := dx.exponent - dy.exponent
      let value :=
        roundRatWithRoundingScaled fmt mode sign dx.significand dy.significand
          exponentDifference
      { value
        status :=
          rationalRoundingStatusScaled fmt mode sign dx.significand dy.significand
            exponentDifference value } := by
  simp [divWithStatus, hx, hy, hxnonzero, hynonzero]

/--
Complete invalid-status classification for division.

The finite branch distinguishes zero-over-zero, exact zero, and nonzero rational rounding.
Exceptional operands use the signaling-NaN and infinity-over-infinity rules.
-/
theorem divWithStatus_invalid
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    (divWithStatus x y mode).status.invalid =
      match toDyadic? x, toDyadic? y with
      | some dx, some dy =>
          let sign := Bool.xor dx.negative dy.negative
          if dy.significand == 0 then
            dx.significand == 0
          else if dx.significand == 0 then
            false
          else
            let exponentDifference := dx.exponent - dy.exponent
            let value :=
              roundRatWithRoundingScaled fmt mode sign dx.significand dy.significand
                exponentDifference
            !rationalRoundingOverflowsScaled fmt mode sign dx.significand dy.significand
                exponentDifference &&
              !isFinite value && !isInf value
      | _, _ =>
          isSNaN x || isSNaN y ||
            (!(isNaN x || isNaN y) && (isInf x && isInf y)) := by
  cases hx : toDyadic? x with
  | none =>
      cases hy : toDyadic? y with
      | none =>
          simp only [hx, hy, divWithStatus, outcomeWithInvalid_invalid]
      | some dy =>
          simp only [hx, hy, divWithStatus, outcomeWithInvalid_invalid]
  | some dx =>
      cases hy : toDyadic? y with
      | none =>
          simp only [hx, hy, divWithStatus, outcomeWithInvalid_invalid]
      | some dy =>
          by_cases hxzero : dx.significand = 0 <;>
            by_cases hyzero : dy.significand = 0 <;>
            simp [divWithStatus, hx, hy, hxzero, hyzero, IEEEStatus.clear]

/-- Division raises divide-by-zero exactly for a finite nonzero numerator over finite zero. -/
theorem divWithStatus_divideByZero
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    (divWithStatus x y mode).status.divideByZero =
      match toDyadic? x, toDyadic? y with
      | some dx, some dy => dx.significand != 0 && dy.significand == 0
      | _, _ => false := by
  cases hx : toDyadic? x with
  | none =>
      cases hy : toDyadic? y <;> {
        simp only [divWithStatus, hx, hy, outcomeWithInvalid_divideByZero]
      }
  | some dx =>
      cases hy : toDyadic? y with
      | none =>
          simp only [divWithStatus, hx, hy, outcomeWithInvalid_divideByZero]
      | some dy =>
          by_cases hxzero : dx.significand = 0 <;>
            by_cases hyzero : dy.significand = 0 <;>
            simp [divWithStatus, hx, hy, hxzero, hyzero, IEEEStatus.clear]

/-- Square root raises invalid exactly for an sNaN or a negative nonzero non-NaN input. -/
theorem sqrtWithStatus_invalid {fmt : FloatFormat}
    (x : Model fmt) (mode : IEEERoundingMode) :
    (sqrtWithStatus x mode).status.invalid =
      (isSNaN x || (!isNaN x && signBit x && !isZero x)) := by
  by_cases hnan : isNaN x = true
  · cases hsnan : isSNaN x <;>
      simp [sqrtWithStatus, hnan, hsnan]
  · have hnanFalse : isNaN x = false :=
      Bool.eq_false_of_not_eq_true hnan
    have hsnanFalse := isSNaN_eq_false_of_isNaN_eq_false x hnanFalse
    by_cases hzero : isZero x = true
    · simp [sqrtWithStatus, hnanFalse, hsnanFalse, hzero]
    · have hzeroFalse : isZero x = false :=
        Bool.eq_false_of_not_eq_true hzero
      by_cases hsign : signBit x = true
      · simp [sqrtWithStatus, hnanFalse, hsnanFalse, hzeroFalse, hsign]
      · have hsignFalse : signBit x = false :=
          Bool.eq_false_of_not_eq_true hsign
        by_cases hinf : isInf x = true
        · simp [sqrtWithStatus, hnanFalse, hsnanFalse, hzeroFalse, hsignFalse,
            hinf]
        · have hinfFalse : isInf x = false :=
            Bool.eq_false_of_not_eq_true hinf
          simp [sqrtWithStatus, hnanFalse, hsnanFalse, hzeroFalse, hsignFalse,
            hinfFalse]

/-- Dividing two finite zeros raises invalid. -/
theorem divWithStatus_invalid_of_zero_div_zero {fmt : FloatFormat}
    {x y : Model fmt} {dx dy : Numerics.Dyadic} {mode : IEEERoundingMode}
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hxzero : dx.significand = 0) (hyzero : dy.significand = 0) :
    (divWithStatus x y mode).status.invalid = true := by
  simp [divWithStatus, hx, hy, hxzero, hyzero]

/-- Dividing a finite nonzero value by a finite zero raises divide-by-zero. -/
theorem divWithStatus_divideByZero_of_nonzero_div_zero {fmt : FloatFormat}
    {x y : Model fmt} {dx dy : Numerics.Dyadic} {mode : IEEERoundingMode}
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hxnonzero : dx.significand ≠ 0) (hyzero : dy.significand = 0) :
    (divWithStatus x y mode).status.divideByZero = true := by
  simp [divWithStatus, hx, hy, hxnonzero, hyzero]

/-- The square root of a negative nonzero non-NaN value raises invalid. -/
theorem sqrtWithStatus_invalid_of_negative_nonzero {fmt : FloatFormat}
    {x : Model fmt} {mode : IEEERoundingMode}
    (hnan : isNaN x = false) (hnegative : signBit x = true) (hnonzero : isZero x = false) :
    (sqrtWithStatus x mode).status.invalid = true := by
  simp [sqrtWithStatus, hnan, hnegative, hnonzero]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
