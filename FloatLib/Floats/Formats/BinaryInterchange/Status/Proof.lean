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
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SqrtSemantics
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.SquareRoot

/-!
# Correctness of IEEE exception status

The executable status kernels in `Status.Runtime` satisfy cross-flag invariants and
operation-level specifications. Import `BinaryInterchange.Status` for the combined public
interface.

The rounding-status classifiers compare an exact dyadic or scaled rational with the supplied
rounded value. Operation wrappers compute that exact witness alongside the value-only operation.
This file proves cross-flag invariants, preservation of the ordinary result, real-order tininess
boundaries, and operation-specific invalid and divide-by-zero conditions. On a positive finite
input, square root raises `inexact` exactly when its delivered value is not the real square root
(`sqrt_inexact_iff`).
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

Both gaps are one `2^(minSubnormalExponent - 2)` step. The equalities pin down the
quarter-subnormal offset used by nearest-even and rule out an off-by-one significand or exponent
in the three executable boundary constants.
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

An already tiny encoding is accepted immediately. Otherwise both nearest modes use the underflow
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
          | .nearest | .nearestAway =>
              ({ exact with negative := false } : Numerics.Dyadic).toReal <
                (underflowMidpoint fmt).toReal
          | .towardZero =>
              ({ exact with negative := false } : Numerics.Dyadic).toReal <
                (minNormalDyadic fmt).toReal
          | .up | .down | .away =>
              if mode.roundsAwayFromZero exact.negative then
                ({ exact with negative := false } : Numerics.Dyadic).toReal ≤
                  (underflowPredecessor fmt).toReal
              else
                ({ exact with negative := false } : Numerics.Dyadic).toReal <
                  (minNormalDyadic fmt).toReal) := by
  cases hrounded : isTinyAfterRounding rounded with
  | false =>
      cases mode <;> cases hnegative : exact.negative <;>
        simp [dyadicIsTinyAfterRounding, hrounded, IEEERoundingMode.roundsAwayFromZero,
          hnegative, cmpDyadic_lt_iff, cmpDyadic_gt_iff]
  | true =>
      simp [dyadicIsTinyAfterRounding, hrounded]

/-- Nearest-away rounding detects tininess at the same boundary as nearest-even rounding. -/
theorem dyadicIsTinyAfterRounding_nearestAway (fmt : FloatFormat) (exact : Numerics.Dyadic)
    (rounded : Model fmt) :
    dyadicIsTinyAfterRounding fmt .nearestAway exact rounded =
      dyadicIsTinyAfterRounding fmt .nearest exact rounded :=
  rfl

/-- Nearest-away rounding detects tininess at the same boundary as nearest-even rounding. -/
theorem rationalIsTinyAfterRoundingScaled_nearestAway (fmt : FloatFormat) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (rounded : Model fmt) :
    rationalIsTinyAfterRoundingScaled fmt .nearestAway sign numerator denominator exponent
        rounded =
      rationalIsTinyAfterRoundingScaled fmt .nearest sign numerator denominator exponent
        rounded :=
  rfl

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
          | .nearest | .nearestAway =>
              scaledRatToReal numerator denominator exponent <
                (underflowMidpoint fmt).toReal
          | .towardZero =>
              scaledRatToReal numerator denominator exponent <
                (minNormalDyadic fmt).toReal
          | .up | .down | .away =>
              if mode.roundsAwayFromZero sign then
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
      | nearest | nearestAway =>
          simp [rationalIsTinyAfterRoundingScaled, hrounded, IEEERoundingMode.roundsAwayFromZero]
          rw [hmidpointComparison]
          cases hcomparison : compare
              (scaledRatToReal numerator denominator exponent)
              (underflowMidpoint fmt).toReal <;>
            simp_all [compare_lt_iff_lt, compare_gt_iff_gt, le_of_lt]
      | away =>
          simp [rationalIsTinyAfterRoundingScaled, hrounded, IEEERoundingMode.roundsAwayFromZero]
          rw [hpredecessorComparison]
          cases hcomparison : compare
              (scaledRatToReal numerator denominator exponent)
              (underflowPredecessor fmt).toReal <;>
            simp_all [compare_lt_iff_lt, compare_gt_iff_gt, le_of_lt]
      | towardZero =>
          simp [rationalIsTinyAfterRoundingScaled, hrounded, IEEERoundingMode.roundsAwayFromZero]
          rw [hnormalComparison]
          cases hcomparison : compare
              (scaledRatToReal numerator denominator exponent)
              (minNormalDyadic fmt).toReal <;>
            simp_all [compare_lt_iff_lt, compare_gt_iff_gt, le_of_lt]
      | up =>
          cases sign with
          | false =>
              simp [rationalIsTinyAfterRoundingScaled, hrounded,
                IEEERoundingMode.roundsAwayFromZero]
              rw [hpredecessorComparison]
              cases hcomparison : compare
                  (scaledRatToReal numerator denominator exponent)
                  (underflowPredecessor fmt).toReal <;>
                simp_all [compare_lt_iff_lt, compare_gt_iff_gt, le_of_lt]
          | true =>
              simp [rationalIsTinyAfterRoundingScaled, hrounded,
                IEEERoundingMode.roundsAwayFromZero]
              rw [hnormalComparison]
              cases hcomparison : compare
                  (scaledRatToReal numerator denominator exponent)
                  (minNormalDyadic fmt).toReal <;>
                simp_all [compare_lt_iff_lt, compare_gt_iff_gt, le_of_lt]
      | down =>
          cases sign with
          | false =>
              simp [rationalIsTinyAfterRoundingScaled, hrounded,
                IEEERoundingMode.roundsAwayFromZero]
              rw [hnormalComparison]
              cases hcomparison : compare
                  (scaledRatToReal numerator denominator exponent)
                  (minNormalDyadic fmt).toReal <;>
                simp_all [compare_lt_iff_lt, compare_gt_iff_gt, le_of_lt]
          | true =>
              simp [rationalIsTinyAfterRoundingScaled, hrounded,
                IEEERoundingMode.roundsAwayFromZero]
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

/-- `outcomeWithInvalid` records its supplied invalid-operation condition. -/
@[simp] theorem outcomeWithInvalid_invalid {fmt : FloatFormat}
    (value : Model fmt) (invalid : Bool) :
    (outcomeWithInvalid value invalid).status.invalid = invalid := by
  cases invalid <;> rfl

/-- `outcomeWithInvalid` never raises divide-by-zero. -/
@[simp] theorem outcomeWithInvalid_divideByZero {fmt : FloatFormat}
    (value : Model fmt) (invalid : Bool) :
    (outcomeWithInvalid value invalid).status.divideByZero = false := by
  cases invalid <;> rfl

/--
`outcomeWithInvalid` carries the exceptional-result ternary convention `.eq`.

This is a convention for NaNs, exact infinities, and placeholders, not a statement that the value
equals an exact real result.
-/
@[simp] theorem outcomeWithInvalid_ternary {fmt : FloatFormat}
    (value : Model fmt) (invalid : Bool) :
    (outcomeWithInvalid value invalid).ternary = .eq := rfl

/-- A dyadic rounding outcome delivers the value it was given. -/
@[simp] theorem dyadicRoundingOutcome_value (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (value : Model fmt) :
    (dyadicRoundingOutcome fmt mode exact value).value = value :=
  rfl

/-- The status of a dyadic rounding outcome is `dyadicRoundingStatus`. -/
@[simp] theorem dyadicRoundingOutcome_status (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (value : Model fmt) :
    (dyadicRoundingOutcome fmt mode exact value).status =
      dyadicRoundingStatus fmt mode exact value :=
  rfl

/-- The ternary value of a dyadic rounding outcome is `dyadicTernary`. -/
@[simp] theorem dyadicRoundingOutcome_ternary (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (value : Model fmt) :
    (dyadicRoundingOutcome fmt mode exact value).ternary = dyadicTernary exact value :=
  rfl

/-- A scaled rational rounding outcome delivers the value it was given. -/
@[simp] theorem rationalRoundingOutcomeScaled_value (fmt : FloatFormat)
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat) (exponent : Int)
    (value : Model fmt) :
    (rationalRoundingOutcomeScaled fmt mode sign numerator denominator exponent value).value =
      value :=
  rfl

/-- The status of a scaled rational rounding outcome is `rationalRoundingStatusScaled`. -/
@[simp] theorem rationalRoundingOutcomeScaled_status (fmt : FloatFormat)
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat) (exponent : Int)
    (value : Model fmt) :
    (rationalRoundingOutcomeScaled fmt mode sign numerator denominator exponent value).status =
      rationalRoundingStatusScaled fmt mode sign numerator denominator exponent value :=
  rfl

/-- The ternary value of a scaled rational rounding outcome is `rationalTernaryScaled`. -/
@[simp] theorem rationalRoundingOutcomeScaled_ternary (fmt : FloatFormat)
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat) (exponent : Int)
    (value : Model fmt) :
    (rationalRoundingOutcomeScaled fmt mode sign numerator denominator exponent value).ternary =
      rationalTernaryScaled sign numerator denominator exponent value :=
  rfl

/-! ## Ternary values -/

/-- A finite value denotes the real value of its decoded dyadic. -/
theorem toReal_eq_toReal_finiteDyadic {fmt : FloatFormat} {x : Model fmt}
    (hfinite : isFinite x = true) :
    toReal x = (finiteDyadic x hfinite).toReal := by
  have hdecode : toDyadic? x = some (finiteDyadic x hfinite) := by
    simp [finiteDyadic]
  rw [toReal_eq, hdecode]

/-- For a finite delivery, the dyadic ternary value is the real comparison with the exact value. -/
theorem dyadicTernary_eq_compare {fmt : FloatFormat} (exact : Numerics.Dyadic)
    {rounded : Model fmt} (hfinite : isFinite rounded = true) :
    dyadicTernary exact rounded = compare (toReal rounded) exact.toReal := by
  rw [dyadicTernary, dite_eq_left hfinite, cmpDyadic_eq_compare,
    toReal_eq_toReal_finiteDyadic hfinite]

/-- A finite delivery has the dyadic ternary value `.lt` exactly when it is below the exact one. -/
theorem dyadicTernary_eq_lt_iff {fmt : FloatFormat} (exact : Numerics.Dyadic)
    {rounded : Model fmt} (hfinite : isFinite rounded = true) :
    dyadicTernary exact rounded = .lt ↔ toReal rounded < exact.toReal := by
  rw [dyadicTernary_eq_compare exact hfinite, compare_lt_iff_lt]

/-- A finite delivery has the dyadic ternary value `.eq` exactly when it equals the exact value. -/
theorem dyadicTernary_eq_eq_iff {fmt : FloatFormat} (exact : Numerics.Dyadic)
    {rounded : Model fmt} (hfinite : isFinite rounded = true) :
    dyadicTernary exact rounded = .eq ↔ toReal rounded = exact.toReal := by
  rw [dyadicTernary_eq_compare exact hfinite, compare_eq_iff_eq]

/-- A finite delivery has the dyadic ternary value `.gt` exactly when it is above the exact one. -/
theorem dyadicTernary_eq_gt_iff {fmt : FloatFormat} (exact : Numerics.Dyadic)
    {rounded : Model fmt} (hfinite : isFinite rounded = true) :
    dyadicTernary exact rounded = .gt ↔ exact.toReal < toReal rounded := by
  rw [dyadicTernary_eq_compare exact hfinite, compare_gt_iff_gt]

/--
A non-finite delivery has the ternary value given by the sign of the exact value, the overflow
convention of `dyadicTernary`.
-/
theorem dyadicTernary_of_isFinite_eq_false {fmt : FloatFormat} (exact : Numerics.Dyadic)
    {rounded : Model fmt} (hfinite : isFinite rounded = false) :
    dyadicTernary exact rounded = if exact.negative then .lt else .gt := by
  simp [dyadicTernary, hfinite]

/--
For a finite delivery and a nonzero denominator, the rational ternary value is the real comparison
with the exact signed rational.
-/
theorem rationalTernaryScaled_eq_compare {fmt : FloatFormat} (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) {rounded : Model fmt}
    (hdenominator : denominator ≠ 0) (hfinite : isFinite rounded = true) :
    rationalTernaryScaled sign numerator denominator exponent rounded =
      compare (toReal rounded) (signedScaledRatToReal sign numerator denominator exponent) := by
  rw [rationalTernaryScaled, dite_eq_left hfinite,
    compareDyadicScaled?_eq_compare sign numerator denominator exponent _ hdenominator,
    ← toReal_eq_toReal_finiteDyadic hfinite]
  rcases lt_trichotomy (toReal rounded)
      (signedScaledRatToReal sign numerator denominator exponent) with hless | hequal | hgreater
  · rw [compare_lt_iff_lt.mpr hless, compare_gt_iff_gt.mpr hless]
    rfl
  · rw [hequal]
    simp
  · rw [compare_gt_iff_gt.mpr hgreater, compare_lt_iff_lt.mpr hgreater]
    rfl

/-- A finite delivery has the rational ternary value `.lt` exactly when it is below the rational. -/
theorem rationalTernaryScaled_eq_lt_iff {fmt : FloatFormat} (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) {rounded : Model fmt}
    (hdenominator : denominator ≠ 0) (hfinite : isFinite rounded = true) :
    rationalTernaryScaled sign numerator denominator exponent rounded = .lt ↔
      toReal rounded < signedScaledRatToReal sign numerator denominator exponent := by
  rw [rationalTernaryScaled_eq_compare sign numerator denominator exponent hdenominator hfinite,
    compare_lt_iff_lt]

/-- A finite delivery has the rational ternary value `.eq` exactly when it equals the rational. -/
theorem rationalTernaryScaled_eq_eq_iff {fmt : FloatFormat} (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) {rounded : Model fmt}
    (hdenominator : denominator ≠ 0) (hfinite : isFinite rounded = true) :
    rationalTernaryScaled sign numerator denominator exponent rounded = .eq ↔
      toReal rounded = signedScaledRatToReal sign numerator denominator exponent := by
  rw [rationalTernaryScaled_eq_compare sign numerator denominator exponent hdenominator hfinite,
    compare_eq_iff_eq]

/-- A finite delivery has the rational ternary value `.gt` exactly when it is above the rational. -/
theorem rationalTernaryScaled_eq_gt_iff {fmt : FloatFormat} (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) {rounded : Model fmt}
    (hdenominator : denominator ≠ 0) (hfinite : isFinite rounded = true) :
    rationalTernaryScaled sign numerator denominator exponent rounded = .gt ↔
      signedScaledRatToReal sign numerator denominator exponent < toReal rounded := by
  rw [rationalTernaryScaled_eq_compare sign numerator denominator exponent hdenominator hfinite,
    compare_gt_iff_gt]

/--
A non-finite delivery has the rational ternary value given by the sign of the exact rational, the
overflow convention of `rationalTernaryScaled`.
-/
theorem rationalTernaryScaled_of_isFinite_eq_false {fmt : FloatFormat} (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) {rounded : Model fmt}
    (hfinite : isFinite rounded = false) :
    rationalTernaryScaled sign numerator denominator exponent rounded =
      if sign then .lt else .gt := by
  simp [rationalTernaryScaled, hfinite]

/--
With denominator one, the rational ternary value is the dyadic ternary value of the same exact
number, so operations may use either representation of their exact result.
-/
theorem rationalTernaryScaled_eq_dyadicTernary {fmt : FloatFormat} (exact : Numerics.Dyadic)
    (rounded : Model fmt) :
    rationalTernaryScaled exact.negative exact.significand 1 exact.exponent rounded =
      dyadicTernary exact rounded := by
  cases hfinite : isFinite rounded
  · rw [rationalTernaryScaled_of_isFinite_eq_false _ _ _ _ hfinite,
      dyadicTernary_of_isFinite_eq_false exact hfinite]
  · rw [rationalTernaryScaled_eq_compare _ _ _ _ one_ne_zero hfinite,
      dyadicTernary_eq_compare exact hfinite]
    congr 1
    cases hnegative : exact.negative <;>
      simp [signedScaledRatToReal, scaledRatToReal, Numerics.Dyadic.toReal,
        Numerics.Dyadic.signedSignificand, hnegative, bpow,
        FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/-- The exact-infinity ternary value is `.eq` exactly for the infinity itself. -/
theorem exactInfinityTernary_eq_eq_iff {fmt : FloatFormat} (negative : Bool)
    (value : Model fmt) :
    exactInfinityTernary negative value = .eq ↔
      isInf value = true ∧ signBit value = negative := by
  unfold exactInfinityTernary
  cases hinf : isInf value <;> cases hsign : signBit value <;> cases negative <;> simp

/--
Any delivery other than the exact infinity itself has the exact-infinity ternary value `.lt` for
`+∞` and `.gt` for `-∞`. For a saturated finite value this is the order, and for the overflow NaN
of a format without infinities it is the convention of `IEEEOutcome.ternary`.
-/
theorem exactInfinityTernary_of_not_infinity {fmt : FloatFormat} (negative : Bool)
    {value : Model fmt} (hvalue : ¬(isInf value = true ∧ signBit value = negative)) :
    exactInfinityTernary negative value = if negative then .gt else .lt := by
  unfold exactInfinityTernary
  rw [ite_eq_right (by simpa [Bool.and_eq_true, beq_iff_eq] using hvalue)]

/-- Squaring is strictly monotone on nonnegative reals, so it preserves comparisons there. -/
private theorem compare_mul_self_eq_compare {left right : ℝ} (hleft : 0 ≤ left)
    (hright : 0 ≤ right) :
    compare (left * left) (right * right) = compare left right := by
  rcases lt_trichotomy left right with hless | hequal | hgreater
  · rw [compare_lt_iff_lt.mpr hless,
      compare_lt_iff_lt.mpr (mul_self_lt_mul_self hleft hless)]
  · subst hequal
    simp
  · rw [compare_gt_iff_gt.mpr hgreater,
      compare_gt_iff_gt.mpr (mul_self_lt_mul_self hright hgreater)]

/-- A finite delivery is compared with the radicand through the exact square of its decoding. -/
theorem dyadicSqrtTernary_of_isFinite {fmt : FloatFormat} (radicand : Numerics.Dyadic)
    {rounded : Model fmt} (hfinite : isFinite rounded = true) :
    dyadicSqrtTernary radicand rounded =
      cmpDyadic
        { negative := false
          significand :=
            (finiteDyadic rounded hfinite).significand *
              (finiteDyadic rounded hfinite).significand
          exponent :=
            (finiteDyadic rounded hfinite).exponent + (finiteDyadic rounded hfinite).exponent }
        radicand := by
  obtain ⟨actual, hactual⟩ := exists_toDyadic?_of_isFinite hfinite
  simp [dyadicSqrtTernary, hactual]

/-- A non-finite delivery has the square-root ternary value `.gt`. -/
theorem dyadicSqrtTernary_of_isFinite_eq_false {fmt : FloatFormat}
    (radicand : Numerics.Dyadic) {rounded : Model fmt} (hfinite : isFinite rounded = false) :
    dyadicSqrtTernary radicand rounded = .gt := by
  have hnone : toDyadic? rounded = none := by
    cases hdecode : toDyadic? rounded with
    | none => rfl
    | some actual =>
        rw [isFinite_eq_true_of_toDyadic?_some hdecode] at hfinite
        contradiction
  simp [dyadicSqrtTernary, hnone]

/--
For a finite nonnegative delivery and a nonnegative radicand, the square-root ternary value is the
real comparison of the delivered value with the exact square root.
-/
theorem dyadicSqrtTernary_eq_compare {fmt : FloatFormat} (radicand : Numerics.Dyadic)
    {rounded : Model fmt} (hfinite : isFinite rounded = true)
    (hrounded : 0 ≤ toReal rounded) (hradicand : 0 ≤ radicand.toReal) :
    dyadicSqrtTernary radicand rounded =
      compare (toReal rounded) (Real.sqrt radicand.toReal) := by
  rw [dyadicSqrtTernary_of_isFinite radicand hfinite, cmpDyadic_eq_compare]
  have hsquare :
      ({ negative := false
         significand :=
           (finiteDyadic rounded hfinite).significand *
             (finiteDyadic rounded hfinite).significand
         exponent :=
           (finiteDyadic rounded hfinite).exponent +
             (finiteDyadic rounded hfinite).exponent } : Numerics.Dyadic).toReal =
        toReal rounded * toReal rounded := by
    rw [toReal_eq_toReal_finiteDyadic hfinite]
    cases hnegative : (finiteDyadic rounded hfinite).negative <;>
      simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hnegative,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] <;>
      ring
  rw [hsquare]
  calc compare (toReal rounded * toReal rounded) radicand.toReal
      = compare (toReal rounded * toReal rounded)
          (Real.sqrt radicand.toReal * Real.sqrt radicand.toReal) := by
        rw [Real.mul_self_sqrt hradicand]
    _ = compare (toReal rounded) (Real.sqrt radicand.toReal) :=
        compare_mul_self_eq_compare hrounded (Real.sqrt_nonneg _)

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

/-- Addition with `status := true` delivers the value of addition in the same direction. -/
@[simp] theorem value_add {fmt : FloatFormat}
    (x y : Model fmt) (mode : IEEERoundingMode) :
    (add x y (mode := mode) (status := true)).value = add x y (mode := mode) := by
  rw [← Internal.Status.add_eq, ← Internal.Directed.add_eq]
  unfold Internal.Status.add
  split <;> simp

/-- Subtraction with `status := true` delivers the value of subtraction in the same direction. -/
@[simp] theorem value_sub {fmt : FloatFormat}
    (x y : Model fmt) (mode : IEEERoundingMode) :
    (sub x y (mode := mode) (status := true)).value = sub x y (mode := mode) := by
  rw [← Internal.Directed.sub_eq]
  exact (value_add x (neg y) mode).trans (Internal.Directed.add_eq mode x (neg y)).symm

/--
Multiplication with `status := true` delivers the value of multiplication in the same direction.
-/
@[simp] theorem value_mul {fmt : FloatFormat}
    (x y : Model fmt) (mode : IEEERoundingMode) :
    (mul x y (mode := mode) (status := true)).value = mul x y (mode := mode) := by
  rw [← Internal.Status.mul_eq, ← Internal.Directed.mul_eq]
  unfold Internal.Status.mul
  split <;> simp

/-- Division with `status := true` delivers the value of division in the same direction. -/
@[simp] theorem value_div {fmt : FloatFormat}
    (x y : Model fmt) (mode : IEEERoundingMode) :
    (div x y (mode := mode) (status := true)).value = div x y (mode := mode) := by
  rw [← Internal.Status.div_eq, ← Internal.Directed.div_eq]
  cases mode <;> unfold Internal.Status.div Internal.Directed.div
  · split
    · rename_i dx dy hx hy
      simp [Internal.Nearest.div, DivBackend.word_eq_spec, Spec.div, hx, hy,
        Internal.Directed.roundRatScaled]
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

/-- FMA with `status := true` delivers the value of FMA in the same direction. -/
@[simp] theorem value_fma {fmt : FloatFormat}
    (x y z : Model fmt) (mode : IEEERoundingMode) :
    (fma x y z (mode := mode) (status := true)).value = fma x y z (mode := mode) := by
  rw [← Internal.Status.fma_eq, ← Internal.Directed.fma_eq]
  unfold Internal.Status.fma
  split <;> simp

/--
Square root with `status := true` delivers the value of square root in the same direction.
-/
@[simp] theorem value_sqrt {fmt : FloatFormat}
    (x : Model fmt) (mode : IEEERoundingMode) :
    (sqrt x (mode := mode) (status := true)).value = sqrt x (mode := mode) := by
  rw [← Internal.Status.sqrt_eq, ← Internal.Directed.sqrt_eq]
  unfold Internal.Status.sqrt
  dsimp only
  split
  · split <;> simp [outcomeWithInvalid]
  · split
    · simp [outcomeWithInvalid]
    · split <;> simp [outcomeWithInvalid]

/-! ## Operation-specific exceptional status -/

/-- Finite addition reports its dyadic rounding status and ternary value. -/
theorem add_status_of_toDyadic
    {fmt : FloatFormat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (mode : IEEERoundingMode)
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy) :
    add x y (mode := mode) (status := true) =
      let exact := addDyadic dx dy
      let value := add x y (mode := mode)
      { value
        status := dyadicRoundingStatus fmt mode exact value
        ternary := dyadicTernary exact value } := by
  simp [← Internal.Status.add_eq, Internal.Status.add, Internal.Directed.add_eq,
    dyadicRoundingOutcome, hx, hy]

/--
Complete invalid-status classification for addition.

Finite operands take the rounded result's classification. Exceptional operands raise invalid
exactly for a signaling NaN or opposite-signed infinities when no NaN was supplied.
-/
theorem add_invalid
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    (add x y (mode := mode) (status := true)).status.invalid =
      match toDyadic? x, toDyadic? y with
      | some dx, some dy =>
          let exact := addDyadic dx dy
          let value := add x y (mode := mode)
          !dyadicRoundingOverflows fmt mode exact &&
            !isFinite value && !isInf value
      | _, _ =>
          isSNaN x || isSNaN y ||
            (!(isNaN x || isNaN y) &&
              (isInf x && isInf y && signBit x != signBit y)) := by
  cases hx : toDyadic? x <;> cases hy : toDyadic? y <;>
    simp [← Internal.Status.add_eq, Internal.Status.add, Internal.Directed.add_eq, hx, hy]

/-- Finite multiplication reports its dyadic rounding status and ternary value. -/
theorem mul_status_of_toDyadic
    {fmt : FloatFormat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (mode : IEEERoundingMode)
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy) :
    mul x y (mode := mode) (status := true) =
      let exact : Numerics.Dyadic :=
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      let value := mul x y (mode := mode)
      { value
        status := dyadicRoundingStatus fmt mode exact value
        ternary := dyadicTernary exact value } := by
  simp [← Internal.Status.mul_eq, Internal.Status.mul, Internal.Directed.mul_eq,
    dyadicRoundingOutcome, hx, hy]

/--
Complete invalid-status classification for multiplication.

Finite operands take the rounded result's classification. Exceptional operands raise invalid
exactly for a signaling NaN or an infinity-times-zero operation without an input NaN.
-/
theorem mul_invalid
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    (mul x y (mode := mode) (status := true)).status.invalid =
      match toDyadic? x, toDyadic? y with
      | some dx, some dy =>
          let exact : Numerics.Dyadic :=
            { negative := Bool.xor dx.negative dy.negative
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent }
          let value := mul x y (mode := mode)
          !dyadicRoundingOverflows fmt mode exact &&
            !isFinite value && !isInf value
      | _, _ =>
          isSNaN x || isSNaN y ||
            (!(isNaN x || isNaN y) &&
              ((isInf x && isZero y) || (isInf y && isZero x))) := by
  cases hx : toDyadic? x <;> cases hy : toDyadic? y <;>
    simp [← Internal.Status.mul_eq, Internal.Status.mul, Internal.Directed.mul_eq, hx, hy]

/-- Finite FMA reports its dyadic rounding status and ternary value. -/
theorem fma_status_of_toDyadic
    {fmt : FloatFormat} {x y z : Model fmt} {dx dy dz : Numerics.Dyadic}
    (mode : IEEERoundingMode)
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hz : toDyadic? z = some dz) :
    fma x y z (mode := mode) (status := true) =
      let product : Numerics.Dyadic :=
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      let exact := addDyadic product dz
      let value := fma x y z (mode := mode)
      { value
        status := dyadicRoundingStatus fmt mode exact value
        ternary := dyadicTernary exact value } := by
  simp [← Internal.Status.fma_eq, Internal.Status.fma, Internal.Directed.fma_eq,
    dyadicRoundingOutcome, hx, hy, hz]

/--
Complete invalid-status classification for fused multiply-add.

Finite operands take the singly rounded result's classification. Exceptional operands use the
IEEE signaling-NaN, infinity-times-zero, and opposite-infinity rules. For the
implementation-defined quiet-NaN case, this library raises invalid for infinity times zero even
when the addend is a quiet NaN, while an input NaN suppresses the opposite-infinity condition.
-/
theorem fma_invalid
    {fmt : FloatFormat} (x y z : Model fmt) (mode : IEEERoundingMode) :
    (fma x y z (mode := mode) (status := true)).status.invalid =
      match toDyadic? x, toDyadic? y, toDyadic? z with
      | some dx, some dy, some dz =>
          let product : Numerics.Dyadic :=
            { negative := Bool.xor dx.negative dy.negative
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent }
          let exact := addDyadic product dz
          let value := fma x y z (mode := mode)
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
    cases hz : toDyadic? z <;> simp [← Internal.Status.fma_eq, Internal.Status.fma,
      Internal.Directed.fma_eq, hx, hy, hz]

/--
Finite nonzero division reports its scaled-rational rounding status and ternary value.
-/
theorem div_status_of_toDyadic_nonzero
    {fmt : FloatFormat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (mode : IEEERoundingMode)
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hxnonzero : dx.significand ≠ 0) (hynonzero : dy.significand ≠ 0) :
    div x y (mode := mode) (status := true) =
      let sign := Bool.xor dx.negative dy.negative
      let exponentDifference := dx.exponent - dy.exponent
      let value :=
        Internal.Directed.roundRatScaled fmt mode sign dx.significand dy.significand
          exponentDifference
      { value
        status :=
          rationalRoundingStatusScaled fmt mode sign dx.significand dy.significand
            exponentDifference value
        ternary :=
          rationalTernaryScaled sign dx.significand dy.significand exponentDifference value } := by
  simp [← Internal.Status.div_eq, Internal.Status.div, rationalRoundingOutcomeScaled, hx, hy,
    hxnonzero, hynonzero]

/--
Complete invalid-status classification for division.

The finite branch distinguishes zero-over-zero, exact zero, and nonzero rational rounding.
Exceptional operands use the signaling-NaN and infinity-over-infinity rules.
-/
theorem div_invalid
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    (div x y (mode := mode) (status := true)).status.invalid =
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
              Internal.Directed.roundRatScaled fmt mode sign dx.significand dy.significand
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
          simp only [hx, hy, ← Internal.Status.div_eq, Internal.Status.div,
            Internal.Directed.div_eq, outcomeWithInvalid_invalid]
      | some dy =>
          simp only [hx, hy, ← Internal.Status.div_eq, Internal.Status.div,
            Internal.Directed.div_eq, outcomeWithInvalid_invalid]
  | some dx =>
      cases hy : toDyadic? y with
      | none =>
          simp only [hx, hy, ← Internal.Status.div_eq, Internal.Status.div,
            Internal.Directed.div_eq, outcomeWithInvalid_invalid]
      | some dy =>
          by_cases hxzero : dx.significand = 0 <;>
            by_cases hyzero : dy.significand = 0 <;>
            simp [← Internal.Status.div_eq, Internal.Status.div, hx, hy, hxzero, hyzero,
              Numerics.IEEEStatus.clear]

/-- Division raises divide-by-zero exactly for a finite nonzero numerator over finite zero. -/
theorem div_divideByZero
    {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    (div x y (mode := mode) (status := true)).status.divideByZero =
      match toDyadic? x, toDyadic? y with
      | some dx, some dy => dx.significand != 0 && dy.significand == 0
      | _, _ => false := by
  cases hx : toDyadic? x with
  | none =>
      cases hy : toDyadic? y <;> {
        simp only [← Internal.Status.div_eq, Internal.Status.div, Internal.Directed.div_eq, hx, hy,
          outcomeWithInvalid_divideByZero]
      }
  | some dx =>
      cases hy : toDyadic? y with
      | none =>
          simp only [← Internal.Status.div_eq, Internal.Status.div, Internal.Directed.div_eq, hx,
            hy, outcomeWithInvalid_divideByZero]
      | some dy =>
          by_cases hxzero : dx.significand = 0 <;>
            by_cases hyzero : dy.significand = 0 <;>
            simp [← Internal.Status.div_eq, Internal.Status.div, hx, hy, hxzero, hyzero,
              Numerics.IEEEStatus.clear]

/-! ### Square-root cases

Square root with `status := true` tests the sign bit first and decodes an input with a clear sign
bit once. The next theorems restate its outcome on NaNs, zeros, negative values, `+∞`, and
positive finite values. These cases cover every input.
-/

/--
When `fmt.fracWidth + 1 < fmt.exponentBias`, the square root of a nonzero decoded radicand never
lies below an underflow boundary. The least positive magnitude `2^minSubnormalExponent` exceeds
the square of `minNormal`, `2^(2 * minNormalExponent)`, and every boundary is at most `minNormal`.
-/
theorem dyadicSqrtIsTinyAfterRounding_eq_false {fmt : FloatFormat}
    (mode : IEEERoundingMode) (hformat : fmt.fracWidth + 1 < fmt.exponentBias)
    {x : Model fmt} {radicand : Numerics.Dyadic} (hx : toDyadic? x = some radicand)
    (hzero : radicand.significand ≠ 0) :
    dyadicSqrtIsTinyAfterRounding fmt mode radicand = false := by
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hmagnitude : (2 : ℝ) ^ fmt.minSubnormalExponent ≤
      ({ radicand with negative := false } : Numerics.Dyadic).toReal := by
    have hexponent := minSubnormalExponent_le_toDyadic? x hx
    have hsignificand : (1 : ℝ) ≤ radicand.significand := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
    have hscale : (2 : ℝ) ^ fmt.minSubnormalExponent ≤ (2 : ℝ) ^ radicand.exponent :=
      zpow_le_zpow_right₀ htwo.le hexponent
    simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand, Bool.false_eq_true,
      ite_false, one_mul]
    change (2 : ℝ) ^ fmt.minSubnormalExponent ≤ (radicand.significand : ℝ) * 2 ^ radicand.exponent
    nlinarith [zpow_pos (by norm_num : (0 : ℝ) < 2) radicand.exponent]
  have hminNormal : (minNormalDyadic fmt).toReal * (minNormalDyadic fmt).toReal <
      (2 : ℝ) ^ fmt.minSubnormalExponent := by
    have hreal : (minNormalDyadic fmt).toReal =
        (2 : ℝ) ^ ((fmt.fracWidth : Int) + fmt.minSubnormalExponent) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
      simp only [minNormalDyadic, Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand,
        Bool.false_eq_true, ite_false, one_mul, pow2_eq_two_pow, Nat.cast_pow, Nat.cast_ofNat]
    rw [hreal, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    apply zpow_lt_zpow_right₀ htwo
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast]
    omega
  have hbelow : ∀ boundary : Numerics.Dyadic, boundary.negative = false →
      boundary.toReal ≤ (minNormalDyadic fmt).toReal →
      cmpDyadic { radicand with negative := false }
          { negative := false
            significand := boundary.significand * boundary.significand
            exponent := boundary.exponent + boundary.exponent } = .gt := by
    intro boundary hnegative hle
    rw [cmpDyadic_gt_iff]
    have hsquare :
        ({ negative := false
           significand := boundary.significand * boundary.significand
           exponent := boundary.exponent + boundary.exponent } : Numerics.Dyadic).toReal =
          boundary.toReal * boundary.toReal := by
      simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hnegative,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    have hnonnegative : 0 ≤ boundary.toReal := by
      simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand, hnegative,
        Bool.false_eq_true, ite_false, one_mul]
      exact mul_nonneg (Nat.cast_nonneg _) (bpow_nonneg _)
    rw [hsquare]
    calc boundary.toReal * boundary.toReal
        ≤ (minNormalDyadic fmt).toReal * (minNormalDyadic fmt).toReal :=
          mul_self_le_mul_self hnonnegative hle
      _ < (2 : ℝ) ^ fmt.minSubnormalExponent := hminNormal
      _ ≤ _ := hmagnitude
  obtain ⟨hpredecessor, hmidpoint⟩ := underflow_boundary_gaps fmt
  have hstep : 0 < FloatLib.Floats.Formats.Flocq.bpow
      Numerics.binaryRadix (fmt.minSubnormalExponent - 2) := bpow_pos _
  cases mode <;> simp only [dyadicSqrtIsTinyAfterRounding]
  · rw [hbelow _ rfl (by linarith)]
  · rw [hbelow _ rfl (by linarith)]
  · rw [hbelow _ rfl le_rfl]
  · rw [hbelow _ rfl (by linarith)]
  · rw [hbelow _ rfl le_rfl]
  · rw [hbelow _ rfl (by linarith)]

/-- A NaN delivers the square-root value and raises invalid only when it is signaling. -/
theorem sqrt_status_of_isNaN {fmt : FloatFormat} {x : Model fmt} (mode : IEEERoundingMode)
    (hnan : isNaN x = true) :
    sqrt x (mode := mode) (status := true) =
      outcomeWithInvalid (sqrt x (mode := mode)) (isSNaN x) := by
  cases hsign : signBit x
  · simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hsign,
    toDyadic?_eq_none_of_isNaN hnan]
  · simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hsign, hnan]

/-- A zero of either sign delivers the square-root value and raises nothing. -/
theorem sqrt_status_of_isZero {fmt : FloatFormat} {x : Model fmt} (mode : IEEERoundingMode)
    (hzero : isZero x = true) :
    sqrt x (mode := mode) (status := true) = outcomeWithInvalid (sqrt x (mode := mode)) false := by
  have hnan :=
    isNaN_eq_false_of_isFinite_eq_true x (isFinite_eq_true_of_isZero_eq_true x hzero)
  cases hsign : signBit x
  · simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hsign,
    toDyadic?_eq_zero_of_isZero_eq_true x hzero]
  · simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hsign, hnan,
    hzero]

/-- A negative value that is neither a NaN nor a zero, `-∞` included, raises invalid. -/
theorem sqrt_status_of_signBit {fmt : FloatFormat} {x : Model fmt} (mode : IEEERoundingMode)
    (hnan : isNaN x = false) (hzero : isZero x = false) (hsign : signBit x = true) :
    sqrt x (mode := mode) (status := true) = outcomeWithInvalid (sqrt x (mode := mode)) true := by
  simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hnan, hzero,
    hsign]

/-- `+∞` delivers the square-root value and raises nothing. -/
theorem sqrt_status_of_isInf {fmt : FloatFormat} {x : Model fmt} (mode : IEEERoundingMode)
    (hinf : isInf x = true) (hsign : signBit x = false) :
    sqrt x (mode := mode) (status := true) = outcomeWithInvalid (sqrt x (mode := mode)) false := by
  have hnone : toDyadic? x = none := by
    cases hdecode : toDyadic? x with
    | none => rfl
    | some exact =>
        rw [isInf_eq_false_of_toDyadic?_some hdecode] at hinf
        contradiction
  have hsnan := isSNaN_eq_false_of_isNaN_eq_false x (isNaN_eq_false_of_isInf_eq_true x hinf)
  simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hsign, hnone,
    hsnan]

/--
On a positive finite input, the ternary value compares the squared delivery with the radicand, the
result is inexact exactly when that comparison is not `.eq`, and an inexact result underflows when
its encoding is zero or subnormal or its exact root lies below the underflow boundary.
-/
theorem sqrt_status_of_toDyadic {fmt : FloatFormat} {x : Model fmt} {exact : Numerics.Dyadic}
    (mode : IEEERoundingMode) (hx : toDyadic? x = some exact) (hzero : exact.significand ≠ 0)
    (hsign : exact.negative = false) :
    sqrt x (mode := mode) (status := true) =
      let value := sqrt x (mode := mode)
      let ternary := dyadicSqrtTernary exact value
      let inexact := ternary != .eq
      { value
        status :=
          { underflow :=
              inexact &&
                (isTinyAfterRounding value || dyadicSqrtIsTinyAfterRounding fmt mode exact)
            inexact }
        ternary } := by
  have hsignBit : signBit x = false := (sign_eq_signBit_of_toDyadic?_some hx).symm.trans hsign
  have hbeq : (exact.significand == 0) = false := by simpa using hzero
  simp only [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hsignBit,
    hx, hbeq, Bool.false_eq_true, ite_false]
  generalize dyadicSqrtTernary exact (sqrt x (mode := mode)) = ternary
  generalize isTinyAfterRounding (sqrt x (mode := mode)) = tiny
  by_cases hformat : fmt.fracWidth + 1 < fmt.exponentBias
  · rw [dyadicSqrtIsTinyAfterRounding_eq_false mode hformat hx hzero]
    cases ternary <;> cases tiny <;> simp [hformat]
  · cases ternary <;> cases tiny <;> simp [hformat]

/-- Square root raises invalid exactly for an sNaN or a negative nonzero non-NaN input. -/
theorem sqrt_invalid {fmt : FloatFormat}
    (x : Model fmt) (mode : IEEERoundingMode) :
    (sqrt x (mode := mode) (status := true)).status.invalid =
      (isSNaN x || (!isNaN x && signBit x && !isZero x)) := by
  by_cases hnan : isNaN x = true
  · rw [sqrt_status_of_isNaN mode hnan]
    simp [hnan]
  · have hnanFalse : isNaN x = false :=
      Bool.eq_false_of_not_eq_true hnan
    have hsnanFalse := isSNaN_eq_false_of_isNaN_eq_false x hnanFalse
    by_cases hzero : isZero x = true
    · rw [sqrt_status_of_isZero mode hzero]
      simp [hsnanFalse, hzero]
    · have hzeroFalse : isZero x = false :=
        Bool.eq_false_of_not_eq_true hzero
      cases hsign : signBit x
      · cases hdecode : toDyadic? x with
        | none => simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq,
          hsign, hdecode, hsnanFalse]
        | some exact =>
            have hexact : (exact.significand == 0) = false := by
              rw [← isZero_eq_beq_zero_of_toDyadic?_some hdecode]
              exact hzeroFalse
            simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hsign,
              hdecode, hexact, hsnanFalse]
      · rw [sqrt_status_of_signBit mode hnanFalse hzeroFalse hsign]
        simp [hsnanFalse, hnanFalse, hzeroFalse]

/-- Dividing two finite zeros raises invalid. -/
theorem div_invalid_of_zero_div_zero {fmt : FloatFormat}
    {x y : Model fmt} {dx dy : Numerics.Dyadic} {mode : IEEERoundingMode}
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hxzero : dx.significand = 0) (hyzero : dy.significand = 0) :
    (div x y (mode := mode) (status := true)).status.invalid = true := by
  simp [← Internal.Status.div_eq, Internal.Status.div, hx, hy, hxzero, hyzero]

/-- Dividing a finite nonzero value by a finite zero raises divide-by-zero. -/
theorem div_divideByZero_of_nonzero_div_zero {fmt : FloatFormat}
    {x y : Model fmt} {dx dy : Numerics.Dyadic} {mode : IEEERoundingMode}
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hxnonzero : dx.significand ≠ 0) (hyzero : dy.significand = 0) :
    (div x y (mode := mode) (status := true)).status.divideByZero = true := by
  simp [← Internal.Status.div_eq, Internal.Status.div, hx, hy, hxnonzero, hyzero]

/-- The square root of a negative nonzero non-NaN value raises invalid. -/
theorem sqrt_invalid_of_negative_nonzero {fmt : FloatFormat}
    {x : Model fmt} {mode : IEEERoundingMode}
    (hnan : isNaN x = false) (hnegative : signBit x = true) (hnonzero : isZero x = false) :
    (sqrt x (mode := mode) (status := true)).status.invalid = true := by
  simp [← Internal.Status.sqrt_eq, Internal.Status.sqrt, Internal.Directed.sqrt_eq, hnan, hnegative,
    hnonzero]

/-! ## Square-root inexactness -/

/--
Square root raises `inexact` exactly when its ternary value is not `.eq`, on every input. The
flag is computed from that value on a positive finite input, and the other cases raise neither.
-/
theorem sqrt_inexact_eq_ternary_bne_eq {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode) :
    (sqrt x (mode := mode) (status := true)).status.inexact =
      ((sqrt x (mode := mode) (status := true)).ternary != .eq) := by
  rw [← Internal.Status.sqrt_eq]
  unfold Internal.Status.sqrt outcomeWithInvalid
  dsimp only
  split
  · split <;> split <;> rfl
  · split
    · split <;> rfl
    · split
      · rfl
      · rfl

/-- Square-root underflow implies inexactness. -/
theorem sqrt_inexact_of_underflow {fmt : FloatFormat} {x : Model fmt}
    {mode : IEEERoundingMode}
      (h : (sqrt x (mode := mode) (status := true)).status.underflow = true) :
    (sqrt x (mode := mode) (status := true)).status.inexact = true := by
  revert h
  rw [← Internal.Status.sqrt_eq]
  unfold Internal.Status.sqrt outcomeWithInvalid
  dsimp only
  split
  · split <;> split <;> simp [Numerics.IEEEStatus.clear]
  · split
    · split <;> simp [Numerics.IEEEStatus.clear]
    · split
      · simp [Numerics.IEEEStatus.clear]
      · intro h
        split at h <;> simp_all

/--
On a positive finite input, square root raises `inexact` exactly when the delivered value is not
the real square root of the input, in every rounding direction and for every descriptor.

The flag is computed as the ternary value's difference from `.eq`
(`sqrt_inexact_eq_ternary_bne_eq`), so on such an input the ternary value is `.eq`
exactly when the delivered value is the real square root.
-/
theorem sqrt_inexact_iff {fmt : FloatFormat} (mode : IEEERoundingMode)
    {x : Model fmt} (hfinite : isFinite x = true) (hzero : isZero x = false)
    (hsign : signBit x = false) :
    (sqrt x (mode := mode) (status := true)).status.inexact = true ↔
      toReal (sqrt x (mode := mode) (status := true)).value ≠ Real.sqrt (toReal x) := by
  have hvalue := toReal_sqrt_nonneg mode hfinite hzero hsign
  have hxpos : 0 < toReal x := by
    have hnonneg := toReal_nonneg_of_isFinite_of_signBit_eq_false x hfinite hsign
    have hne : toReal x ≠ 0 := by
      intro h
      rw [← isZero_eq_true_iff_toReal_eq_zero x hfinite, hzero] at h
      contradiction
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  obtain ⟨exact, hexact⟩ := exists_toDyadic?_of_isFinite hfinite
  have hreal : toReal x = exact.toReal := by
    simp [toReal_eq, hexact]
  have hradicand : 0 ≤ exact.toReal := hreal ▸ hxpos.le
  have hinexact : (sqrt x (mode := mode) (status := true)).status.inexact =
      (dyadicSqrtTernary exact (sqrt x (mode := mode)) != .eq) := by
    rw [sqrt_status_of_toDyadic mode hexact
      (significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hexact hzero)
      ((sign_eq_signBit_of_toDyadic?_some hexact).trans hsign)]
  rw [hinexact, value_sqrt]
  cases hresult : isFinite (sqrt x (mode := mode))
  · rw [dyadicSqrtTernary_of_isFinite_eq_false exact hresult,
      toReal_eq_zero_of_isFinite_eq_false hresult]
    constructor
    · intro _
      exact (Real.sqrt_pos.mpr hxpos).ne
    · intro _
      rfl
  · rw [dyadicSqrtTernary_eq_compare _ hresult hvalue hradicand, ← hreal, bne_iff_ne, ne_eq,
      compare_eq_iff_eq]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
