/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.DyadicOrder
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Logarithm
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact

/-!
# Tininess after rounding in real order

IEEE 754 detects underflow after rounding: a result is tiny when rounding the exact value to the
destination precision with an unbounded exponent range gives a magnitude below the smallest
normal. The executable classifiers in `Status.Runtime` decide this with exact comparisons against
three positive boundaries, `underflowPredecessor`, `underflowMidpoint` and `minNormalDyadic`.

Here we restate those classifiers in real order: for exact dyadics
(`dyadicIsTinyAfterRounding_eq_true_iff`), for scaled rationals
(`rationalIsTinyAfterRoundingScaled_eq_true_iff`), and for the square-root boundary test, which
can never fire when the exponent range is wide compared with the precision
(`dyadicSqrtIsTinyAfterRounding_eq_false`). `Status.Proof` uses them for the operation statuses.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats.Formats.Flocq

/-! ## Underflow boundaries and the dyadic classifier -/

/-- The classifier on the delivered result accepts just the finite zero and subnormal encodings. -/
@[simp] theorem isTinyAfterRounding_eq_true_iff {fmt : FloatFormat}
    (rounded : Model fmt) :
    isTinyAfterRounding rounded = true ↔
      isFinite rounded = true ∧ expField rounded = 0 := by
  simp [isTinyAfterRounding]

/--
The underflow midpoint lies halfway between the unbounded-grid predecessor and the smallest
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
  -- Raising the exponent of `scale` by `steps` multiplies it by `2 ^ steps`.
  have hsteps (steps : Nat) :
      FloatLib.Floats.Formats.Flocq.bpow
          Numerics.binaryRadix (fmt.minSubnormalExponent - 2 + steps) =
        scale * 2 ^ steps := by
    simp only [scale, FloatLib.Floats.Formats.Flocq.bpow.add_exp]
    norm_num [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]
  have hpredecessorScale :
      FloatLib.Floats.Formats.Flocq.bpow
          Numerics.binaryRadix (fmt.minSubnormalExponent - 1) =
        scale * 2 := by
    simpa [show fmt.minSubnormalExponent - 2 + 1 = fmt.minSubnormalExponent - 1 by ring] using
      hsteps 1
  have hnormalScale :
      FloatLib.Floats.Formats.Flocq.bpow
          Numerics.binaryRadix fmt.minSubnormalExponent =
        scale * 4 := by
    have h := hsteps 2
    rw [show fmt.minSubnormalExponent - 2 + ((2 : Nat) : Int) = fmt.minSubnormalExponent by
      push_cast; ring] at h
    rw [h]
    norm_num
  have hpositive := pow2_pos fmt.fracWidth
  have htwo : 1 ≤ 2 * pow2 fmt.fracWidth := by omega
  have hfour : 1 ≤ 4 * pow2 fmt.fracWidth := by omega
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
  -- All three boundaries are positive dyadics, so the scaled comparator decides real order.
  have hmidpoint := compareDyadicScaled?_false_eq_compare numerator denominator exponent
    (underflowMidpoint fmt) hdenominator
  have hnormal := compareDyadicScaled?_false_eq_compare numerator denominator exponent
    (minNormalDyadic fmt) hdenominator
  have hpredecessor := compareDyadicScaled?_false_eq_compare numerator denominator exponent
    (underflowPredecessor fmt) hdenominator
  cases hrounded : isTinyAfterRounding rounded with
  | false =>
      -- In each direction and sign, read the comparison against that direction's boundary.
      cases mode <;> cases sign <;>
        simp only [rationalIsTinyAfterRoundingScaled, hrounded,
          IEEERoundingMode.roundsAwayFromZero, hmidpoint, hnormal, hpredecessor,
          Bool.false_eq_true, ite_false, ite_true, Bool.not_false, Bool.not_true, false_or,
          true_and] <;>
        split <;> simp_all [compare_lt_iff_lt, compare_gt_iff_gt, le_of_lt]
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

/-! ## Square-root tininess -/

/-- A nonzero decoded dyadic has magnitude at least the least positive subnormal. -/
private theorem two_zpow_minSubnormalExponent_le_magnitude {fmt : FloatFormat} {x : Model fmt}
    {exact : Numerics.Dyadic} (hx : toDyadic? x = some exact) (hzero : exact.significand ≠ 0) :
    (2 : ℝ) ^ fmt.minSubnormalExponent ≤
      ({ exact with negative := false } : Numerics.Dyadic).toReal := by
  have hscale : (2 : ℝ) ^ fmt.minSubnormalExponent ≤ (2 : ℝ) ^ exact.exponent :=
    zpow_le_zpow_right₀ (by norm_num) (minSubnormalExponent_le_toDyadic? x hx)
  have hsignificand : (1 : ℝ) ≤ exact.significand := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
  simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand, Bool.false_eq_true,
    ite_false, one_mul]
  change (2 : ℝ) ^ fmt.minSubnormalExponent ≤ (exact.significand : ℝ) * 2 ^ exact.exponent
  nlinarith [zpow_pos (by norm_num : (0 : ℝ) < 2) exact.exponent]

/--
When `fmt.fracWidth + 1 < fmt.exponentBias`, the square of the smallest normal,
`2^(2 * minNormalExponent)`, lies below the least positive subnormal `2^minSubnormalExponent`.
-/
private theorem minNormalDyadic_mul_self_lt {fmt : FloatFormat}
    (hformat : fmt.fracWidth + 1 < fmt.exponentBias) :
    (minNormalDyadic fmt).toReal * (minNormalDyadic fmt).toReal <
      (2 : ℝ) ^ fmt.minSubnormalExponent := by
  have hreal : (minNormalDyadic fmt).toReal =
      (2 : ℝ) ^ ((fmt.fracWidth : Int) + fmt.minSubnormalExponent) := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
    simp only [minNormalDyadic, Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand,
      Bool.false_eq_true, ite_false, one_mul, pow2_eq_two_pow, Nat.cast_pow, Nat.cast_ofNat]
  rw [hreal, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  apply zpow_lt_zpow_right₀ (by norm_num)
  simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
    Int.ofNat_eq_natCast]
  omega

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
  -- A positive boundary at most `minNormal` has its square below the radicand.
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
      simpa using Dyadic.toReal_mul boundary boundary
    have hnonnegative : 0 ≤ boundary.toReal := by
      simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand, hnegative,
        Bool.false_eq_true, ite_false, one_mul]
      exact mul_nonneg (Nat.cast_nonneg _) (bpow_nonneg _)
    rw [hsquare]
    calc boundary.toReal * boundary.toReal
        ≤ (minNormalDyadic fmt).toReal * (minNormalDyadic fmt).toReal :=
          mul_self_le_mul_self hnonnegative hle
      _ < (2 : ℝ) ^ fmt.minSubnormalExponent := minNormalDyadic_mul_self_lt hformat
      _ ≤ _ := two_zpow_minSubnormalExponent_le_magnitude hx hzero
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

end Model
end FloatLib.Floats.Formats.BinaryInterchange
