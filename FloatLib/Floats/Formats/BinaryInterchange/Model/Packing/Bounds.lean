/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Core
import Mathlib.Tactic.Ring.RingNF

/-!
# Bounds for normal field packing

A normal exponent becomes a positive, in-range biased field, and removing the hidden bit from a
normalized significand leaves a legal fraction. Together these bounds show that the finite-range
packing guard accepts every in-range IEEE normal value.

Nearest and directed rounding share these arithmetic facts before either correctness proof layer
is imported.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- The smallest normal exponent does not exceed the largest normal exponent. -/
theorem minNormalExponent_le_maxNormalExponent (fmt : FloatFormat) :
    fmt.minNormalExponent ≤ fmt.maxNormalExponent := by
  unfold FloatFormat.minNormalExponent FloatFormat.maxNormalExponent
  have hmax : (0 : Int) < Int.ofNat fmt.maxFiniteExpField :=
    Int.natCast_pos.mpr fmt.maxFiniteExpField_pos
  omega

/-! ## Normal field bounds -/

/-- A normal unbiased exponent produces a positive biased exponent field. -/
theorem biasedExponent_pos (fmt : FloatFormat) (exponent : Int)
    (hmin : fmt.minNormalExponent ≤ exponent) :
    0 < exponent + Int.ofNat fmt.exponentBias := by
  unfold FloatFormat.minNormalExponent at hmin
  omega

/-- Conversion of a normal biased exponent through `Int.toNat` is exact. -/
theorem ofNat_toNat_biasedExponent (fmt : FloatFormat) (exponent : Int)
    (hmin : fmt.minNormalExponent ≤ exponent) :
    Int.ofNat (Int.toNat (exponent + Int.ofNat fmt.exponentBias)) =
      exponent + Int.ofNat fmt.exponentBias :=
  Int.toNat_of_nonneg (biasedExponent_pos fmt exponent hmin).le

/--
An exponent at most the largest normal exponent is encoded within the descriptor's finite exponent
range. An exponent below the normal range encodes as the zero field.
-/
theorem encodedExponent_le_maxFiniteExpField
    (fmt : FloatFormat) (exponent : Int)
    (hmax : exponent ≤ fmt.maxNormalExponent) :
    Int.toNat (exponent + Int.ofNat fmt.exponentBias) ≤
      fmt.maxFiniteExpField := by
  unfold FloatFormat.maxNormalExponent at hmax
  simp only [Int.ofNat_eq_natCast] at hmax ⊢
  omega

/-- A normal unbiased exponent never encodes as the zero exponent field. -/
theorem encodedExponent_ne_zero
    (fmt : FloatFormat) (exponent : Int)
    (hmin : fmt.minNormalExponent ≤ exponent) :
    Int.toNat (exponent + Int.ofNat fmt.exponentBias) ≠ 0 := by
  have hpositiveInt :
      (0 : Int) < Int.ofNat (Int.toNat (exponent + Int.ofNat fmt.exponentBias)) := by
    rw [ofNat_toNat_biasedExponent fmt exponent hmin]
    exact biasedExponent_pos fmt exponent hmin
  exact Nat.ne_of_gt (Int.natCast_pos.mp hpositiveInt)

/-- Decoding a normal biased exponent recovers the intended normalized dyadic scale. -/
theorem decode_encodedExponent
    (fmt : FloatFormat) (exponent : Int)
    (hmin : fmt.minNormalExponent ≤ exponent) :
    Int.ofNat (Int.toNat (exponent + Int.ofNat fmt.exponentBias)) -
        Int.ofNat fmt.exponentBias - Int.ofNat fmt.fracWidth =
      exponent - Int.ofNat fmt.fracWidth := by
  rw [ofNat_toNat_biasedExponent fmt exponent hmin]
  ring

/--
Removing the implicit leading bit from a mantissa below `2^(fracWidth + 1)` fits the fraction
field. Below `2^fracWidth` the truncated subtraction is zero.
-/
theorem normalizedMantissa_sub_pow2_lt
    (fmt : FloatFormat) (mantissa : Nat)
    (hhigh : mantissa < pow2 (fmt.fracWidth + 1)) :
    mantissa - pow2 fmt.fracWidth < 2 ^ fmt.fracWidth := by
  rw [pow2_eq_two_pow] at hhigh ⊢
  rw [pow_succ] at hhigh
  omega

/-- Restoring the implicit leading bit gives back the normalized mantissa. -/
theorem pow2_add_normalizedMantissa_sub (fmt : FloatFormat) (mantissa : Nat)
    (hlow : pow2 fmt.fracWidth ≤ mantissa) :
    pow2 fmt.fracWidth + (mantissa - pow2 fmt.fracWidth) = mantissa :=
  Nat.add_sub_of_le hlow

namespace Directed.Internal

/--
Removing the hidden bit from a normalized IEEE significand leaves a legal fraction field.

Both dyadic and rational packing use this fact. Keeping it here makes the format argument
independent of the exact-number representation used by the caller.
-/
theorem fraction_le_maxFiniteFracField_ieee
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mantissa : Nat)
    (hhigh : mantissa < pow2 (fmt.fracWidth + 1)) :
    mantissa - pow2 fmt.fracWidth ≤ fmt.maxFiniteFracField := by
  have hfraction : mantissa - pow2 fmt.fracWidth < pow2 fmt.fracWidth := by
    simpa [pow2_eq_two_pow] using normalizedMantissa_sub_pow2_lt fmt mantissa hhigh
  simp only [FloatFormat.maxFiniteFracField,
    FloatFormat.encoding_eq_ieee_of_isIEEE fmt hfmt,
    FloatFormat.fracMaskNat, pow2_eq_two_pow]
  simpa [pow2_eq_two_pow] using Nat.le_sub_one_of_lt hfraction

/--
Fields with an exponent at most the largest normal exponent and a legal fraction cannot trigger
the overflow guard shared by the dyadic and rational packers.
-/
theorem packingGuard_eq_false
    (fmt : FloatFormat) (exponent : Int) (fraction : Nat)
    (hmax : exponent ≤ fmt.maxNormalExponent)
    (hfraction : fraction ≤ fmt.maxFiniteFracField) :
    let encodedExponent :=
      Int.toNat (exponent + Int.ofNat fmt.exponentBias)
    (decide (encodedExponent > fmt.maxFiniteExpField) ||
        encodedExponent == fmt.maxFiniteExpField &&
          decide (fraction > fmt.maxFiniteFracField)) =
      false := by
  have hexponent :=
    encodedExponent_le_maxFiniteExpField fmt exponent hmax
  have hexponentNot :
      ¬Int.toNat (exponent + Int.ofNat fmt.exponentBias) >
        fmt.maxFiniteExpField :=
    not_lt_of_ge hexponent
  have hfractionNot : ¬fraction > fmt.maxFiniteFracField :=
    not_lt_of_ge hfraction
  simp only [hexponentNot, hfractionNot, decide_false,
    Bool.and_false, Bool.or_false]

/--
An IEEE significand below `2^(fracWidth + 1)` at an exponent at most the largest normal exponent
cannot trigger the overflow guard shared by the dyadic and rational packers: the encoded exponent
does not exceed the maximal finite field and the fraction is legal.
-/
theorem normalizedGuard_eq_false
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mantissa : Nat)
    (exponent : Int)
    (hhigh : mantissa < pow2 (fmt.fracWidth + 1))
    (hmax : exponent ≤ fmt.maxNormalExponent) :
    let encodedExponent :=
      Int.toNat (exponent + Int.ofNat fmt.exponentBias)
    let fraction := mantissa - pow2 fmt.fracWidth
    (decide (encodedExponent > fmt.maxFiniteExpField) ||
        encodedExponent == fmt.maxFiniteExpField &&
          decide (fraction > fmt.maxFiniteFracField)) =
      false :=
  packingGuard_eq_false fmt exponent (mantissa - pow2 fmt.fracWidth) hmax
    (fraction_le_maxFiniteFracField_ieee fmt hfmt mantissa hhigh)

end Directed.Internal
end Model
end FloatLib.Floats.Formats.BinaryInterchange
