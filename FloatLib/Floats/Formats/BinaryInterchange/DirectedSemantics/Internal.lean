/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Dyadic.Core.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Dyadic.Core.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Dyadic.Packing

/-!
# Shared internal facts for directed binary semantics

These descriptor and field-packing facts are common to dyadic and rational directed rounding.
Keeping them below both proof layers prevents each numerical representation from rebuilding the
same IEEE-specialization arguments.

## Dyadic

This module exports the format-generic normalization, executable branch, grid-bound, and
field-packing theorems for directed dyadic rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Directed.Internal

open FloatLib.Floats

/--
Encoding an in-range IEEE normal exponent produces a field strictly below the all-ones pattern.
-/
theorem encodedExponent_lt_expAllOnes_ieee
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (exponent : Int)
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hmax : exponent ≤ fmt.maxNormalExponent) :
    Int.toNat (exponent + Int.ofNat fmt.exponentBias) <
      fmt.expAllOnesNat := by
  have hexponent :=
    encodedExponent_le_maxFiniteExpField fmt exponent hmin hmax
  have hlt : fmt.maxFiniteExpField < fmt.expAllOnesNat := by
    have hfour : 4 ≤ 2 ^ fmt.expWidth := by
      simpa using
        Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
          fmt.expWidth_ge_two
    unfold FloatFormat.maxFiniteExpField FloatFormat.expAllOnesNat
    rw [FloatFormat.encoding_eq_ieee_of_isIEEE fmt hfmt]
    simp only [FloatFormat.Encoding.maxFiniteExponent]
    omega
  exact hexponent.trans_lt hlt

/-- Any fraction field packed with an in-range IEEE normal exponent denotes a finite value. -/
theorem isFinite_ofFields_of_normal_exponent
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (fraction : Nat) (exponent : Int)
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hmax : exponent ≤ fmt.maxNormalExponent) :
    isFinite
        (ofFields fmt false
          (Int.toNat (exponent + Int.ofNat fmt.exponentBias))
          fraction) = true :=
  isFinite_ofFields_ieee fmt hfmt false _ _
    (encodedExponent_lt_expAllOnes_ieee fmt hfmt exponent hmin hmax)

/-- Packing an in-range normalized IEEE mantissa and exponent produces a finite encoding. -/
theorem isFinite_ofFields_normalized
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mantissa : Nat) (exponent : Int)
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hmax : exponent ≤ fmt.maxNormalExponent) :
    isFinite
        (ofFields fmt false
          (Int.toNat (exponent + Int.ofNat fmt.exponentBias))
          (mantissa - pow2 fmt.fracWidth)) = true :=
  isFinite_ofFields_of_normal_exponent fmt hfmt _ exponent hmin hmax

/--
A normalization carry preserves the represented real value while moving one bit from the
significand into the exponent.
-/
theorem normalizationCarry_value
    (fmt : FloatFormat) (exponent : Int) :
    (pow2 fmt.fracWidth : ℝ) *
        bpow (exponent + 1 - Int.ofNat fmt.fracWidth) =
      (pow2 (fmt.fracWidth + 1) : ℝ) *
        bpow (exponent - Int.ofNat fmt.fracWidth) := by
  rw [← bpow_ofNat fmt.fracWidth,
    ← bpow_ofNat (fmt.fracWidth + 1)]
  rw [← bpow_add, ← bpow_add]
  congr 1
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  ring

end Directed.Internal
end Model
end FloatLib.Floats.Formats.BinaryInterchange
