/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.NearestEven
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Packing.Downward
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Packing.Upward
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof

/-!
# Quotient and exponent semantics

Exact rational rounding reduces to an integer quotient after a power-of-two rescaling. This
module proves bounds for small quotients and relates the scaled leading exponent to the order of
the numerator and denominator. It also identifies the subnormal and normal grid exponents used
by `roundAt`.

These lemmas supply the bounds and exponent identities used by the nearest-even packing proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics
open Directed.Internal

section

/--
A quotient at or below one half rounds to the even integer zero. With a zero denominator the bound
forces a zero numerator, which also rounds to zero.
-/
theorem roundQuotientEven_eq_zero_of_two_mul_le
    (numerator denominator : Nat)
    (hhalf : 2 * numerator ≤ denominator) :
    roundQuotientEven numerator denominator = 0 := by
  by_cases hdenominator : denominator = 0
  · obtain rfl : numerator = 0 := by omega
    subst denominator
    rfl
  have hnumeratorLt : numerator < denominator := by
    have hdenominatorPos := Nat.pos_of_ne_zero hdenominator
    omega
  have hquotient : numerator / denominator = 0 :=
    Nat.div_eq_of_lt hnumeratorLt
  have hremainder : numerator % denominator = numerator :=
    Nat.mod_eq_of_lt hnumeratorLt
  unfold roundQuotientEven
  simp only [hquotient, hremainder, Nat.zero_mod, beq_self_eq_true]
  by_cases hstrict : 2 * numerator < denominator
  · simp [hstrict]
  · have hequal : denominator = 2 * numerator := by omega
    simp [hequal]

/-- A proper fraction rounds to either zero or one. -/
theorem roundQuotientEven_le_one_of_lt
    (numerator denominator : Nat) (hlt : numerator < denominator) :
    roundQuotientEven numerator denominator ≤ 1 := by
  have hdenominator : denominator ≠ 0 := by omega
  have hsandwich :=
    roundQuotDirected_false_le_roundQuotientEven_le_true
      numerator denominator hdenominator
  have hceil : roundQuotDirected true numerator denominator ≤ 1 := by
    by_cases hnumerator : numerator = 0
    · simp [roundQuotDirected, Numerics.roundQuotient_up_eq, hnumerator]
    · simp [roundQuotDirected, Numerics.roundQuotient_up_eq, hdenominator,
        Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, hnumerator]
  exact hsandwich.2.trans hceil

/--
A scaled rational whose leading exponent stays below `k` has scaled numerator below `2^k` times its
scaled denominator.
-/
private theorem scaleByPowerOfTwo_fst_lt_bpow_mul_snd
    (numerator denominator : Nat) (shift k : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hk : Numerics.RationalBinary.floorLog2 numerator denominator + shift + 1 ≤ k) :
    ((Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift).1 : Real) <
      bpow k * (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift).2 := by
  have hratio :=
    (scaleByPowerOfTwo_floorLog2_bounds numerator denominator shift hnumerator
      hdenominator).2.trans_le (bpow_le_bpow_of_le hk)
  have hscaledDenominator :
      0 < ((Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift).2 : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator shift
        hdenominator)
  exact (div_lt_iff₀ hscaledDenominator).mp hratio

/--
If a scaled rational's leading exponent is negative, its scaled numerator is strictly smaller
than its denominator.
-/
theorem scaleByPowerOfTwo_fst_lt_snd_of_neg_log
    (numerator denominator : Nat) (shift : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hnegative : Numerics.RationalBinary.floorLog2 numerator denominator + shift < 0) :
    (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift).1 <
      (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift).2 := by
  have hcast := scaleByPowerOfTwo_fst_lt_bpow_mul_snd numerator denominator shift 0
    hnumerator hdenominator (by omega)
  rw [bpow_zero, one_mul] at hcast
  exact_mod_cast hcast

/--
Values whose scaled leading exponent is below `-1` are strictly below one half of a grid unit and
therefore round to zero under nearest-even.
-/
theorem roundQuotientEven_scaled_eq_zero
    (numerator denominator : Nat) (shift : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hsmall : Numerics.RationalBinary.floorLog2 numerator denominator + shift < -1) :
    roundQuotientEven
        (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift).1
        (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift).2 = 0 := by
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift
  have hcast := scaleByPowerOfTwo_fst_lt_bpow_mul_snd numerator denominator shift (-1)
    hnumerator hdenominator (by omega)
  rw [bpow_neg_one] at hcast
  have hhalf : 2 * scaled.1 ≤ scaled.2 := by
    have : (2 : Real) * scaled.1 < scaled.2 := by linarith
    exact_mod_cast this.le
  exact roundQuotientEven_eq_zero_of_two_mul_le scaled.1 scaled.2 hhalf

/--
Nearest-even subnormal-path rounding is at most the smallest normal mantissa, for every value below
the normal range.
-/
theorem roundQuotientEven_subnormal_le
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hhigh :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minNormalExponent) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))
    roundQuotientEven scaled.1 scaled.2 ≤ pow2 fmt.fracWidth := by
  dsimp only
  let shift :=
    exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt)
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift
  have hscaledDenominator : scaled.2 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator shift hdenominator
  have hsandwich :=
    roundQuotDirected_false_le_roundQuotientEven_le_true
      scaled.1 scaled.2 hscaledDenominator
  have hupper :=
    roundQuotDirected_le_pow2_of_div_lt true scaled.1 scaled.2 fmt.fracWidth
      (scaleByPowerOfTwo_subnormal_lt_pow2 fmt numerator denominator exponent
        hnumerator hdenominator hhigh)
  exact hsandwich.2.trans hupper

/-! ## Format exponent selection -/

/-- The nearest-even implementation's half-min-subnormal cutoff in semantic form. -/
theorem neg_normalMantissaExpOffset_eq_minSubnormalExponent_sub_one
    (fmt : FloatFormat) :
    -Int.ofNat (FloatFormat.normalMantissaExpOffset fmt) =
      fmt.minSubnormalExponent - 1 := by
  unfold FloatFormat.normalMantissaExpOffset FloatFormat.minSubnormalExponent
    FloatFormat.minNormalExponent
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  ring

/-- Values below the normal range use the descriptor's minimum-subnormal grid. -/
theorem fexpOf_total_eq_minSubnormal
    (fmt : FloatFormat) (totalExponent : Int)
    (hsubnormal : totalExponent < fmt.minNormalExponent) :
    fexpOf fmt (totalExponent + 1) = fmt.minSubnormalExponent := by
  simp only [fexpOf, fltExp, FloatFormat.minSubnormalExponent,
    Int.ofNat_eq_natCast]
  apply max_eq_right
  omega

/-- Normal values use the descriptor's precision-shifted rounded-real grid. -/
theorem fexpOf_total_eq_normal
    (fmt : FloatFormat) (totalExponent : Int)
    (hnormal : fmt.minNormalExponent ≤ totalExponent) :
    fexpOf fmt (totalExponent + 1) = totalExponent - Int.ofNat fmt.fracWidth := by
  simp only [fexpOf, fltExp, FloatFormat.minSubnormalExponent,
    Int.ofNat_eq_natCast]
  omega


end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
