/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Nat.Log
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Packing.Bounds
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Power
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Dyadic

/-!
# Basic lemmas for format-parameterized directed rounding

Shared arithmetic facts support both directed dyadic and rational rounding proofs. Further
lemmas give closed forms for the smallest positive subnormal and a strict power-of-two bound for
the largest finite value. All statements are uniform in `FloatFormat`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats

section

/-- Increasing a natural exponent by one does not decrease its power of two. -/
theorem pow2_le_pow2_succ (exponent : Nat) :
    pow2 exponent ≤ pow2 (exponent + 1) := by
  simp [pow2, Nat.shiftLeft_succ]

/-- Natural powers of two are positive. -/
theorem pow2_pos (exponent : Nat) : 0 < pow2 exponent := by
  simp [pow2_eq_two_pow]

/-- Natural powers of two grow strictly with the exponent. -/
theorem pow2_lt_pow2_succ (exponent : Nat) :
    pow2 exponent < pow2 (exponent + 1) := by
  simpa only [pow2_eq_two_pow] using
    Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) (Nat.lt_succ_self exponent)

/-- Split a natural power of two across an exponent sum. -/
theorem pow2_add (left right : Nat) :
    pow2 (left + right) = pow2 left * pow2 right := by
  simp [pow2_eq_two_pow, Nat.pow_add]

/-- Multiplicative form of `pow2_add`. -/
theorem pow2_mul (left right : Nat) :
    pow2 left * pow2 right = pow2 (left + right) :=
  (pow2_add left right).symm

/-! ## Floor and ceiling shifts -/

/-- Shifting right and restoring the removed power of two cannot exceed the original number. -/
theorem shiftRight_mul_pow2_le (n shift : Nat) :
    Nat.shiftRight n shift * pow2 shift ≤ n := by
  have h := Nat.div_mul_le_self n (2 ^ shift)
  simpa [Nat.shiftRight_eq_div_pow, pow2_eq_two_pow, Nat.mul_comm] using h

/-- A ceiling right shift, followed by restoration of its scale, covers the original number. -/
theorem le_shiftRightCeil_mul_pow2 (n shift : Nat) :
    n ≤ Numerics.shiftRightCeil n shift * pow2 shift := by
  classical
  cases shift with
  | zero =>
      simp [Numerics.shiftRightCeil, pow2_eq_two_pow]
  | succ shift =>
      set divisor : Nat := pow2 (Nat.succ shift)
      have hdivisor : 0 < divisor := pow2_pos (Nat.succ shift)
      set quotient : Nat := n / divisor
      set remainder : Nat := n % divisor
      have hn : n = quotient * divisor + remainder := by
        simpa [quotient, remainder, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (Nat.div_add_mod n divisor).symm
      have hremainder : remainder < divisor := Nat.mod_lt n hdivisor
      have hshift : Nat.shiftRight n (Nat.succ shift) = quotient := by
        simp [quotient, divisor, Nat.shiftRight_eq_div_pow, pow2_eq_two_pow]
      have hrem : n - Nat.shiftLeft quotient (Nat.succ shift) = remainder := by
        have hleft : Nat.shiftLeft quotient (Nat.succ shift) = quotient * divisor := by
          simp [Nat.shiftLeft_eq, divisor, pow2_eq_two_pow]
        rw [hleft, hn]
        simp
      have hshift' : n >>> (shift + 1) = quotient := by
        simpa [Nat.succ_eq_add_one] using hshift
      have hrem' : n - quotient <<< (shift + 1) = remainder := by
        simpa [Nat.succ_eq_add_one] using hrem
      by_cases hzero : remainder = 0
      · have hn' : n = quotient * divisor := by
          simp [hn, hzero]
        have hceil : Numerics.shiftRightCeil n (Nat.succ shift) = quotient := by
          have hshiftNonzero : (Nat.succ shift == 0) = false := by
            simp
          simp (config := { zeta := true })
            [Numerics.shiftRightCeil, hshiftNonzero]
          rw [hshift', hrem']
          simp [hzero]
        have hceil' :
            Numerics.shiftRightCeil (quotient * divisor) (Nat.succ shift) = quotient := by
          simpa [hn'] using hceil
        simp [hn', hceil', divisor]
      · have hnle : n ≤ (quotient + 1) * divisor := by
          have hsum :
              quotient * divisor + remainder ≤ quotient * divisor + divisor :=
            Nat.add_le_add_left (Nat.le_of_lt hremainder) (quotient * divisor)
          have hmul : (quotient + 1) * divisor = quotient * divisor + divisor := by
            simp [Nat.add_mul]
          have : n ≤ quotient * divisor + divisor := by
            simpa [hn] using hsum
          simpa [hmul] using this
        have hceil : Numerics.shiftRightCeil n (Nat.succ shift) = quotient + 1 := by
          have hshiftNonzero : (Nat.succ shift == 0) = false := by
            simp
          simp (config := { zeta := true })
            [Numerics.shiftRightCeil, hshiftNonzero]
          rw [hshift', hrem']
          simp [hzero]
        simp [hceil, hnle, divisor]

/-- A ceiling shift is at most one larger than the corresponding floor shift. -/
theorem _root_.FloatLib.Numerics.shiftRightCeil_le_shiftRight_add_one (n shift : Nat) :
    Numerics.shiftRightCeil n shift ≤ Nat.shiftRight n shift + 1 := by
  cases shift with
  | zero =>
      simp [Numerics.shiftRightCeil]
  | succ shift =>
      simp (config := { zeta := true }) [Numerics.shiftRightCeil]
      split <;> omega

/-- A floor right shift never exceeds the corresponding ceiling right shift. -/
theorem _root_.FloatLib.Numerics.shiftRight_le_shiftRightCeil (n shift : Nat) :
    Nat.shiftRight n shift ≤ Numerics.shiftRightCeil n shift := by
  cases shift with
  | zero =>
      simp [Numerics.shiftRightCeil]
  | succ shift =>
      simp (config := { zeta := true }) [Numerics.shiftRightCeil]
      split <;> omega

/-- The leading power of two does not exceed a nonzero natural number. -/
theorem pow2_log2_le {n : Nat} (hn : n ≠ 0) :
    pow2 (Nat.log2 n) ≤ n := by
  have h : 2 ^ Nat.log2 n ≤ n := (Nat.le_log2 hn).1 le_rfl
  simpa [pow2_eq_two_pow] using h

/-- A natural number is below the next power after its leading bit. -/
theorem lt_pow2_log2_add_one (n : Nat) :
    n < pow2 (Nat.log2 n + 1) := by
  simpa [pow2_eq_two_pow] using Nat.lt_log2_self (n := n)

/-! ## Format constants -/

/-- The subnormal grid starts strictly below the smallest normal exponent. -/
theorem minSubnormalExponent_lt_minNormalExponent (fmt : FloatFormat) :
    fmt.minSubnormalExponent < fmt.minNormalExponent := by
  unfold FloatFormat.minSubnormalExponent
  have hfrac : (0 : Int) < Int.ofNat fmt.fracWidth :=
    Int.natCast_pos.mpr fmt.fracWidth_pos
  omega

/-- The subnormal exponent plus the stored fraction width is the minimum normal exponent. -/
theorem minSubnormalExponent_add_fracWidth (fmt : FloatFormat) :
    fmt.minSubnormalExponent + Int.ofNat fmt.fracWidth =
      fmt.minNormalExponent := by
  unfold FloatFormat.minSubnormalExponent
  omega

/-- The smallest positive subnormal packs a clear sign, exponent field zero, and fraction one. -/
theorem posMinSubnormal_eq_ofFields (fmt : FloatFormat) :
    posMinSubnormal fmt = ofFields fmt false 0 1 := by
  apply congrArg ofBits
  apply BitVec.eq_of_toNat_eq
  simp [mkBits, FloatFormat.fracMask, FloatFormat.fracMaskNat, FloatFormat.ofWordNat]
  have hbitWidthPos : 0 < fmt.bitWidth := by
    unfold FloatFormat.bitWidth
    omega
  have hfracWidthLe : fmt.fracWidth ≤ fmt.bitWidth := by
    unfold FloatFormat.bitWidth
    omega
  have honeBitWidth : 1 < 2 ^ fmt.bitWidth :=
    Nat.one_lt_two_pow (Nat.ne_of_gt hbitWidthPos)
  have hpowLe : 2 ^ fmt.fracWidth ≤ 2 ^ fmt.bitWidth :=
    Nat.pow_le_pow_right (by decide) hfracWidthLe
  have hmaskLt : 2 ^ fmt.fracWidth - 1 < 2 ^ fmt.bitWidth := by
    have hfracPowPos : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos fmt.fracWidth
    omega
  rw [Nat.mod_eq_of_lt honeBitWidth, Nat.mod_eq_of_lt hmaskLt]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt fmt.fracWidth_pos))]

/-- The smallest positive subnormal denotes one unit at the minimum subnormal exponent. -/
@[simp] theorem toReal_posMinSubnormal (fmt : FloatFormat) :
    toReal (posMinSubnormal fmt) = bpow fmt.minSubnormalExponent := by
  rw [posMinSubnormal_eq_ofFields]
  have hfit : 1 < 2 ^ fmt.fracWidth :=
    Nat.one_lt_two_pow (Nat.ne_of_gt fmt.fracWidth_pos)
  simpa [bpow] using
    toReal_ofFields_subnormal fmt false 1 one_ne_zero hfit

/-- Closed form for the largest finite positive value of an arbitrary format. -/
theorem toReal_posMaxFinite (fmt : FloatFormat) :
    toReal (posMaxFinite fmt) =
      ((pow2 fmt.fracWidth + fmt.maxFiniteFracField : Nat) : ℝ) *
        bpow (fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) := by
  rw [show posMaxFinite fmt =
      ofFields fmt false fmt.maxFiniteExpField fmt.maxFiniteFracField by rfl]
  rw [toReal_ofFields_normal_of_isFinite fmt false fmt.maxFiniteExpField
    fmt.maxFiniteFracField (Nat.ne_of_gt fmt.maxFiniteExpField_pos)
    fmt.maxFiniteExpField_lt_two_pow fmt.maxFiniteFracField_lt_two_pow
    (by simpa [posMaxFinite, maxFinite] using isFinite_posMaxFinite fmt)]
  simp only [Bool.false_eq_true, ite_false, one_mul]
  congr 1

/-- A signed magnitude `±mantissa * 2^exponent` has the magnitude as its absolute value. -/
private theorem abs_signed_mul_bpow (sign : Bool) (mantissa : Nat) (exponent : Int) :
    |(if sign then (-1 : ℝ) else 1) * (mantissa : ℝ) * bpow exponent| =
      (mantissa : ℝ) * bpow exponent := by
  cases sign <;> simp [abs_mul, abs_of_nonneg (bpow_nonneg _)]

/-- The largest finite value of every format is positive. -/
theorem toReal_posMaxFinite_pos (fmt : FloatFormat) : 0 < toReal (posMaxFinite fmt) := by
  rw [toReal_posMaxFinite]
  refine mul_pos (Nat.cast_pos.mpr ?_) (bpow_pos _)
  have := pow2_pos fmt.fracWidth
  omega

/-- The largest finite value of every format is nonnegative. -/
theorem toReal_posMaxFinite_nonneg (fmt : FloatFormat) : 0 ≤ toReal (posMaxFinite fmt) :=
  (toReal_posMaxFinite_pos fmt).le

/--
A signed magnitude whose mantissa and exponent do not exceed those of the largest finite value is
bounded by that value.
-/
theorem abs_signed_mul_bpow_le_toReal_posMaxFinite
    (fmt : FloatFormat) (sign : Bool) (mantissa : Nat) (exponent : Int)
    (hmantissa : mantissa ≤ pow2 fmt.fracWidth + fmt.maxFiniteFracField)
    (hexponent : exponent ≤ fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) :
    |(if sign then (-1 : ℝ) else 1) * (mantissa : ℝ) * bpow exponent| ≤
      toReal (posMaxFinite fmt) := by
  rw [abs_signed_mul_bpow, toReal_posMaxFinite]
  exact mul_le_mul (by exact_mod_cast hmantissa) (bpow_le_bpow_of_le hexponent)
    (bpow_nonneg _) (Nat.cast_nonneg _)

/--
A finite word's exponent field is at most `maxFiniteExpField`. An IEEE encoding reserves the
all-ones field for infinities and NaNs, and the other encodings use every field for finite values.
-/
theorem expField_le_maxFiniteExpField_of_isFinite {fmt : FloatFormat} (x : Model fmt)
    (hfinite : isFinite x = true) :
    expField x ≤ fmt.maxFiniteExpField := by
  have hexponentLt := expField_lt_pow2 x
  cases hencoding : fmt.encoding with
  | ieee =>
      have hexponentNe : expField x ≠ fmt.expAllOnesNat := by
        have hfiniteIEEE : IEEE.isFinite x = true := by
          simpa [isFinite, hencoding] using hfinite
        exact (bne_iff_ne).mp hfiniteIEEE
      simp only [FloatFormat.maxFiniteExpField, FloatFormat.Encoding.maxFiniteExponent,
        hencoding]
      unfold FloatFormat.expAllOnesNat at hexponentNe
      omega
  | finiteMaxNaN | finiteUnsignedZero | finite =>
      simp only [FloatFormat.maxFiniteExpField, FloatFormat.Encoding.maxFiniteExponent,
        hencoding]
      omega

/-- A natural number below `2^k`, scaled by `2^e`, lies below `2^E` whenever `k + e ≤ E`. -/
theorem natCast_mul_bpow_lt_bpow {m k : Nat} {e E : Int} (hm : m < 2 ^ k)
    (hE : (k : Int) + e ≤ E) :
    (m : ℝ) * bpow e < bpow E := by
  have hmReal : (m : ℝ) < bpow (k : Int) := by
    rw [bpow_natCast]
    exact_mod_cast hm
  calc (m : ℝ) * bpow e
      < bpow (k : Int) * bpow e := mul_lt_mul_of_pos_right hmReal (bpow_pos _)
    _ = bpow ((k : Int) + e) := (bpow_add _ _).symm
    _ ≤ bpow E := bpow_le_bpow_of_le hE

/-- The largest finite value is at least the power of two at the largest normal exponent. -/
private theorem bpow_maxNormalExponent_le_toReal_posMaxFinite (fmt : FloatFormat) :
    bpow fmt.maxNormalExponent ≤ toReal (posMaxFinite fmt) := by
  have h := abs_signed_mul_bpow_le_toReal_posMaxFinite fmt false (pow2 fmt.fracWidth)
    (fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) (Nat.le_add_right _ _) le_rfl
  have hpower :
      ((pow2 fmt.fracWidth : Nat) : ℝ) *
          bpow (fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) =
        bpow fmt.maxNormalExponent := by
    rw [← bpow_ofNat, ← bpow_add]
    congr 1
    ring
  rw [← hpower]
  simpa [abs_of_nonneg (bpow_nonneg _)] using h

/--
Every finite value lies between the two largest-finite endpoints, in every encoding.

The finiteness hypothesis excludes infinities and NaNs, and the bound follows from the
descriptor's exponent and fraction fields. A finite-with-NaN encoding reserves only the largest
fraction at the largest exponent, so a smaller exponent may carry any fraction and still stays
below the next binade boundary.
-/
theorem abs_toReal_le_posMaxFinite_of_isFinite
    {fmt : FloatFormat} (x : Model fmt) (hfinite : isFinite x = true) :
    |toReal x| ≤ toReal (posMaxFinite fmt) := by
  have hexponentLt := expField_lt_pow2 x
  have hfractionLt := fracField_lt_pow2 x
  have hexponentLe := expField_le_maxFiniteExpField_of_isFinite x hfinite
  have hfieldsFinite :
      isFinite
          (ofFields fmt (signBit x) (expField x) (fracField x)) =
        true := by
    simpa only [ofFields_signBit_expField_fracField] using hfinite
  have hmaximumNonneg : 0 ≤ toReal (posMaxFinite fmt) := by
    rw [toReal_posMaxFinite]
    exact mul_nonneg (Nat.cast_nonneg _) (bpow_nonneg _)
  rw [← ofFields_signBit_expField_fracField x]
  by_cases hexponentZero : expField x = 0
  · by_cases hfractionZero : fracField x = 0
    · rw [toReal_eq, toDyadic?_ofFields_of_isFinite fmt _ _ _ hexponentLt hfractionLt
        hfieldsFinite]
      simpa [hexponentZero, hfractionZero, Numerics.Dyadic.toReal,
        Numerics.Dyadic.signedSignificand] using hmaximumNonneg
    · rw [hexponentZero,
        toReal_ofFields_subnormal fmt (signBit x) (fracField x) hfractionZero hfractionLt]
      apply abs_signed_mul_bpow_le_toReal_posMaxFinite
      · rw [pow2_eq_two_pow]
        omega
      · have := fmt.maxFiniteExpField_pos
        unfold FloatFormat.minSubnormalExponent FloatFormat.minNormalExponent
          FloatFormat.maxNormalExponent
        simp only [Int.ofNat_eq_natCast]
        omega
  · rw [toReal_ofFields_normal_of_isFinite fmt (signBit x)
        (expField x) (fracField x) hexponentZero hexponentLt hfractionLt hfieldsFinite]
    by_cases hexponentMax : expField x = fmt.maxFiniteExpField
    · apply abs_signed_mul_bpow_le_toReal_posMaxFinite
      · have hfractionLe : fracField x ≤ fmt.maxFiniteFracField := by
          cases hencoding : fmt.encoding with
          | finiteMaxNaN =>
              have hallOnes : expField x = fmt.expAllOnesNat := by
                simp only [hexponentMax, FloatFormat.maxFiniteExpField,
                  FloatFormat.Encoding.maxFiniteExponent, FloatFormat.expAllOnesNat, hencoding]
              have hnotMask : fracField x ≠ fmt.fracMaskNat := by
                intro hmask
                simp [isFinite, isNaN, hencoding, hallOnes, hmask] at hfinite
              simp only [FloatFormat.maxFiniteFracField, hencoding,
                FloatFormat.fracMaskNat] at hnotMask ⊢
              omega
          | ieee | finiteUnsignedZero | finite =>
              simp only [FloatFormat.maxFiniteFracField, hencoding,
                FloatFormat.fracMaskNat]
              omega
        omega
      · unfold FloatFormat.maxNormalExponent
        simp only [Int.ofNat_eq_natCast]
        omega
    · have hmantissa : pow2 fmt.fracWidth + fracField x < 2 ^ (fmt.fracWidth + 1) := by
        rw [pow2_eq_two_pow, pow_succ]
        omega
      rw [abs_signed_mul_bpow]
      refine le_trans (natCast_mul_bpow_lt_bpow hmantissa ?_).le
        (bpow_maxNormalExponent_le_toReal_posMaxFinite fmt)
      unfold FloatFormat.maxNormalExponent
      simp only [Int.ofNat_eq_natCast]
      push_cast
      omega

/--
The decoded value of a word lies within the largest finite magnitude, in every encoding. This is
`abs_toReal_le_posMaxFinite_of_isFinite` read through the decoder.
-/
theorem abs_toReal_le_posMaxFinite_of_toDyadic?_some
    {fmt : FloatFormat} (x : Model fmt) {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) :
    |d.toReal| ≤ toReal (posMaxFinite fmt) := by
  simpa [toReal_eq, hd] using
    abs_toReal_le_posMaxFinite_of_isFinite x (isFinite_eq_true_of_toDyadic?_some hd)

/--
The leading bit of a nonzero decoded significand lies below the fraction width for a word with a
zero exponent field, whose exponent is the least subnormal exponent, and exactly at the fraction
width for a normal word, whose exponent is its unbiased field less the fraction width.
-/
theorem log2_significand_of_toDyadic?_some
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) (hm : d.significand ≠ 0) :
    (expField x = 0 ∧ d.significand.log2 < fmt.fracWidth ∧
        d.exponent = fmt.minSubnormalExponent) ∨
      (expField x ≠ 0 ∧ d.significand.log2 = fmt.fracWidth ∧
        d.exponent =
          Int.ofNat (expField x) - Int.ofNat fmt.exponentBias - Int.ofNat fmt.fracWidth) := by
  have hfrac := fracField_lt_pow2 x
  rcases toDyadic?_some_cases hd with ⟨hs, -⟩ | ⟨he, -, hs, hexp⟩ | ⟨he, hs, hexp⟩
  · exact absurd hs hm
  · exact Or.inl ⟨he, (Nat.log2_lt hm).2 (hs ▸ hfrac), hexp⟩
  · refine Or.inr ⟨he, le_antisymm ?_ ?_, hexp⟩
    · exact Nat.lt_succ_iff.mp <| (Nat.log2_lt hm).2 (by
        rw [hs, pow2_eq_two_pow, pow_succ]
        omega)
    · exact (Nat.le_log2 hm).2 (by rw [hs, pow2_eq_two_pow]; omega)

/-- The largest finite value is strictly below the next normal power of two. -/
theorem toReal_posMaxFinite_lt_bpow (fmt : FloatFormat) :
    toReal (posMaxFinite fmt) <
      bpow (fmt.maxNormalExponent + 1) := by
  rw [toReal_posMaxFinite]
  apply natCast_mul_bpow_lt_bpow (k := fmt.fracWidth + 1)
  · have hfraction := fmt.maxFiniteFracField_lt_two_pow
    simp only [pow2_eq_two_pow, pow_succ]
    omega
  · simp only [Int.ofNat_eq_natCast]
    push_cast
    omega

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
