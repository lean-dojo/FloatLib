/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Scaling

/-!
# Binary exponent bounds for positive rational numbers

Before it rounds a positive quotient, the executable rational rounder places it between
consecutive powers of two with `Numerics.RationalBinary.floorLog2`. We prove that this placement
is right, independently of any format, including the asymmetric numerator and denominator cases
that make quotient normalization easy to get wrong.

One result serves every exponent width and both directed rounding modes. Division and conversion
proofs share this one rational lemma and don't repeat leading-bit arguments for each format.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

/-! ## Executable power-of-two comparisons -/

/--
`Numerics.RationalBinary.lessThanPowerOfTwo` tests whether a natural quotient is below a binary
power.
-/
theorem lessThanPowerOfTwo_eq_true_iff
    (numerator denominator : Nat) (exponent : Int)
    (hdenominator : denominator ≠ 0) :
    Numerics.RationalBinary.lessThanPowerOfTwo numerator denominator exponent = true ↔
      (numerator : Real) / (denominator : Real) < bpow exponent := by
  have hdenominatorPos : (0 : Real) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  rw [div_lt_iff₀ hdenominatorPos]
  cases exponent with
  | ofNat shift =>
      rw [Int.ofNat_eq_natCast, bpow_natCast, mul_comm]
      simp only [Numerics.RationalBinary.lessThanPowerOfTwo, decide_eq_true_eq]
      rw [show Nat.shiftLeft denominator shift = denominator * 2 ^ shift from
        Nat.shiftLeft_eq _ _]
      norm_cast
  | negSucc shift =>
      rw [bpow_negSucc, ← div_eq_inv_mul, lt_div_iff₀ (by rw [pow2_eq_two_pow]; positivity)]
      simp only [Numerics.RationalBinary.lessThanPowerOfTwo, decide_eq_true_eq, pow2_eq_two_pow]
      rw [show Nat.shiftLeft numerator (shift + 1) = numerator * 2 ^ (shift + 1) from
        Nat.shiftLeft_eq _ _]
      norm_cast

/--
`Numerics.RationalBinary.atLeastPowerOfTwo` tests whether a binary power is at most the real
quotient of two natural numbers with nonzero denominator.
-/
theorem atLeastPowerOfTwo_eq_true_iff
    (numerator denominator : Nat) (exponent : Int)
    (hdenominator : denominator ≠ 0) :
    Numerics.RationalBinary.atLeastPowerOfTwo numerator denominator exponent = true ↔
      bpow exponent ≤ (numerator : Real) / (denominator : Real) := by
  have hdenominatorPos : (0 : Real) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  rw [le_div_iff₀ hdenominatorPos]
  cases exponent with
  | ofNat shift =>
      rw [Int.ofNat_eq_natCast, bpow_natCast, mul_comm]
      simp only [Numerics.RationalBinary.atLeastPowerOfTwo, decide_eq_true_eq, ge_iff_le]
      rw [show Nat.shiftLeft denominator shift = denominator * 2 ^ shift from
        Nat.shiftLeft_eq _ _]
      norm_cast
  | negSucc shift =>
      rw [bpow_negSucc, ← div_eq_inv_mul, div_le_iff₀ (by rw [pow2_eq_two_pow]; positivity)]
      simp only [Numerics.RationalBinary.atLeastPowerOfTwo, decide_eq_true_eq, pow2_eq_two_pow,
        ge_iff_le]
      rw [show Nat.shiftLeft numerator (shift + 1) = numerator * 2 ^ (shift + 1) from
        Nat.shiftLeft_eq _ _]
      norm_cast

/-! ## Coarse logarithm bounds -/

/-- Closed form for the lower coarse exponent candidate. -/
theorem bpow_log2_sub_log2_sub_one
    (numeratorLog denominatorLog : Nat) :
    bpow (Int.ofNat numeratorLog - Int.ofNat denominatorLog - 1) =
      (2 : Real) ^ numeratorLog / (2 : Real) ^ denominatorLog.succ := by
  change (2 : ℝ) ^ (Int.ofNat numeratorLog - Int.ofNat denominatorLog - 1) =
    (2 : ℝ) ^ numeratorLog / (2 : ℝ) ^ denominatorLog.succ
  rw [zpow_sub₀ (by norm_num), zpow_sub₀ (by norm_num)]
  simp [pow_succ, div_eq_mul_inv]
  ring

/-- Closed form for the upper coarse exponent candidate. -/
theorem bpow_log2_sub_log2_add_one
    (numeratorLog denominatorLog : Nat) :
    bpow (Int.ofNat numeratorLog - Int.ofNat denominatorLog + 1) =
      (2 : Real) ^ numeratorLog.succ / (2 : Real) ^ denominatorLog := by
  have hexponent :
      Int.ofNat numeratorLog - Int.ofNat denominatorLog + 1 =
        Int.ofNat numeratorLog.succ - Int.ofNat denominatorLog := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [hexponent]
  change (2 : ℝ) ^ (Int.ofNat numeratorLog.succ - Int.ofNat denominatorLog) =
    (2 : ℝ) ^ numeratorLog.succ / (2 : ℝ) ^ denominatorLog
  rw [zpow_sub₀ (by norm_num)]
  rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]

/--
The difference of the numerator and denominator leading-bit positions locates a positive quotient
within one binary exponent.
-/
theorem log2_sub_log2_bounds
    (numerator denominator : Nat)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    let exponent :=
      Int.ofNat (Nat.log2 numerator) - Int.ofNat (Nat.log2 denominator)
    bpow (exponent - 1) ≤
        (numerator : Real) / (denominator : Real) ∧
      (numerator : Real) / (denominator : Real) <
        bpow (exponent + 1) := by
  let numeratorLog := Nat.log2 numerator
  let denominatorLog := Nat.log2 denominator
  let exponent := Int.ofNat numeratorLog - Int.ofNat denominatorLog
  have hnumeratorLower : 2 ^ numeratorLog ≤ numerator := by
    simpa [numeratorLog, Nat.log2_eq_log_two] using
      Nat.pow_log_le_self (b := 2) (x := numerator) hnumerator
  have hnumeratorUpper : numerator < 2 ^ numeratorLog.succ := by
    simpa [numeratorLog, Nat.log2_eq_log_two] using
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) numerator
  have hdenominatorLower : 2 ^ denominatorLog ≤ denominator := by
    simpa [denominatorLog, Nat.log2_eq_log_two] using
      Nat.pow_log_le_self (b := 2) (x := denominator) hdenominator
  have hdenominatorUpper : denominator < 2 ^ denominatorLog.succ := by
    simpa [denominatorLog, Nat.log2_eq_log_two] using
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) denominator
  have hnumeratorLowerReal :
      (2 : Real) ^ numeratorLog ≤ numerator := by
    exact_mod_cast hnumeratorLower
  have hnumeratorUpperReal :
      (numerator : Real) < (2 : Real) ^ numeratorLog.succ := by
    exact_mod_cast hnumeratorUpper
  have hdenominatorLowerReal :
      (2 : Real) ^ denominatorLog ≤ denominator := by
    exact_mod_cast hdenominatorLower
  have hdenominatorUpperReal :
      (denominator : Real) < (2 : Real) ^ denominatorLog.succ := by
    exact_mod_cast hdenominatorUpper
  have hdenominatorPos : (0 : Real) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  have hlower :
      (2 : Real) ^ numeratorLog / (2 : Real) ^ denominatorLog.succ ≤
        (numerator : Real) / denominator := by
    have hpowerPos : (0 : Real) < (2 : Real) ^ denominatorLog.succ :=
      pow_pos (by norm_num) _
    have hdenominatorLe :
        (denominator : Real) ≤ (2 : Real) ^ denominatorLog.succ :=
      hdenominatorUpperReal.le
    exact
      (div_le_div_of_nonneg_right hnumeratorLowerReal hpowerPos.le).trans
        (div_le_div_of_nonneg_left
          (Nat.cast_nonneg numerator) hdenominatorPos hdenominatorLe)
  have hupper :
      (numerator : Real) / denominator <
        (2 : Real) ^ numeratorLog.succ / (2 : Real) ^ denominatorLog := by
    have hpowerPos : (0 : Real) < (2 : Real) ^ denominatorLog :=
      pow_pos (by norm_num) _
    exact
      (div_lt_div_of_pos_right hnumeratorUpperReal hdenominatorPos).trans_le
        (div_le_div_of_nonneg_left
          (le_of_lt (pow_pos (by norm_num) _)) hpowerPos hdenominatorLowerReal)
  refine ⟨?_, ?_⟩
  · rw [show bpow (exponent - 1) =
        (2 : Real) ^ numeratorLog / (2 : Real) ^ denominatorLog.succ by
      simpa [exponent] using
        bpow_log2_sub_log2_sub_one numeratorLog denominatorLog]
    exact hlower
  · rw [show bpow (exponent + 1) =
        (2 : Real) ^ numeratorLog.succ / (2 : Real) ^ denominatorLog by
      simpa [exponent] using
        bpow_log2_sub_log2_add_one numeratorLog denominatorLog]
    exact hupper

/-! ## Exact floor-logarithm characterization -/

/-- Two intervals of the form `[2^e, 2^(e+1))` containing the same value have equal exponents. -/
theorem bpow_interval_exponent_unique
    (value : Real) (left right : Int)
    (hleftLower : bpow left ≤ value)
    (hleftUpper : value < bpow (left + 1))
    (hrightLower : bpow right ≤ value)
    (hrightUpper : value < bpow (right + 1)) :
    left = right := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hleftRight | hrightLeft
  · have hsuccessor : left + 1 ≤ right := by grind
    have hpower : bpow (left + 1) ≤ bpow right := by
      simpa [bpow, bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
        (zpow_le_zpow_iff_right₀ (by norm_num : (1 : Real) < 2)).2 hsuccessor
    exact (not_lt_of_ge (hpower.trans hrightLower)) hleftUpper
  · have hsuccessor : right + 1 ≤ left := by grind
    have hpower : bpow (right + 1) ≤ bpow left := by
      simpa [bpow, bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
        (zpow_le_zpow_iff_right₀ (by norm_num : (1 : Real) < 2)).2 hsuccessor
    exact (not_lt_of_ge (hpower.trans hleftLower)) hrightUpper

/--
`Numerics.RationalBinary.floorLog2` places a positive quotient between consecutive powers of two.
-/
theorem floorLog2_bounds
    (numerator denominator : Nat)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    let exponent := Numerics.RationalBinary.floorLog2 numerator denominator
    bpow exponent ≤ (numerator : Real) / (denominator : Real) ∧
      (numerator : Real) / (denominator : Real) < bpow (exponent + 1) := by
  let ratio : Real := (numerator : Real) / denominator
  let initialExponent :=
    Int.ofNat (Nat.log2 numerator) - Int.ofNat (Nat.log2 denominator)
  let lowerExponent :=
    if Numerics.RationalBinary.lessThanPowerOfTwo numerator denominator initialExponent then
      initialExponent - 1
    else
      initialExponent
  have hinitial :
      bpow (initialExponent - 1) ≤ ratio ∧
        ratio < bpow (initialExponent + 1) := by
    simpa [ratio, initialExponent] using
      log2_sub_log2_bounds numerator denominator hnumerator hdenominator
  have hlower : bpow lowerExponent ≤ ratio := by
    by_cases hlt : Numerics.RationalBinary.lessThanPowerOfTwo numerator denominator initialExponent = true
    · have hexponent : lowerExponent = initialExponent - 1 := by
        simp [lowerExponent, hlt]
      simpa [hexponent] using hinitial.1
    · have hltFalse :
          Numerics.RationalBinary.lessThanPowerOfTwo numerator denominator initialExponent = false := by
        simpa using hlt
      have hexponent : lowerExponent = initialExponent := by
        simp [lowerExponent, hltFalse]
      have hnotLt :
          ¬ratio < bpow initialExponent := by
        intro hratio
        exact hlt <|
          (lessThanPowerOfTwo_eq_true_iff numerator denominator initialExponent hdenominator).2
            (by simpa [ratio] using hratio)
      simpa [hexponent] using le_of_not_gt hnotLt
  have hupper : ratio < bpow (lowerExponent + 1) := by
    by_cases hlt : Numerics.RationalBinary.lessThanPowerOfTwo numerator denominator initialExponent = true
    · have hexponent : lowerExponent = initialExponent - 1 := by
        simp [lowerExponent, hlt]
      have hratio :
          ratio < bpow initialExponent :=
        (lessThanPowerOfTwo_eq_true_iff
          numerator denominator initialExponent hdenominator).1 hlt
      simpa [hexponent] using hratio
    · have hexponent : lowerExponent = initialExponent := by
        simp [lowerExponent, hlt]
      simpa [hexponent] using hinitial.2
  have hfinalFalse :
      Numerics.RationalBinary.atLeastPowerOfTwo numerator denominator (lowerExponent + 1) = false := by
    by_contra hnotFalse
    have htrue :
        Numerics.RationalBinary.atLeastPowerOfTwo numerator denominator (lowerExponent + 1) = true := by
      exact Bool.eq_true_of_not_eq_false hnotFalse
    have hratio :
        bpow (lowerExponent + 1) ≤ ratio :=
      (atLeastPowerOfTwo_eq_true_iff
        numerator denominator (lowerExponent + 1) hdenominator).1 htrue
    exact (not_lt_of_ge hratio) hupper
  have hfloor :
      Numerics.RationalBinary.floorLog2 numerator denominator = lowerExponent := by
    simp only [Numerics.RationalBinary.floorLog2]
    rw [show
      (Int.ofNat (Nat.log2 numerator) - Int.ofNat (Nat.log2 denominator)) =
        initialExponent by rfl]
    rw [show
      (if Numerics.RationalBinary.lessThanPowerOfTwo numerator denominator initialExponent then
          initialExponent - 1
        else initialExponent) = lowerExponent by rfl]
    simp [hfinalFalse]
  simpa [hfloor, ratio] using And.intro hlower hupper

/-- The shift-based rational logarithm agrees with Mathlib's integer logarithm on positive inputs. -/
theorem floorLog2_eq_int_log (numerator denominator : Nat)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    Numerics.RationalBinary.floorLog2 numerator denominator =
      Int.log 2 ((numerator : ℝ) / denominator) := by
  have hratio : 0 < (numerator : ℝ) / denominator :=
    div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hnumerator))
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdenominator))
  have h := floorLog2_bounds numerator denominator hnumerator hdenominator
  change (2 : ℝ) ^ _ ≤ _ ∧ _ < (2 : ℝ) ^ _ at h
  have hl := (Int.zpow_le_iff_le_log (by decide : 1 < 2) hratio).mp h.1
  have hu := (Int.lt_zpow_iff_log_lt (by decide : 1 < 2) hratio).mp h.2
  omega

/-- Viewing a positive natural number as a quotient by one preserves its floor binary logarithm. -/
theorem floorLog2_den_one (n : Nat) (hn : n ≠ 0) :
    Numerics.RationalBinary.floorLog2 n 1 = (n.log2 : Int) := by
  simpa only [Nat.cast_one, div_one, Int.log_natCast, Nat.log2_eq_log_two,
    Int.ofNat_eq_natCast] using floorLog2_eq_int_log n 1 hn (by decide)

/--
A binary interval characterization determines `Numerics.RationalBinary.floorLog2`. The positive
lower bound forces a nonzero numerator and denominator.
-/
theorem floorLog2_eq_of_bounds
    (numerator denominator : Nat) (exponent : Int)
    (hlower :
      bpow exponent ≤ (numerator : Real) / (denominator : Real))
    (hupper :
      (numerator : Real) / (denominator : Real) < bpow (exponent + 1)) :
    Numerics.RationalBinary.floorLog2 numerator denominator = exponent := by
  have hpositive : 0 < (numerator : Real) / (denominator : Real) :=
    (bpow_pos exponent).trans_le hlower
  have hnumerator : numerator ≠ 0 := by
    rintro rfl
    simp at hpositive
  have hdenominator : denominator ≠ 0 := by
    rintro rfl
    simp at hpositive
  have hfloor :=
    floorLog2_bounds numerator denominator hnumerator hdenominator
  exact bpow_interval_exponent_unique
    ((numerator : Real) / (denominator : Real))
    (Numerics.RationalBinary.floorLog2 numerator denominator) exponent
    hfloor.1 hfloor.2 hlower hupper

/--
The leading exponent of a scaled positive rational bounds its exact real value between
consecutive binary powers.
-/
theorem scaledRatToReal_floorLog2_bounds
    (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    bpow (Numerics.RationalBinary.floorLog2 numerator denominator + exponent) ≤
        scaledRatToReal numerator denominator exponent ∧
      scaledRatToReal numerator denominator exponent <
        bpow (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1) := by
  have hbounds :=
    floorLog2_bounds numerator denominator hnumerator hdenominator
  constructor
  · rw [bpow_add]
    exact mul_le_mul_of_nonneg_right hbounds.1 (bpow_nonneg exponent)
  · calc
      scaledRatToReal numerator denominator exponent =
          (numerator : Real) / denominator * bpow exponent := rfl
      _ < bpow (Numerics.RationalBinary.floorLog2 numerator denominator + 1) * bpow exponent :=
        mul_lt_mul_of_pos_right hbounds.2 (bpow_pos exponent)
      _ = bpow (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1) := by
        rw [← bpow_add]
        congr 1
        ring

/-- Exact binary scaling adds its exponent to the rational floor logarithm. -/
theorem floorLog2_scaleByPowerOfTwo
    (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    Numerics.RationalBinary.floorLog2 (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator exponent).1
        (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator exponent).2 =
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent := by
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator exponent
  have hscaledNumerator : scaled.1 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_fst_ne_zero numerator denominator exponent hnumerator
  have hscaledDenominator : scaled.2 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator exponent hdenominator
  obtain ⟨hlower, hupper⟩ :=
    scaledRatToReal_floorLog2_bounds numerator denominator exponent hnumerator hdenominator
  rw [← scaleByPowerOfTwo_real] at hlower hupper
  exact floorLog2_eq_of_bounds scaled.1 scaled.2 _ hlower hupper

/--
After moving an external binary exponent into a positive rational, its quotient stays between
the binary powers determined by the original leading exponent plus that scale.
-/
theorem scaleByPowerOfTwo_floorLog2_bounds
    (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator exponent
    bpow (Numerics.RationalBinary.floorLog2 numerator denominator + exponent) ≤
        (scaled.1 : Real) / (scaled.2 : Real) ∧
      (scaled.1 : Real) / (scaled.2 : Real) <
        bpow (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1) := by
  dsimp only
  rw [scaleByPowerOfTwo_real]
  exact scaledRatToReal_floorLog2_bounds numerator denominator exponent hnumerator hdenominator

/-! ## Comparison with a positive dyadic -/

/-- Dividing by a positive real is strictly monotone, so it preserves comparisons. -/
private theorem compare_div_one_eq_compare
    (left right : Real) (hright : 0 < right) :
    compare (left / right) 1 = compare left right := by
  have hmono : StrictMono fun value : Real => value / right :=
    fun _ _ h => div_lt_div_of_pos_right h hright
  simpa only [cmp_eq_compare, div_self hright.ne'] using hmono.cmp_map_eq left right

/-- The cast of natural numbers to the reals preserves comparisons. -/
private theorem compare_eq_compare_natCast (left right : Nat) :
    compare left right = compare (left : Real) (right : Real) := by
  simpa only [cmp_eq_compare] using (Nat.strictMono_cast.cmp_map_eq left right).symm

private theorem scaledRatToReal_div_positiveDyadic
    (numerator denominator : Nat) (exponent : Int)
    (value : Numerics.Dyadic)
    (hdenominator : denominator ≠ 0)
    (hvalueSign : value.negative = false)
    (hvalue : value.significand ≠ 0) :
    scaledRatToReal numerator denominator exponent / value.toReal =
      scaledRatToReal numerator (denominator * value.significand)
        (exponent - value.exponent) := by
  have hdenominatorReal : (denominator : Real) ≠ 0 := by
    exact_mod_cast hdenominator
  have hvalueReal : (value.significand : Real) ≠ 0 := by
    exact_mod_cast hvalue
  have hpower : bpow value.exponent ≠ 0 :=
    ne_of_gt (bpow_pos value.exponent)
  simp only [scaledRatToReal, Numerics.Dyadic.toReal,
    Numerics.Dyadic.signedSignificand, hvalueSign, Bool.false_eq_true, ite_false]
  simp only [Nat.cast_mul]
  change
    (numerator : Real) / denominator * bpow exponent /
        ((value.significand : Real) * bpow value.exponent) =
      (numerator : Real) / (denominator * value.significand) *
        bpow (exponent - value.exponent)
  rw [show bpow (exponent - value.exponent) =
      bpow exponent / bpow value.exponent by
    exact FloatLib.Floats.Formats.Flocq.bpow.sub_exp
      Numerics.binaryRadix exponent value.exponent]
  field_simp [hdenominatorReal, hvalueReal, hpower]

private theorem compareScaledPositiveMagnitude
    (numerator denominator : Nat) (exponent : Int)
    (value : Numerics.Dyadic)
    (hnumerator : numerator ≠ 0)
    (hdenominator : denominator ≠ 0)
    (hvalueSign : value.negative = false)
    (hvalue : value.significand ≠ 0) :
    let relativeExponent := exponent - value.exponent
    let scaledDenominator := denominator * value.significand
    let leadingExponent :=
      Numerics.RationalBinary.floorLog2 numerator scaledDenominator +
        relativeExponent
    let magnitudeOrder :=
      if leadingExponent < 0 then
        .lt
      else if leadingExponent > 0 then
        .gt
      else
        let scaled :=
          Numerics.RationalBinary.scaleByPowerOfTwo
            numerator scaledDenominator relativeExponent
        compare scaled.1 scaled.2
    magnitudeOrder =
      compare (scaledRatToReal numerator denominator exponent) value.toReal := by
  dsimp only
  have hscaledDenominator : denominator * value.significand ≠ 0 :=
    Nat.mul_ne_zero hdenominator hvalue
  have hvaluePositive := Dyadic.toReal_pos_of_negative_eq_false hvalueSign hvalue
  have hbounds :=
    scaledRatToReal_floorLog2_bounds numerator (denominator * value.significand)
      (exponent - value.exponent) hnumerator hscaledDenominator
  rw [← compare_div_one_eq_compare _ _ hvaluePositive,
    scaledRatToReal_div_positiveDyadic numerator denominator exponent value
      hdenominator hvalueSign hvalue]
  split_ifs with hless hgreater
  · symm
    apply compare_lt_iff_lt.mpr
    refine hbounds.2.trans_le ?_
    rw [← bpow_zero]
    exact (FloatLib.Floats.Formats.Flocq.bpow_le_bpow_iff Numerics.binaryRadix _ _).2 (by omega)
  · symm
    apply compare_gt_iff_gt.mpr
    refine lt_of_lt_of_le ?_ hbounds.1
    rw [← bpow_zero]
    exact (FloatLib.Floats.Formats.Flocq.bpow_lt_bpow_iff Numerics.binaryRadix _ _).2 hgreater
  · have hpositive :
        (0 : Real) <
          (Numerics.RationalBinary.scaleByPowerOfTwo numerator (denominator * value.significand)
            (exponent - value.exponent)).2 := by
      exact_mod_cast Nat.pos_of_ne_zero
        (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero _ _ _ hscaledDenominator)
    rw [compare_eq_compare_natCast, ← compare_div_one_eq_compare _ _ hpositive,
      scaleByPowerOfTwo_real]

/--
The optimized comparison of a nonnegative scaled rational with a positive dyadic returns their
real-number ordering.

The comparison first uses the leading exponent of the ratio to the dyadic. Only when that
exponent is zero does it compare the scaled numerator and denominator.
-/
private theorem compareDyadicScaled?_false_eq_compare_of_positive
    (numerator denominator : Nat) (exponent : Int)
    (value : Numerics.Dyadic)
    (hdenominator : denominator ≠ 0)
    (hvalueSign : value.negative = false)
    (hvalue : value.significand ≠ 0) :
    Numerics.RationalBinary.compareDyadicScaled?
        false numerator denominator exponent value =
      some (compare
        (scaledRatToReal numerator denominator exponent) value.toReal) := by
  by_cases hnumerator : numerator = 0
  · subst numerator
    have hvaluePositive := Dyadic.toReal_pos_of_negative_eq_false hvalueSign hvalue
    have hcomparison :
        compare (scaledRatToReal 0 denominator exponent) value.toReal =
          .lt := by
      apply compare_lt_iff_lt.mpr
      simpa [scaledRatToReal] using hvaluePositive
    simp [Numerics.RationalBinary.compareDyadicScaled?,
      hdenominator, hvalue, hvalueSign, hcomparison]
  · simpa [Numerics.RationalBinary.compareDyadicScaled?,
      hdenominator, hnumerator, hvalue, hvalueSign] using
      compareScaledPositiveMagnitude
        numerator denominator exponent value hnumerator hdenominator
          hvalueSign hvalue

/-! ## Comparison with an arbitrary dyadic -/

/-- Negation is strictly antitone, so it reverses comparisons. -/
private theorem compare_neg_neg_eq_swap (left right : Real) :
    compare (-left) (-right) = (compare left right).swap := by
  have hanti : StrictAnti fun value : Real => -value := fun _ _ h => neg_lt_neg h
  rw [← cmp_eq_compare, ← cmp_eq_compare, hanti.cmp_map_eq, cmp_swap]

private theorem dyadic_toReal_eq_zero (value : Numerics.Dyadic)
    (hvalue : value.significand = 0) :
    value.toReal = 0 := by
  simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hvalue]

private theorem dyadic_toReal_neg (value : Numerics.Dyadic)
    (hvalueSign : value.negative = true) :
    value.toReal = -({ value with negative := false } : Numerics.Dyadic).toReal := by
  simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hvalueSign]

/--
The optimized comparison of a signed scaled rational with an arbitrary dyadic returns their
real-number ordering whenever the denominator is nonzero.

Zero operands and opposite signs are decided from the signs alone. Two negative operands compare
their magnitudes in reverse order, which reduces to the comparison of two positive values.
-/
theorem compareDyadicScaled?_eq_compare
    (negative : Bool) (numerator denominator : Nat) (exponent : Int)
    (value : Numerics.Dyadic) (hdenominator : denominator ≠ 0) :
    Numerics.RationalBinary.compareDyadicScaled?
        negative numerator denominator exponent value =
      some (compare (signedScaledRatToReal negative numerator denominator exponent)
        value.toReal) := by
  by_cases hnumerator : numerator = 0
  · subst numerator
    have hzero : signedScaledRatToReal negative 0 denominator exponent = 0 := by
      cases negative <;> simp [signedScaledRatToReal, scaledRatToReal]
    rw [hzero]
    by_cases hvalue : value.significand = 0
    · simp [Numerics.RationalBinary.compareDyadicScaled?, hdenominator, hvalue,
        dyadic_toReal_eq_zero value hvalue]
    · cases hvalueSign : value.negative
      · simp [Numerics.RationalBinary.compareDyadicScaled?, hdenominator, hvalue, hvalueSign,
          compare_lt_iff_lt.mpr (Dyadic.toReal_pos_of_negative_eq_false hvalueSign hvalue)]
      · simp [Numerics.RationalBinary.compareDyadicScaled?, hdenominator, hvalue, hvalueSign,
          compare_gt_iff_gt.mpr (Dyadic.toReal_lt_zero_of_negative_eq_true hvalueSign hvalue)]
  · have hrational := scaledRatToReal_pos numerator denominator exponent hnumerator hdenominator
    by_cases hvalue : value.significand = 0
    · cases negative
      · simp [Numerics.RationalBinary.compareDyadicScaled?, hdenominator, hnumerator, hvalue,
          signedScaledRatToReal, dyadic_toReal_eq_zero value hvalue,
          compare_gt_iff_gt.mpr hrational]
      · simp [Numerics.RationalBinary.compareDyadicScaled?, hdenominator, hnumerator, hvalue,
          signedScaledRatToReal, dyadic_toReal_eq_zero value hvalue,
          compare_lt_iff_lt.mpr (neg_lt_zero.mpr hrational)]
    · cases negative <;> cases hvalueSign : value.negative
      · simpa [signedScaledRatToReal] using
          compareDyadicScaled?_false_eq_compare_of_positive numerator denominator exponent value
            hdenominator hvalueSign hvalue
      · have hnegative := Dyadic.toReal_lt_zero_of_negative_eq_true hvalueSign hvalue
        simp [Numerics.RationalBinary.compareDyadicScaled?, hdenominator, hnumerator, hvalue,
          hvalueSign, signedScaledRatToReal, compare_gt_iff_gt.mpr (hnegative.trans hrational)]
      · have hpositive := Dyadic.toReal_pos_of_negative_eq_false hvalueSign hvalue
        simp [Numerics.RationalBinary.compareDyadicScaled?, hdenominator, hnumerator, hvalue,
          hvalueSign, signedScaledRatToReal,
          compare_lt_iff_lt.mpr ((neg_lt_zero.mpr hrational).trans hpositive)]
      · have hfalse :=
          compareDyadicScaled?_false_eq_compare_of_positive numerator denominator exponent
            { value with negative := false } hdenominator rfl hvalue
        have hunfold :
            Numerics.RationalBinary.compareDyadicScaled? true numerator denominator exponent
                value =
              (Numerics.RationalBinary.compareDyadicScaled? false numerator denominator exponent
                { value with negative := false }).map Ordering.swap := by
          simp [Numerics.RationalBinary.compareDyadicScaled?, hdenominator, hnumerator, hvalue,
            hvalueSign]
        rw [hunfold, hfalse, dyadic_toReal_neg value hvalueSign]
        simp [signedScaledRatToReal, compare_neg_neg_eq_swap]


/--
The optimized comparison of a nonnegative scaled rational with any dyadic returns their real-number
ordering whenever the denominator is nonzero.
-/
theorem compareDyadicScaled?_false_eq_compare
    (numerator denominator : Nat) (exponent : Int)
    (value : Numerics.Dyadic)
    (hdenominator : denominator ≠ 0) :
    Numerics.RationalBinary.compareDyadicScaled?
        false numerator denominator exponent value =
      some (compare
        (scaledRatToReal numerator denominator exponent) value.toReal) := by
  simpa [signedScaledRatToReal] using
    compareDyadicScaled?_eq_compare false numerator denominator exponent value hdenominator

/-- Nonnegative scaled-rational comparison returns `.lt` if and only if the real order is strict. -/
theorem compareDyadicScaled?_false_eq_lt_iff
    (numerator denominator : Nat) (exponent : Int)
    (value : Numerics.Dyadic)
    (hdenominator : denominator ≠ 0) :
    Numerics.RationalBinary.compareDyadicScaled?
        false numerator denominator exponent value = some .lt ↔
      scaledRatToReal numerator denominator exponent < value.toReal := by
  rw [compareDyadicScaled?_false_eq_compare
    numerator denominator exponent value hdenominator]
  simp [compare_lt_iff_lt]

/-- Nonnegative scaled-rational comparison returns `.eq` if and only if the reals are equal. -/
theorem compareDyadicScaled?_false_eq_eq_iff
    (numerator denominator : Nat) (exponent : Int)
    (value : Numerics.Dyadic)
    (hdenominator : denominator ≠ 0) :
    Numerics.RationalBinary.compareDyadicScaled?
        false numerator denominator exponent value = some .eq ↔
      scaledRatToReal numerator denominator exponent = value.toReal := by
  rw [compareDyadicScaled?_false_eq_compare
    numerator denominator exponent value hdenominator]
  simp

/-- Nonnegative scaled-rational comparison returns `.gt` if and only if the reverse is strict. -/
theorem compareDyadicScaled?_false_eq_gt_iff
    (numerator denominator : Nat) (exponent : Int)
    (value : Numerics.Dyadic)
    (hdenominator : denominator ≠ 0) :
    Numerics.RationalBinary.compareDyadicScaled?
        false numerator denominator exponent value = some .gt ↔
      value.toReal < scaledRatToReal numerator denominator exponent := by
  rw [compareDyadicScaled?_false_eq_compare
    numerator denominator exponent value hdenominator]
  simp [compare_gt_iff_gt]

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
