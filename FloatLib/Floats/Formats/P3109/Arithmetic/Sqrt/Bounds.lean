/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Runtime
public import FloatLib.Floats.Formats.P3109.Projection.Rounding
public import Mathlib.Analysis.Real.Sqrt
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Logarithm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Exact square-root bounds for P3109

Integer square root after integer division gives the floor of the real square root of the
rational quotient. Cross multiplication of squared nonnegative thresholds preserves its order
exactly. These facts justify rounding even when the square root is irrational.

The precision bound proves that the rounded candidate fits the existing P3109 encoder for every
valid descriptor, including precision one and subnormal results.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic

/-- The square of the lower integer candidate does not exceed the rational radicand. -/
theorem sqrtFloor_sq_le (numerator denominator : Nat) (hd : 0 < denominator) :
    sqrtFloor numerator denominator ^ 2 * denominator ≤ numerator :=
  (Nat.le_div_iff_mul_le hd).mp (Nat.sqrt_le' _)

/-- The next candidate's square is strictly above the exact radicand. -/
theorem lt_succ_sqrtFloor_sq (numerator denominator : Nat) (hd : 0 < denominator) :
    numerator < (sqrtFloor numerator denominator + 1) ^ 2 * denominator :=
  (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_sqrt' _)

/-- Integer square root of the quotient brackets the actual real square root. -/
theorem sqrtFloor_real_bounds (numerator denominator : Nat) (hd : 0 < denominator) :
    (sqrtFloor numerator denominator : Real) ≤ Real.sqrt (numerator / denominator) ∧
      Real.sqrt (numerator / denominator) < sqrtFloor numerator denominator + 1 := by
  have hdReal : (0 : Real) < denominator := by exact_mod_cast hd
  have hn : (0 : Real) ≤ numerator / denominator := by positivity
  constructor
  · apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ hdReal).mpr
    exact_mod_cast sqrtFloor_sq_le numerator denominator hd
  · apply (Real.sqrt_lt hn (by positivity)).mpr
    apply (div_lt_iff₀ hdReal).mpr
    exact_mod_cast lt_succ_sqrtFloor_sq numerator denominator hd

/-- The executable lower candidate is the natural floor of the real square root. -/
theorem floor_real_sqrt (numerator denominator : Nat) (hd : 0 < denominator) :
    ⌊Real.sqrt (numerator / denominator)⌋₊ = sqrtFloor numerator denominator :=
  (Nat.floor_eq_iff (Real.sqrt_nonneg _)).mpr
    (sqrtFloor_real_bounds numerator denominator hd)

/-- Squaring a nonnegative rational threshold preserves strict comparison with the root. -/
theorem sqrt_lt_threshold_iff (numerator denominator scale threshold : Nat)
    (hd : 0 < denominator) (hs : 0 < scale) :
    Real.sqrt ((numerator : Real) / denominator) < (threshold : Real) / scale ↔
      numerator * scale ^ 2 < denominator * threshold ^ 2 := by
  have hdReal : (0 : Real) < denominator := by exact_mod_cast hd
  have hsReal : (0 : Real) < scale := by exact_mod_cast hs
  rw [Real.sqrt_lt (by positivity) (by positivity), div_pow,
    div_lt_div_iff₀ hdReal (pow_pos hsReal 2)]
  norm_cast
  rw [_root_.mul_comm (threshold ^ 2)]

/-- A rational threshold equals the real root exactly when its square equals the radicand. -/
theorem sqrt_eq_threshold_iff (numerator denominator scale threshold : Nat)
    (hd : 0 < denominator) (hs : 0 < scale) :
    Real.sqrt ((numerator : Real) / denominator) = (threshold : Real) / scale ↔
      numerator * scale ^ 2 = denominator * threshold ^ 2 := by
  have hdReal : (0 : Real) < denominator := by exact_mod_cast hd
  have hsReal : (0 : Real) < scale := by exact_mod_cast hs
  have hthreshold : (0 : Real) ≤ threshold / scale := by positivity
  rw [← Real.sqrt_sq hthreshold, Real.sqrt_inj (by positivity) (sq_nonneg _),
    div_pow, div_eq_div_iff (ne_of_gt hdReal) (ne_of_gt (pow_pos hsReal 2))]
  norm_cast
  rw [_root_.mul_comm (threshold ^ 2)]

/-- The integer comparator agrees with comparison of the real root. -/
theorem compareSqrt_eq_real (numerator denominator scale threshold : Nat)
    (hd : 0 < denominator) (hs : 0 < scale) :
    compareSqrt numerator denominator scale threshold =
      compare (Real.sqrt ((numerator : Real) / denominator)) ((threshold : Real) / scale) := by
  simp only [compareSqrt, LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq,
    sqrt_lt_threshold_iff numerator denominator scale threshold hd hs,
    sqrt_eq_threshold_iff numerator denominator scale threshold hd hs]

/-- The lower root candidate is strictly below the descriptor's significand limit. -/
theorem sqrtFloor_lt_precision (format : Format) (numerator denominator : Nat)
    (hn : numerator ≠ 0) (hd : denominator ≠ 0) :
    let quantum := sqrtQuantum format numerator denominator
    let scaled := RationalBinary.scaleByPowerOfTwo numerator denominator (-2 * quantum)
    sqrtFloor scaled.1 scaled.2 < 2 ^ format.precision := by
  let leading := RationalBinary.floorLog2 numerator denominator
  let quantum := sqrtQuantum format numerator denominator
  let scaled := RationalBinary.scaleByPowerOfTwo numerator denominator (-2 * quantum)
  have hscaledDenominator : scaled.2 ≠ 0 :=
    RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator (-2 * quantum) hd
  have hbounds :=
    BinaryInterchange.Model.scaleByPowerOfTwo_floorLog2_bounds
      numerator denominator (-2 * quantum) hn hd
  have hexponent : leading + (-2 * quantum) + 1 ≤ Int.ofNat (2 * format.precision) := by
    have hleading := le_max_left (leading / 2) format.minimumNormalExponent
    dsimp [quantum, sqrtQuantum, leading] at *
    omega
  have hratio : (scaled.1 : Real) / scaled.2 < ((2 ^ format.precision : Nat) : Real) ^ 2 := by
    have hupper : (scaled.1 : Real) / scaled.2 <
        BinaryInterchange.Model.bpow (leading + (-2 * quantum) + 1) := hbounds.2
    have hpower := (Flocq.bpow_le_bpow_iff Numerics.binaryRadix _ _).2 hexponent
    have hnat := BinaryInterchange.Model.bpow_ofNat (2 * format.precision)
    calc
      (scaled.1 : Real) / scaled.2 <
          BinaryInterchange.Model.bpow (Int.ofNat (2 * format.precision)) :=
        hupper.trans_le hpower
      _ = ((2 ^ format.precision : Nat) : Real) ^ 2 := by
        rw [hnat, BinaryInterchange.Model.pow2_eq_two_pow]
        norm_cast
        rw [Nat.mul_comm 2, pow_mul]
  have hdReal : (0 : Real) < scaled.2 := by
    exact_mod_cast Nat.pos_of_ne_zero hscaledDenominator
  have hmul : scaled.1 < (2 ^ format.precision) ^ 2 * scaled.2 := by
    exact_mod_cast (div_lt_iff₀ hdReal).mp hratio
  exact Nat.sqrt_lt'.mpr ((Nat.div_lt_iff_lt_mul
    (Nat.pos_of_ne_zero hscaledDenominator)).mpr hmul)

/-- Every mode's rounded square root fits the direct encoder's precision grid. -/
theorem roundSqrtRatToPrecision_fitsPrecisionGrid
    (format : Format) (mode : RoundingMode) (radicand : Rat) :
    format.FitsPrecisionGrid (roundSqrtRatToPrecision format mode radicand) := by
  unfold roundSqrtRatToPrecision
  simp only [beq_iff_eq]
  split
  · exact Or.inl rfl
  next hnonzero =>
    let quantum := sqrtQuantum format radicand.num.natAbs radicand.den
    let scaled :=
      RationalBinary.scaleByPowerOfTwo radicand.num.natAbs radicand.den (-2 * quantum)
    let lower := sqrtFloor scaled.1 scaled.2
    let rounded :=
      if sqrtRoundAway format mode quantum scaled.1 scaled.2 lower then lower + 1 else lower
    have hlower : lower < 2 ^ format.precision :=
      sqrtFloor_lt_precision format _ _ hnonzero radicand.den_nz
    have hrounded : rounded ≤ 2 ^ format.precision := by
      unfold rounded
      split <;> omega
    have hquantum : format.minimumQuantumExponent ≤ quantum :=
      format.quantumExponent_lower _
    change format.FitsPrecisionGrid
      (if rounded = 0 then .zero else ⟨false, rounded, quantum⟩)
    by_cases hzero : rounded = 0
    · simp [hzero, Format.FitsPrecisionGrid]
    · simp [hzero, Format.FitsPrecisionGrid, hrounded, hquantum]

end FloatLib.Floats.Formats.P3109.Arithmetic
