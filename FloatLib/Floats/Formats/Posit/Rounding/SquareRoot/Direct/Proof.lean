/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Direct.PrefixProof
public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Proof
import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Correctness of direct posit square-root packing

The integer-root prefix and its exact sticky bit select the same Posit as exact squared-boundary
rounding. The proof uses rational points inside the generated root cell to bracket the
mathematical square root. Both rational witnesses round to the same posit, so monotonicity
identifies the rounding of the root between them.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DirectDyadicSquareRoot

open FloatLib.Numerics

/-- Denominator chosen to place rational witnesses close to both ends of an integer root cell. -/
private def cellDenominator (root : Nat) : Nat :=
  4 * (root + 1)

private theorem cellDenominator_pos (root : Nat) :
    0 < cellDenominator root := by
  simp [cellDenominator]

private theorem one_lt_cellDenominator (root : Nat) :
    1 < cellDenominator root := by
  unfold cellDenominator
  omega

/-- The lower rational witness squares to less than `root² + 1`. -/
private theorem lowerFraction_square_lt_succ_square
    (root : Nat) :
    ((root : Rat) + 1 / (cellDenominator root : Nat)) *
        ((root : Rat) + 1 / (cellDenominator root : Nat)) <
      (root : Rat) * root + 1 := by
  have hroot : (0 : Rat) ≤ root := by positivity
  have hdenominator : (0 : Rat) < cellDenominator root := by
    exact_mod_cast cellDenominator_pos root
  unfold cellDenominator
  field_simp
  push_cast at *
  nlinarith

/-- The upper rational witness squares to more than `(root + 1)² - 1`. -/
private theorem predFraction_square_gt_pred_square
    (root : Nat) :
    (root : Rat) * root + 2 * root <
      ((root : Rat) + (cellDenominator root - 1 : Nat) /
          (cellDenominator root : Nat)) *
        ((root : Rat) + (cellDenominator root - 1 : Nat) /
          (cellDenominator root : Nat)) := by
  have hroot : (0 : Rat) ≤ root := by positivity
  have hdenominatorNat := cellDenominator_pos root
  have hdenominator : (0 : Rat) < cellDenominator root := by
    exact_mod_cast hdenominatorNat
  have hpred :
      ((cellDenominator root - 1 : Nat) : Rat) =
        (cellDenominator root : Rat) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hpred]
  unfold cellDenominator at *
  field_simp
  push_cast at *
  nlinarith

/-- For an inexact integer root, the lower witness's square is below the scaled radicand. -/
private theorem lowerFraction_square_lt_scaled
    (precision : Nat) (radicand : FloatLib.Numerics.Dyadic)
    (hremainder : squareRemainder precision radicand ≠ 0) :
    let root := truncatedRoot precision radicand
    ((root : Rat) + 1 / (cellDenominator root : Nat)) *
        ((root : Rat) + 1 / (cellDenominator root : Nat)) <
      (scaledRadicand precision radicand : Rat) := by
  let root := truncatedRoot precision radicand
  have hrootSquareLe :=
    truncatedRoot_square_le precision radicand
  change root * root ≤ scaledRadicand precision radicand at hrootSquareLe
  have hrootSquareNe :
      scaledRadicand precision radicand ≠ root * root := by
    intro heq
    apply hremainder
    exact (squareRemainder_eq_zero_iff precision radicand).2
      (by simpa [root] using heq)
  have hgap :
      root * root + 1 ≤ scaledRadicand precision radicand := by
    omega
  exact
    (lowerFraction_square_lt_succ_square root).trans_le
      (by exact_mod_cast hgap)

/-- The upper witness's square exceeds the scaled radicand. -/
private theorem scaled_lt_predFraction_square
    (precision : Nat) (radicand : FloatLib.Numerics.Dyadic) :
    let root := truncatedRoot precision radicand
    (scaledRadicand precision radicand : Rat) <
      ((root : Rat) + (cellDenominator root - 1 : Nat) /
          (cellDenominator root : Nat)) *
        ((root : Rat) + (cellDenominator root - 1 : Nat) /
          (cellDenominator root : Nat)) := by
  let root := truncatedRoot precision radicand
  have hnext :=
    scaledRadicand_lt_succ_truncatedRoot_square precision radicand
  have hnextExpand :
      (root + 1) * (root + 1) =
        root * root + 2 * root + 1 := by
    ring
  rw [hnextExpand] at hnext
  have hgap :
      scaledRadicand precision radicand ≤
        root * root + 2 * root := by
    omega
  exact
    (by exact_mod_cast hgap : (scaledRadicand precision radicand : Rat) ≤
      (root : Rat) * root + 2 * root) |>.trans_lt
      (predFraction_square_gt_pred_square root)

/-- Denominator of the rational witnesses chosen inside the root cell of `radicand`. -/
private def rootCellDenominator
    (format : Format) (radicand : FloatLib.Numerics.Dyadic) : Nat :=
  cellDenominator (truncatedRoot (prefixPrecision format) radicand)

/-- Squaring a root cell point separates the cell fraction from the restored root scale. -/
private theorem rootCellPoint_mul_self
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (remainder denominator : Nat) :
    rootCellPoint format radicand remainder denominator *
        rootCellPoint format radicand remainder denominator =
      (((truncatedRoot (prefixPrecision format) radicand : Nat) : Rat) +
            (remainder : Rat) / (denominator : Rat)) *
          (((truncatedRoot (prefixPrecision format) radicand : Nat) : Rat) +
            (remainder : Rat) / (denominator : Rat)) *
        ((2 : Rat) ^ (radicand.exponent.ediv 2 - Int.ofNat (prefixPrecision format)) *
          (2 : Rat) ^ (radicand.exponent.ediv 2 - Int.ofNat (prefixPrecision format))) := by
  unfold rootCellPoint
  ring

/-- A root cell point with a positive cell fraction is positive. -/
private theorem rootCellPoint_pos
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    {remainder denominator : Nat}
    (hremainder : 0 < remainder) (hdenominator : 0 < denominator) :
    0 < rootCellPoint format radicand remainder denominator := by
  have hremainderRat : (0 : Rat) < remainder := by exact_mod_cast hremainder
  have hdenominatorRat : (0 : Rat) < denominator := by exact_mod_cast hdenominator
  have hscale :
      (0 : Rat) <
        (2 : Rat) ^ (radicand.exponent.ediv 2 - Int.ofNat (prefixPrecision format)) :=
    zpow_pos (by norm_num) _
  unfold rootCellPoint
  positivity

/-- The lower cell witness lies strictly below the mathematical square root. -/
private theorem lowerRootCellPoint_lt_sqrt
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (hnegative : radicand.negative = false)
    (hremainder :
      squareRemainder (prefixPrecision format) radicand ≠ 0) :
    (rootCellPoint format radicand 1 (rootCellDenominator format radicand) : Real) <
      Real.sqrt (radicand.toRat : Real) := by
  have hcell :=
    lowerFraction_square_lt_scaled (prefixPrecision format) radicand hremainder
  have hscaleSquarePositive :
      (0 : Rat) <
        (2 : Rat) ^ (radicand.exponent.ediv 2 - Int.ofNat (prefixPrecision format)) *
          (2 : Rat) ^ (radicand.exponent.ediv 2 - Int.ofNat (prefixPrecision format)) :=
    mul_pos (zpow_pos (by norm_num) _) (zpow_pos (by norm_num) _)
  rw [Real.lt_sqrt (by
    exact_mod_cast (rootCellPoint_pos format radicand one_pos (cellDenominator_pos _)).le)]
  norm_cast
  rw [pow_two, rootCellPoint_mul_self,
    toRat_eq_scaledRadicand_mul_scale_sq (prefixPrecision format) radicand hnegative]
  simpa [rootCellDenominator, mul_assoc] using
    mul_lt_mul_of_pos_right hcell hscaleSquarePositive

/-- The upper cell witness lies strictly above the mathematical square root. -/
private theorem sqrt_lt_upperRootCellPoint
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (hnegative : radicand.negative = false) :
    Real.sqrt (radicand.toRat : Real) <
      (rootCellPoint format radicand (rootCellDenominator format radicand - 1)
        (rootCellDenominator format radicand) : Real) := by
  have hcell :=
    scaled_lt_predFraction_square (prefixPrecision format) radicand
  have hscaleSquarePositive :
      (0 : Rat) <
        (2 : Rat) ^ (radicand.exponent.ediv 2 - Int.ofNat (prefixPrecision format)) *
          (2 : Rat) ^ (radicand.exponent.ediv 2 - Int.ofNat (prefixPrecision format)) :=
    mul_pos (zpow_pos (by norm_num) _) (zpow_pos (by norm_num) _)
  have hone := one_lt_cellDenominator (truncatedRoot (prefixPrecision format) radicand)
  rw [Real.sqrt_lt' (by
    exact_mod_cast rootCellPoint_pos format radicand
      (by unfold rootCellDenominator; omega) (cellDenominator_pos _))]
  norm_cast
  rw [pow_two, rootCellPoint_mul_self,
    toRat_eq_scaledRadicand_mul_scale_sq (prefixPrecision format) radicand hnegative]
  simpa [rootCellDenominator, mul_assoc] using
    mul_lt_mul_of_pos_right hcell hscaleSquarePositive

/-- With zero square remainder, the root cell's lower endpoint is the exact square root. -/
private theorem exactRootCellPoint_eq_sqrt
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (hsignificand : radicand.significand ≠ 0)
    (hnegative : radicand.negative = false)
    (hremainder :
      squareRemainder (prefixPrecision format) radicand = 0) :
    (rootCellPoint format radicand 0 1 : Real) =
      Real.sqrt (radicand.toRat : Real) := by
  let precision := prefixPrecision format
  let root := truncatedRoot precision radicand
  let scale : Rat :=
    (2 : Rat) ^
      (radicand.exponent.ediv 2 - Int.ofNat precision)
  have hrootPositive :
      0 < root := by
    exact truncatedRoot_pos precision radicand hsignificand
  have hscalePositive : 0 < scale :=
    zpow_pos (by norm_num) _
  have hpoint :
      rootCellPoint format radicand 0 1 =
        (root : Rat) * scale := by
    simp [rootCellPoint, precision, root, scale]
  have hscaled :
      scaledRadicand precision radicand = root * root := by
    simpa [precision, root] using
      (squareRemainder_eq_zero_iff precision radicand).1
        (by simpa [precision] using hremainder)
  have hsource :=
    toRat_eq_scaledRadicand_mul_scale_sq
      precision radicand hnegative
  change
    radicand.toRat =
      (scaledRadicand precision radicand : Rat) * scale * scale at hsource
  have hsourcePoint :
      radicand.toRat =
        rootCellPoint format radicand 0 1 *
          rootCellPoint format radicand 0 1 := by
    rw [hsource, hpoint, hscaled, Nat.cast_mul]
    ring
  have hsourceNonnegative : (0 : Real) ≤ (radicand.toRat : Real) := by
    exact_mod_cast
      (FloatLib.Numerics.Dyadic.toRat_pos_of_significand_ne_zero
        radicand hsignificand hnegative).le
  have hpointNonnegative :
      (0 : Real) ≤
        (rootCellPoint format radicand 0 1 : Real) := by
    rw [hpoint]
    positivity
  symm
  apply
    (Real.sqrt_eq_iff_mul_self_eq
      hsourceNonnegative hpointNonnegative).2
  exact_mod_cast hsourcePoint

/--
The destination-width prefix kernel equals exact squared-boundary rounding on every nonnegative
input.
-/
theorem roundCode_eq_dyadic
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (hnegative : radicand.negative = false) :
    roundCode format radicand =
      DyadicSquareRoot.roundCode format radicand := by
  by_cases hsignificand : radicand.significand = 0
  · simp [roundCode, DyadicSquareRoot.roundCode,
      hsignificand, hnegative]
  have hradicandPositive :
      0 < radicand.toRat :=
    FloatLib.Numerics.Dyadic.toRat_pos_of_significand_ne_zero
      radicand hsignificand hnegative
  rw [DyadicSquareRoot.roundCode_eq_reference_of_nonnegative
      format radicand hnegative,
    Model.roundSqrtCode_eq_roundPositiveCode
      format radicand.toRat hradicandPositive.le]
  by_cases hremainder :
      squareRemainder (prefixPrecision format) radicand = 0
  · rw [roundCode_eq_fraction format radicand 0 1 hsignificand hnegative
        one_pos one_pos (by simp [hremainder]),
      ← Model.RealRounding.roundPositiveCode_ratCast,
      exactRootCellPoint_eq_sqrt format radicand hsignificand hnegative
        hremainder]
  · have hone :=
      one_lt_cellDenominator (truncatedRoot (prefixPrecision format) radicand)
    have hdenominator : 0 < rootCellDenominator format radicand :=
      cellDenominator_pos _
    apply Nat.le_antisymm
    · rw [roundCode_eq_fraction format radicand 1
          (rootCellDenominator format radicand) hsignificand hnegative
          hdenominator (by unfold rootCellDenominator; omega)
          (by simp [hremainder]),
        ← Model.RealRounding.roundPositiveCode_ratCast]
      exact Model.RealRounding.roundPositiveCode_mono format
        (lowerRootCellPoint_lt_sqrt format radicand hnegative hremainder).le
    · rw [roundCode_eq_fraction format radicand
          (rootCellDenominator format radicand - 1)
          (rootCellDenominator format radicand) hsignificand hnegative
          hdenominator (by omega)
          (by unfold rootCellDenominator; simp [hremainder]; omega),
        ← Model.RealRounding.roundPositiveCode_ratCast]
      exact Model.RealRounding.roundPositiveCode_mono format
        (sqrt_lt_upperRootCellPoint format radicand hnegative).le

/-- Every direct square-root code is a finite nonnegative Posit encoding. -/
theorem roundCode_lt_signMask
    (format : Format) (radicand : FloatLib.Numerics.Dyadic) :
    roundCode format radicand < format.signMaskNat := by
  unfold roundCode
  split
  · exact format.signMaskNat_pos
  · exact DirectDyadicPacking.roundPositiveCode_lt_signMask
      format (rootPrefix format radicand)

/-- Every direct square-root code lies inside the complete encoding modulus. -/
theorem roundCode_lt_modulus
    (format : Format) (radicand : FloatLib.Numerics.Dyadic) :
    roundCode format radicand < format.modulus :=
  (roundCode_lt_signMask format radicand).trans
    format.signMaskNat_lt_modulus

/-- Re-encoding the selected square-root code gives the model-valued result. -/
theorem ofNatBits_roundCode
    (format : Format) (radicand : FloatLib.Numerics.Dyadic) :
    Model.ofNatBits (roundCode format radicand) =
      round format radicand :=
  rfl

/-- Direct nonnegative square-root packing equals exact squared-boundary packing. -/
theorem round_eq_dyadic
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (hnegative : radicand.negative = false) :
    round format radicand =
      DyadicSquareRoot.round format radicand := by
  unfold round DyadicSquareRoot.round
  rw [roundCode_eq_dyadic format radicand hnegative]

/-- Direct square-root packing equals exact squared-boundary packing on its mathematical domain. -/
theorem round_eq_dyadic_of_not_negative
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (hnonnegative : ¬radicand.toRat < 0) :
    round format radicand =
      DyadicSquareRoot.round format radicand := by
  by_cases hsignificand : radicand.significand = 0
  · simp [round, roundCode, DyadicSquareRoot.round,
      DyadicSquareRoot.roundCode, hsignificand]
  · exact round_eq_dyadic format radicand
      (DyadicSquareRoot.negative_eq_false_of_not_toRat_neg radicand
        hsignificand hnonnegative)

/-- Direct nonnegative square-root packing refines the rational specification. -/
theorem round_eq_reference_of_nonnegative
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (hnegative : radicand.negative = false) :
    round format radicand =
      Model.roundSqrtRat format radicand.toRat := by
  rw [round_eq_dyadic format radicand hnegative,
    DyadicSquareRoot.round_eq_reference_of_nonnegative
      format radicand hnegative]

/-- Refinement stated by the mathematical square-root domain condition. -/
theorem round_eq_reference_of_not_negative
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (hnonnegative : ¬radicand.toRat < 0) :
    round format radicand =
      Model.roundSqrtRat format radicand.toRat := by
  rw [round_eq_dyadic_of_not_negative format radicand hnonnegative,
    DyadicSquareRoot.round_eq_reference_of_not_negative
      format radicand hnonnegative]

end FloatLib.Floats.Formats.Posit.Model.DirectDyadicSquareRoot
