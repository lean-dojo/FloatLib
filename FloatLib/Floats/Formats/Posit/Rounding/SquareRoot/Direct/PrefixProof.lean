/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Direct.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Direct.Runtime

/-!
# Exact semantics of arbitrary-width square-root prefixes

The direct square-root kernel scales a positive dyadic by an even power of two, computes its
integer square root, and jams whether the exact root continues beyond that integer prefix.
This module proves the representation-independent integer facts. Posit-specific square-root
refinement is kept in `Direct.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DirectDyadicSquareRoot

open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit.Model.StickyPrefix

/-- Dyadic exponent parity is always zero or one. -/
theorem exponentParity_lt_two
    (radicand : FloatLib.Numerics.Dyadic) :
    exponentParity radicand < 2 := by
  unfold exponentParity
  change (radicand.exponent % 2).toNat < 2
  have hnonnegative :
      0 ≤ radicand.exponent % 2 :=
    Int.emod_nonneg _ (by decide)
  apply (Int.toNat_lt hnonnegative).2
  simpa using Int.emod_lt radicand.exponent
    (by decide : (2 : Int) ≠ 0)

/-- Casting the executable parity recovers the Euclidean exponent remainder. -/
theorem exponentParity_cast
    (radicand : FloatLib.Numerics.Dyadic) :
    Int.ofNat (exponentParity radicand) =
      radicand.exponent.emod 2 := by
  unfold exponentParity
  exact Int.toNat_of_nonneg
    (Int.emod_nonneg radicand.exponent (by decide : (2 : Int) ≠ 0))

/-- The source exponent splits into the generated root scale and its two restored half-scales. -/
theorem sourceExponent_eq
    (precision : Nat) (radicand : FloatLib.Numerics.Dyadic) :
    radicand.exponent =
      Int.ofNat (exponentParity radicand + 2 * precision) +
        (radicand.exponent.ediv 2 - Int.ofNat precision) +
        (radicand.exponent.ediv 2 - Int.ofNat precision) := by
  have hcast :
      Int.ofNat (exponentParity radicand + 2 * precision) =
        Int.ofNat (exponentParity radicand) +
          2 * Int.ofNat precision := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat]
  rw [hcast, exponentParity_cast]
  have hdivision :
      radicand.exponent.ediv 2 * 2 +
          radicand.exponent.emod 2 =
        radicand.exponent := by
    exact Int.ediv_mul_add_emod radicand.exponent 2
  omega

/--
The scaled integer radicand and two copies of the restored root scale denote the source dyadic.
-/
theorem toRat_eq_scaledRadicand_mul_scale_sq
    (precision : Nat) (radicand : FloatLib.Numerics.Dyadic)
    (hnegative : radicand.negative = false) :
    radicand.toRat =
      (scaledRadicand precision radicand : Rat) *
        (2 : Rat) ^
          (radicand.exponent.ediv 2 - Int.ofNat precision) *
        (2 : Rat) ^
          (radicand.exponent.ediv 2 - Int.ofNat precision) := by
  unfold FloatLib.Numerics.Dyadic.toRat
  simp only [FloatLib.Numerics.Dyadic.signedSignificand, hnegative,
    Bool.false_eq_true, ite_false, Rat.ofInt_eq_cast]
  unfold scaledRadicand
  rw [show
      radicand.significand.shiftLeft
          (exponentParity radicand + 2 * precision) =
        radicand.significand *
          2 ^ (exponentParity radicand + 2 * precision) by
    simpa using Nat.shiftLeft_eq radicand.significand
      (exponentParity radicand + 2 * precision)]
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast]
  rw [show
      ((Int.ofNat radicand.significand : Int) : Rat) =
        (radicand.significand : Rat) by norm_num]
  conv_lhs =>
    rw [sourceExponent_eq precision radicand]
  rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0),
    zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
  simp only [Int.ofNat_eq_natCast]
  simp only [mul_assoc]

/-- Scaling preserves positivity of a nonzero source significand. -/
theorem scaledRadicand_pos
    (precision : Nat) (radicand : FloatLib.Numerics.Dyadic)
    (hsignificand : radicand.significand ≠ 0) :
    0 < scaledRadicand precision radicand := by
  unfold scaledRadicand
  rw [show
      radicand.significand.shiftLeft
          (exponentParity radicand + 2 * precision) =
        radicand.significand *
          2 ^ (exponentParity radicand + 2 * precision) by
    simpa using Nat.shiftLeft_eq radicand.significand
      (exponentParity radicand + 2 * precision)]
  exact Nat.mul_pos (Nat.pos_of_ne_zero hsignificand)
    (Nat.two_pow_pos _)

/-- The truncated root is positive for every nonzero source significand. -/
theorem truncatedRoot_pos
    (precision : Nat) (radicand : FloatLib.Numerics.Dyadic)
    (hsignificand : radicand.significand ≠ 0) :
    0 < truncatedRoot precision radicand := by
  rw [truncatedRoot, Nat.sqrt_pos]
  exact scaledRadicand_pos precision radicand hsignificand

/-- The truncated root's square is the lower endpoint of the exact root cell. -/
theorem truncatedRoot_square_le
    (precision : Nat) (radicand : FloatLib.Numerics.Dyadic) :
    truncatedRoot precision radicand *
        truncatedRoot precision radicand ≤
      scaledRadicand precision radicand := by
  unfold truncatedRoot
  exact Nat.sqrt_le _

/-- The scaled radicand lies strictly below the square of the next integer root. -/
theorem scaledRadicand_lt_succ_truncatedRoot_square
    (precision : Nat) (radicand : FloatLib.Numerics.Dyadic) :
    scaledRadicand precision radicand <
      (truncatedRoot precision radicand + 1) *
        (truncatedRoot precision radicand + 1) := by
  unfold truncatedRoot
  simpa [pow_two] using
    Nat.lt_succ_sqrt' (scaledRadicand precision radicand)

/-- The exact square remainder vanishes exactly for an integral scaled root. -/
theorem squareRemainder_eq_zero_iff
    (precision : Nat) (radicand : FloatLib.Numerics.Dyadic) :
    squareRemainder precision radicand = 0 ↔
      scaledRadicand precision radicand =
        truncatedRoot precision radicand *
          truncatedRoot precision radicand := by
  unfold squareRemainder truncatedRoot
  rw [Nat.sub_eq_zero_iff_le]
  constructor
  · intro hle
    exact Nat.le_antisymm hle (Nat.sqrt_le _)
  · intro heq
    exact heq.le

/--
Generating `precision` fractional root bits puts the truncated root's leading bit at or above
that position.
-/
theorem precision_le_truncatedRoot_log2
    (precision : Nat) (radicand : FloatLib.Numerics.Dyadic)
    (hsignificand : radicand.significand ≠ 0) :
    precision ≤ (truncatedRoot precision radicand).log2 := by
  have hroot :
      2 ^ precision ≤ truncatedRoot precision radicand := by
    unfold truncatedRoot
    rw [Nat.le_sqrt]
    unfold scaledRadicand
    rw [show
        radicand.significand.shiftLeft
            (exponentParity radicand + 2 * precision) =
          radicand.significand *
            2 ^ (exponentParity radicand + 2 * precision) by
      simpa using Nat.shiftLeft_eq radicand.significand
        (exponentParity radicand + 2 * precision)]
    have hshift :
        2 * precision ≤ exponentParity radicand + 2 * precision := by
      omega
    have hpower :
        2 ^ (2 * precision) ≤
          2 ^ (exponentParity radicand + 2 * precision) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hshift
    have hsource :
        2 ^ (exponentParity radicand + 2 * precision) ≤
          radicand.significand *
            2 ^ (exponentParity radicand + 2 * precision) := by
      exact Nat.le_mul_of_pos_left _
        (Nat.pos_of_ne_zero hsignificand)
    calc
      2 ^ precision * 2 ^ precision =
          2 ^ (2 * precision) := by
            rw [← pow_add]
            congr 1
            omega
      _ ≤ 2 ^ (exponentParity radicand + 2 * precision) := hpower
      _ ≤ radicand.significand *
          2 ^ (exponentParity radicand + 2 * precision) := hsource
  exact
    (Nat.le_log2
      (Nat.ne_of_gt
        (truncatedRoot_pos precision radicand hsignificand))).2 hroot

/-- Exact rational continuation at the scale represented by a generated root prefix. -/
def rootCellPoint
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (remainder denominator : Nat) : Rat :=
  let precision := prefixPrecision format
  (((truncatedRoot precision radicand : Nat) : Rat) +
      (remainder : Rat) / (denominator : Rat)) *
    (2 : Rat) ^
      (radicand.exponent.ediv 2 - Int.ofNat precision)

/--
The executable prefix rounds exactly like any proper rational continuation in the same integer
root cell.

Only exactness versus a nonzero continuation is observable after sticky-bit jamming. This theorem
lets the square-root refinement proof choose convenient rational lower and upper witnesses around
the mathematical root.
-/
theorem roundCode_eq_fraction
    (format : Format) (radicand : FloatLib.Numerics.Dyadic)
    (remainder denominator : Nat)
    (hsignificand : radicand.significand ≠ 0)
    (hnegative : radicand.negative = false)
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hzero :
      squareRemainder (prefixPrecision format) radicand = 0 ↔
        remainder = 0) :
    roundCode format radicand =
      Model.roundPositiveCode format
        (rootCellPoint format radicand remainder denominator) := by
  let precision := prefixPrecision format
  let root := truncatedRoot precision radicand
  let leading := root.log2
  let targetExponent :=
    radicand.exponent.ediv 2 - Int.ofNat precision
  have hrootPositive :
      0 < root := by
    exact truncatedRoot_pos precision radicand hsignificand
  have hrootNonzero : root ≠ 0 :=
    Nat.ne_of_gt hrootPositive
  have hleadingWidth :
      format.payloadBits ≤ leading := by
    change format.payloadBits ≤
      (truncatedRoot precision radicand).log2
    simpa [precision, prefixPrecision] using
      precision_le_truncatedRoot_log2
        (prefixPrecision format) radicand hsignificand
  have hlower :
      2 ^ leading ≤ root := by
    dsimp [leading]
    exact Nat.log2_self_le hrootNonzero
  have hupper :
      root < 2 ^ (leading + 1) := by
    dsimp [leading]
    exact Nat.lt_log2_self
  have hkernel :=
    DirectDyadicQuotient.roundPositiveCode_prefix_eq_reference
      format targetExponent root remainder denominator leading
      hleadingWidth hlower hupper hdenominator hremainder
  unfold roundCode
  simp only [beq_eq_false_iff_ne.mpr hsignificand,
    hnegative, Bool.false_or, Bool.false_eq_true, ite_false]
  unfold rootPrefix prefixAtPrecision
  rw [StickyPrefix.jamRemainder_congr
    (truncatedRoot (prefixPrecision format) radicand)
    (squareRemainder (prefixPrecision format) radicand)
    remainder hzero]
  simpa [rootCellPoint, precision, root, leading, targetExponent] using
    hkernel

end FloatLib.Floats.Formats.Posit.Model.DirectDyadicSquareRoot
