/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Direct.Jamming
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Direct.Runtime

/-!
# Normalization and correctness of direct quotient prefixes

The direct quotient kernel normalizes significands, emits a bounded quotient window, and records
any nonzero discarded suffix with a sticky bit. This module follows those stages: common-leading
normalization, retained-prefix bounds, recovery of the input dyadic ratio, and the final
`prefixAtLeading` correctness theorems.

`Direct.Jamming` proves the exact-fraction comparison lemmas shared by these stages. Posit layout
and final rounding refinement remain in `Direct.Proof`; the results here are uniform in width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DirectDyadicQuotient

open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding
open FloatLib.Floats.Formats.Posit.Model.StickyPrefix

/-! ## Common-leading normalization -/

/-- Shifting a nonzero integer from its leading bit to a larger common position normalizes it. -/
theorem shiftToCommon_bounds
    (value common : Nat)
    (hvalue : value ≠ 0)
    (hleading : value.log2 ≤ common) :
    2 ^ common ≤ value <<< (common - value.log2) ∧
      value <<< (common - value.log2) < 2 ^ (common + 1) := by
  have hlower : 2 ^ value.log2 ≤ value :=
    Nat.log2_self_le hvalue
  have hupper : value < 2 ^ (value.log2 + 1) :=
    Nat.lt_log2_self
  simp only [Nat.shiftLeft_eq]
  constructor
  · calc
      2 ^ common =
          2 ^ value.log2 * 2 ^ (common - value.log2) := by
        rw [← pow_add, Nat.add_sub_of_le hleading]
      _ ≤ value * 2 ^ (common - value.log2) :=
        Nat.mul_le_mul_right _ hlower
  · calc
      value * 2 ^ (common - value.log2) <
          2 ^ (value.log2 + 1) *
            2 ^ (common - value.log2) :=
        Nat.mul_lt_mul_of_pos_right hupper
          (Nat.two_pow_pos _)
      _ = 2 ^ (common + 1) := by
        rw [← pow_add]
        congr 1
        omega

/--
Proof facts carried by a pair of significands after common-leading normalization.

The executable record deliberately stores only values needed by the quotient kernel. These
facts live in `Prop`, so proofs can name the common bounds without enlarging runtime data.
-/
structure NormalizedSignificands.Spec
    (normalized : NormalizedSignificands)
    (numerator denominator : Nat) : Prop where
  /-- The recorded numerator leading position is exact. -/
  numeratorLeading_eq :
    normalized.numeratorLeading = numerator.log2
  /-- The recorded denominator leading position is exact. -/
  denominatorLeading_eq :
    normalized.denominatorLeading = denominator.log2
  /-- The numerator is shifted to the common leading position. -/
  numerator_eq :
    normalized.numerator =
      numerator *
        2 ^ (max numerator.log2 denominator.log2 - numerator.log2)
  /-- The denominator is shifted to the common leading position. -/
  denominator_eq :
    normalized.denominator =
      denominator *
        2 ^ (max numerator.log2 denominator.log2 - denominator.log2)
  /-- The normalized numerator reaches the common leading bit. -/
  numerator_lower :
    2 ^ max numerator.log2 denominator.log2 ≤ normalized.numerator
  /-- The normalized numerator has no bit above the common leading bit. -/
  numerator_upper :
    normalized.numerator <
      2 ^ (max numerator.log2 denominator.log2 + 1)
  /-- The normalized denominator reaches the common leading bit. -/
  denominator_lower :
    2 ^ max numerator.log2 denominator.log2 ≤ normalized.denominator
  /-- The normalized denominator has no bit above the common leading bit. -/
  denominator_upper :
    normalized.denominator <
      2 ^ (max numerator.log2 denominator.log2 + 1)

/-- Common-leading normalization records exact positions, values, and bounds. -/
theorem normalizeSignificands_spec
    (numerator denominator : Nat)
    (hnumerator : numerator ≠ 0)
    (hdenominator : denominator ≠ 0) :
    NormalizedSignificands.Spec
      (normalizeSignificands numerator denominator)
      numerator denominator := by
  let commonLeading := max numerator.log2 denominator.log2
  have hnumeratorBounds :=
    shiftToCommon_bounds numerator commonLeading hnumerator
      (Nat.le_max_left _ _)
  have hdenominatorBounds :=
    shiftToCommon_bounds denominator commonLeading hdenominator
      (Nat.le_max_right _ _)
  have hnumeratorBounds' :
      2 ^ max numerator.log2 denominator.log2 ≤
          numerator * 2 ^ (max numerator.log2 denominator.log2 - numerator.log2) ∧
        numerator * 2 ^ (max numerator.log2 denominator.log2 - numerator.log2) <
          2 ^ (max numerator.log2 denominator.log2 + 1) := by
    simpa [commonLeading, Nat.shiftLeft_eq] using hnumeratorBounds
  have hdenominatorBounds' :
      2 ^ max numerator.log2 denominator.log2 ≤
          denominator * 2 ^ (max numerator.log2 denominator.log2 - denominator.log2) ∧
        denominator * 2 ^ (max numerator.log2 denominator.log2 - denominator.log2) <
          2 ^ (max numerator.log2 denominator.log2 + 1) := by
    simpa [commonLeading, Nat.shiftLeft_eq] using hdenominatorBounds
  refine
    { numeratorLeading_eq := rfl
      denominatorLeading_eq := rfl
      numerator_eq := by simp [normalizeSignificands, Nat.shiftLeft_eq]
      denominator_eq := by simp [normalizeSignificands, Nat.shiftLeft_eq]
      numerator_lower := ?_
      numerator_upper := ?_
      denominator_lower := ?_
      denominator_upper := ?_ }
  · simpa [normalizeSignificands, Nat.shiftLeft_eq] using hnumeratorBounds'.1
  · simpa [normalizeSignificands, Nat.shiftLeft_eq] using hnumeratorBounds'.2
  · simpa [normalizeSignificands, Nat.shiftLeft_eq] using hdenominatorBounds'.1
  · simpa [normalizeSignificands, Nat.shiftLeft_eq] using hdenominatorBounds'.2

/-- Common-leading normalization changes a ratio only by the recorded leading-position offset. -/
theorem shiftedRatio_eq
    (numerator denominator commonLeading : Nat)
    (hnumeratorLeading : numerator.log2 ≤ commonLeading)
    (hdenominatorLeading : denominator.log2 ≤ commonLeading) :
    (((numerator * 2 ^ (commonLeading - numerator.log2) : Nat) : Rat) /
        ((denominator * 2 ^ (commonLeading - denominator.log2) : Nat) : Rat)) =
      (numerator : Rat) / (denominator : Rat) *
        (2 : Rat) ^
          (Int.ofNat denominator.log2 - Int.ofNat numerator.log2) := by
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_div_mul_comm]
  congr 1
  rw [← zpow_natCast, ← zpow_natCast,
    ← zpow_sub₀ (by norm_num : (2 : Rat) ≠ 0)]
  congr 1
  rw [Int.ofNat_sub hnumeratorLeading,
    Int.ofNat_sub hdenominatorLeading]
  simp only [Int.ofNat_eq_natCast]
  omega

/--
The quotient selected from two equally normalized integers has the requested leading position.
-/
theorem normalizedQuotient_bounds
    (leading common numerator denominator : Nat)
    (hnumeratorLower : 2 ^ common ≤ numerator)
    (hnumeratorUpper : numerator < 2 ^ (common + 1))
    (hdenominatorLower : 2 ^ common ≤ denominator)
    (hdenominatorUpper : denominator < 2 ^ (common + 1)) :
    let steps := if numerator < denominator then leading + 1 else leading
    2 ^ leading ≤ (numerator * 2 ^ steps) / denominator ∧
      (numerator * 2 ^ steps) / denominator < 2 ^ (leading + 1) := by
  have hdenominatorPositive : 0 < denominator :=
    (Nat.two_pow_pos common).trans_le hdenominatorLower
  by_cases hbelow : numerator < denominator
  · rw [ite_eq_left hbelow]
    constructor
    · apply (Nat.le_div_iff_mul_le hdenominatorPositive).2
      have hdenominatorLe : denominator ≤ 2 * numerator := by
        have hpowerLe :
            2 ^ (common + 1) ≤ 2 * numerator := by
          rw [pow_succ]
          simpa [Nat.mul_comm] using
            Nat.mul_le_mul_left 2 hnumeratorLower
        omega
      calc
        2 ^ leading * denominator ≤
            2 ^ leading * (2 * numerator) :=
          Nat.mul_le_mul_left _ hdenominatorLe
        _ = numerator * 2 ^ (leading + 1) := by
          rw [pow_succ]
          ring
    · apply (Nat.div_lt_iff_lt_mul hdenominatorPositive).2
      calc
        numerator * 2 ^ (leading + 1) <
            denominator * 2 ^ (leading + 1) :=
          Nat.mul_lt_mul_of_pos_right hbelow
            (Nat.two_pow_pos _)
        _ = 2 ^ (leading + 1) * denominator := by
          ring
  · rw [ite_eq_right hbelow]
    have hordered : denominator ≤ numerator :=
      Nat.le_of_not_gt hbelow
    constructor
    · apply (Nat.le_div_iff_mul_le hdenominatorPositive).2
      simpa [Nat.mul_comm] using
        Nat.mul_le_mul_left (2 ^ leading) hordered
    · apply (Nat.div_lt_iff_lt_mul hdenominatorPositive).2
      have hnumeratorLt : numerator < 2 * denominator := by
        have hpowerLe :
            2 ^ (common + 1) ≤ 2 * denominator := by
          rw [pow_succ]
          simpa [Nat.mul_comm] using
            Nat.mul_le_mul_left 2 hdenominatorLower
        omega
      calc
        numerator * 2 ^ leading <
            (2 * denominator) * 2 ^ leading :=
          Nat.mul_lt_mul_of_pos_right hnumeratorLt
            (Nat.two_pow_pos _)
        _ = 2 ^ (leading + 1) * denominator := by
          rw [pow_succ]
          ring

/-- Jamming a normalized quotient preserves its leading position without overflowing it. -/
theorem jamRemainder_bounds
    (leading quotient remainder : Nat)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1)) :
    2 ^ leading ≤ jamRemainder quotient remainder ∧
      jamRemainder quotient remainder < 2 ^ (leading + 1) := by
  rw [jamRemainder_eq]
  by_cases hremainder : remainder = 0
  · simp [hremainder, hlower, hupper]
  · rw [ite_eq_right hremainder]
    by_cases heven : quotient % 2 = 0
    · rw [ite_eq_left heven]
      constructor
      · omega
      · have hpowerEven : 2 ^ (leading + 1) % 2 = 0 := by
          rw [pow_succ]
          omega
        omega
    · rw [ite_eq_right heven]
      exact ⟨hlower, hupper⟩

/-! ## Bracketing the retained quotient prefix -/

/--
The retained prefix of a normalized jammed quotient is at most the exact normalized quotient.

This is the representation-independent lower-bracket theorem used by Posit candidate proofs.
-/
theorem trailingRat_streamPrefix_jammed_le_quotientFraction
    (exponentField quotient remainder denominator leading retained : Nat)
    (hleading : 0 < leading)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hretained : retained < leading + 2) :
    Model.trailingRat retained
        (streamPrefix
          (exactTailRaw exponentField
            (jamRemainder quotient remainder) leading)
          (leading + 2) retained) ≤
      (((quotient : Rat) +
            (remainder : Rat) / (denominator : Rat)) /
          (2 ^ leading : Nat) *
        (2 : Rat) ^ Int.ofNat exponentField) := by
  let width := leading + 2
  let raw := exactTailRaw exponentField quotient leading
  let jammedRaw :=
    exactTailRaw exponentField
      (jamRemainder quotient remainder) leading
  let pfx := streamPrefix jammedRaw width retained
  let shift := width - retained
  have hrawBound : raw < 2 ^ width := by
    dsimp [raw, width]
    exact exactTailRaw_lt_two_pow exponentField quotient leading
      hexponent hlower hupper
  have hjammedRaw :
      jammedRaw = jamRemainder raw remainder := by
    dsimp [jammedRaw, raw]
    exact exactTailRaw_jamRemainder
      exponentField quotient remainder leading hleading hlower
  have hpaddedLe :
      pfx * 2 ^ shift ≤ raw := by
    dsimp [pfx, shift, width]
    rw [hjammedRaw]
    exact paddedStreamPrefix_jamRemainder_le
      raw remainder (leading + 2) retained hretained
  have hpaddedBound :
      pfx * 2 ^ shift < 2 ^ width :=
    lt_of_le_of_lt hpaddedLe hrawBound
  have hprefixValue :
      Model.trailingRat retained pfx =
        Model.trailingRat width (pfx * 2 ^ shift) := by
    have hwidth : retained + shift = width := by
      dsimp [shift, width]
      omega
    rw [← hwidth]
    exact (trailingRat_mul_two_pow retained pfx shift).symm
  have hprefixLeRaw :
      Model.trailingRat retained pfx ≤
        Model.trailingRat width raw := by
    rw [hprefixValue]
    rcases hpaddedLe.eq_or_lt with hequal | hlt
    · rw [hequal]
    · exact
        (Model.trailingRat_lt_of_lt hpaddedBound hrawBound hlt).le
  have hrawValue :
      Model.trailingRat width raw =
        (quotient : Rat) / (2 ^ leading : Nat) *
          (2 : Rat) ^ Int.ofNat exponentField := by
    dsimp [width, raw]
    exact trailingRat_exactTailRaw exponentField quotient leading
      hexponent hlower hupper
  have hfractionLower :=
    (quotientFraction_bounds quotient remainder denominator
      hdenominator hremainder).1
  have hleadingPositive : (0 : Rat) < (2 ^ leading : Nat) := by
    exact_mod_cast Nat.two_pow_pos leading
  have hpowerNonnegative :
      (0 : Rat) ≤ (2 : Rat) ^ Int.ofNat exponentField :=
    (zpow_pos (by norm_num) _).le
  change
    Model.trailingRat retained pfx ≤
      (((quotient : Rat) +
            (remainder : Rat) / (denominator : Rat)) /
          (2 ^ leading : Nat)) *
        (2 : Rat) ^ Int.ofNat exponentField
  calc
    Model.trailingRat retained pfx ≤
        Model.trailingRat width raw := hprefixLeRaw
    _ =
        (quotient : Rat) / (2 ^ leading : Nat) *
          (2 : Rat) ^ Int.ofNat exponentField := hrawValue
    _ ≤
        (((quotient : Rat) +
              (remainder : Rat) / (denominator : Rat)) /
            (2 ^ leading : Nat)) *
          (2 : Rat) ^ Int.ofNat exponentField :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hfractionLower hleadingPositive.le)
        hpowerNonnegative

/--
The exact normalized quotient is below the successor of its retained jammed prefix.

The explicit successor bound is precisely the in-regime condition supplied by Posit layout.
-/
theorem quotientFraction_lt_trailingRat_streamPrefix_jammed_succ
    (exponentField quotient remainder denominator leading retained : Nat)
    (hleading : 0 < leading)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hretained : retained < leading + 2)
    (hsuccessor :
      streamPrefix
          (exactTailRaw exponentField
            (jamRemainder quotient remainder) leading)
          (leading + 2) retained + 1 <
        2 ^ retained) :
    (((quotient : Rat) +
            (remainder : Rat) / (denominator : Rat)) /
          (2 ^ leading : Nat) *
        (2 : Rat) ^ Int.ofNat exponentField) <
      Model.trailingRat retained
        (streamPrefix
            (exactTailRaw exponentField
              (jamRemainder quotient remainder) leading)
            (leading + 2) retained + 1) := by
  let width := leading + 2
  let raw := exactTailRaw exponentField quotient leading
  let jammedRaw :=
    exactTailRaw exponentField
      (jamRemainder quotient remainder) leading
  let pfx := streamPrefix jammedRaw width retained
  let shift := width - retained
  let boundary := (pfx + 1) * 2 ^ shift
  have hjammedRaw :
      jammedRaw = jamRemainder raw remainder := by
    dsimp [jammedRaw, raw]
    exact exactTailRaw_jamRemainder
      exponentField quotient remainder leading hleading hlower
  have hwidth : retained + shift = width := by
    dsimp [shift, width]
    omega
  have hboundaryBound : boundary < 2 ^ width := by
    dsimp [boundary]
    rw [← hwidth, Nat.pow_add]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos shift)).2
      (by simpa [pfx, jammedRaw, width] using hsuccessor)
  have hexactBoundary :
      (raw : Rat) + (remainder : Rat) / (denominator : Rat) <
        (boundary : Rat) := by
    dsimp [boundary, pfx, shift, width]
    rw [hjammedRaw]
    exact quotientFraction_lt_paddedStreamPrefix_jamRemainder_succ
      raw remainder denominator (leading + 2) retained
      hdenominator hremainder hretained
  have hnormalizedBoundary :=
    (quotientFraction_lt_trailingRat_iff
      exponentField quotient remainder denominator leading boundary
      hexponent hlower hupper hdenominator hremainder
      (by simpa [width] using hboundaryBound)).2
      (by simpa [raw] using hexactBoundary)
  have hboundaryValue :
      Model.trailingRat retained (pfx + 1) =
        Model.trailingRat width boundary := by
    dsimp [boundary]
    rw [← hwidth]
    exact (trailingRat_mul_two_pow retained (pfx + 1) shift).symm
  change
    (((quotient : Rat) +
            (remainder : Rat) / (denominator : Rat)) /
          (2 ^ leading : Nat) *
        (2 : Rat) ^ Int.ofNat exponentField) <
      Model.trailingRat retained (pfx + 1)
  rw [hboundaryValue]
  simpa [width] using hnormalizedBoundary

/-- Every normalized quotient tail is strictly below the next regime scale. -/
theorem quotientFraction_normalized_lt_sixteen
    (exponentField quotient remainder denominator leading : Nat)
    (hexponent : exponentField < 4)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator) :
    (((quotient : Rat) +
            (remainder : Rat) / (denominator : Rat)) /
          (2 ^ leading : Nat) *
        (2 : Rat) ^ Int.ofNat exponentField) <
      16 := by
  have hfractionUpper :=
    (quotientFraction_bounds quotient remainder denominator
      hdenominator hremainder).2
  have hquotientSuccessorLe :
      quotient + 1 ≤ 2 ^ (leading + 1) := by
    omega
  have hnormalizedNumerator :
      (quotient : Rat) +
          (remainder : Rat) / (denominator : Rat) <
        (2 ^ (leading + 1) : Nat) := by
    have hquotientSuccessorLeRat :
        (quotient : Rat) + 1 ≤ (2 ^ (leading + 1) : Nat) := by
      exact_mod_cast hquotientSuccessorLe
    linarith
  have hleadingPositive : (0 : Rat) < (2 ^ leading : Nat) := by
    exact_mod_cast Nat.two_pow_pos leading
  have hratioLtTwo :
      ((quotient : Rat) +
          (remainder : Rat) / (denominator : Rat)) /
          (2 ^ leading : Nat) <
        2 := by
    rw [div_lt_iff₀ hleadingPositive]
    have hpower :
        ((2 ^ (leading + 1) : Nat) : Rat) =
          2 * (2 ^ leading : Nat) := by
      rw [pow_succ, Nat.cast_mul]
      norm_num
      ring
    rw [← hpower]
    exact hnormalizedNumerator
  have hpowerPositive :
      (0 : Rat) < (2 : Rat) ^ Int.ofNat exponentField :=
    zpow_pos (by norm_num) _
  have hpowerLe :
      (2 : Rat) ^ Int.ofNat exponentField ≤ 8 := by
    have hcases :
        exponentField = 0 ∨ exponentField = 1 ∨
          exponentField = 2 ∨ exponentField = 3 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl <;> norm_num
  calc
    (((quotient : Rat) +
            (remainder : Rat) / (denominator : Rat)) /
          (2 ^ leading : Nat)) *
        (2 : Rat) ^ Int.ofNat exponentField <
      2 * (2 : Rat) ^ Int.ofNat exponentField :=
        mul_lt_mul_of_pos_right hratioLtTwo hpowerPositive
    _ ≤ 2 * 8 :=
      mul_le_mul_of_nonneg_left hpowerLe (by norm_num)
    _ = 16 := by norm_num

/-! ## Recovering the input dyadic ratio -/

/-- Euclidean division exposes a scaled rational as its quotient plus proper remainder. -/
theorem scaledRatio_eq_quotientFraction
    (numerator denominator steps : Nat)
    (hdenominator : denominator ≠ 0) :
    (numerator : Rat) * (2 ^ steps : Nat) / (denominator : Rat) =
      (((numerator * 2 ^ steps) / denominator : Nat) : Rat) +
        (((numerator * 2 ^ steps) % denominator : Nat) : Rat) /
          (denominator : Rat) := by
  have hdenominatorRat : (denominator : Rat) ≠ 0 := by
    exact_mod_cast hdenominator
  have hdecompose :=
    Nat.mod_add_div (numerator * 2 ^ steps) denominator
  field_simp [hdenominatorRat]
  exact_mod_cast (by simpa [Nat.add_comm] using hdecompose.symm)

/--
Moving the normalization and quotient-digit scales into the result exponent recovers the exact
dyadic ratio.
-/
theorem dyadicRatio_eq_quotientFraction_mul_zpow
    (numerator denominator normalizedNumerator normalizedDenominator
      quotient remainder : Nat)
    (numeratorExponent denominatorExponent : Int)
    (numeratorLeading denominatorLeading steps : Nat)
    (hnormalized :
      (normalizedNumerator : Rat) / (normalizedDenominator : Rat) =
        (numerator : Rat) / (denominator : Rat) *
          (2 : Rat) ^
            (Int.ofNat denominatorLeading - Int.ofNat numeratorLeading))
    (hquotient :
      (normalizedNumerator : Rat) * (2 ^ steps : Nat) /
          (normalizedDenominator : Rat) =
        (quotient : Rat) +
          (remainder : Rat) / (normalizedDenominator : Rat)) :
    (numerator : Rat) * (2 : Rat) ^ numeratorExponent /
        ((denominator : Rat) * (2 : Rat) ^ denominatorExponent) =
      ((quotient : Rat) +
          (remainder : Rat) / (normalizedDenominator : Rat)) *
        (2 : Rat) ^
          (numeratorExponent - denominatorExponent +
            Int.ofNat numeratorLeading - Int.ofNat denominatorLeading -
            Int.ofNat steps) := by
  have hsteps :
      ((2 ^ steps : Nat) : Rat) =
        (2 : Rat) ^ Int.ofNat steps := by
    simp [zpow_natCast]
  have hfraction :
      (quotient : Rat) +
          (remainder : Rat) / (normalizedDenominator : Rat) =
        (numerator : Rat) / (denominator : Rat) *
          (2 : Rat) ^
            (Int.ofNat denominatorLeading - Int.ofNat numeratorLeading +
              Int.ofNat steps) := by
    calc
      (quotient : Rat) +
            (remainder : Rat) / (normalizedDenominator : Rat) =
          (normalizedNumerator : Rat) * (2 ^ steps : Nat) /
            (normalizedDenominator : Rat) :=
        hquotient.symm
      _ = ((normalizedNumerator : Rat) /
            (normalizedDenominator : Rat)) * (2 ^ steps : Nat) := by
        ring
      _ = ((numerator : Rat) / (denominator : Rat) *
            (2 : Rat) ^
              (Int.ofNat denominatorLeading - Int.ofNat numeratorLeading)) *
            (2 ^ steps : Nat) := by
        rw [hnormalized]
      _ = (numerator : Rat) / (denominator : Rat) *
          (2 : Rat) ^
            (Int.ofNat denominatorLeading - Int.ofNat numeratorLeading +
              Int.ofNat steps) := by
        rw [hsteps]
        calc
          (numerator : Rat) / (denominator : Rat) *
                (2 : Rat) ^
                  (Int.ofNat denominatorLeading - Int.ofNat numeratorLeading) *
              (2 : Rat) ^ Int.ofNat steps =
            (numerator : Rat) / (denominator : Rat) *
              ((2 : Rat) ^
                  (Int.ofNat denominatorLeading - Int.ofNat numeratorLeading) *
                (2 : Rat) ^ Int.ofNat steps) := by
              ring
          _ = _ := by
            rw [← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
  rw [hfraction]
  calc
    (numerator : Rat) * (2 : Rat) ^ numeratorExponent /
          ((denominator : Rat) * (2 : Rat) ^ denominatorExponent) =
        (numerator : Rat) / (denominator : Rat) *
          (2 : Rat) ^ (numeratorExponent - denominatorExponent) := by
      rw [zpow_sub₀ (by norm_num : (2 : Rat) ≠ 0)]
      ring
    _ = ((numerator : Rat) / (denominator : Rat) *
          (2 : Rat) ^
            (Int.ofNat denominatorLeading - Int.ofNat numeratorLeading +
              Int.ofNat steps)) *
        (2 : Rat) ^
          (numeratorExponent - denominatorExponent +
            Int.ofNat numeratorLeading - Int.ofNat denominatorLeading -
            Int.ofNat steps) := by
      rw [show
          (2 : Rat) ^ (numeratorExponent - denominatorExponent) =
            (2 : Rat) ^
                (Int.ofNat denominatorLeading - Int.ofNat numeratorLeading +
                  Int.ofNat steps) *
              (2 : Rat) ^
                (numeratorExponent - denominatorExponent +
                  Int.ofNat numeratorLeading - Int.ofNat denominatorLeading -
                  Int.ofNat steps) by
        rw [← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
        congr 1
        omega]
      ring

/-! ## Executable prefix correctness -/

/--
The quotient and remainder generated by an arbitrary-width prefix form a normalized Euclidean
window at exactly the requested leading bit.
-/
theorem prefixAtLeading_quotient_spec
    (leading : Nat)
    (numerator denominator : FloatLib.Numerics.Dyadic)
    (hnumerator : numerator.significand ≠ 0)
    (hdenominator : denominator.significand ≠ 0) :
    let normalized :=
      normalizeSignificands numerator.significand denominator.significand
    let steps :=
      if normalized.numerator < normalized.denominator then leading + 1 else leading
    let scaledNumerator := normalized.numerator * 2 ^ steps
    0 < normalized.denominator ∧
      2 ^ leading ≤ scaledNumerator / normalized.denominator ∧
      scaledNumerator / normalized.denominator < 2 ^ (leading + 1) ∧
      scaledNumerator % normalized.denominator < normalized.denominator := by
  let normalized :=
    normalizeSignificands numerator.significand denominator.significand
  let commonLeading :=
    max numerator.significand.log2 denominator.significand.log2
  let steps :=
    if normalized.numerator < normalized.denominator then leading + 1 else leading
  have hnormalized :=
    normalizeSignificands_spec numerator.significand denominator.significand
      hnumerator hdenominator
  have hquotient :=
    normalizedQuotient_bounds leading commonLeading
      normalized.numerator normalized.denominator
      hnormalized.numerator_lower hnormalized.numerator_upper
      hnormalized.denominator_lower hnormalized.denominator_upper
  have hdenominatorPositive :
      0 < normalized.denominator :=
    (Nat.two_pow_pos commonLeading).trans_le
      hnormalized.denominator_lower
  exact
    ⟨hdenominatorPositive, hquotient.1, hquotient.2,
      Nat.mod_lt _ hdenominatorPositive⟩

/-- The executable arbitrary-width prefix is normalized at exactly the requested leading bit. -/
theorem prefixAtLeading_significand_bounds
    (leading : Nat)
    (numerator denominator : FloatLib.Numerics.Dyadic)
    (hnumerator : numerator.significand ≠ 0)
    (hdenominator : denominator.significand ≠ 0) :
    2 ^ leading ≤
        (prefixAtLeading leading numerator denominator).significand ∧
      (prefixAtLeading leading numerator denominator).significand <
        2 ^ (leading + 1) := by
  let normalized :=
    normalizeSignificands numerator.significand denominator.significand
  let commonLeading :=
    max numerator.significand.log2 denominator.significand.log2
  let steps :=
    if normalized.numerator < normalized.denominator then leading + 1 else leading
  have hnormalized :=
    normalizeSignificands_spec numerator.significand denominator.significand
      hnumerator hdenominator
  have hquotient :=
    normalizedQuotient_bounds leading commonLeading
      normalized.numerator normalized.denominator
      hnormalized.numerator_lower hnormalized.numerator_upper
      hnormalized.denominator_lower hnormalized.denominator_upper
  change
    2 ^ leading ≤
        (normalized.numerator * 2 ^ steps) / normalized.denominator ∧
      (normalized.numerator * 2 ^ steps) / normalized.denominator <
        2 ^ (leading + 1) at hquotient
  have hjammed :=
    jamRemainder_bounds leading
      ((normalized.numerator * 2 ^ steps) / normalized.denominator)
      ((normalized.numerator * 2 ^ steps) % normalized.denominator)
      hquotient.1 hquotient.2
  simpa [prefixAtLeading, normalized, steps, Nat.shiftLeft_eq] using
    hjammed

/--
Before jamming, the generated quotient and exact Euclidean remainder denote the input dyadic
ratio at the exponent stored in the executable prefix.
-/
theorem prefixAtLeading_exactFraction
    (leading : Nat)
    (numerator denominator : FloatLib.Numerics.Dyadic)
    (hnumerator : numerator.significand ≠ 0)
    (hdenominator : denominator.significand ≠ 0)
    (hnumeratorNegative : numerator.negative = false)
    (hdenominatorNegative : denominator.negative = false) :
    let normalized :=
      normalizeSignificands numerator.significand denominator.significand
    let steps :=
      if normalized.numerator < normalized.denominator then leading + 1 else leading
    let scaledNumerator := normalized.numerator * 2 ^ steps
    numerator.toRat / denominator.toRat =
      (((scaledNumerator / normalized.denominator : Nat) : Rat) +
          ((scaledNumerator % normalized.denominator : Nat) : Rat) /
            (normalized.denominator : Rat)) *
        (2 : Rat) ^
          (numerator.exponent - denominator.exponent +
            Int.ofNat normalized.numeratorLeading -
            Int.ofNat normalized.denominatorLeading -
            Int.ofNat steps) := by
  let normalized :=
    normalizeSignificands numerator.significand denominator.significand
  let commonLeading :=
    max numerator.significand.log2 denominator.significand.log2
  let steps :=
    if normalized.numerator < normalized.denominator then leading + 1 else leading
  have hnormalized :=
    normalizeSignificands_spec numerator.significand denominator.significand
      hnumerator hdenominator
  have hnormalizedRatio :
      (normalized.numerator : Rat) / (normalized.denominator : Rat) =
        (numerator.significand : Rat) / (denominator.significand : Rat) *
          (2 : Rat) ^
            (Int.ofNat normalized.denominatorLeading -
              Int.ofNat normalized.numeratorLeading) := by
    rw [hnormalized.numeratorLeading_eq,
      hnormalized.denominatorLeading_eq,
      hnormalized.numerator_eq,
      hnormalized.denominator_eq]
    exact shiftedRatio_eq numerator.significand denominator.significand
      commonLeading (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hnormalizedDenominator : normalized.denominator ≠ 0 := by
    have hpositive :=
      (Nat.two_pow_pos commonLeading).trans_le
        hnormalized.denominator_lower
    exact Nat.ne_of_gt hpositive
  have hquotient :=
    scaledRatio_eq_quotientFraction
      normalized.numerator normalized.denominator steps
      hnormalizedDenominator
  have hratio :=
    dyadicRatio_eq_quotientFraction_mul_zpow
      numerator.significand denominator.significand
      normalized.numerator normalized.denominator
      ((normalized.numerator * 2 ^ steps) / normalized.denominator)
      ((normalized.numerator * 2 ^ steps) % normalized.denominator)
      numerator.exponent denominator.exponent
      normalized.numeratorLeading normalized.denominatorLeading steps
      hnormalizedRatio hquotient
  simpa [FloatLib.Numerics.Dyadic.toRat,
    FloatLib.Numerics.Dyadic.signedSignificand,
    hnumeratorNegative, hdenominatorNegative,
    normalized, steps] using hratio

end FloatLib.Floats.Formats.Posit.Model.DirectDyadicQuotient
