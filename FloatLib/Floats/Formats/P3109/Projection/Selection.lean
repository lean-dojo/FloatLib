/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Direction
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Selection

/-!
# Mathematical meaning of dyadic rounding decisions

The shift-based implementation of §4.7.4 has the same fractional-part formulas as the rational
implementation. In particular the stochastic decisions hold for every supplied word, including
words of width zero. No probability or distribution hypothesis is used.

Reference: P3109 unapproved interim report 4.0.3, revision `34f5964`, §4.7.4.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109
namespace Format.Internal

/-- Scaling a dyadic fraction by a power of two agrees with exact rational division. -/
theorem scaleFractionFloor_eq_rational (remainder discarded output : Nat) :
    scaleFractionFloor remainder discarded output =
      scaleRationalFractionFloor remainder (2 ^ discarded) output := by
  unfold scaleFractionFloor scaleRationalFractionFloor
  simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.shiftRight_eq',
    Nat.shiftRight_eq_div_pow]
  split
  · rename_i h
    have hp : 2 ^ output = 2 ^ (output - discarded) * 2 ^ discarded := by
      rw [← pow_add, Nat.sub_add_cancel h]
    rw [hp, ← Nat.mul_assoc, Nat.mul_div_cancel]
    exact Nat.two_pow_pos _
  · rename_i h
    have hp : 2 ^ discarded = 2 ^ output * 2 ^ (discarded - output) := by
      rw [← pow_add, Nat.add_sub_of_le (by omega)]
    rw [hp, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel]
    exact Nat.two_pow_pos _

/-- The same scaling identity before taking a floor or nearest integer. -/
theorem scaled_fraction_eq (remainder discarded output : Nat) :
    ((remainder : Rat) / 2 ^ discarded) * 2 ^ output =
      if discarded ≤ output then (remainder : Rat) * 2 ^ (output - discarded)
      else (remainder : Rat) / 2 ^ (discarded - output) := by
  split
  · rename_i h
    have hp : (2 : Rat) ^ output = 2 ^ (output - discarded) * 2 ^ discarded := by
      rw [← pow_add, Nat.sub_add_cancel h]
    rw [hp]
    field_simp
  · rename_i h
    have hp : (2 : Rat) ^ discarded = 2 ^ output * 2 ^ (discarded - output) := by
      rw [← pow_add, Nat.add_sub_of_le (by omega)]
    rw [hp]
    field_simp

/-- The shift-based stochastic-C helper computes the report's RNITE exactly. -/
theorem scaleFractionNearestEven_eq (remainder discarded output : Nat) :
    scaleFractionNearestEven remainder discarded output =
      RationalRounding.nearestEven (((remainder : Rat) / 2 ^ discarded) * 2 ^ output) := by
  rw [scaled_fraction_eq]
  unfold scaleFractionNearestEven
  split
  · have hc : (remainder : Rat) * 2 ^ (output - discarded) =
        ((remainder * 2 ^ (output - discarded) : Nat) : Rat) := by norm_cast
    have hn (n : Nat) : RationalRounding.nearestEven (n : Rat) = n := by
      simp only [RationalRounding.nearestEven, Nat.floor_natCast]
      simp
    rw [hc]
    rw [hn]
    simp [Nat.shiftLeft_eq]
  · rw [Numerics.roundShiftRightEven_eq_roundQuotientEven,
      RationalRounding.roundQuotientEven_eq_nearestEven _ _ (Nat.two_pow_pos _)]
    norm_cast

/-- Every valid dyadic remainder uses exactly the report's rational rounding decision. -/
theorem roundAway_eq_rational (format : Format) (mode : RoundingMode)
    (negative : Bool) (quantum : Int) (lower remainder discarded : Nat)
    (hrange : remainder < 2 ^ discarded) :
    roundAway format mode negative quantum lower remainder discarded =
      RationalRounding.roundAway mode negative (format.lowerCodeIsEven quantum lower)
        ((remainder : Rat) / 2 ^ discarded) := by
  have hb := RationalRounding.roundRationalAwayWithParity_eq mode negative
    (format.lowerCodeIsEven quantum lower) remainder (2 ^ discarded) (Nat.two_pow_pos discarded)
  push_cast at hb
  rw [← hb]
  by_cases hr : remainder = 0
  · simp [roundAway, roundRationalAwayWithParity, hr]
  have hd : 0 < discarded := by
    by_contra h
    have : discarded = 0 := by omega
    simp [this] at hrange
    omega
  have hp : 2 ^ discarded = 2 * 2 ^ (discarded - 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, discarded = n + 1 := ⟨discarded - 1, by omega⟩
    simp [pow_succ, Nat.mul_comm]
  have heven :
      scaleFractionNearestEven remainder discarded =
        scaleRationalFractionNearestEven remainder (2 ^ discarded) := by
    funext output
    rw [scaleFractionNearestEven_eq,
      RationalRounding.scaleRationalFractionNearestEven_eq _ _ _ (Nat.two_pow_pos _)]
    norm_cast
  have hle : 2 ^ discarded ≤ 2 * remainder ↔ 2 ^ (discarded - 1) ≤ remainder := by
    rw [hp]
    omega
  have hlt : 2 ^ discarded < 2 * remainder ↔ 2 ^ (discarded - 1) < remainder := by
    rw [hp]
    omega
  have heq : 2 ^ discarded = 2 * remainder ↔ remainder = 2 ^ (discarded - 1) := by
    rw [hp]
    omega
  cases mode <;>
    simp only [roundAway, roundRationalAwayWithParity, beq_iff_eq, hr, if_false,
      Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, scaleFractionFloor_eq_rational, heven,
      hle, hlt]
  have hb : (2 ^ discarded == 2 * remainder) = (remainder == 2 ^ (discarded - 1)) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq] using heq
  rw [hb]

end Format.Internal

namespace Format

/--
For every finite dyadic, precision rounding selects the report's floor or successor using the
exact fractional part. The witnesses include its binary denominator, so the fractional part lies
in `[0, 1)`. The theorem includes zero inputs and every stochastic word.
-/
theorem roundFiniteToPrecision_report_spec (format : Format) (mode : RoundingMode)
    (value : Numerics.Dyadic) :
    ∃ lower remainder discarded : Nat,
      remainder < 2 ^ discarded ∧
      value.toRat =
        Internal.signRat value.negative * ((lower : Rat) + (remainder : Rat) / 2 ^ discarded) *
          (2 : Rat) ^ format.quantumExponent value ∧
      (format.roundFiniteToPrecision mode value).toRat =
        Internal.signRat value.negative *
          ((if RationalRounding.roundAway mode value.negative
            (format.lowerCodeIsEven (format.quantumExponent value) lower)
            ((remainder : Rat) / 2 ^ discarded) then lower + 1 else lower : Nat) : Rat) *
          (2 : Rat) ^ format.quantumExponent value := by
  by_cases hz : value.significand = 0
  · refine ⟨0, 0, 0, by norm_num, ?_, ?_⟩
    · simp [hz]
    · simp [roundFiniteToPrecision, hz]
  · obtain ⟨lower, rem, d, hr, hv, hs, ho⟩ :=
      Internal.roundFiniteToPrecision_spec format mode value hz
    refine ⟨lower, rem, d, hr, hv, ?_⟩
    rw [ho, hs, Internal.roundAway_eq_rational format mode _ _ _ _ _ hr]

end Format
end FloatLib.Floats.Formats.P3109
