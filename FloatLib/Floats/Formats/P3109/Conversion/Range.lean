/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Conversion.Comparison
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Direction
public import FloatLib.Floats.Formats.P3109.Projection.Range

/-!
# Range preservation before P3109 saturation

An input in the finite interval cannot round past either endpoint in any mode. The endpoint
is an integer multiple of the input quantum, and each mode preserves integers and chooses one
of the two adjacent candidates. Thus precision-rounding overflow implies that the exact input
was already outside the finite interval. This is a one-way implication.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109
namespace RationalRounding

/-- Choosing either adjacent candidate, while preserving integers, cannot cross an integer bound. -/
theorem roundedInteger_le_natCast (mode : RoundingMode) (negative : Bool) (parity : Nat → Bool)
    (value : Rat) (bound : Nat) (hnonneg : 0 ≤ value) (hv : value ≤ bound) :
    roundedInteger mode negative parity value ≤ bound := by
  by_cases heq : value = bound
  · rw [heq, roundedInteger_natCast]
  · have hlt : value < bound := lt_of_le_of_ne hv heq
    have hf := (Nat.floor_lt hnonneg).mpr hlt
    exact le_trans (roundedInteger_bounds mode negative parity value).2 (by omega)

/-- Rounding preserves an upper grid endpoint whenever the input quantum divides that endpoint. -/
theorem abs_roundAt_le_grid (mode : RoundingMode) (quantum : Int) (parity : Nat → Bool)
    (value : Rat) (significand : Nat) (exponent : Int)
    (hq : quantum ≤ exponent)
    (hv : |value| ≤ (significand : Rat) * (2 : Rat) ^ exponent) :
    |roundAt mode quantum parity value| ≤ (significand : Rat) * (2 : Rat) ^ exponent := by
  let bound := significand * 2 ^ (exponent - quantum).toNat
  have he : (exponent - quantum).toNat = exponent - quantum :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hq)
  have hb : (bound : Rat) * (2 : Rat) ^ quantum =
      (significand : Rat) * (2 : Rat) ^ exponent := by
    dsimp only [bound]
    push_cast
    rw [← zpow_natCast, he, mul_assoc, ← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
    congr 2
    omega
  have hs : scaledMagnitude value quantum ≤ (bound : Rat) := by
    apply (mul_le_mul_iff_left₀ (zpow_pos (by norm_num : (0 : Rat) < 2) quantum)).mp
    simpa only [mul_comm ((2 : Rat) ^ quantum), scaledMagnitude_mul_quantum, hb] using hv
  have hi := roundedInteger_le_natCast mode (value.num < 0) parity _ bound
    (scaledMagnitude_nonneg _ _) hs
  rw [roundAt, abs_signed, abs_of_nonneg (by positivity)]
  rw [← hb]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) (by positivity)

end RationalRounding

namespace Format

/-- Decoding uses a strictly bounded significand; a carry is introduced only by rounding. -/
theorem decodePositiveFinite_significand_lt_precision (format : Format) (bits : Nat) :
    (format.decodePositiveFinite bits).significand < 2 ^ format.precision := by
  have hp : 2 ^ format.precision = 2 * 2 ^ format.trailingBits := by
    rw [← format.trailingBits_add_one, pow_succ]
    omega
  have hm := Nat.mod_lt bits (Nat.two_pow_pos format.trailingBits)
  unfold decodePositiveFinite
  split
  · simp only [Dyadic.zero_significand]
    positivity
  · dsimp only
    split <;> dsimp only <;> omega

/-- An in-range nonzero magnitude chooses a quantum dividing every upper grid bound. -/
theorem rationalQuantum_le_grid_exponent (format : Format) (value : Rat)
    (significand : Nat) (exponent : Int) (hvalue : value ≠ 0)
    (hs : significand < 2 ^ format.precision)
    (he : format.minimumQuantumExponent ≤ exponent)
    (hv : |value| ≤ (significand : Rat) * (2 : Rat) ^ exponent) :
    RationalRounding.quantum format.precision format.exponentBias value ≤ exponent := by
  have hlead := (RationalRounding.leadingExponent_bounds value hvalue).1
  have hs' : (significand : Rat) < (2 : Rat) ^ format.precision := by exact_mod_cast hs
  have hupper : |value| < (2 : Rat) ^ (exponent + (format.precision : Int)) := by
    calc
      |value| ≤ (significand : Rat) * (2 : Rat) ^ exponent := hv
      _ < (2 : Rat) ^ format.precision * (2 : Rat) ^ exponent :=
        mul_lt_mul_of_pos_right hs' (by positivity)
      _ = _ := by rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0), zpow_natCast]; ring
  have hlog : RationalBinary.floorLog2 value.num.natAbs value.den <
      exponent + (format.precision : Int) := by
    by_contra h
    have hp := zpow_le_zpow_right₀ (by norm_num : (1 : Rat) ≤ 2) (le_of_not_gt h)
    linarith
  unfold RationalRounding.quantum
  unfold minimumQuantumExponent at he
  simp only [Int.ofNat_eq_natCast] at he
  omega

/-- Every mode preserves the finite magnitude bound before saturation. -/
theorem abs_roundFiniteRatToPrecision_le_maxFinite (format : Format) (mode : RoundingMode)
    (value : Rat) (hv : |value| ≤ format.maxFinite.toRat) :
    |(format.roundFiniteRatToPrecision mode value).toRat| ≤ format.maxFinite.toRat := by
  rw [roundFiniteRatToPrecision_toRat]
  by_cases hz : value = 0
  · simp [hz, RationalRounding.round, format.maxFinite_toRat_pos.le]
  have hs := format.decodePositiveFinite_significand_lt_precision format.maxFiniteBits
  have hn : format.maxFinite.significand ≠ 0 := by
    exact (format.decodePositiveFinite_significand_eq_zero_iff _).not.mpr
      format.maxFiniteBits_pos.ne'
  have he := (format.maxFinite_fitsPrecisionGrid.resolve_left hn).2
  have hm : format.maxFinite.toRat =
      (format.maxFinite.significand : Rat) * (2 : Rat) ^ format.maxFinite.exponent := by
    have hsign : format.maxFinite.negative = false := format.decodePositiveFinite_negative _
    simp [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand, hsign]
  rw [hm] at hv ⊢
  exact RationalRounding.abs_roundAt_le_grid mode _ _ value _ _
    (format.rationalQuantum_le_grid_exponent value _ _ hz hs he hv) hv

/-- Rounding a nonnegative rational cannot introduce a negative result. -/
theorem roundFiniteRatToPrecision_nonneg (format : Format) (mode : RoundingMode)
    (value : Rat) (hv : 0 ≤ value) :
    0 ≤ (format.roundFiniteRatToPrecision mode value).toRat := by
  rw [roundFiniteRatToPrecision_toRat]
  have hn : ¬value.num < 0 := by
    rw [← Rat.num_nonneg] at hv
    omega
  simp only [RationalRounding.round, RationalRounding.roundAt, RationalRounding.signed,
    hn, decide_false, Bool.false_eq_true, if_false]
  positivity

/-- The descriptor's closed finite interval is preserved by every supplied rounding mode. -/
theorem roundFiniteRatToPrecision_mem_range (format : Format) (mode : RoundingMode)
    (value : Rat) (hlo : format.minFinite.toRat ≤ value) (hhi : value ≤ format.maxFinite.toRat) :
    format.minFinite.toRat ≤ (format.roundFiniteRatToPrecision mode value).toRat ∧
      (format.roundFiniteRatToPrecision mode value).toRat ≤ format.maxFinite.toRat := by
  cases hsign : format.signedness with
  | signed =>
      simp only [minFinite, hsign, Dyadic.neg_toRat] at hlo ⊢
      exact abs_le.mp (format.abs_roundFiniteRatToPrecision_le_maxFinite mode value
        (abs_le.mpr ⟨hlo, hhi⟩))
  | unsigned =>
      simp only [minFinite, hsign, Dyadic.zero_toRat] at hlo ⊢
      exact ⟨format.roundFiniteRatToPrecision_nonneg mode value hlo,
        le_trans (le_abs_self _) (format.abs_roundFiniteRatToPrecision_le_maxFinite mode value
          (by rwa [abs_of_nonneg hlo]))⟩

end Format
end FloatLib.Floats.Formats.P3109

namespace FloatLib.Floats.ExecFloat.P3109.Conversion

open Formats.P3109

/--
Precision-rounding overflow entails that the exact rational was outside the finite interval.
This holds before saturation, for every mode and every supplied stochastic word.
-/
theorem roundedExceedsFiniteRange_implies_outside (format : Format) (mode : RoundingMode)
    (exact : Rat) (hoverflow : roundedExceedsFiniteRange format mode exact = true) :
    exact < format.minFinite.toRat ∨ format.maxFinite.toRat < exact := by
  rw [roundedExceedsFiniteRange_eq_decide, decide_eq_true_eq] at hoverflow
  by_contra hin
  push Not at hin
  have hrounded := format.roundFiniteRatToPrecision_mem_range mode exact hin.1 hin.2
  exact hoverflow.elim (not_lt_of_ge hrounded.1) (not_lt_of_ge hrounded.2)

/-- The executable overflow indicator implies the executable exact-out-of-range indicator. -/
theorem roundedExceedsFiniteRange_implies_exceedsFiniteRange
    (format : Format) (mode : RoundingMode) (exact : Rat)
    (hoverflow : roundedExceedsFiniteRange format mode exact = true) :
    exceedsFiniteRange format exact = true := by
  rw [exceedsFiniteRange_eq_decide, decide_eq_true_eq]
  exact roundedExceedsFiniteRange_implies_outside format mode exact hoverflow

/-- A finite conversion's overflow flag witnesses exclusion of its exact input from the range. -/
theorem status_overflow_implies_outside (format : Format) (policy : ProjectionPolicy)
    (exact : Rat) (hoverflow : (status format policy (.finite exact)).overflow = true) :
    exact < format.minFinite.toRat ∨ format.maxFinite.toRat < exact :=
  roundedExceedsFiniteRange_implies_outside format policy.rounding exact hoverflow

end FloatLib.Floats.ExecFloat.P3109.Conversion
