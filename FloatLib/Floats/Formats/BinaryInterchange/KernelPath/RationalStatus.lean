/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Proof

import Mathlib.Tactic.Positivity

/-!
# The status of a rational result is the status of its sticky dyadic

The reference status of a quotient or of a rational literal is defined on the exact rational
`± (n / d) * 2 ^ e` (`Model.rationalRoundingStatusScaled`, `Model.rationalTernaryScaled`), and
the status of a sum or a product on an exact dyadic (`Model.dyadicRoundingStatus`,
`Model.dyadicTernary`). Both compare the exact result with the same thresholds and with the
delivered value, and all of those are multiples of a quarter of the least positive subnormal
number, `2 ^ (minSubnormalExponent - 2)`.

So the rational can be replaced by its sticky dyadic: with `q` the floor of the rational in
units of that quarter and `s` one when a remainder is left, the dyadic
`± (2 * q + s) * 2 ^ (minSubnormalExponent - 3)` compares with every such multiple as the
rational does (`sticky_compare`). `rationalRoundingStatusScaled_sticky` and
`rationalTernaryScaled_sticky` state the result for every format, every rounding direction and
every delivered value.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
`q` is the floor of the nonnegative real `x` in units of `u`, and `s` is zero when `x` is that
multiple of `u` and one otherwise.
-/
structure Sticky (x u : ℝ) (q s : Nat) : Prop where
  /-- The floor is at most the value. -/
  low : (q : ℝ) * u ≤ x
  /-- The value is below the next multiple. -/
  high : x < ((q : ℝ) + 1) * u
  /-- The sticky bit says whether the value is the floor. -/
  bit : (s = 0 ∧ x = (q : ℝ) * u) ∨ (s = 1 ∧ x ≠ (q : ℝ) * u)

/-- A value compares with a multiple of the unit as its sticky half-unit value does. -/
theorem sticky_compare {x u : ℝ} {q s : Nat} (hu : 0 < u) (h : Sticky x u q s) (T : ℤ) :
    compare x ((T : ℝ) * u) = compare ((2 * (q : ℝ) + (s : ℝ)) * (u / 2)) ((T : ℝ) * u) := by
  obtain ⟨hlow, hhigh, hbit⟩ := h
  rcases hbit with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · rw [hx]
    congr 1
    push_cast
    ring
  · have hgt : (q : ℝ) * u < x := lt_of_le_of_ne hlow (Ne.symm hx)
    have hy : (2 * (q : ℝ) + ((1 : Nat) : ℝ)) * (u / 2) = (q : ℝ) * u + u / 2 := by
      push_cast
      ring
    rw [hy]
    rcases le_or_gt T (q : ℤ) with hT | hT
    · have hTu : (T : ℝ) * u ≤ (q : ℝ) * u :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hT) hu.le
      rw [compare_gt_iff_gt.mpr (by linarith), compare_gt_iff_gt.mpr (by linarith)]
    · have hT' : (q : ℤ) + 1 ≤ T := hT
      have hTu : ((q : ℝ) + 1) * u ≤ (T : ℝ) * u :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hT') hu.le
      rw [compare_lt_iff_lt.mpr (by linarith), compare_lt_iff_lt.mpr (by linarith)]

/-- The negated value compares with a multiple of the unit as its negated sticky value does. -/
theorem sticky_compare_neg {x u : ℝ} {q s : Nat} (hu : 0 < u) (h : Sticky x u q s) (T : ℤ) :
    compare (-x) ((T : ℝ) * u) =
      compare (-((2 * (q : ℝ) + (s : ℝ)) * (u / 2))) ((T : ℝ) * u) := by
  obtain ⟨hlow, hhigh, hbit⟩ := h
  rcases hbit with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · rw [hx]
    congr 2
    push_cast
    ring
  · have hgt : (q : ℝ) * u < x := lt_of_le_of_ne hlow (Ne.symm hx)
    have hy : (2 * (q : ℝ) + ((1 : Nat) : ℝ)) * (u / 2) = (q : ℝ) * u + u / 2 := by
      push_cast
      ring
    rw [hy]
    rcases le_or_gt (-(q : ℤ)) T with hT | hT
    · have hTu : -((q : ℝ) * u) ≤ (T : ℝ) * u := by
        have := mul_le_mul_of_nonneg_right
          (show ((-(q : ℤ) : ℤ) : ℝ) ≤ (T : ℝ) by exact_mod_cast hT) hu.le
        push_cast at this
        linarith
      rw [compare_lt_iff_lt.mpr (by linarith), compare_lt_iff_lt.mpr (by linarith)]
    · have hT' : T + 1 ≤ -(q : ℤ) := hT
      have hTu : (T : ℝ) * u ≤ -(((q : ℝ) + 1) * u) := by
        have := mul_le_mul_of_nonneg_right
          (show ((T + 1 : ℤ) : ℝ) ≤ ((-(q : ℤ) : ℤ) : ℝ) by exact_mod_cast hT') hu.le
        push_cast at this
        linarith
      rw [compare_gt_iff_gt.mpr (by linarith), compare_gt_iff_gt.mpr (by linarith)]

/-- A dyadic whose exponent is at least `c` is an integer multiple of `2 ^ c`. -/
theorem dyadic_onGrid (t : Numerics.Dyadic) (c : Int) (h : c ≤ t.exponent) :
    ∃ T : ℤ, t.toReal = (T : ℝ) * (2 : ℝ) ^ c := by
  refine ⟨t.signedSignificand * 2 ^ (t.exponent - c).toNat, ?_⟩
  unfold Numerics.Dyadic.toReal
  have hexp : t.exponent = ((t.exponent - c).toNat : Int) + c := by omega
  conv_lhs => rw [hexp, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  push_cast
  ac_rfl

/-- The real value of the sticky dyadic of a quotient: its half-unit multiple with the sign. -/
theorem sticky_toReal (sign : Bool) (q s : Nat) (c : Int) :
    Numerics.Dyadic.toReal ⟨sign, 2 * q + s, c - 1⟩ =
      (if sign then -1 else 1) * ((2 * (q : ℝ) + (s : ℝ)) * ((2 : ℝ) ^ c / 2)) := by
  unfold Numerics.Dyadic.toReal Numerics.Dyadic.signedSignificand
  rw [zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  cases sign
  · simp only [Bool.false_eq_true, ite_false, Int.ofNat_eq_natCast]
    push_cast
    ring
  · simp only [ite_true, Int.ofNat_eq_natCast]
    push_cast
    ring

/--
The scaled comparison of a signed rational with a dyadic on the grid of `2 ^ c` is the dyadic
comparison of the sticky dyadic of the rational with it.
-/
theorem compareDyadicScaled?_sticky (sign : Bool) (n d : Nat) (e c : Int) (hd : d ≠ 0)
    (q s : Nat) (h : Sticky (Model.scaledRatToReal n d e) ((2 : ℝ) ^ c) q s)
    (t : Numerics.Dyadic) (ht : c ≤ t.exponent) :
    Numerics.RationalBinary.compareDyadicScaled? sign n d e t =
      some (Model.cmpDyadic ⟨sign, 2 * q + s, c - 1⟩ t) := by
  obtain ⟨T, hT⟩ := dyadic_onGrid t c ht
  have hu : (0 : ℝ) < (2 : ℝ) ^ c := zpow_pos (by norm_num) c
  rw [Model.compareDyadicScaled?_eq_compare sign n d e t hd, Model.cmpDyadic_eq_compare,
    sticky_toReal, hT]
  congr 1
  cases sign
  · simp only [Model.signedScaledRatToReal, Bool.false_eq_true, ite_false, one_mul]
    exact sticky_compare hu h T
  · simp only [Model.signedScaledRatToReal, ite_true, neg_one_mul]
    exact sticky_compare_neg hu h T

/-! ## The thresholds of a format lie on the grid -/

/--
Every threshold that the status of a rounding compares with has an exponent of at least
`minSubnormalExponent - 2`.
-/
theorem threshold_exponents (fmt : FloatFormat) :
    fmt.minSubnormalExponent - 2 ≤ (Model.overflowMidpoint fmt).exponent ∧
      fmt.minSubnormalExponent - 2 ≤ (Model.overflowLimit fmt).exponent ∧
      fmt.minSubnormalExponent - 2 ≤ (Model.maxFiniteDyadic fmt).exponent ∧
      fmt.minSubnormalExponent - 2 ≤ (Model.underflowMidpoint fmt).exponent ∧
      fmt.minSubnormalExponent - 2 ≤ (Model.minNormalDyadic fmt).exponent ∧
      fmt.minSubnormalExponent - 2 ≤ (Model.underflowPredecessor fmt).exponent := by
  have hpos := fmt.maxFiniteExpField_pos
  simp only [Model.overflowMidpoint, Model.overflowLimit, Model.maxFiniteDyadic,
    Model.underflowMidpoint, Model.minNormalDyadic, Model.underflowPredecessor,
    FloatFormat.maxNormalExponent, FloatFormat.minSubnormalExponent,
    FloatFormat.minNormalExponent, Int.ofNat_eq_natCast]
  omega

/-- The exact value of a finite delivered value has an exponent on the grid. -/
theorem finiteDyadic_exponent {fmt : FloatFormat} (rounded : Model fmt)
    (hfinite : Model.isFinite rounded = true) :
    fmt.minSubnormalExponent - 2 ≤ (Model.finiteDyadic rounded hfinite).exponent := by
  have h := Model.minSubnormalExponent_le_toDyadic? rounded
    (d := Model.finiteDyadic rounded hfinite) (by simp [Model.finiteDyadic])
  omega

/-! ## The overflow test of the directions that round a magnitude up -/

/-- A binary power of the reference is a power of two. -/
theorem bpow_eq_zpow (e : Int) : Model.bpow e = (2 : ℝ) ^ e := by
  simp [Model.bpow, FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
    Numerics.Radix.toReal]

/--
The magnitude overflow test of a rational result, which the reference computes from the
leading exponent first, is the comparison of the rational with the largest finite value.
-/
theorem rationalMagnitudeOverflowsScaled_eq (fmt : FloatFormat) (n d : Nat) (e : Int)
    (hd : d ≠ 0) :
    Model.rationalMagnitudeOverflowsScaled fmt n d e =
      (Numerics.RationalBinary.compareDyadicScaled? false n d e (Model.maxFiniteDyadic fmt) ==
        some .gt) := by
  have htwo : (2 : ℝ) ≠ 0 := two_ne_zero
  have hfrac := fmt.maxFiniteFracField_lt_two_pow
  have hsig : (Model.maxFiniteDyadic fmt).significand =
      2 ^ fmt.fracWidth + fmt.maxFiniteFracField := by
    simp [Model.maxFiniteDyadic, Model.pow2_eq_two_pow]
  have hsig0 : (Model.maxFiniteDyadic fmt).significand ≠ 0 := by
    have := Nat.two_pow_pos fmt.fracWidth
    omega
  by_cases hn : n = 0
  · subst hn
    have hcond : (d == 0 || (0 : Nat) == 0) = true := by simp
    have hneg : (Model.maxFiniteDyadic fmt).negative = false := rfl
    simp only [Model.rationalMagnitudeOverflowsScaled,
      Numerics.RationalBinary.compareDyadicScaled?, beq_iff_eq, hd, hsig0, hcond, hneg,
      ite_true, ite_false, Bool.false_eq_true]
    rfl
  · rw [Model.compareDyadicScaled?_false_eq_compare n d e _ hd]
    have hbounds := Model.scaledRatToReal_floorLog2_bounds n d e hn hd
    rw [bpow_eq_zpow, bpow_eq_zpow] at hbounds
    have hM : (Model.maxFiniteDyadic fmt).toReal =
        ((2 : ℝ) ^ fmt.fracWidth + (fmt.maxFiniteFracField : ℝ)) *
          (2 : ℝ) ^ (fmt.maxNormalExponent - (fmt.fracWidth : Int)) := by
      simp [Model.maxFiniteDyadic, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
        Model.pow2_eq_two_pow]
    have hscale : (0 : ℝ) < (2 : ℝ) ^ (fmt.maxNormalExponent - (fmt.fracWidth : Int)) :=
      zpow_pos (by norm_num) _
    have hMlow : (2 : ℝ) ^ fmt.maxNormalExponent ≤ (Model.maxFiniteDyadic fmt).toReal := by
      rw [hM]
      have hsplit : (2 : ℝ) ^ fmt.maxNormalExponent =
          (2 : ℝ) ^ fmt.fracWidth * (2 : ℝ) ^ (fmt.maxNormalExponent - (fmt.fracWidth : Int)) := by
        rw [← zpow_natCast, ← zpow_add₀ htwo]
        congr 1
        omega
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right (by linarith) hscale.le
    have hMhigh : (Model.maxFiniteDyadic fmt).toReal <
        (2 : ℝ) ^ (fmt.maxNormalExponent + 1) := by
      rw [hM]
      have hsplit : (2 : ℝ) ^ (fmt.maxNormalExponent + 1) =
          ((2 : ℝ) ^ fmt.fracWidth + (2 : ℝ) ^ fmt.fracWidth) *
            (2 : ℝ) ^ (fmt.maxNormalExponent - (fmt.fracWidth : Int)) := by
        rw [← two_mul, ← pow_succ', ← zpow_natCast, ← zpow_add₀ htwo]
        congr 1
        push_cast
        omega
      rw [hsplit]
      have hlt : (fmt.maxFiniteFracField : ℝ) < (2 : ℝ) ^ fmt.fracWidth := by
        exact_mod_cast hfrac
      exact mul_lt_mul_of_pos_right (by linarith) hscale
    have hMpos : (0 : ℝ) < (Model.maxFiniteDyadic fmt).toReal :=
      lt_of_lt_of_le (zpow_pos (by norm_num) _) hMlow
    have hcond : (d == 0 || n == 0) = false := by simp [hd, hn]
    unfold Model.rationalMagnitudeOverflowsScaled
    simp only [hcond, Bool.false_eq_true, ite_false]
    by_cases hlt : Numerics.RationalBinary.floorLog2 n d + e < fmt.maxNormalExponent
    · have hx : Model.scaledRatToReal n d e < (Model.maxFiniteDyadic fmt).toReal :=
        lt_of_lt_of_le hbounds.2
          (le_trans (zpow_le_zpow_right₀ (by norm_num) (by omega)) hMlow)
      simp only [hlt, ite_true, compare_lt_iff_lt.mpr hx]
      rfl
    · by_cases hgt : Numerics.RationalBinary.floorLog2 n d + e > fmt.maxNormalExponent
      · have hx : (Model.maxFiniteDyadic fmt).toReal < Model.scaledRatToReal n d e :=
          lt_of_lt_of_le hMhigh
            (le_trans (zpow_le_zpow_right₀ (by norm_num) (by omega)) hbounds.1)
        simp only [hlt, hgt, ite_true, ite_false, compare_gt_iff_gt.mpr hx]
        rfl
      · simp only [hlt, hgt, ite_false]
        -- The leading exponents agree: the two values are compared as a ratio.
        have hratio : Model.scaledRatToReal n d e / (Model.maxFiniteDyadic fmt).toReal =
            Model.scaledRatToReal n (d * (Model.maxFiniteDyadic fmt).significand)
              (e - (Model.maxFiniteDyadic fmt).exponent) := by
          have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
          have hsR : ((Model.maxFiniteDyadic fmt).significand : ℝ) ≠ 0 := by
            exact_mod_cast hsig0
          have hneg : (Model.maxFiniteDyadic fmt).negative = false := rfl
          have hpow : (2 : ℝ) ^ (Model.maxFiniteDyadic fmt).exponent ≠ 0 :=
            (zpow_pos (by norm_num) _).ne'
          simp only [Model.scaledRatToReal, bpow_eq_zpow, Numerics.Dyadic.toReal,
            Numerics.Dyadic.signedSignificand, hneg, Bool.false_eq_true, ite_false,
            Int.ofNat_eq_natCast, Int.cast_natCast, Nat.cast_mul, zpow_sub₀ htwo]
          field_simp
        have hreal := Model.scaleByPowerOfTwo_real n
          (d * (Model.maxFiniteDyadic fmt).significand) (e - (Model.maxFiniteDyadic fmt).exponent)
        have hden : 0 < (Numerics.RationalBinary.scaleByPowerOfTwo n
            (d * (Model.maxFiniteDyadic fmt).significand)
            (e - (Model.maxFiniteDyadic fmt).exponent)).2 := by
          have hpos : 0 < d * (Model.maxFiniteDyadic fmt).significand :=
            Nat.mul_pos (Nat.pos_of_ne_zero hd) (Nat.pos_of_ne_zero hsig0)
          cases e - (Model.maxFiniteDyadic fmt).exponent with
          | ofNat shift => exact hpos
          | negSucc shift =>
            change 0 < Nat.shiftLeft (d * (Model.maxFiniteDyadic fmt).significand) (shift + 1)
            rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
            exact Nat.mul_pos hpos (Nat.two_pow_pos _)
        rw [← hratio] at hreal
        generalize Numerics.RationalBinary.scaleByPowerOfTwo n _ _ = scaled at hreal hden ⊢
        have hden' : (0 : ℝ) < (scaled.2 : ℝ) := by exact_mod_cast hden
        have hiff : scaled.1 > scaled.2 ↔
            (Model.maxFiniteDyadic fmt).toReal < Model.scaledRatToReal n d e := by
          constructor
          · intro h
            have h1 : (1 : ℝ) < (scaled.1 : ℝ) / (scaled.2 : ℝ) := by
              rw [lt_div_iff₀ hden', one_mul]
              exact_mod_cast h
            rw [hreal, lt_div_iff₀ hMpos, one_mul] at h1
            exact h1
          · intro h
            have h1 : (1 : ℝ) <
                Model.scaledRatToReal n d e / (Model.maxFiniteDyadic fmt).toReal := by
              rw [lt_div_iff₀ hMpos, one_mul]
              exact h
            rw [← hreal, lt_div_iff₀ hden', one_mul] at h1
            exact_mod_cast h1
        by_cases hx : (Model.maxFiniteDyadic fmt).toReal < Model.scaledRatToReal n d e
        · rw [compare_gt_iff_gt.mpr hx, decide_eq_true (hiff.mpr hx)]
          rfl
        · have hnot : ¬ scaled.1 > scaled.2 := fun h => hx (hiff.mp h)
          rw [decide_eq_false hnot]
          rcases lt_or_eq_of_le (not_lt.mp hx) with h | h
          · rw [compare_lt_iff_lt.mpr h]
            rfl
          · rw [compare_eq_iff_eq.mpr h]
            rfl

/-! ## The parts of the status -/

section Parts

variable (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (sign : Bool) (n d : Nat) (e : Int)
  (q s : Nat)

/--
The tininess test of a rational result is that of its sticky dyadic, for every delivered value.
-/
theorem rationalIsTinyAfterRoundingScaled_sticky (hd : d ≠ 0)
    (h : Sticky (Model.scaledRatToReal n d e) ((2 : ℝ) ^ (fmt.minSubnormalExponent - 2)) q s)
    (rounded : Model fmt) :
    Model.rationalIsTinyAfterRoundingScaled fmt mode sign n d e rounded =
      Model.dyadicIsTinyAfterRounding fmt mode
        ⟨sign, 2 * q + s, fmt.minSubnormalExponent - 2 - 1⟩ rounded := by
  obtain ⟨-, -, -, hmid, hmin, hpred⟩ := threshold_exponents fmt
  have hmidpoint := compareDyadicScaled?_sticky false n d e _ hd q s h
    (Model.underflowMidpoint fmt) hmid
  have hnormal := compareDyadicScaled?_sticky false n d e _ hd q s h
    (Model.minNormalDyadic fmt) hmin
  have hpredecessor := compareDyadicScaled?_sticky false n d e _ hd q s h
    (Model.underflowPredecessor fmt) hpred
  unfold Model.rationalIsTinyAfterRoundingScaled Model.dyadicIsTinyAfterRounding
  cases Model.isTinyAfterRounding rounded
  · cases mode <;> cases sign <;>
      simp only [Model.IEEERoundingMode.roundsAwayFromZero, hmidpoint, hnormal, hpredecessor,
        Bool.false_eq_true, ite_false, ite_true, Bool.not_false, Bool.not_true] <;>
      first
        | (generalize Model.cmpDyadic _ (Model.underflowMidpoint fmt) = order
           cases order <;> rfl)
        | (generalize Model.cmpDyadic _ (Model.minNormalDyadic fmt) = order
           cases order <;> rfl)
        | (generalize Model.cmpDyadic _ (Model.underflowPredecessor fmt) = order
           cases order <;> rfl)
  · rfl

/-- The overflow test of a rational result is that of its sticky dyadic. -/
theorem rationalRoundingOverflowsScaled_sticky (hd : d ≠ 0)
    (h : Sticky (Model.scaledRatToReal n d e) ((2 : ℝ) ^ (fmt.minSubnormalExponent - 2)) q s) :
    Model.rationalRoundingOverflowsScaled fmt mode sign n d e =
      Model.dyadicRoundingOverflows fmt mode
        ⟨sign, 2 * q + s, fmt.minSubnormalExponent - 2 - 1⟩ := by
  obtain ⟨hmid, hlim, hmax, -, -, -⟩ := threshold_exponents fmt
  have hmidpoint := compareDyadicScaled?_sticky false n d e _ hd q s h
    (Model.overflowMidpoint fmt) hmid
  have hlimit := compareDyadicScaled?_sticky false n d e _ hd q s h
    (Model.overflowLimit fmt) hlim
  have hmagnitude : Model.rationalMagnitudeOverflowsScaled fmt n d e =
      (Model.cmpDyadic ⟨false, 2 * q + s, fmt.minSubnormalExponent - 2 - 1⟩
        (Model.maxFiniteDyadic fmt) == .gt) := by
    rw [rationalMagnitudeOverflowsScaled_eq fmt n d e hd,
      compareDyadicScaled?_sticky false n d e _ hd q s h (Model.maxFiniteDyadic fmt) hmax]
    generalize Model.cmpDyadic _ (Model.maxFiniteDyadic fmt) = order
    cases order <;> rfl
  unfold Model.rationalRoundingOverflowsScaled Model.dyadicRoundingOverflows
  cases mode <;> cases sign <;>
    simp only [Model.rationalNearestEvenOverflowsScaled,
      Model.rationalNearestAwayOverflowsScaled, Model.rationalTruncationOverflowsScaled,
      Model.dyadicNearestEvenOverflows, Model.dyadicNearestAwayOverflows,
      Model.dyadicTruncationOverflows, Model.dyadicMagnitudeOverflows, hmidpoint, hlimit,
      hmagnitude, Bool.false_eq_true, ite_false, ite_true] <;>
    first
      | (generalize Model.cmpDyadic _ (Model.overflowMidpoint fmt) = order
         cases order <;> rfl)
      | (generalize Model.cmpDyadic _ (Model.overflowLimit fmt) = order
         cases order <;> rfl)

/-- Reversing a comparison of real numbers swaps its result. -/
theorem compare_swap_real (a b : ℝ) : compare a b = (compare b a).swap := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_gt_iff_gt.mpr h]
    rfl
  · rw [h, compare_eq_iff_eq.mpr rfl]
    rfl
  · rw [compare_gt_iff_gt.mpr h, compare_lt_iff_lt.mpr h]
    rfl

/--
The status of delivering `rounded` for a rational result is the status of delivering it for the
sticky dyadic of that rational, for every format, every rounding direction and every delivered
value.
-/
theorem rationalRoundingStatusScaled_sticky (hd : d ≠ 0)
    (h : Sticky (Model.scaledRatToReal n d e) ((2 : ℝ) ^ (fmt.minSubnormalExponent - 2)) q s)
    (rounded : Model fmt) :
    Model.rationalRoundingStatusScaled fmt mode sign n d e rounded =
      Model.dyadicRoundingStatus fmt mode
        ⟨sign, 2 * q + s, fmt.minSubnormalExponent - 2 - 1⟩ rounded := by
  unfold Model.rationalRoundingStatusScaled Model.dyadicRoundingStatus
  rw [rationalRoundingOverflowsScaled_sticky fmt mode sign n d e q s hd h,
    rationalIsTinyAfterRoundingScaled_sticky fmt mode sign n d e q s hd h rounded]
  by_cases hfinite : Model.isFinite rounded = true
  · have hcompare := compareDyadicScaled?_sticky sign n d e _ hd q s h
      (Model.finiteDyadic rounded hfinite) (finiteDyadic_exponent rounded hfinite)
    simp only [hfinite, dite_true, Model.rationalEqualsDyadicScaled, hcompare]
    generalize Model.cmpDyadic _ (Model.finiteDyadic rounded hfinite) = order
    cases order <;> rfl
  · have hfalse : Model.isFinite rounded = false := Bool.eq_false_of_not_eq_true hfinite
    simp only [hfalse, Bool.false_eq_true, dite_false]

/--
The ternary value of delivering `rounded` for a rational result is the ternary value of
delivering it for the sticky dyadic of that rational.
-/
theorem rationalTernaryScaled_sticky (hd : d ≠ 0)
    (h : Sticky (Model.scaledRatToReal n d e) ((2 : ℝ) ^ (fmt.minSubnormalExponent - 2)) q s)
    (rounded : Model fmt) :
    Model.rationalTernaryScaled sign n d e rounded =
      Model.dyadicTernary ⟨sign, 2 * q + s, fmt.minSubnormalExponent - 2 - 1⟩ rounded := by
  unfold Model.rationalTernaryScaled Model.dyadicTernary
  by_cases hfinite : Model.isFinite rounded = true
  · have hcompare := compareDyadicScaled?_sticky sign n d e _ hd q s h
      (Model.finiteDyadic rounded hfinite) (finiteDyadic_exponent rounded hfinite)
    simp only [hfinite, dite_true, hcompare]
    rw [Model.cmpDyadic_eq_compare, Model.cmpDyadic_eq_compare]
    exact (compare_swap_real _ _).symm
  · have hfalse : Model.isFinite rounded = false := Bool.eq_false_of_not_eq_true hfinite
    simp only [hfalse, Bool.false_eq_true, dite_false]

end Parts

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
