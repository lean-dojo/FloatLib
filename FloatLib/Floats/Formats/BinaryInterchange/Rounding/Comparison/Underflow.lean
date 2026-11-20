/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Comparison.Overflow
import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Decode

/-!
# The underflow flag of a rounding by comparisons

IEEE 754-2019 §7.5 signals underflow, under default exception handling, for an inexact result
that is tiny. FloatLib detects tininess after rounding: a nonzero result is tiny when its
rounding to the precision of the format with an unbounded exponent range lies strictly between
plus and minus the least normal magnitude. Just below the least normal magnitude that grid has
half the spacing of the subnormal numbers, so tininess is decided by a boundary of the direction
(`AlgebraicRounding.TinyAfterRounding`): the least normal magnitude itself when the direction
truncates the magnitude, the value of the grid before it (`underflowPredecessor`) when the
direction rounds the magnitude up, and their midpoint (`underflowMidpoint`) to nearest, where
a tie goes to the least normal magnitude under both tie rules. The predicate is stated by these
boundaries, which are the ones of the tininess of the arithmetic operations
(`dyadicIsTinyAfterRounding_eq_true_iff`).

`ComparisonRounding.outcome` decides the flag from the encoding it delivers: a zero or a
subnormal number is tiny, and the least normal magnitude is tiny when the magnitude of the
located number is before the boundary. This module proves that the decision is the boundary
alone, for every format descriptor and every rounding direction:

* `AlgebraicRounding.abs_roundAt_lt_minNormal_iff` and `abs_roundAt_eq_minNormal`: where the
  rounding on the grid of the format, subnormal numbers included, is below the least normal
  magnitude, and where it is that magnitude.
* `ComparisonRounding.outcome_underflow_iff`, `deliver_underflow_iff`,
  `Rule.deliver_underflow_iff`, `unary_underflow_iff` and `binary_underflow_iff`: `underflow`
  is raised exactly when the result is inexact and the magnitude of the located number is tiny
  after rounding in the direction, through the flags, the rules and the operand tables. That
  includes a format with one zero, and a result beyond the range, which is never tiny.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats FloatLib.Numerics FloatLib.Floats.Formats.Flocq

variable {fmt : FloatFormat}

namespace AlgebraicRounding

/--
The magnitudes that are tiny after rounding by `rule`: their rounding to the precision of `fmt`
with an unbounded exponent range is below the least normal magnitude. That is below the least
normal magnitude when the rule truncates, at most the value of that grid before it when the
rule rounds up, and below the midpoint of the two to nearest.
-/
def TinyAfterRounding (fmt : FloatFormat) (rule : MagnitudeRounding) (t : ℝ) : Prop :=
  match rule with
  | .down => t < (minNormalDyadic fmt).toReal
  | .up => t ≤ (underflowPredecessor fmt).toReal
  | .nearestEven | .nearestAway => t < (underflowMidpoint fmt).toReal

/--
The magnitudes whose rounding by `rule` on the grid of `fmt`, subnormal numbers included, is
below the least normal magnitude: below it when the rule truncates, at most the largest
subnormal number when the rule rounds up, and below their midpoint to nearest. That midpoint is
`underflowPredecessor`, and a tie goes to the least normal magnitude under both tie rules.
-/
def RoundsBelowNormal (fmt : FloatFormat) (rule : MagnitudeRounding) (t : ℝ) : Prop :=
  match rule with
  | .down => t < (minNormalDyadic fmt).toReal
  | .up => t ≤ (minNormalDyadic fmt).toReal - Flocq.bpow binaryRadix fmt.minSubnormalExponent
  | .nearestEven | .nearestAway => t < (underflowPredecessor fmt).toReal

/-- The least normal magnitude and the two boundaries below it are multiples of the subnormal
spacing, with an odd integer `m` for the largest subnormal number. -/
private theorem bottom_cell_values (fmt : FloatFormat) :
    ∃ m : ℕ, m % 2 = 1 ∧
      (minNormalDyadic fmt).toReal =
        ((m : ℝ) + 1) * Flocq.bpow binaryRadix fmt.minSubnormalExponent ∧
      (underflowPredecessor fmt).toReal =
        ((m : ℝ) + 1 / 2) * Flocq.bpow binaryRadix fmt.minSubnormalExponent ∧
      (underflowMidpoint fmt).toReal =
        ((m : ℝ) + 3 / 4) * Flocq.bpow binaryRadix fmt.minSubnormalExponent ∧
      (m : ℝ) + 1 = ((2 ^ fmt.fracWidth : ℕ) : ℝ) ∧ 1 ≤ m := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero fmt.fracWidth_pos.ne'
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = 2 ^ fmt.fracWidth :=
    ⟨2 ^ fmt.fracWidth - 1, Nat.sub_add_cancel Nat.one_le_two_pow⟩
  have hsplit : m + 1 = 2 ^ k * 2 := by rw [hm, hk, pow_succ]
  have hcast : (m : ℝ) + 1 = ((2 ^ fmt.fracWidth : ℕ) : ℝ) := by
    rw [← hm]
    push_cast
    rfl
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  refine ⟨m, by omega, ?_, ?_, ?_, hcast, by omega⟩
  · simp only [minNormalDyadic, Numerics.Dyadic.toReal_mk_false]
    rw [pow2_eq_two_pow, ← hcast, Flocq.bpow_binaryRadix]
  · have hsignificand : 2 * pow2 fmt.fracWidth - 1 = 2 * m + 1 := by
      rw [pow2_eq_two_pow, ← hm]
      omega
    simp only [underflowPredecessor, Numerics.Dyadic.toReal_mk_false]
    rw [hsignificand, Flocq.bpow_binaryRadix, zpow_sub_one₀ htwo]
    push_cast
    ring
  · have hsignificand : 4 * pow2 fmt.fracWidth - 1 = 4 * m + 3 := by
      rw [pow2_eq_two_pow, ← hm]
      omega
    simp only [underflowMidpoint, Numerics.Dyadic.toReal_mk_false]
    rw [hsignificand, Flocq.bpow_binaryRadix,
      show fmt.minSubnormalExponent - 2 = fmt.minSubnormalExponent - 1 - 1 by ring,
      zpow_sub_one₀ htwo, zpow_sub_one₀ htwo]
    push_cast
    ring

/-- The canonical exponent of a positive magnitude below the least normal one is the exponent
of the subnormal numbers. -/
private theorem cexp_of_lt_minNormal {t : ℝ} (hpositive : 0 < t)
    (hlt : t < (minNormalDyadic fmt).toReal) :
    cexp binaryRadix (fexpOf fmt) t = fmt.minSubnormalExponent := by
  obtain ⟨m, -, hnormal, -, -, hcast, -⟩ := bottom_cell_values fmt
  have hupper : |t| <
      Flocq.bpow binaryRadix ((fmt.fracWidth : ℤ) + fmt.minSubnormalExponent) := by
    rw [abs_of_pos hpositive, Flocq.bpow.add_exp, Flocq.bpow_binaryRadix (fmt.fracWidth : ℤ),
      zpow_natCast]
    rw [hnormal, hcast] at hlt
    push_cast at hlt
    exact hlt
  have hmagnitude := magnitude_le_of_abs_lt_bpow binaryRadix t _ hpositive.ne' hupper
  simp only [cexp, fexpOf, fltExp]
  omega

/--
A magnitude from the largest subnormal number up to the least normal magnitude rounds, in every
direction, to one of the two. A guard bit and a sticky bit name its place between them, and the
rule of the direction decides from them; the largest subnormal significand is odd.
-/
private theorem roundAt_bottom_cell (mode : IEEERoundingMode) {t : ℝ}
    (hlower : (minNormalDyadic fmt).toReal -
      Flocq.bpow binaryRadix fmt.minSubnormalExponent ≤ t)
    (hupper : t < (minNormalDyadic fmt).toReal) :
    ∃ guard sticky : Bool,
      (guard = true ↔ (underflowPredecessor fmt).toReal ≤ t) ∧
      (sticky = true ↔
        t ≠ (minNormalDyadic fmt).toReal - Flocq.bpow binaryRadix fmt.minSubnormalExponent ∧
          t ≠ (underflowPredecessor fmt).toReal) ∧
      roundAt fmt t mode =
        if (mode.magnitudeRounding false).increment true guard sticky = true
        then (minNormalDyadic fmt).toReal
        else (minNormalDyadic fmt).toReal -
          Flocq.bpow binaryRadix fmt.minSubnormalExponent := by
  obtain ⟨m, hodd, hnormal, hpredecessor, -, -, hm⟩ := bottom_cell_values fmt
  have hpow := Flocq.bpow.pos binaryRadix fmt.minSubnormalExponent
  have hsubnormal : (minNormalDyadic fmt).toReal -
      Flocq.bpow binaryRadix fmt.minSubnormalExponent =
      (m : ℝ) * Flocq.bpow binaryRadix fmt.minSubnormalExponent := by
    rw [hnormal]
    ring
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpositive : 0 < t := by
    refine lt_of_lt_of_le ?_ hlower
    rw [hsubnormal]
    exact mul_pos (by linarith) hpow
  have hcexp := cexp_of_lt_minNormal hpositive hupper
  obtain ⟨w, rfl⟩ : ∃ w : ℝ, t = w * Flocq.bpow binaryRadix fmt.minSubnormalExponent :=
    ⟨t / Flocq.bpow binaryRadix fmt.minSubnormalExponent, (div_mul_cancel₀ t hpow.ne').symm⟩
  rw [hsubnormal] at hlower ⊢
  rw [hnormal] at hupper ⊢
  have hwlo : (m : ℝ) ≤ w := le_of_mul_le_mul_right hlower hpow
  have hwhi : w < (m : ℝ) + 1 := lt_of_mul_lt_mul_right hupper hpow.le
  have hscaled : scaledMantissa binaryRadix (fexpOf fmt)
      (w * Flocq.bpow binaryRadix fmt.minSubnormalExponent) = w := by
    rw [scaledMantissa_eq_div, hcexp, mul_div_cancel_right₀ _ hpow.ne']
  have hparity : (m % 2 == 1) = true := by simpa using hodd
  have hround (guard sticky : Bool)
      (hbracket : InbetweenInt (m : ℤ) w (location guard sticky)) :
      roundAt fmt (w * Flocq.bpow binaryRadix fmt.minSubnormalExponent) mode =
        if (mode.magnitudeRounding false).increment true guard sticky = true
        then ((m : ℝ) + 1) * Flocq.bpow binaryRadix fmt.minSubnormalExponent
        else (m : ℝ) * Flocq.bpow binaryRadix fmt.minSubnormalExponent := by
    have hlocated : Located fmt (w * Flocq.bpow binaryRadix fmt.minSubnormalExponent) m
        fmt.minSubnormalExponent guard sticky :=
      ⟨hcexp, by rw [hscaled]; exact hbracket⟩
    rw [hlocated.roundAt_eq mode, hparity]
    split_ifs <;> push_cast <;> ring
  have hpredLe : (underflowPredecessor fmt).toReal ≤
      w * Flocq.bpow binaryRadix fmt.minSubnormalExponent ↔ (m : ℝ) + 1 / 2 ≤ w := by
    rw [hpredecessor]
    exact ⟨fun h => le_of_mul_le_mul_right h hpow,
      fun h => mul_le_mul_of_nonneg_right h hpow.le⟩
  have hsubNe : w * Flocq.bpow binaryRadix fmt.minSubnormalExponent ≠
      (m : ℝ) * Flocq.bpow binaryRadix fmt.minSubnormalExponent ↔ w ≠ (m : ℝ) :=
    not_congr ⟨fun h => mul_right_cancel₀ hpow.ne' h, fun h => by rw [h]⟩
  have hpredNe : w * Flocq.bpow binaryRadix fmt.minSubnormalExponent ≠
      (underflowPredecessor fmt).toReal ↔ w ≠ (m : ℝ) + 1 / 2 := by
    rw [hpredecessor]
    exact not_congr ⟨fun h => mul_right_cancel₀ hpow.ne' h, fun h => by rw [h]⟩
  rcases lt_trichotomy w ((m : ℝ) + 1 / 2) with hlt | heq | hgt
  · rcases eq_or_lt_of_le hwlo with hexact | hstrict
    · refine ⟨false, false, ?_, ?_, hround false false (.exact (by simpa using hexact.symm))⟩
      · rw [hpredLe]
        exact iff_of_false (by decide) (not_le.mpr hlt)
      · rw [hsubNe]
        exact iff_of_false (by decide) fun h => h.1 hexact.symm
    · refine ⟨false, true, ?_, ?_, hround false true
        (.inexact .lt ⟨by simpa using hstrict, by push_cast; linarith⟩
          ((cmp_eq_lt_iff _ _).mpr (by push_cast; linarith)))⟩
      · rw [hpredLe]
        exact iff_of_false (by decide) (not_le.mpr hlt)
      · rw [hsubNe, hpredNe]
        exact iff_of_true rfl ⟨hstrict.ne', hlt.ne⟩
  · refine ⟨true, false, ?_, ?_, hround true false
      (.inexact .eq ⟨by push_cast; linarith, by push_cast; linarith⟩
        ((cmp_eq_eq_iff _ _).mpr (by push_cast; linarith)))⟩
    · rw [hpredLe]
      exact iff_of_true rfl heq.ge
    · rw [hpredNe]
      exact iff_of_false (by decide) fun h => h.2 heq
  · refine ⟨true, true, ?_, ?_, hround true true
      (.inexact .gt ⟨by push_cast; linarith, by push_cast; linarith⟩
        ((cmp_eq_gt_iff _ _).mpr (by push_cast; linarith)))⟩
    · rw [hpredLe]
      exact iff_of_true rfl hgt.le
    · rw [hsubNe, hpredNe]
      exact iff_of_true rfl ⟨(show (m : ℝ) < w by linarith).ne', hgt.ne'⟩

/-- The order of the largest subnormal number, the two boundaries and the least normal
magnitude. -/
private theorem bottom_cell_order (fmt : FloatFormat) :
    (minNormalDyadic fmt).toReal - Flocq.bpow binaryRadix fmt.minSubnormalExponent <
        (underflowPredecessor fmt).toReal ∧
      (underflowPredecessor fmt).toReal < (underflowMidpoint fmt).toReal ∧
      (underflowMidpoint fmt).toReal < (minNormalDyadic fmt).toReal := by
  obtain ⟨m, -, hnormal, hpredecessor, hmidpoint, -, -⟩ := bottom_cell_values fmt
  have hpow := Flocq.bpow.pos binaryRadix fmt.minSubnormalExponent
  rw [hnormal, hpredecessor, hmidpoint]
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/--
**Where the rounding of a real number stays below the least normal magnitude.** For every
format descriptor and rounding direction, the rounding of `t` on the grid of the format,
subnormal numbers included, is below the least normal magnitude exactly when `t` is before the
boundary of the rule that the direction applies to a positive value.
-/
theorem roundAt_lt_minNormal_iff (mode : IEEERoundingMode) (t : ℝ) :
    roundAt fmt t mode < (minNormalDyadic fmt).toReal ↔
      RoundsBelowNormal fmt (mode.magnitudeRounding false) t := by
  obtain ⟨hsubPred, hpredMid, hmidNormal⟩ := bottom_cell_order fmt
  have hsubNormal : (minNormalDyadic fmt).toReal -
      Flocq.bpow binaryRadix fmt.minSubnormalExponent < (minNormalDyadic fmt).toReal :=
    hsubPred.trans (hpredMid.trans hmidNormal)
  -- The largest subnormal number and the least normal magnitude are on the grid.
  have hgridSub : GenericRepresentable binaryRadix (fexpOf fmt)
      ((minNormalDyadic fmt).toReal - Flocq.bpow binaryRadix fmt.minSubnormalExponent) := by
    obtain ⟨guard, sticky, -, -, hvalue⟩ :=
      roundAt_bottom_cell (fmt := fmt) .towardZero le_rfl hsubNormal
    have hgrid := genericFormat_roundAt fmt
      ((minNormalDyadic fmt).toReal - Flocq.bpow binaryRadix fmt.minSubnormalExponent)
      .towardZero
    rw [hvalue] at hgrid
    simpa [IEEERoundingMode.magnitudeRounding, MagnitudeRounding.increment] using hgrid
  have hgridNormal : GenericRepresentable binaryRadix (fexpOf fmt)
      (minNormalDyadic fmt).toReal := by
    obtain ⟨guard, sticky, hguard, -, hvalue⟩ :=
      roundAt_bottom_cell (fmt := fmt) .away hsubPred.le (hpredMid.trans hmidNormal)
    have hgrid := genericFormat_roundAt fmt (underflowPredecessor fmt).toReal .away
    rw [hvalue] at hgrid
    simpa [IEEERoundingMode.magnitudeRounding, MagnitudeRounding.increment,
      hguard.mpr le_rfl] using hgrid
  rcases lt_or_ge t ((minNormalDyadic fmt).toReal -
      Flocq.bpow binaryRadix fmt.minSubnormalExponent) with hbelow | hlower
  · -- Below the largest subnormal number the rounding is at most that number.
    have hle : roundAt fmt t mode ≤ (minNormalDyadic fmt).toReal -
        Flocq.bpow binaryRadix fmt.minSubnormalExponent := by
      have h := roundAt_mono fmt hbelow.le mode
      rwa [roundAt_of_genericFormat fmt hgridSub mode] at h
    refine iff_of_true (hle.trans_lt hsubNormal) ?_
    generalize mode.magnitudeRounding false = rule
    cases rule with
    | down => exact hbelow.trans hsubNormal
    | up => exact hbelow.le
    | nearestEven => exact hbelow.trans hsubPred
    | nearestAway => exact hbelow.trans hsubPred
  rcases lt_or_ge t (minNormalDyadic fmt).toReal with hupper | habove
  · -- Between the two the rule decides.
    obtain ⟨guard, sticky, hguard, hsticky, hvalue⟩ := roundAt_bottom_cell mode hlower hupper
    have hsplit : ∀ condition : Prop, [Decidable condition] →
        ((if condition then (minNormalDyadic fmt).toReal
          else (minNormalDyadic fmt).toReal -
            Flocq.bpow binaryRadix fmt.minSubnormalExponent) < (minNormalDyadic fmt).toReal ↔
          ¬condition) := by
      intro condition _
      by_cases h : condition
      · rw [ite_eq_left h]
        exact iff_of_false (lt_irrefl _) (not_not.mpr h)
      · rw [ite_eq_right h]
        exact iff_of_true hsubNormal h
    rw [hvalue, hsplit]
    generalize mode.magnitudeRounding false = rule
    cases rule with
    | down =>
        simp only [MagnitudeRounding.increment]
        exact iff_of_true (by decide) hupper
    | up =>
        simp only [MagnitudeRounding.increment, Bool.or_eq_true, not_or]
        constructor
        · rintro ⟨hg, hs⟩
          have hnotPred : ¬(underflowPredecessor fmt).toReal ≤ t := fun h => hg (hguard.mpr h)
          by_contra hgt
          exact hs (hsticky.mpr ⟨fun h => hgt h.le, fun h => hnotPred h.ge⟩)
        · intro (h : t ≤ (minNormalDyadic fmt).toReal -
            Flocq.bpow binaryRadix fmt.minSubnormalExponent)
          have hequal := le_antisymm h hlower
          exact ⟨fun hg => absurd (hguard.mp hg) (not_le.mpr (hequal ▸ hsubPred)),
            fun hs => (hsticky.mp hs).1 hequal⟩
    | nearestEven =>
        simp only [MagnitudeRounding.increment, Bool.or_true, Bool.and_true]
        exact (not_congr hguard).trans not_le
    | nearestAway =>
        simp only [MagnitudeRounding.increment]
        exact (not_congr hguard).trans not_le
  · -- From the least normal magnitude on the rounding is at least that magnitude.
    have hge : (minNormalDyadic fmt).toReal ≤ roundAt fmt t mode := by
      have h := roundAt_mono fmt habove mode
      rwa [roundAt_of_genericFormat fmt hgridNormal mode] at h
    refine iff_of_false (not_lt.mpr hge) ?_
    generalize mode.magnitudeRounding false = rule
    cases rule with
    | down => exact not_lt.mpr habove
    | up => exact fun h : t ≤ _ => by linarith
    | nearestEven => exact fun h : t < _ => by linarith
    | nearestAway => exact fun h : t < _ => by linarith

/-- The same statement for a magnitude `t > 0` with either sign: the rounding is below the
least normal magnitude exactly when `t` is before the boundary of the rule for that sign. -/
theorem abs_roundAt_lt_minNormal_iff (mode : IEEERoundingMode) (negative : Bool) {t : ℝ}
    (ht : 0 < t) :
    |roundAt fmt (if negative then -t else t) mode| < (minNormalDyadic fmt).toReal ↔
      RoundsBelowNormal fmt (mode.magnitudeRounding negative) t := by
  have hnonneg (mode : IEEERoundingMode) : 0 ≤ roundAt fmt t mode := by
    simpa only [roundAt_zero] using roundAt_mono fmt ht.le mode
  cases negative with
  | false =>
      change |roundAt fmt t mode| < _ ↔ _
      rw [abs_of_nonneg (hnonneg mode)]
      exact roundAt_lt_minNormal_iff mode t
  | true =>
      change |roundAt fmt (-t) mode| < _ ↔ _
      rw [roundAt_neg fmt t mode, abs_neg, abs_of_nonneg (hnonneg mode.negate)]
      have h := roundAt_lt_minNormal_iff (fmt := fmt) mode.negate t
      rwa [IEEERoundingMode.magnitudeRounding_negate, Bool.not_false] at h

/-- A magnitude `t > 0` below the least normal magnitude that is not before the boundary of the
direction rounds to the least normal magnitude. -/
theorem abs_roundAt_eq_minNormal (mode : IEEERoundingMode) (negative : Bool) {t : ℝ}
    (ht : 0 < t) (hboundary : ¬RoundsBelowNormal fmt (mode.magnitudeRounding negative) t)
    (hlt : t < (minNormalDyadic fmt).toReal) :
    |roundAt fmt (if negative then -t else t) mode| = (minNormalDyadic fmt).toReal := by
  refine le_antisymm ?_
    (not_lt.mp fun h => hboundary ((abs_roundAt_lt_minNormal_iff mode negative ht).mp h))
  -- The least normal magnitude is on the grid, so the rounding of a smaller magnitude is at
  -- most it.
  have hgrid : ∀ mode : IEEERoundingMode,
      roundAt fmt t mode ≤ (minNormalDyadic fmt).toReal := by
    intro mode
    by_contra hgt
    obtain ⟨hsubPred, hpredMid, hmidNormal⟩ := bottom_cell_order fmt
    have hsubNormal : (minNormalDyadic fmt).toReal -
        Flocq.bpow binaryRadix fmt.minSubnormalExponent < (minNormalDyadic fmt).toReal :=
      hsubPred.trans (hpredMid.trans hmidNormal)
    by_cases hlower : (minNormalDyadic fmt).toReal -
        Flocq.bpow binaryRadix fmt.minSubnormalExponent ≤ t
    · obtain ⟨guard, sticky, -, -, hvalue⟩ := roundAt_bottom_cell mode hlower hlt
      rw [hvalue] at hgt
      split_ifs at hgt
      · exact hgt le_rfl
      · exact hgt (by linarith)
    · have hbelow := not_le.mp hlower
      have hlimit := roundAt_mono fmt hbelow.le mode
      obtain ⟨guard, sticky, -, -, hvalue⟩ :=
        roundAt_bottom_cell (fmt := fmt) mode le_rfl hsubNormal
      rw [hvalue] at hlimit
      split_ifs at hlimit
      · exact hgt hlimit
      · exact hgt (by linarith)
  have hnonneg (mode : IEEERoundingMode) : 0 ≤ roundAt fmt t mode := by
    simpa only [roundAt_zero] using roundAt_mono fmt ht.le mode
  cases negative with
  | false =>
      change |roundAt fmt t mode| ≤ _
      rw [abs_of_nonneg (hnonneg mode)]
      exact hgrid mode
  | true =>
      change |roundAt fmt (-t) mode| ≤ _
      rw [roundAt_neg fmt t mode, abs_neg, abs_of_nonneg (hnonneg mode.negate)]
      exact hgrid mode.negate

/-- A magnitude that rounds below the least normal magnitude on the grid of the format is tiny
after rounding. -/
theorem TinyAfterRounding.of_roundsBelowNormal {rule : MagnitudeRounding} {t : ℝ}
    (h : RoundsBelowNormal fmt rule t) : TinyAfterRounding fmt rule t := by
  obtain ⟨hsubPred, hpredMid, -⟩ := bottom_cell_order fmt
  cases rule with
  | down => exact h
  | up => exact (show t ≤ _ from h).trans hsubPred.le
  | nearestEven => exact (show t < _ from h).trans hpredMid
  | nearestAway => exact (show t < _ from h).trans hpredMid

/-- A magnitude that is tiny after rounding is below the least normal magnitude. -/
theorem TinyAfterRounding.lt_minNormal {rule : MagnitudeRounding} {t : ℝ}
    (h : TinyAfterRounding fmt rule t) : t < (minNormalDyadic fmt).toReal := by
  obtain ⟨-, hpredMid, hmidNormal⟩ := bottom_cell_order fmt
  cases rule with
  | down => exact h
  | up => exact (show t ≤ _ from h).trans_lt (hpredMid.trans hmidNormal)
  | nearestEven => exact (show t < _ from h).trans hmidNormal
  | nearestAway => exact (show t < _ from h).trans hmidNormal

end AlgebraicRounding

namespace ComparisonRounding

/--
The decision of `outcome` on the tininess of a delivery of the least normal magnitude: the
comparison of the magnitude of the located number, which `magnitude` orders against a rational,
with the boundary of the direction. A direction that truncates the magnitude delivers the least
normal magnitude only from that magnitude on, which is not tiny.
-/
def roundsTiny (fmt : FloatFormat) (mode : IEEERoundingMode) (negative : Bool)
    (magnitude : ℚ → Ordering) : Bool :=
  match mode with
  | .nearest | .nearestAway => magnitude (underflowMidpoint fmt).toRat == .lt
  | .towardZero => false
  | .up | .down | .away =>
      mode.roundsAwayFromZero negative && magnitude (underflowPredecessor fmt).toRat != .gt

/-- For an exact comparator of a magnitude, `roundsTiny` holds exactly when the direction does
not truncate the magnitude and the magnitude is tiny after rounding. -/
theorem roundsTiny_iff {magnitude : ℚ → Ordering} {t : ℝ}
    (hmagnitude : ∀ boundary : ℚ, magnitude boundary = cmp t (boundary : ℝ))
    (mode : IEEERoundingMode) (negative : Bool) :
    roundsTiny fmt mode negative magnitude = true ↔
      mode.magnitudeRounding negative ≠ .down ∧
        AlgebraicRounding.TinyAfterRounding fmt (mode.magnitudeRounding negative) t := by
  have hlt (d : Numerics.Dyadic) : (magnitude d.toRat == .lt) = true ↔ t < d.toReal := by
    rw [hmagnitude, Numerics.Dyadic.cast_toRat]
    rcases lt_trichotomy t d.toReal with h | h | h
    · rw [(cmp_eq_lt_iff _ _).mpr h]
      exact iff_of_true rfl h
    · rw [(cmp_eq_eq_iff _ _).mpr h]
      exact iff_of_false (by decide) (not_lt.mpr h.ge)
    · rw [(cmp_eq_gt_iff _ _).mpr h]
      exact iff_of_false (by decide) (not_lt.mpr h.le)
  have hle (d : Numerics.Dyadic) : (magnitude d.toRat != .gt) = true ↔ t ≤ d.toReal := by
    rw [hmagnitude, Numerics.Dyadic.cast_toRat]
    rcases lt_trichotomy t d.toReal with h | h | h
    · rw [(cmp_eq_lt_iff _ _).mpr h]
      exact iff_of_true rfl h.le
    · rw [(cmp_eq_eq_iff _ _).mpr h]
      exact iff_of_true rfl h.le
    · rw [(cmp_eq_gt_iff _ _).mpr h]
      exact iff_of_false (by decide) (not_le.mpr h)
  cases mode <;> cases negative <;>
    first
    | exact (hlt _).trans ⟨fun h => ⟨by decide, h⟩, fun h => h.2⟩
    | exact (hle _).trans ⟨fun h => ⟨by decide, h⟩, fun h => h.2⟩
    | exact iff_of_false (fun h => Bool.false_ne_true h) (fun h => h.1 rfl)

/-- The underflow flag of a finite delivery is `inexact` and the tininess that `outcome` reads
off the encoding: a zero or a subnormal number, or the least normal magnitude with the decision
`roundsTiny`. -/
private theorem outcome_underflow_eq {value : Model fmt} {delivered : ℚ}
    (hdelivered : toRat? value = some delivered) (compare : ℚ → Ordering)
    (mode : IEEERoundingMode) (known : Option Ordering) :
    (outcome fmt compare value mode known).status.underflow =
      ((isTinyAfterRounding value ||
          ((expField value == 1 && fracField value == 0) &&
            roundsTiny fmt mode (signBit value) fun boundary =>
              if signBit value = true then (compare (-boundary)).swap else compare boundary)) &&
        (outcome fmt compare value mode known).status.inexact) := by
  unfold outcome
  simp only [hdelivered]
  rfl

/-- The least normal magnitude is the leading one of the significand in the lowest binade. -/
private theorem toReal_minNormalDyadic (fmt : FloatFormat) :
    (minNormalDyadic fmt).toReal =
      (2 : ℝ) ^ fmt.fracWidth * (2 : ℝ) ^ fmt.minSubnormalExponent := by
  simp only [minNormalDyadic, Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand,
    Bool.false_eq_true, ite_false, one_mul, pow2_eq_two_pow, Nat.cast_pow, Nat.cast_ofNat]

/-- The least normal magnitude is at most the largest finite value. -/
private theorem toReal_minNormalDyadic_le_posMaxFinite (fmt : FloatFormat) :
    (minNormalDyadic fmt).toReal ≤ toReal (posMaxFinite fmt) := by
  have hsplit : fmt.minNormalExponent = (fmt.fracWidth : Int) + fmt.minSubnormalExponent := by
    simp only [FloatFormat.minSubnormalExponent, Int.ofNat_eq_natCast]
    ring
  have h := bpow_minNormal_le_posMaxFinite fmt
  rw [hsplit] at h
  rw [toReal_minNormalDyadic, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  exact h

/-- The magnitude of a finite value from its fields: the fraction field in the lowest binade,
and the significand with its leading one, scaled by the binade, above it. -/
private theorem abs_toReal_of_fields {value : Model fmt} (hfinite : isFinite value = true) :
    |toReal value| =
      (if expField value = 0 then (fracField value : ℝ)
        else (2 : ℝ) ^ fmt.fracWidth + (fracField value : ℝ)) *
        ((2 : ℝ) ^ (expField value - 1) * (2 : ℝ) ^ fmt.minSubnormalExponent) := by
  obtain ⟨d, hd, -, hsignificand, hexponent⟩ := KernelPath.toDyadic?_of_isFinite value hfinite
  have hreal : toReal value = d.toReal := by simp [toReal_eq, hd]
  have hcast : (d.significand : ℝ) = if expField value = 0 then (fracField value : ℝ)
      else (2 : ℝ) ^ fmt.fracWidth + (fracField value : ℝ) := by
    rw [hsignificand]
    split_ifs <;> push_cast <;> rfl
  rw [hreal, ← hcast]
  by_cases hzero : d.significand = 0
  · rw [(Dyadic.toReal_eq_zero_iff d).mpr hzero, hzero]
    simp
  · have hpow : (0 : ℝ) <
        (2 : ℝ) ^ (expField value - 1) * (2 : ℝ) ^ fmt.minSubnormalExponent :=
      mul_pos (pow_pos (by norm_num) _) (zpow_pos (by norm_num) _)
    rw [Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand, hexponent hzero,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, abs_mul, abs_of_pos hpow]
    congr 1
    cases d.negative <;> simp

/-- A finite value is a zero or a subnormal number exactly when its magnitude is below the
least normal magnitude. -/
private theorem isTinyAfterRounding_iff_abs_lt {value : Model fmt}
    (hfinite : isFinite value = true) :
    isTinyAfterRounding value = true ↔ |toReal value| < (minNormalDyadic fmt).toReal := by
  have hfraction : (fracField value : ℝ) < (2 : ℝ) ^ fmt.fracWidth := by
    exact_mod_cast fracField_lt_pow2 value
  have hstep := zpow_pos (by norm_num : (0 : ℝ) < 2) fmt.minSubnormalExponent
  have hfields : isTinyAfterRounding value = true ↔ expField value = 0 := by
    simp [isTinyAfterRounding, hfinite]
  rw [hfields, abs_toReal_of_fields hfinite, toReal_minNormalDyadic]
  by_cases hexponent : expField value = 0
  · refine iff_of_true hexponent ?_
    rw [ite_eq_left hexponent, hexponent]
    simp only [Nat.zero_sub, pow_zero, one_mul]
    exact mul_lt_mul_of_pos_right hfraction hstep
  · refine iff_of_false hexponent (not_lt.mpr ?_)
    rw [ite_eq_right hexponent]
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (expField value - 1) := one_le_pow₀ (by norm_num)
    have hleading : (0 : ℝ) < (2 : ℝ) ^ fmt.fracWidth := pow_pos (by norm_num) _
    have hfirst : 0 ≤ (2 : ℝ) ^ fmt.fracWidth *
        (((2 : ℝ) ^ (expField value - 1) - 1) * (2 : ℝ) ^ fmt.minSubnormalExponent) :=
      mul_nonneg hleading.le (mul_nonneg (sub_nonneg.mpr hone) hstep.le)
    have hsecond : 0 ≤ (fracField value : ℝ) *
        ((2 : ℝ) ^ (expField value - 1) * (2 : ℝ) ^ fmt.minSubnormalExponent) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (zero_le_one.trans hone) hstep.le)
    linarith [hfirst, hsecond]

/-- A finite value has the fields of the least normal magnitude exactly when it has that
magnitude. -/
private theorem leastNormal_iff_abs_eq {value : Model fmt} (hfinite : isFinite value = true) :
    (expField value == 1 && fracField value == 0) = true ↔
      |toReal value| = (minNormalDyadic fmt).toReal := by
  have hfraction : (fracField value : ℝ) < (2 : ℝ) ^ fmt.fracWidth := by
    exact_mod_cast fracField_lt_pow2 value
  have hstep := zpow_pos (by norm_num : (0 : ℝ) < 2) fmt.minSubnormalExponent
  have hleading : (0 : ℝ) < (2 : ℝ) ^ fmt.fracWidth := pow_pos (by norm_num) _
  rw [abs_toReal_of_fields hfinite, toReal_minNormalDyadic, Bool.and_eq_true, beq_iff_eq,
    beq_iff_eq]
  constructor
  · rintro ⟨hexponent, hzero⟩
    rw [hexponent, hzero]
    simp
  · intro hmagnitude
    by_cases hexponent : expField value = 0
    · rw [ite_eq_left hexponent, hexponent] at hmagnitude
      simp only [Nat.zero_sub, pow_zero, one_mul] at hmagnitude
      exact absurd hmagnitude (mul_lt_mul_of_pos_right hfraction hstep).ne
    · rw [ite_eq_right hexponent, ← mul_assoc] at hmagnitude
      have hcancel := mul_right_cancel₀ hstep.ne' hmagnitude
      have hnonneg : (0 : ℝ) ≤ (fracField value : ℝ) := Nat.cast_nonneg _
      by_cases hone : expField value = 1
      · refine ⟨hone, ?_⟩
        rw [hone] at hcancel
        simp only [Nat.sub_self, pow_zero, mul_one] at hcancel
        have hfield : (fracField value : ℝ) = 0 := by linarith
        exact_mod_cast hfield
      · exfalso
        have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ (expField value - 1) := by
          have hle : 1 ≤ expField value - 1 := by omega
          calc (2 : ℝ) = 2 ^ 1 := (pow_one _).symm
            _ ≤ 2 ^ (expField value - 1) := pow_le_pow_right₀ (by norm_num) hle
        linarith [mul_nonneg hnonneg (zero_le_two.trans htwo),
          mul_le_mul_of_nonneg_left htwo hleading.le, hcancel, hleading]

/--
**The underflow flag is the underflow of the standard.** For every format descriptor and
rounding direction, a comparator of the nonzero real number `target` and a value that is the
rounding of `target` (`RoundsTo`), the outcome raises `underflow` exactly when it raises
`inexact` and the magnitude of `target` is tiny after rounding in the direction: its rounding
to the precision of the format with an unbounded exponent range is below the least normal
magnitude (IEEE 754-2019 §7.5 with tininess detected after rounding).
-/
theorem outcome_underflow_iff {compare : ℚ → Ordering} {target : ℝ}
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (hne : target ≠ 0) {value : Model fmt} {mode : IEEERoundingMode} {known : Option Ordering}
    (hvalue : RoundsTo fmt mode target (decide (target < 0)) value) :
    (outcome fmt compare value mode known).status.underflow = true ↔
      (outcome fmt compare value mode known).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide (target < 0))) |target| := by
  have htarget : (if decide (target < 0) = true then -|target| else |target|) = target := by
    by_cases h : target < 0
    · rw [ite_eq_left (decide_eq_true h), abs_of_neg h, _root_.neg_neg]
    · rw [ite_eq_right (by simpa using h), abs_of_nonneg (not_lt.mp h)]
  have hpositive : 0 < |target| := abs_pos.mpr hne
  have hleast : 0 < (minNormalDyadic fmt).toReal := by
    rw [toReal_minNormalDyadic]
    positivity
  have hminimum := toReal_minNormalDyadic_le_posMaxFinite fmt
  have hbelow := AlgebraicRounding.abs_roundAt_lt_minNormal_iff (fmt := fmt) mode
    (decide (target < 0)) hpositive
  rw [htarget] at hbelow
  have hnormal : ¬AlgebraicRounding.RoundsBelowNormal fmt
      (mode.magnitudeRounding (decide (target < 0))) |target| →
      |target| < (minNormalDyadic fmt).toReal →
      |roundAt fmt target mode| = (minNormalDyadic fmt).toReal := by
    intro hboundary hlt
    have h := AlgebraicRounding.abs_roundAt_eq_minNormal (fmt := fmt) mode
      (decide (target < 0)) hpositive hboundary hlt
    rwa [htarget] at h
  -- A magnitude that is tiny after rounding rounds to at most the least normal magnitude.
  have hnotTiny : toReal (posMaxFinite fmt) < |roundAt fmt target mode| →
      ¬AlgebraicRounding.TinyAfterRounding fmt
        (mode.magnitudeRounding (decide (target < 0))) |target| := by
    intro hbeyond htiny
    by_cases hboundary : AlgebraicRounding.RoundsBelowNormal fmt
        (mode.magnitudeRounding (decide (target < 0))) |target|
    · linarith [hbelow.mpr hboundary]
    · linarith [hnormal hboundary htiny.lt_minNormal]
  have hdecision (h : signBit value = decide (target < 0)) :
      roundsTiny fmt mode (signBit value) (fun boundary =>
        if signBit value = true then (compare (-boundary)).swap else compare boundary) = true ↔
      mode.magnitudeRounding (decide (target < 0)) ≠ .down ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide (target < 0))) |target| := by
    rw [h]
    exact roundsTiny_iff (magnitude_abs hcompare) mode _
  cases hdelivered : toRat? value with
  | none =>
      have hbeyond : toReal (posMaxFinite fmt) < |roundAt fmt target mode| := by
        by_contra hrange
        obtain ⟨q, hq, -⟩ :=
          Algebraic.exists_toRat?_of_isFinite (hvalue.finite (not_lt.mp hrange)).1
        rw [hdelivered] at hq
        exact absurd hq (by simp)
      refine iff_of_false ?_ (fun h => hnotTiny hbeyond h.2)
      have hunderflow : (outcome fmt compare value mode known).status.underflow = false := by
        unfold outcome
        split
        · next q hq =>
            rw [hdelivered] at hq
            exact absurd hq (by simp)
        · rfl
      rw [hunderflow]
      exact Bool.false_ne_true
  | some delivered =>
      have hfinite := Algebraic.isFinite_of_toRat?_eq_some hdelivered
      rw [outcome_underflow_eq hdelivered, Bool.and_eq_true]
      refine and_comm.trans (and_congr_right fun _ => ?_)
      rw [Bool.or_eq_true, Bool.and_eq_true, isTinyAfterRounding_iff_abs_lt hfinite,
        leastNormal_iff_abs_eq hfinite]
      by_cases hrange : |roundAt fmt target mode| ≤ toReal (posMaxFinite fmt)
      · -- In range: the delivery is the rounding on the grid of the format.
        have hreal := (hvalue.finite hrange).2
        have hsign (heq : |roundAt fmt target mode| = (minNormalDyadic fmt).toReal) :
            signBit value = decide (target < 0) := by
          refine hvalue.signBit_of_toReal_ne_zero hne hfinite fun hzero => ?_
          rw [← hreal, hzero, abs_zero] at heq
          exact hleast.ne heq
        rw [hreal]
        constructor
        · rintro (hlt | ⟨heq, hrounds⟩)
          · exact .of_roundsBelowNormal (hbelow.mp hlt)
          · exact ((hdecision (hsign heq)).mp hrounds).2
        · intro htiny
          by_cases hboundary : AlgebraicRounding.RoundsBelowNormal fmt
              (mode.magnitudeRounding (decide (target < 0))) |target|
          · exact .inl (hbelow.mpr hboundary)
          · have heq := hnormal hboundary htiny.lt_minNormal
            refine .inr ⟨heq, (hdecision (hsign heq)).mpr ⟨fun hdown => ?_, htiny⟩⟩
            rw [hdown] at hboundary htiny
            exact hboundary htiny
      · -- Out of range: the delivery is the largest finite value of the sign, which is not tiny.
        have hbeyond := not_le.mp hrange
        refine iff_of_false ?_ (hnotTiny hbeyond)
        have hmaximum := hvalue.eq_maxFinite hbeyond hfinite
        have hmagnitude : |toReal value| = toReal (posMaxFinite fmt) := by
          rw [hmaximum, toReal_maxFinite]
          have hlargest := toReal_posMaxFinite_pos fmt
          cases decide (target < 0) <;> simp [abs_of_pos hlargest]
        rw [hmagnitude]
        rintro (hlt | ⟨-, hrounds⟩)
        · exact absurd hminimum (not_le.mpr hlt)
        · have hsign : signBit value = decide (target < 0) := by
            rw [hmaximum]
            simp [maxFinite]
          exact hnotTiny hbeyond ((hdecision hsign).mp hrounds).2

/--
**A delivery raises `underflow` exactly when the standard asks for it.** For every format
descriptor, a comparator of the nonzero real number `target` and a hint that is right about
`target` and has its sign, `deliver` raises `underflow` in the direction `mode` exactly when it
raises `inexact` and the magnitude of `target` is tiny after rounding in the direction.
-/
theorem deliver_underflow_iff {compare : ℚ → Ordering} {target : ℝ}
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (hne : target ≠ 0) (mode : IEEERoundingMode) {hint : Unit → Option (Hint fmt)}
    (hsound : Hint.Sound hint target) (hsigned : Hint.Signed hint target) :
    (deliver fmt compare mode hint).status.underflow = true ↔
      (deliver fmt compare mode hint).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide (target < 0))) |target| :=
  outcome_underflow_iff hcompare hne (resolve_roundsTo compare hne hcompare hsound hsigned)

/-- A rule that locates the nonzero real number `target` raises `underflow` exactly when it
raises `inexact` and the magnitude of `target` is tiny after rounding in the direction. -/
theorem Rule.deliver_underflow_iff {rule : Rule} {target : ℝ} (hrule : rule.Locates target)
    (hne : target ≠ 0) (mode : IEEERoundingMode) {hint : Unit → Option (Hint fmt)}
    (hsound : Hint.Sound hint target) (hsigned : Hint.Signed hint target) :
    (rule.deliver fmt mode hint).status.underflow = true ↔
      (rule.deliver fmt mode hint).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide (target < 0))) |target| := by
  cases rule with
  | zero negative => exact absurd hrule hne
  | real compare => exact ComparisonRounding.deliver_underflow_iff hrule hne mode hsound hsigned
  | infinity negative => exact absurd hrule id
  | pole negative => exact absurd hrule id
  | invalid => exact absurd hrule id

/--
**The underflow flag of a function of one operand.** For every format descriptor, a finite
operand whose rule locates the nonzero real number `target` and a hint that is right about
`target` and has its sign at that operand, the result in the direction `mode` raises
`underflow` exactly when it raises `inexact` and the magnitude of `target` is tiny after
rounding in the direction.
-/
theorem unary_underflow_iff (rule : Operand → Rule) {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) {target : ℝ}
    (hrule : (rule (.finite (signBit x) q)).Locates target) (hne : target ≠ 0)
    (mode : IEEERoundingMode) {hint : Operand → Unit → Option (Hint fmt)}
    (hsound : Hint.Sound (hint (.finite (signBit x) q)) target)
    (hsigned : Hint.Signed (hint (.finite (signBit x) q)) target) :
    (unary rule x mode hint).status.underflow = true ↔
      (unary rule x mode hint).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide (target < 0))) |target| := by
  rw [unary_of_toRat? rule hq]
  exact Rule.deliver_underflow_iff hrule hne mode hsound hsigned

/--
**The underflow flag of a function of two operands.** For every format descriptor, finite
operands whose rule locates the nonzero real number `target` and a hint that is right about
`target` and has its sign at those operands, the result in the direction `mode` raises
`underflow` exactly when it raises `inexact` and the magnitude of `target` is tiny after
rounding in the direction.
-/
theorem binary_underflow_iff (rule : Operand → Operand → Rule) {x y : Model fmt} {p q : ℚ}
    (hp : toRat? x = some p) (hq : toRat? y = some q) {target : ℝ}
    (hrule : (rule (.finite (signBit x) p) (.finite (signBit y) q)).Locates target)
    (hne : target ≠ 0) (mode : IEEERoundingMode)
    {hint : Operand → Operand → Unit → Option (Hint fmt)}
    (hsound : Hint.Sound (hint (.finite (signBit x) p) (.finite (signBit y) q)) target)
    (hsigned : Hint.Signed (hint (.finite (signBit x) p) (.finite (signBit y) q)) target) :
    (binary rule x y mode hint).status.underflow = true ↔
      (binary rule x y mode hint).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding fmt
          (mode.magnitudeRounding (decide (target < 0))) |target| := by
  rw [binary_of_toRat? rule hp hq]
  exact Rule.deliver_underflow_iff hrule hne mode hsound hsigned

end ComparisonRounding

end FloatLib.Floats.Formats.BinaryInterchange.Model
