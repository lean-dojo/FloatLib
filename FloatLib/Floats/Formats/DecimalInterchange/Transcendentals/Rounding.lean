/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Semantics
public import FloatLib.Floats.Formats.Flocq.Theory.Format.Formats
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Affine
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Order

/-!
# Decimal projection and real nearest-even rounding

The decimal digit-counting algorithm selects the canonical exponent of the radix-ten Flocq
format. Its exact quotient decision also agrees with the real nearest-even integer rounder.
Consequently every finite nearest-even decimal projection equals rounding on the independent
real grid, including subnormals and ties.

The real grid has gradual underflow and no upper exponent bound. Finiteness of the executable
projection is an explicit hypothesis; infinities cannot denote its real result. The proofs use
only the descriptor's positive precision and quantum bounds, without requiring quantum zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Transcendentals

open FloatLib.Numerics

/-- Decimal precision and gradual underflow, with an unbounded upper exponent. -/
def fexpOf (f : Format) : ℤ → ℤ :=
  Flocq.fltExp f.minQuantum f.precision

instance (f : Format) : Flocq.ValidExp (fexpOf f) :=
  Flocq.fltValidExp f.minQuantum f.precision (by exact_mod_cast f.precision_pos)

/-- Nearest-even real rounding at the descriptor's decimal precision and least quantum. -/
noncomputable abbrev roundAt (f : Format) (x : ℝ) : ℝ :=
  Flocq.round (β := decimalRadix) (fexp := fexpOf f) Flocq.nearestEven x

/-- The real decimal rounding specification fixes zero. -/
theorem roundAt_zero (f : Format) : roundAt f 0 = 0 :=
  Flocq.round_preserves_generic Flocq.nearestEven 0 Flocq.generic_format_zero

/-- Decimal nearest-even rounding is monotone across canonical-exponent boundaries. -/
theorem roundAt_mono (f : Format) {x y : ℝ} (hxy : x ≤ y) :
    roundAt f x ≤ roundAt f y :=
  Flocq.round_mono Flocq.nearestEven hxy

/-- The exact decimal digit count selects the Flocq canonical exponent away from zero. -/
theorem cexp_eq_roundingQuantum (f : Format) {x : ℚ} (hx : x ≠ 0) :
    Flocq.cexp decimalRadix (fexpOf f) (x : ℝ) = roundingQuantum f |x| := by
  have hxreal : (x : ℝ) ≠ 0 := by exact_mod_cast hx
  have hmin := roundingQuantum_ge_min f |x|
  have hu : 0 < (10 : ℚ) ^ roundingQuantum f |x| := zpow_pos (by norm_num) _
  have hupper := (div_lt_iff₀ hu).mp (div_roundingQuantum_lt f (abs_nonneg x))
  rw [Format.coefficientBound_eq, Nat.cast_pow, Nat.cast_ofNat] at hupper
  have hupper' : |(x : ℝ)| <
      Flocq.bpow decimalRadix (roundingQuantum f |x| + (f.precision : ℤ)) := by
    simp only [Flocq.bpow, Radix.toReal, decimalRadix, Nat.cast_ofNat,
      zpow_add₀ (by norm_num : (10 : ℝ) ≠ 0), zpow_natCast]
    have hcast := (Rat.cast_lt (K := ℝ)).mpr hupper
    simpa only [Rat.cast_abs, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_zpow,
      mul_comm] using hcast
  have hmag := Flocq.magnitude_le_of_abs_lt_bpow decimalRadix
    (x : ℝ) _ hxreal hupper'
  apply le_antisymm
  · change max (Flocq.magnitude decimalRadix (x : ℝ) - f.precision)
        f.minQuantum ≤ roundingQuantum f |x|
    exact max_le (by omega) hmin
  · by_cases hq : roundingQuantum f |x| = f.minQuantum
    · change roundingQuantum f |x| ≤
        max (Flocq.magnitude decimalRadix (x : ℝ) - f.precision) f.minQuantum
      rw [hq]
      exact le_max_right _ _
    · have hstrict : f.minQuantum < roundingQuantum f |x| :=
        lt_of_le_of_ne hmin (Ne.symm hq)
      have hlower := (le_div_iff₀ hu).mp
        (payloadBound_le_div_roundingQuantum f (abs_nonneg x) hstrict)
      rw [Format.payloadBound_eq, Nat.cast_pow, Nat.cast_ofNat] at hlower
      have hprec : ((f.precision - 1 : ℕ) : ℤ) = (f.precision : ℤ) - 1 := by
        have := f.precision_pos
        omega
      have hlower' :
          Flocq.bpow decimalRadix (roundingQuantum f |x| + f.precision - 1) ≤
            |(x : ℝ)| := by
        have hcast := (Rat.cast_le (K := ℝ)).mpr hlower
        rw [show roundingQuantum f |x| + (f.precision : ℤ) - 1 =
          ((f.precision - 1 : ℕ) : ℤ) + roundingQuantum f |x| by omega]
        simpa only [Flocq.bpow, Radix.toReal, decimalRadix, Nat.cast_ofNat,
          zpow_add₀ (by norm_num : (10 : ℝ) ≠ 0), zpow_natCast, Rat.cast_abs,
          Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_zpow] using hcast
      have hmag' := (Flocq.bpow_lt_bpow_iff decimalRadix _ _).mp
        (hlower'.trans_lt (Flocq.abs_lt_bpow_magnitude decimalRadix (x : ℝ) hxreal))
      change roundingQuantum f |x| ≤
        max (Flocq.magnitude decimalRadix (x : ℝ) - f.precision) f.minQuantum
      exact le_max_of_le_left (by omega)

/-- Decimal nearest-even coefficient rounding uses the shared exact quotient decision. -/
theorem roundMagnitude_eq_roundQuotientEven (s : Bool) (x : ℚ) :
    RoundingMode.nearestEven.roundMagnitude s x =
      roundQuotientEven x.num.toNat x.den := by
  simp only [RoundingMode.roundMagnitude, roundQuotientEven, decide_eq_true_eq,
    beq_iff_eq]
  split_ifs <;> simp_all <;> omega

private theorem roundRatEven_of_nonneg {x : ℚ} (hx : 0 ≤ x) (s : Bool) :
    roundRatEven x = (RoundingMode.nearestEven.roundMagnitude s x : ℤ) := by
  have hn := Rat.num_nonneg.mpr hx
  have habs : x.num.natAbs = x.num.toNat := by omega
  simp [roundRatEven, not_lt.mpr hn, roundMagnitude_eq_roundQuotientEven,
    habs]

private theorem roundRatEven_neg (x : ℚ) : roundRatEven (-x) = -roundRatEven x := by
  by_cases hx : x = 0
  · simp [hx, roundRatEven, roundQuotientEven]
  · have hn : x.num ≠ 0 := by simpa using hx
    simp only [roundRatEven, Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den,
      Int.natAbs_neg, neg_lt_zero]
    split_ifs <;> omega

/-- The real specification agrees with exact rational rounding at the selected quantum. -/
theorem roundAt_ratCast (f : Format) {x : ℚ} (hx : x ≠ 0) :
    roundAt f (x : ℝ) =
      (roundRatEven (x / (10 : ℚ) ^ roundingQuantum f |x|) : ℝ) *
        (10 : ℝ) ^ roundingQuantum f |x| := by
  change (Flocq.nearestEven
      (Flocq.scaledMantissa decimalRadix (fexpOf f) (x : ℝ)) : ℝ) *
      Flocq.bpow decimalRadix (Flocq.cexp decimalRadix (fexpOf f) (x : ℝ)) = _
  rw [Flocq.scaledMantissa_eq_div, cexp_eq_roundingQuantum f hx]
  change (Flocq.nearestEven ((x : ℝ) / (10 : ℝ) ^ roundingQuantum f |x|) : ℝ) *
    (10 : ℝ) ^ roundingQuantum f |x| = _
  have hcast : (x : ℝ) / (10 : ℝ) ^ roundingQuantum f |x| =
      ((x / (10 : ℚ) ^ roundingQuantum f |x| : ℚ) : ℝ) := by push_cast; rfl
  rw [hcast, Flocq.nearestEven_ratCast]

private theorem roundRatEven_signed (s : Bool) {x : ℚ} (hx : 0 ≤ x) :
    roundRatEven (if s then -x else x) =
      if s then -(RoundingMode.nearestEven.roundMagnitude s x : ℤ)
      else (RoundingMode.nearestEven.roundMagnitude s x : ℤ) := by
  cases s
  · exact roundRatEven_of_nonneg hx false
  · simpa only [Bool.true_eq, ite_true, roundRatEven_neg] using
      congrArg Neg.neg (roundRatEven_of_nonneg hx true)

/-- Every finite nearest-even decimal projection equals the independent real rounding. -/
theorem project_nearestEven_eq_roundAt (f : Format) (x : ℚ)
    (preferred : ℤ) (negativeZero : Bool)
    {value : ℚ}
    (hvalue : (project f .nearestEven x preferred negativeZero).value.toRat? = some value) :
    (value : ℝ) = roundAt f (x : ℝ) := by
  let s := if x = 0 then negativeZero else decide (x < 0)
  have hq : (roundedPair f .nearestEven s |x|).2 ≤ f.maxQuantum := by
    by_contra h
    have hgt : f.maxQuantum < (roundedPair f .nearestEven s |x|).2 := lt_of_not_ge h
    change (projectMagnitude f .nearestEven s |x| preferred).value.toRat? = some value
      at hvalue
    rw [projectMagnitude_eq, ite_eq_left hgt] at hvalue
    cases hvalue
  have hv := projectMagnitude_value f .nearestEven s |x| preferred hq
  change (project f .nearestEven x preferred negativeZero).value.toRat? = _ at hv
  have heq := Option.some.inj (hvalue.symm.trans hv)
  by_cases hx : x = 0
  · have hz : RoundingMode.nearestEven.roundMagnitude s (0 : ℚ) = 0 :=
      RoundingMode.roundMagnitude_natCast RoundingMode.nearestEven s 0
    have heq0 : value = 0 := by
      simpa only [hx, abs_zero, RoundingMode.roundAt, zero_div, hz,
        Nat.cast_zero, mul_zero, zero_mul] using heq
    rw [heq0, hx, Rat.cast_zero, roundAt_zero]
  · rw [roundAt_ratCast f hx, heq]
    have hstep : 0 < (10 : ℚ) ^ roundingQuantum f |x| := zpow_pos (by norm_num) _
    have harg : x / (10 : ℚ) ^ roundingQuantum f |x| =
        if s then -(|x| / (10 : ℚ) ^ roundingQuantum f |x|)
        else |x| / (10 : ℚ) ^ roundingQuantum f |x| := by
      calc
        x / (10 : ℚ) ^ roundingQuantum f |x| =
            (if s then -|x| else |x|) / (10 : ℚ) ^ roundingQuantum f |x| :=
          congrArg (fun y : ℚ => y / (10 : ℚ) ^ roundingQuantum f |x|)
            (signed_abs x negativeZero).symm
        _ = _ := by cases s <;> simp [neg_div]
    rw [harg, roundRatEven_signed s (div_nonneg (abs_nonneg x) hstep.le)]
    cases s <;> simp [RoundingMode.roundAt, Rat.cast_zpow]

/-- Real interpretation of a decimal datum; nonfinite datums use the conventional zero fallback. -/
noncomputable def toReal (datum : Datum) : ℝ :=
  (datum.toRat?.getD 0 : ℚ)

/-- Exact finite decoding commutes with the rational-to-real embedding. -/
theorem toReal_of_toRat?_eq_some {datum : Datum} {value : ℚ}
    (hvalue : datum.toRat? = some value) : toReal datum = (value : ℝ) := by
  simp [toReal, hvalue]

/-- Nearest-even real rounding has at most half a decimal ULP of absolute error. -/
theorem roundAt_error_le_half_ulp (f : Format) (x : ℝ) :
    |roundAt f x - x| ≤ Flocq.ulp decimalRadix (fexpOf f) x / 2 :=
  Flocq.error_bound_ulp Flocq.nearestEven x

/-- The real specification selects a nearest value on the decimal gradual-underflow grid. -/
theorem roundAt_nearest (f : Format) (x : ℝ) :
    Flocq.RoundNearestPoint (Flocq.genericFormat decimalRadix (fexpOf f)) x
      (roundAt f x) :=
  Flocq.round_nearestEven_point x

end FloatLib.Floats.Formats.DecimalInterchange.Transcendentals
