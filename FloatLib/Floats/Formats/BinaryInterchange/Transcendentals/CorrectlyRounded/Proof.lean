/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.PowerProof
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Certified.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.CorrectlyRounded.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Pi.Proof

/-!
# Correct rounding of the total binary exponential and logarithm

Take an IEEE descriptor and a finite input in the function's domain. Then
`CorrectlyRounded.exp`, `log`, `expMinus1`, `logPlus1` and `expMul` return a finite value if and
only if the real result (in absolute value for `log`, `logPlus1` and `expMul`) lies below
`Certified.overflowThreshold`, and every finite value they return is the nearest-even rounding of
the real result. Nothing is assumed about the search budget or the distance from a rounding
boundary. A search result is correctly rounded by its enclosure, and otherwise the exact
comparators order the real result against every candidate
(`AlgebraicRounding.toReal_round_eq_roundAt`). The threshold itself rounds to the first power of
two past the finite range (`roundAt_overflowThreshold`), so no finite value is the rounding of a
real at or beyond it.

At or beyond the threshold the result is the infinity with the sign of the real result. A finite
logarithm or `logPlus1` of a finite input comes from an input in the domain. So on a finite input
in the domain every finite result is correctly rounded, and every other result is that infinity.

From there the standard model bounds each error by `unitRoundoffAt fmt` times the magnitude of
the exact result plus `underflowErrorAt fmt`. Rounding keeps the sign of an exact result beyond
`underflowErrorAt fmt`, and a nonzero finite input is at least twice that in magnitude, so
`expMinus1` of a negative input is negative and `logPlus1` of a positive input is positive.
Whenever the certified search of `exp`, `expMinus1`, `log`, or `logPlus1` returns a result, the
total function returns the same encoding.

## Main results

* `toReal_exp_eq_roundAt`, `toReal_log_eq_roundAt`, `toReal_expMinus1_eq_roundAt`,
  `toReal_logPlus1_eq_roundAt`, `toReal_expMul_eq_roundAt`: correct rounding when the exact result
  is below the overflow threshold, and `toReal_exp_of_isFinite` and its siblings for every finite
  result.
* `isFinite_exp_iff` and its siblings: the result is finite if and only if the exact result is
  below the overflow threshold.
* `exp_eq_nativeOverflow` and its siblings: when the exact result reaches the threshold, the
  result is a signed infinity.
* `toReal_pos_of_isFinite_log`, `neg_one_lt_toReal_of_isFinite_logPlus1`: a finite result comes
  from an input in the domain.
* `abs_toReal_exp_sub_le` and its siblings: the mixed relative and absolute error bound.
* `toReal_exp_nonneg`, `toReal_expMinus1_lt_zero`, `toReal_logPlus1_pos`, `toReal_expMul_nonneg`
  and their siblings: signs of the results.
* `exp_eq_of_certified_exp_eq_ok` and its siblings: agreement with the certified search.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.CorrectlyRounded

open FloatLib.Numerics

/-! ## Exact comparisons -/

private theorem cmp_eq_cmp {x y x' y' : ℝ} (hlt : x < y ↔ x' < y') (hgt : y < x ↔ y' < x') :
    cmp x y = cmp x' y' := by
  simp only [cmp, cmpUsing, hlt, hgt]

/-- `compareAbsExpMinus1` orders `|exp argument - 1|` against every rational boundary. -/
theorem compareAbsExpMinus1_eq_real (argument boundary : ℚ) :
    compareAbsExpMinus1 argument boundary =
      cmp |Real.exp (argument : ℝ) - 1| (boundary : ℝ) := by
  unfold compareAbsExpMinus1
  split
  · rename_i hnegative
    have hexp : Real.exp (argument : ℝ) < 1 :=
      Real.exp_lt_one_iff.mpr (by exact_mod_cast hnegative)
    rw [ElementaryComparison.compareExp_eq_real, cmp_swap, abs_of_neg (by linarith), neg_sub]
    push_cast
    exact cmp_eq_cmp sub_lt_comm lt_sub_comm
  · rename_i hnonnegative
    have hexp : 1 ≤ Real.exp (argument : ℝ) :=
      Real.one_le_exp (by exact_mod_cast le_of_not_gt hnonnegative)
    rw [ElementaryComparison.compareExp_eq_real, abs_of_nonneg (by linarith)]
    push_cast
    exact cmp_eq_cmp sub_lt_iff_lt_add.symm lt_sub_iff_add_lt.symm

private theorem log_max_inv {x : ℝ} (hx : 0 < x) : Real.log (max x x⁻¹) = |Real.log x| := by
  rcases le_total 1 x with hone | hone
  · rw [max_eq_left ((inv_le_one_of_one_le₀ hone).trans hone),
      abs_of_nonneg (Real.log_nonneg hone)]
  · rw [max_eq_right (hone.trans (one_le_inv₀ hx |>.mpr hone)), Real.log_inv,
      abs_of_nonpos (Real.log_nonpos hx.le hone)]

/-- `compareAbsLog` orders `|log argument|` against every rational boundary. -/
theorem compareAbsLog_eq_real (argument : ℚ) (hpositive : 0 < argument) (boundary : ℚ) :
    compareAbsLog argument hpositive boundary =
      cmp |Real.log (argument : ℝ)| (boundary : ℝ) := by
  rw [compareAbsLog, ElementaryComparison.compareLog_eq_real]
  push_cast
  rw [log_max_inv (by exact_mod_cast hpositive)]

/-- `compareExpMul` orders `exp argument * weight` against every boundary, for `weight > 0`. -/
theorem compareExpMul_eq_real (argument weight : ℚ) (hweight : 0 < weight) (boundary : ℚ) :
    compareExpMul argument weight boundary =
      cmp (Real.exp (argument : ℝ) * weight) (boundary : ℝ) := by
  have hreal : (0 : ℝ) < weight := by exact_mod_cast hweight
  rw [compareExpMul, ElementaryComparison.compareExp_eq_real]
  push_cast
  exact cmp_eq_cmp (lt_div_iff₀ hreal) (div_lt_iff₀ hreal)

/-! ## The overflow threshold -/

/-- The overflow threshold is `2 ^ (emax + 1) - 2 ^ (emax - fracWidth - 1)`. -/
theorem cast_overflowThreshold (fmt : FloatFormat) :
    (Certified.overflowThreshold fmt : ℝ) =
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (fmt.maxNormalExponent + 1) -
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (fmt.maxNormalExponent - fmt.fracWidth - 1) := by
  have hsplit : (2 : ℝ) ^ (fmt.maxNormalExponent + 1) =
      2 ^ (fmt.fracWidth + 2) * 2 ^ (fmt.maxNormalExponent - fmt.fracWidth - 1) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 1
    push_cast
    ring
  rw [Flocq.bpow_binaryRadix, Flocq.bpow_binaryRadix, hsplit, Certified.overflowThreshold,
    Dyadic.cast_toRat, Dyadic.toReal_mk_false, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]
  push_cast
  ring

/-- Every IEEE descriptor's overflow threshold exceeds one. -/
theorem one_lt_overflowThreshold {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) :
    (1 : ℝ) < Certified.overflowThreshold fmt := by
  have h := pi_lt_overflowThreshold fmt hfmt
  rw [← cast_overflowThreshold] at h
  linarith [Real.pi_gt_three]

/-- Nearest-even rounding sends the overflow threshold to the first power of two past the range. -/
theorem roundAt_overflowThreshold {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) :
    roundAt fmt (Certified.overflowThreshold fmt) =
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (fmt.maxNormalExponent + 1) := by
  obtain ⟨-, hbias⟩ := (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt
  have hmax := FloatFormat.maxNormalExponent_eq_ieee fmt hfmt
  simp only [FloatFormat.ieeeMaxNormalExponent, Int.ofNat_eq_natCast] at hmax
  have hbiasPos := FloatFormat.bias_pos fmt
  have hfrac := fmt.fracWidth_pos
  set E := fmt.maxNormalExponent
  set f := fmt.fracWidth
  have hthreshold := cast_overflowThreshold fmt
  rw [Flocq.bpow_binaryRadix, Flocq.bpow_binaryRadix] at hthreshold
  set T := (Certified.overflowThreshold fmt : ℝ)
  have hsmall : (2 : ℝ) ^ (E - f - 1) < 2 ^ E := zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have hpos : (0 : ℝ) < 2 ^ (E - f - 1) := zpow_pos (by norm_num) _
  have hsplit : (2 : ℝ) ^ (E + 1) = 2 * 2 ^ E := by rw [zpow_add_one₀ (by norm_num)]; ring
  have hT : 0 < T := by linarith
  have hmagnitude : FloatLib.Floats.Formats.Flocq.magnitude Numerics.binaryRadix T = E + 1 := by
    apply FloatLib.Floats.Formats.Flocq.magnitude_eq_of_bpow_bounds
    · rw [abs_of_pos hT, Flocq.bpow_binaryRadix, show E + 1 - 1 = E by ring]
      linarith
    · rw [abs_of_pos hT, Flocq.bpow_binaryRadix]
      linarith
  have hcexp : FloatLib.Floats.Formats.Flocq.cexp Numerics.binaryRadix (fexpOf fmt) T = E - f := by
    rw [FloatLib.Floats.Formats.Flocq.cexp, hmagnitude, fexpOf,
      FloatLib.Floats.Formats.Flocq.fltExp]
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast, hbias]
    omega
  have hscaled : FloatLib.Floats.Formats.Flocq.scaledMantissa Numerics.binaryRadix (fexpOf fmt) T =
      ((2 ^ (f + 1) : ℤ) : ℝ) - 1 / 2 := by
    rw [FloatLib.Floats.Formats.Flocq.scaledMantissa, hcexp, Flocq.bpow_binaryRadix, hthreshold,
      sub_mul, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
    push_cast
    rw [show E + 1 + -(E - f) = ((f + 1 : ℕ) : ℤ) by push_cast; ring,
      show E - f - 1 + -(E - f) = -1 by ring, zpow_natCast]
    norm_num
  have hfloor : ⌊((2 ^ (f + 1) : ℤ) : ℝ) - 1 / 2⌋ = 2 ^ (f + 1) - 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  have hodd : ¬Even ((2 : ℤ) ^ (f + 1) - 1) := by
    rw [Int.not_even_iff_odd]
    exact (Int.even_pow.mpr ⟨even_two, by omega⟩).sub_odd odd_one
  have hnearest :
      FloatLib.Floats.Formats.Flocq.nearestEven (((2 ^ (f + 1) : ℤ) : ℝ) - 1 / 2) =
        2 ^ (f + 1) := by
    unfold FloatLib.Floats.Formats.Flocq.nearestEven
    simp only [hfloor, hodd, ite_false]
    push_cast
    norm_num
  unfold roundAt FloatLib.Floats.Formats.Flocq.round FloatLib.Floats.Formats.Flocq.toReal
  rw [hscaled, hnearest, hcexp, Flocq.bpow_binaryRadix, Flocq.bpow_binaryRadix]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
  congr 1
  push_cast
  ring

/-- A finite value that is the rounding of `y` has `|y|` below the overflow threshold. -/
theorem abs_lt_overflowThreshold_of_toReal_eq_roundAt {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) {result : Model fmt} (hresult : isFinite result = true) {y : ℝ}
    (hy : toReal result = roundAt fmt y) : |y| < Certified.overflowThreshold fmt := by
  by_contra hlarge
  have hround := roundAt_mono fmt (le_of_not_gt hlarge)
  rw [roundAt_overflowThreshold hfmt] at hround
  have habs : |roundAt fmt y| = roundAt fmt |y| := by
    rcases le_total 0 y with hy0 | hy0
    · rw [abs_of_nonneg hy0, abs_of_nonneg (by simpa using roundAt_mono fmt hy0)]
    · rw [abs_of_nonpos hy0, abs_of_nonpos (by simpa using roundAt_mono fmt hy0), roundAt_neg,
        IEEERoundingMode.negate_nearest]
  have hbound := abs_toReal_le_posMaxFinite_of_isFinite result hresult
  have hmaximum := toReal_posMaxFinite_lt_bpow fmt
  rw [hy, habs] at hbound
  linarith

/-! ## Enclosure searches -/

/-- The logarithm enclosure contains `log (scaled * 2 ^ binaryExponent)`. -/
theorem contains_logEnclosure {scaled : ℚ} (hscaled : 0 < scaled) (binaryExponent : ℤ)
    (precision : Nat) :
    (logEnclosure scaled binaryExponent precision).Contains
      (Real.log ((scaled : ℝ) * 2 ^ binaryExponent)) := by
  rw [logEnclosure, FloatLib.Numerics.Enclosure.BinaryGrid.contains_toRationalInterval]
  have h := Interval.BinaryGrid.containsReal_add precision
    (Certified.containsReal_logReduced hscaled precision)
    (FloatLib.Numerics.Enclosure.BinaryGrid.containsReal_scaleRat precision
      (FloatLib.Numerics.Enclosure.Constants.containsReal_ln2Grid precision) binaryExponent)
  rw [Real.log_mul (by exact_mod_cast hscaled.ne') (zpow_ne_zero _ (by norm_num)),
    Real.log_zpow]
  simpa using h

private theorem exists_enclosure_of_logSearch_eq_some {fmt : FloatFormat} {argument : ℚ}
    (hpositive : 0 < argument) {budget : Certified.Budget} {result : Model fmt}
    (hresult : logSearch fmt argument budget = some result) :
    ∃ interval : RationalInterval, interval.Contains (Real.log argument) ∧
      Enclosure.round? fmt interval = some result := by
  unfold logSearch at hresult
  split at hresult
  · obtain ⟨_, precision, haccept⟩ := RationalInterval.exists_of_refine_eq_some hresult
    obtain ⟨hscaled, hsplit⟩ := Certified.splitTwoPow_spec hpositive
    have hcontains := contains_logEnclosure hscaled (Certified.splitTwoPow argument).2 precision
    rw [hsplit] at hcontains
    exact ⟨_, hcontains, haccept⟩
  · simp at hresult

/-- A settled logarithm search is finite and correctly rounded. -/
theorem logSearch_spec {fmt : FloatFormat} {argument : ℚ} (hpositive : 0 < argument)
    {budget : Certified.Budget} {result : Model fmt}
    (hresult : logSearch fmt argument budget = some result) :
    isFinite result = true ∧ toReal result = roundAt fmt (Real.log argument) := by
  obtain ⟨_, hcontains, haccept⟩ := exists_enclosure_of_logSearch_eq_some hpositive hresult
  exact ⟨Enclosure.isFinite_of_round?_eq_some haccept,
    Enclosure.toReal_eq_roundAt_of_round?_eq_some hcontains haccept⟩

/-- The reduced exponential enclosure contains `exp (argument - multiple * log 2)`. -/
theorem contains_expReducedEnclosure (argument : ℚ) (multiple : ℤ)
    (extraBits degree precision : Nat) :
    (expReducedEnclosure argument multiple extraBits degree precision).Contains
      (Real.exp (argument - multiple * Real.log 2)) := by
  have h := Certified.contains_expReduced (r := argument - ((multiple : ℚ) : ℝ) * Real.log 2)
    (fun grid => Interval.BinaryGrid.containsReal_sub grid
      (Interval.BinaryGrid.containsReal_enclose grid argument)
      (FloatLib.Numerics.Enclosure.BinaryGrid.containsReal_scaleRat grid
        (FloatLib.Numerics.Enclosure.Constants.containsReal_ln2Grid grid) multiple))
    extraBits degree precision
  simpa [expReducedEnclosure] using h

private theorem exp_sub_mul_log_two_mul_zpow (x : ℝ) (k : ℤ) :
    Real.exp (x - k * Real.log 2) * 2 ^ k = Real.exp x := by
  have hpow : (2 : ℝ) ^ k = Real.exp (k * Real.log 2) := by
    rw [← Real.log_zpow, Real.exp_log (zpow_pos (by norm_num) k)]
  rw [hpow, ← Real.exp_add, sub_add_cancel]

/-- A settled weighted-exponential search is finite and correctly rounded. -/
theorem expMulSearch_spec {fmt : FloatFormat} {argument : ℚ} {weight : Numerics.Dyadic}
    {budget : Certified.Budget} {result : Model fmt}
    (hresult : expMulSearch fmt argument weight budget = some result) :
    isFinite result = true ∧
      toReal result = roundAt fmt (Real.exp argument * weight.toReal) := by
  dsimp only [expMulSearch] at hresult
  split at hresult
  · obtain ⟨degree, precision, haccept⟩ := RationalInterval.exists_of_refine_eq_some hresult
    have hcontains := RationalInterval.contains_scale
      (contains_expReducedEnclosure argument (logTwoMultiple argument)
        (Certified.magnitudeBits (logTwoMultiple argument) + 1) degree precision)
      weight.signedSignificand
    refine ⟨Enclosure.isFinite_of_roundScaled?_eq_some haccept, ?_⟩
    rw [Enclosure.toReal_eq_roundAt_of_roundScaled?_eq_some hcontains haccept]
    congr 1
    rw [zpow_add₀ (by norm_num), Dyadic.toReal, ← exp_sub_mul_log_two_mul_zpow argument
      (logTwoMultiple argument)]
    push_cast
    ring
  · simp at hresult

/-! ## Rational arguments -/

variable {fmt : FloatFormat}

/-- An exact comparator rounds a target below the overflow threshold to a finite value. -/
private theorem isFinite_round (hfmt : fmt.isIEEE = true) {sign : Bool}
    {compare : ℚ → Ordering} {target : ℝ}
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (hrange : target < Certified.overflowThreshold fmt) :
    isFinite (AlgebraicRounding.round fmt sign compare) = true :=
  AlgebraicRounding.isFinite_round_of_lt_overflow fmt hfmt sign compare target hcompare
    (cast_overflowThreshold fmt ▸ hrange)

/-- A finite exact-comparison rounding of a signed magnitude is its nearest-even rounding. -/
private theorem toReal_round (hfmt : fmt.isIEEE = true) {sign : Bool}
    {compare : ℚ → Ordering} {target value : ℝ} (hnonneg : 0 ≤ target)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (hvalue : (if sign then -target else target) = value)
    (hfinite : isFinite (AlgebraicRounding.round fmt sign compare) = true) :
    toReal (AlgebraicRounding.round fmt sign compare) = roundAt fmt value := by
  rw [← hvalue]
  exact AlgebraicRounding.toReal_round_eq_roundAt fmt hfmt sign compare target hnonneg hcompare
    hfinite

private theorem signed_abs_exp_sub_one (argument : ℚ) :
    (if decide (argument < 0) then -|Real.exp (argument : ℝ) - 1|
      else |Real.exp (argument : ℝ) - 1|) = Real.exp argument - 1 := by
  by_cases hnegative : argument < 0
  · have hexp : Real.exp (argument : ℝ) - 1 < 0 := by
      linarith [Real.exp_lt_one_iff.mpr (show (argument : ℝ) < 0 by exact_mod_cast hnegative)]
    rw [decide_eq_true hnegative, ite_eq_left rfl, abs_of_neg hexp, _root_.neg_neg]
  · have hexp : 0 ≤ Real.exp (argument : ℝ) - 1 := by
      linarith [Real.one_le_exp (show 0 ≤ (argument : ℝ) by
        exact_mod_cast le_of_not_gt hnegative)]
    rw [decide_eq_false hnegative, ite_eq_right Bool.false_ne_true, abs_of_nonneg hexp]

private theorem signed_abs_log {argument : ℚ} (hpositive : 0 < argument) :
    (if decide (argument < 1) then -|Real.log (argument : ℝ)| else |Real.log (argument : ℝ)|) =
      Real.log argument := by
  have hreal : (0 : ℝ) < argument := by exact_mod_cast hpositive
  by_cases hbelow : argument < 1
  · rw [decide_eq_true hbelow, ite_eq_left rfl,
      abs_of_neg (Real.log_neg hreal (by exact_mod_cast hbelow)), _root_.neg_neg]
  · rw [decide_eq_false hbelow, ite_eq_right Bool.false_ne_true,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast le_of_not_gt hbelow))]

private theorem signed_abs_toRat (weight : Numerics.Dyadic) :
    (if weight.negative then -|(weight.toRat : ℝ)| else |(weight.toRat : ℝ)|) =
      weight.toReal := by
  have hscale : (0 : ℝ) ≤ (weight.significand : ℝ) * 2 ^ weight.exponent := by positivity
  cases hsign : weight.negative <;>
    simp [Dyadic.toReal, Dyadic.signedSignificand, hsign, abs_of_nonneg hscale]

/-- `expRat` returns the certified exponential whenever the certified search does. -/
theorem expRat_eq_of_certified_expRat_eq_ok {argument : ℚ} {budget : Certified.Budget}
    {result : Model fmt} (hresult : Certified.expRat fmt argument budget = .ok result) :
    expRat fmt argument budget = result := by
  simp [expRat, hresult]

private theorem isFinite_expRat (hfmt : fmt.isIEEE = true) {argument : ℚ}
    (hrange : Real.exp (argument : ℝ) < Certified.overflowThreshold fmt)
    (budget : Certified.Budget) : isFinite (expRat fmt argument budget) = true := by
  unfold expRat
  split
  · exact Certified.isFinite_of_expRat_eq_ok ‹_›
  · exact isFinite_round hfmt (ElementaryComparison.compareExp_eq_real argument) hrange

private theorem toReal_expRat (hfmt : fmt.isIEEE = true) {argument : ℚ}
    {budget : Certified.Budget} (hfinite : isFinite (expRat fmt argument budget) = true) :
    toReal (expRat fmt argument budget) = roundAt fmt (Real.exp argument) := by
  cases hsearch : Certified.expRat fmt argument budget with
  | ok result =>
      rw [expRat_eq_of_certified_expRat_eq_ok hsearch]
      exact Certified.toReal_of_expRat_eq_ok hsearch
  | error _ =>
      simp only [expRat, hsearch] at hfinite ⊢
      exact toReal_round hfmt (Real.exp_pos _).le
        (ElementaryComparison.compareExp_eq_real argument) (by simp) hfinite

/-- `expMinus1Rat` returns the certified `expMinus1` whenever the certified search does. -/
theorem expMinus1Rat_eq_of_certified_expMinus1Rat_eq_ok {argument : ℚ} {budget : Certified.Budget}
    {result : Model fmt} (hresult : Certified.expMinus1Rat fmt argument budget = .ok result) :
    expMinus1Rat fmt argument budget = result := by
  simp [expMinus1Rat, hresult]

private theorem isFinite_expMinus1Rat (hfmt : fmt.isIEEE = true) {argument : ℚ}
    (hrange : Real.exp (argument : ℝ) - 1 < Certified.overflowThreshold fmt)
    (budget : Certified.Budget) : isFinite (expMinus1Rat fmt argument budget) = true := by
  unfold expMinus1Rat
  split
  · exact Certified.isFinite_of_expMinus1Rat_eq_ok ‹_›
  · refine isFinite_round hfmt (compareAbsExpMinus1_eq_real argument) ?_
    rcases le_or_gt 0 (Real.exp (argument : ℝ) - 1) with hexp | hexp
    · rwa [abs_of_nonneg hexp]
    · rw [abs_of_neg hexp]
      linarith [one_lt_overflowThreshold hfmt, Real.exp_pos (argument : ℝ)]

private theorem toReal_expMinus1Rat (hfmt : fmt.isIEEE = true) {argument : ℚ}
    {budget : Certified.Budget} (hfinite : isFinite (expMinus1Rat fmt argument budget) = true) :
    toReal (expMinus1Rat fmt argument budget) = roundAt fmt (Real.exp argument - 1) := by
  cases hsearch : Certified.expMinus1Rat fmt argument budget with
  | ok result =>
      rw [expMinus1Rat_eq_of_certified_expMinus1Rat_eq_ok hsearch]
      exact Certified.toReal_of_expMinus1Rat_eq_ok hsearch
  | error _ =>
      simp only [expMinus1Rat, hsearch] at hfinite ⊢
      exact toReal_round hfmt (abs_nonneg _) (compareAbsExpMinus1_eq_real argument)
        (signed_abs_exp_sub_one argument) hfinite

private theorem isFinite_logRat (hfmt : fmt.isIEEE = true) {argument : ℚ}
    (hpositive : 0 < argument)
    (hrange : |Real.log (argument : ℝ)| < Certified.overflowThreshold fmt)
    (budget : Certified.Budget) :
    isFinite (logRat fmt argument hpositive budget) = true := by
  unfold logRat
  split
  · exact (logSearch_spec hpositive ‹_›).1
  · exact isFinite_round hfmt (compareAbsLog_eq_real argument hpositive) hrange

private theorem toReal_logRat (hfmt : fmt.isIEEE = true) {argument : ℚ}
    (hpositive : 0 < argument) {budget : Certified.Budget}
    (hfinite : isFinite (logRat fmt argument hpositive budget) = true) :
    toReal (logRat fmt argument hpositive budget) = roundAt fmt (Real.log argument) := by
  cases hsearch : logSearch fmt argument budget with
  | some result =>
      simp only [logRat, hsearch]
      exact (logSearch_spec hpositive hsearch).2
  | none =>
      simp only [logRat, hsearch] at hfinite ⊢
      exact toReal_round hfmt (abs_nonneg _) (compareAbsLog_eq_real argument hpositive)
        (signed_abs_log hpositive) hfinite

private theorem isFinite_expMulRat (hfmt : fmt.isIEEE = true) {argument : ℚ}
    {weight : Numerics.Dyadic} (hweight : weight.toRat ≠ 0)
    (hrange : |Real.exp (argument : ℝ) * weight.toReal| < Certified.overflowThreshold fmt)
    (budget : Certified.Budget) :
    isFinite (expMulRat fmt argument weight budget) = true := by
  unfold expMulRat
  split
  · exact (expMulSearch_spec ‹_›).1
  · refine isFinite_round hfmt (target := Real.exp (argument : ℝ) * |(weight.toRat : ℝ)|)
      (by simpa using compareExpMul_eq_real argument _ (abs_pos.mpr hweight)) ?_
    rwa [abs_mul, abs_of_pos (Real.exp_pos _), ← Dyadic.cast_toRat] at hrange

private theorem toReal_expMulRat (hfmt : fmt.isIEEE = true) {argument : ℚ}
    {weight : Numerics.Dyadic} (hweight : weight.toRat ≠ 0) {budget : Certified.Budget}
    (hfinite : isFinite (expMulRat fmt argument weight budget) = true) :
    toReal (expMulRat fmt argument weight budget) =
      roundAt fmt (Real.exp argument * weight.toReal) := by
  cases hsearch : expMulSearch fmt argument weight budget with
  | some result =>
      simp only [expMulRat, hsearch]
      exact (expMulSearch_spec hsearch).2
  | none =>
      simp only [expMulRat, hsearch] at hfinite ⊢
      refine toReal_round hfmt (target := Real.exp (argument : ℝ) * |(weight.toRat : ℝ)|)
        (by positivity) (by simpa using compareExpMul_eq_real argument _ (abs_pos.mpr hweight))
        ?_ hfinite
      rw [← mul_neg, ← mul_ite, signed_abs_toRat]

/-! ## Encoded inputs -/

private theorem isZero_eq_false_of_toRat?_eq_some {input : Model fmt} {argument : ℚ}
    (hinput : toRat? input = some argument) (hargument : argument ≠ 0) :
    isZero input = false := by
  refine Bool.eq_false_iff.mpr fun hzero => hargument ?_
  have h := (isZero_eq_true_iff_toReal_eq_zero input
    (Algebraic.isFinite_of_toRat?_eq_some hinput)).mp hzero
  rw [Algebraic.toReal_of_toRat?_eq_some hinput] at h
  exact_mod_cast h

private theorem isZero_of_toRat?_eq_some_zero {input : Model fmt}
    (hinput : toRat? input = some 0) : isZero input = true :=
  (isZero_eq_true_iff_toReal_eq_zero input (Algebraic.isFinite_of_toRat?_eq_some hinput)).mpr
    (by rw [Algebraic.toReal_of_toRat?_eq_some hinput, Rat.cast_zero])

/-- The shifted argument of `logPlus1` is positive above `-1`. -/
private theorem one_add_pos_of_neg_one_lt {input : Model fmt} {argument : ℚ}
    (hreal : toReal input = argument) (hdomain : -1 < toReal input) : 0 < 1 + argument := by
  have : (-1 : ℝ) < argument := hreal ▸ hdomain
  exact_mod_cast (by linarith : (0 : ℝ) < 1 + argument)

/-- The exponential of a finite input is `expRat` at its exact value. -/
theorem exp_eq_expRat {input : Model fmt} {argument : ℚ} (hinput : toRat? input = some argument)
    (budget : Certified.Budget) : exp input budget = expRat fmt argument budget := by
  have hfinite := Algebraic.isFinite_of_toRat?_eq_some hinput
  simp [exp, isNaN_eq_false_of_isFinite_eq_true input hfinite,
    isInf_eq_false_of_isFinite_eq_true input hfinite, hinput]

/-- `expMinus1` returns either zero unchanged. -/
@[simp] theorem expMinus1_of_isZero {input : Model fmt} (hzero : isZero input = true)
    (budget : Certified.Budget) : expMinus1 input budget = input := by
  have hfinite := isFinite_eq_true_of_isZero_eq_true input hzero
  simp [expMinus1, isNaN_eq_false_of_isFinite_eq_true input hfinite,
    isInf_eq_false_of_isFinite_eq_true input hfinite, hzero]

/-- `expMinus1` of a finite nonzero input is `expMinus1Rat` at its exact value. -/
theorem expMinus1_eq_expMinus1Rat {input : Model fmt} {argument : ℚ}
    (hinput : toRat? input = some argument) (hargument : argument ≠ 0)
    (budget : Certified.Budget) :
    expMinus1 input budget = expMinus1Rat fmt argument budget := by
  have hfinite := Algebraic.isFinite_of_toRat?_eq_some hinput
  simp [expMinus1, isNaN_eq_false_of_isFinite_eq_true input hfinite,
    isInf_eq_false_of_isFinite_eq_true input hfinite,
    isZero_eq_false_of_toRat?_eq_some hinput hargument, hinput]

/-- The logarithm of a finite positive input is `logRat` at its exact value. -/
theorem log_eq_logRat {input : Model fmt} {argument : ℚ} (hinput : toRat? input = some argument)
    (hpositive : 0 < argument) (budget : Certified.Budget) :
    log input budget = logRat fmt argument hpositive budget := by
  have hfinite := Algebraic.isFinite_of_toRat?_eq_some hinput
  simp [log, isNaN_eq_false_of_isFinite_eq_true input hfinite,
    isInf_eq_false_of_isFinite_eq_true input hfinite,
    isZero_eq_false_of_toRat?_eq_some hinput hpositive.ne', hinput, hpositive]

/-- `logPlus1` returns either zero unchanged. -/
@[simp] theorem logPlus1_of_isZero {input : Model fmt} (hzero : isZero input = true)
    (budget : Certified.Budget) : logPlus1 input budget = input := by
  have hfinite := isFinite_eq_true_of_isZero_eq_true input hzero
  simp [logPlus1, isNaN_eq_false_of_isFinite_eq_true input hfinite,
    isInf_eq_false_of_isFinite_eq_true input hfinite, hzero]

/-- `logPlus1` of a finite nonzero input above `-1` is `logRat` at one plus its exact value. -/
theorem logPlus1_eq_logRat {input : Model fmt} {argument : ℚ}
    (hinput : toRat? input = some argument) (hargument : argument ≠ 0)
    (hpositive : 0 < 1 + argument) (budget : Certified.Budget) :
    logPlus1 input budget = logRat fmt (1 + argument) hpositive budget := by
  have hfinite := Algebraic.isFinite_of_toRat?_eq_some hinput
  simp [logPlus1, isNaN_eq_false_of_isFinite_eq_true input hfinite,
    isInf_eq_false_of_isFinite_eq_true input hfinite,
    isZero_eq_false_of_toRat?_eq_some hinput hargument, hinput, hpositive]

/-- A finite input times a finite nonzero weight is `expMulRat` at their exact values. -/
theorem expMul_eq_expMulRat {input weight : Model fmt} {argument : ℚ} {factor : Numerics.Dyadic}
    (hinput : toRat? input = some argument) (hweight : toDyadic? weight = some factor)
    (hfactor : factor.toRat ≠ 0) (budget : Certified.Budget) :
    expMul input weight budget = expMulRat fmt argument factor budget := by
  have hfinite := Algebraic.isFinite_of_toRat?_eq_some hinput
  have hweightRat : toRat? weight = some factor.toRat := by simp [toRat?, hweight]
  simp [expMul, isNaN_eq_false_of_isFinite_eq_true input hfinite,
    isInf_eq_false_of_isFinite_eq_true input hfinite, isNaN_eq_false_of_toDyadic?_some hweight,
    isInf_eq_false_of_toDyadic?_some hweight, isZero_eq_false_of_toRat?_eq_some hweightRat hfactor,
    hinput, hweight]

/-- A finite input times a zero weight is the zero with the weight's sign. -/
@[simp] theorem expMul_of_isZero {input weight : Model fmt} (hinput : isFinite input = true)
    (hweight : isZero weight = true) (budget : Certified.Budget) :
    expMul input weight budget = zero fmt (signBit weight) := by
  have hfinite := isFinite_eq_true_of_isZero_eq_true weight hweight
  simp [expMul, isNaN_eq_false_of_isFinite_eq_true input hinput,
    isInf_eq_false_of_isFinite_eq_true input hinput,
    isNaN_eq_false_of_isFinite_eq_true weight hfinite,
    isInf_eq_false_of_isFinite_eq_true weight hfinite, hweight]

/-- A finite nonzero weight decodes to a dyadic with a nonzero rational value. -/
private theorem exists_toDyadic?_eq {weight : Model fmt} (hweight : isFinite weight = true)
    (hzero : isZero weight = false) :
    ∃ factor : Numerics.Dyadic, toDyadic? weight = some factor ∧ factor.toRat ≠ 0 ∧
      toReal weight = factor.toReal := by
  obtain ⟨factor, hfactor⟩ := exists_toDyadic?_of_isFinite hweight
  have hreal : toReal weight = factor.toReal := by rw [toReal_eq, hfactor]
  refine ⟨factor, hfactor, fun hrat => ?_, hreal⟩
  rw [← Bool.not_eq_true, isZero_eq_true_iff_toReal_eq_zero weight hweight, hreal,
    ← Dyadic.cast_toRat, hrat, Rat.cast_zero] at hzero
  exact hzero rfl

/-! ## Correct rounding and finiteness -/

/-- A finite exponential of a finite input is the correctly rounded exponential. -/
theorem toReal_exp_of_isFinite (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) {budget : Certified.Budget}
    (hfinite : isFinite (exp input budget) = true) :
    toReal (exp input budget) = roundAt fmt (Real.exp (toReal input)) := by
  obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  rw [exp_eq_expRat hdecode] at hfinite ⊢
  rw [hreal]
  exact toReal_expRat hfmt hfinite

/--
The exponential of a finite input is finite when its exact result is below the overflow threshold.
-/
theorem isFinite_exp (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true)
    (hrange : Real.exp (toReal input) < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} : isFinite (exp input budget) = true := by
  obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  rw [exp_eq_expRat hdecode]
  exact isFinite_expRat hfmt (hreal ▸ hrange) budget

/--
The exponential of a finite input is finite if and only if its exact result is below the overflow
threshold.
-/
theorem isFinite_exp_iff (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) {budget : Certified.Budget} :
    isFinite (exp input budget) = true ↔
      Real.exp (toReal input) < Certified.overflowThreshold fmt := by
  refine ⟨fun hfinite => ?_, fun hrange => isFinite_exp hfmt hinput hrange⟩
  have h := abs_lt_overflowThreshold_of_toReal_eq_roundAt hfmt hfinite
    (toReal_exp_of_isFinite hfmt hinput hfinite)
  rwa [abs_of_pos (Real.exp_pos _)] at h

/--
The exponential of a finite input is correctly rounded when its exact result is below the overflow
threshold.
-/
theorem toReal_exp_eq_roundAt (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true)
    (hrange : Real.exp (toReal input) < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} :
    toReal (exp input budget) = roundAt fmt (Real.exp (toReal input)) :=
  toReal_exp_of_isFinite hfmt hinput (isFinite_exp hfmt hinput hrange)

/-- A finite `expMinus1` of a finite input is the correctly rounded `exp x - 1`. -/
theorem toReal_expMinus1_of_isFinite (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) {budget : Certified.Budget}
    (hfinite : isFinite (expMinus1 input budget) = true) :
    toReal (expMinus1 input budget) = roundAt fmt (Real.exp (toReal input) - 1) := by
  obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  by_cases hzero : argument = 0
  · subst hzero
    simp [expMinus1_of_isZero (isZero_of_toRat?_eq_some_zero hdecode), hreal]
  · rw [expMinus1_eq_expMinus1Rat hdecode hzero] at hfinite ⊢
    rw [hreal]
    exact toReal_expMinus1Rat hfmt hfinite

/--
`expMinus1` of a finite input is finite when its exact result is below the overflow threshold.
-/
theorem isFinite_expMinus1 (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true)
    (hrange : Real.exp (toReal input) - 1 < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} : isFinite (expMinus1 input budget) = true := by
  obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  by_cases hzero : argument = 0
  · subst hzero
    rwa [expMinus1_of_isZero (isZero_of_toRat?_eq_some_zero hdecode)]
  · rw [expMinus1_eq_expMinus1Rat hdecode hzero]
    exact isFinite_expMinus1Rat hfmt (hreal ▸ hrange) budget

/--
`expMinus1` of a finite input is finite if and only if its exact result is below the overflow
threshold.
-/
theorem isFinite_expMinus1_iff (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) {budget : Certified.Budget} :
    isFinite (expMinus1 input budget) = true ↔
      Real.exp (toReal input) - 1 < Certified.overflowThreshold fmt :=
  ⟨fun hfinite => (le_abs_self _).trans_lt (abs_lt_overflowThreshold_of_toReal_eq_roundAt hfmt
      hfinite (toReal_expMinus1_of_isFinite hfmt hinput hfinite)),
    fun hrange => isFinite_expMinus1 hfmt hinput hrange⟩

/--
`expMinus1` of a finite input is correctly rounded when its exact result is below the overflow
threshold.
-/
theorem toReal_expMinus1_eq_roundAt (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true)
    (hrange : Real.exp (toReal input) - 1 < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} :
    toReal (expMinus1 input budget) = roundAt fmt (Real.exp (toReal input) - 1) :=
  toReal_expMinus1_of_isFinite hfmt hinput (isFinite_expMinus1 hfmt hinput hrange)

/-- A finite logarithm of a finite positive input is the correctly rounded logarithm. -/
theorem toReal_log_of_isFinite (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hpositive : 0 < toReal input)
    {budget : Certified.Budget} (hfinite : isFinite (log input budget) = true) :
    toReal (log input budget) = roundAt fmt (Real.log (toReal input)) := by
  obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  have hargument : 0 < argument := by exact_mod_cast hreal ▸ hpositive
  rw [log_eq_logRat hdecode hargument] at hfinite ⊢
  rw [hreal]
  exact toReal_logRat hfmt hargument hfinite

/--
The logarithm of a finite positive input is finite when its exact result is below the overflow
threshold in magnitude.
-/
theorem isFinite_log (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hpositive : 0 < toReal input)
    (hrange : |Real.log (toReal input)| < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} : isFinite (log input budget) = true := by
  obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  have hargument : 0 < argument := by exact_mod_cast hreal ▸ hpositive
  rw [log_eq_logRat hdecode hargument]
  exact isFinite_logRat hfmt hargument (hreal ▸ hrange) budget

/--
The logarithm of a finite positive input is finite if and only if its exact result is below the
overflow threshold in magnitude.
-/
theorem isFinite_log_iff (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hpositive : 0 < toReal input)
    {budget : Certified.Budget} :
    isFinite (log input budget) = true ↔
      |Real.log (toReal input)| < Certified.overflowThreshold fmt :=
  ⟨fun hfinite => abs_lt_overflowThreshold_of_toReal_eq_roundAt hfmt hfinite
      (toReal_log_of_isFinite hfmt hinput hpositive hfinite),
    fun hrange => isFinite_log hfmt hinput hpositive hrange⟩

/--
The logarithm of a finite positive input is correctly rounded when its exact result is below the
overflow threshold in magnitude.
-/
theorem toReal_log_eq_roundAt (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hpositive : 0 < toReal input)
    (hrange : |Real.log (toReal input)| < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} :
    toReal (log input budget) = roundAt fmt (Real.log (toReal input)) :=
  toReal_log_of_isFinite hfmt hinput hpositive (isFinite_log hfmt hinput hpositive hrange)

/-- A finite `logPlus1` of a finite input above `-1` is the correctly rounded `log (1 + x)`. -/
theorem toReal_logPlus1_of_isFinite (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hdomain : -1 < toReal input)
    {budget : Certified.Budget} (hfinite : isFinite (logPlus1 input budget) = true) :
    toReal (logPlus1 input budget) = roundAt fmt (Real.log (1 + toReal input)) := by
  obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  by_cases hzero : argument = 0
  · subst hzero
    simp [logPlus1_of_isZero (isZero_of_toRat?_eq_some_zero hdecode), hreal]
  · have hpositive := one_add_pos_of_neg_one_lt hreal hdomain
    rw [logPlus1_eq_logRat hdecode hzero hpositive] at hfinite ⊢
    rw [hreal]
    simpa using toReal_logRat hfmt hpositive hfinite

/--
`logPlus1` of a finite input above `-1` is finite when its exact result is below the overflow
threshold in magnitude.
-/
theorem isFinite_logPlus1 (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hdomain : -1 < toReal input)
    (hrange : |Real.log (1 + toReal input)| < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} : isFinite (logPlus1 input budget) = true := by
  obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  by_cases hzero : argument = 0
  · subst hzero
    rwa [logPlus1_of_isZero (isZero_of_toRat?_eq_some_zero hdecode)]
  · have hpositive := one_add_pos_of_neg_one_lt hreal hdomain
    rw [logPlus1_eq_logRat hdecode hzero hpositive]
    exact isFinite_logRat hfmt hpositive (by simpa [hreal] using hrange) budget

/--
`logPlus1` of a finite input above `-1` is finite if and only if its exact result is below the
overflow threshold in magnitude.
-/
theorem isFinite_logPlus1_iff (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hdomain : -1 < toReal input)
    {budget : Certified.Budget} :
    isFinite (logPlus1 input budget) = true ↔
      |Real.log (1 + toReal input)| < Certified.overflowThreshold fmt :=
  ⟨fun hfinite => abs_lt_overflowThreshold_of_toReal_eq_roundAt hfmt hfinite
      (toReal_logPlus1_of_isFinite hfmt hinput hdomain hfinite),
    fun hrange => isFinite_logPlus1 hfmt hinput hdomain hrange⟩

/--
`logPlus1` of a finite input above `-1` is correctly rounded when its exact result is below the
overflow threshold in magnitude.
-/
theorem toReal_logPlus1_eq_roundAt (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hdomain : -1 < toReal input)
    (hrange : |Real.log (1 + toReal input)| < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} :
    toReal (logPlus1 input budget) = roundAt fmt (Real.log (1 + toReal input)) :=
  toReal_logPlus1_of_isFinite hfmt hinput hdomain (isFinite_logPlus1 hfmt hinput hdomain hrange)

/-- A finite weighted exponential of finite operands is the correctly rounded product. -/
theorem toReal_expMul_of_isFinite (hfmt : fmt.isIEEE = true) {input weight : Model fmt}
    (hinput : isFinite input = true) (hweight : isFinite weight = true)
    {budget : Certified.Budget} (hfinite : isFinite (expMul input weight budget) = true) :
    toReal (expMul input weight budget) =
      roundAt fmt (Real.exp (toReal input) * toReal weight) := by
  cases hzero : isZero weight
  · obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
    obtain ⟨factor, hfactor, hnonzero, hweightReal⟩ := exists_toDyadic?_eq hweight hzero
    rw [expMul_eq_expMulRat hdecode hfactor hnonzero] at hfinite ⊢
    rw [hreal, hweightReal]
    exact toReal_expMulRat hfmt hnonzero hfinite
  · rw [expMul_of_isZero hinput hzero, toReal_eq_zero_of_isZero weight hzero]
    simp

/--
The weighted exponential of finite operands is finite when its exact result is below the overflow
threshold in magnitude.
-/
theorem isFinite_expMul (hfmt : fmt.isIEEE = true) {input weight : Model fmt}
    (hinput : isFinite input = true) (hweight : isFinite weight = true)
    (hrange : |Real.exp (toReal input) * toReal weight| < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} : isFinite (expMul input weight budget) = true := by
  cases hzero : isZero weight
  · obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
    obtain ⟨factor, hfactor, hnonzero, hweightReal⟩ := exists_toDyadic?_eq hweight hzero
    rw [expMul_eq_expMulRat hdecode hfactor hnonzero]
    exact isFinite_expMulRat hfmt hnonzero (by rwa [hreal, hweightReal] at hrange) budget
  · rw [expMul_of_isZero hinput hzero]
    exact isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt _)

/--
The weighted exponential of finite operands is finite if and only if its exact result is below the
overflow threshold in magnitude.
-/
theorem isFinite_expMul_iff (hfmt : fmt.isIEEE = true) {input weight : Model fmt}
    (hinput : isFinite input = true) (hweight : isFinite weight = true)
    {budget : Certified.Budget} :
    isFinite (expMul input weight budget) = true ↔
      |Real.exp (toReal input) * toReal weight| < Certified.overflowThreshold fmt :=
  ⟨fun hfinite => abs_lt_overflowThreshold_of_toReal_eq_roundAt hfmt hfinite
      (toReal_expMul_of_isFinite hfmt hinput hweight hfinite),
    fun hrange => isFinite_expMul hfmt hinput hweight hrange⟩

/--
The weighted exponential of finite operands is correctly rounded when its exact result is below the
overflow threshold in magnitude.
-/
theorem toReal_expMul_eq_roundAt (hfmt : fmt.isIEEE = true) {input weight : Model fmt}
    (hinput : isFinite input = true) (hweight : isFinite weight = true)
    (hrange : |Real.exp (toReal input) * toReal weight| < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} :
    toReal (expMul input weight budget) =
      roundAt fmt (Real.exp (toReal input) * toReal weight) :=
  toReal_expMul_of_isFinite hfmt hinput hweight (isFinite_expMul hfmt hinput hweight hrange)

/-! ## Overflow and the domain -/

private theorem expRat_eq_nativeOverflow (hfmt : fmt.isIEEE = true) {argument : ℚ}
    {budget : Certified.Budget} (hnonfinite : isFinite (expRat fmt argument budget) = false) :
    expRat fmt argument budget = nativeOverflow fmt false := by
  cases hsearch : Certified.expRat fmt argument budget with
  | ok result =>
      simp [expRat, hsearch, Certified.isFinite_of_expRat_eq_ok hsearch] at hnonfinite
  | error _ =>
      simp only [expRat, hsearch] at hnonfinite ⊢
      exact AlgebraicRounding.round_eq_nativeOverflow_of_isFinite_eq_false fmt hfmt _ _ hnonfinite

private theorem expMinus1Rat_eq_nativeOverflow (hfmt : fmt.isIEEE = true) {argument : ℚ}
    {budget : Certified.Budget}
    (hnonfinite : isFinite (expMinus1Rat fmt argument budget) = false) :
    expMinus1Rat fmt argument budget = nativeOverflow fmt (decide (argument < 0)) := by
  cases hsearch : Certified.expMinus1Rat fmt argument budget with
  | ok result =>
      simp [expMinus1Rat, hsearch, Certified.isFinite_of_expMinus1Rat_eq_ok hsearch] at hnonfinite
  | error _ =>
      simp only [expMinus1Rat, hsearch] at hnonfinite ⊢
      exact AlgebraicRounding.round_eq_nativeOverflow_of_isFinite_eq_false fmt hfmt _ _ hnonfinite

private theorem logRat_eq_nativeOverflow (hfmt : fmt.isIEEE = true) {argument : ℚ}
    (hpositive : 0 < argument) {budget : Certified.Budget}
    (hnonfinite : isFinite (logRat fmt argument hpositive budget) = false) :
    logRat fmt argument hpositive budget = nativeOverflow fmt (decide (argument < 1)) := by
  cases hsearch : logSearch fmt argument budget with
  | some result =>
      simp [logRat, hsearch, (logSearch_spec hpositive hsearch).1] at hnonfinite
  | none =>
      simp only [logRat, hsearch] at hnonfinite ⊢
      exact AlgebraicRounding.round_eq_nativeOverflow_of_isFinite_eq_false fmt hfmt _ _ hnonfinite

private theorem expMulRat_eq_nativeOverflow (hfmt : fmt.isIEEE = true) {argument : ℚ}
    {weight : Numerics.Dyadic} {budget : Certified.Budget}
    (hnonfinite : isFinite (expMulRat fmt argument weight budget) = false) :
    expMulRat fmt argument weight budget = nativeOverflow fmt weight.negative := by
  cases hsearch : expMulSearch fmt argument weight budget with
  | some result =>
      simp [expMulRat, hsearch, (expMulSearch_spec hsearch).1] at hnonfinite
  | none =>
      simp only [expMulRat, hsearch] at hnonfinite ⊢
      exact AlgebraicRounding.round_eq_nativeOverflow_of_isFinite_eq_false fmt hfmt _ _ hnonfinite

/--
The exponential of a finite input is `+∞` when its exact result is at or above the overflow
threshold.
-/
theorem exp_eq_nativeOverflow (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true)
    (hrange : Certified.overflowThreshold fmt ≤ Real.exp (toReal input))
    {budget : Certified.Budget} : exp input budget = nativeOverflow fmt false := by
  have hnonfinite : isFinite (exp input budget) = false := Bool.eq_false_iff.mpr
    fun hfinite => ((isFinite_exp_iff hfmt hinput).mp hfinite).not_ge hrange
  obtain ⟨argument, hdecode, -⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  rw [exp_eq_expRat hdecode] at hnonfinite ⊢
  exact expRat_eq_nativeOverflow hfmt hnonfinite

/--
`expMinus1` of a finite input is `+∞` when its exact result is at or above the overflow threshold.
-/
theorem expMinus1_eq_nativeOverflow (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true)
    (hrange : Certified.overflowThreshold fmt ≤ Real.exp (toReal input) - 1)
    {budget : Certified.Budget} : expMinus1 input budget = nativeOverflow fmt false := by
  have hnonfinite : isFinite (expMinus1 input budget) = false := Bool.eq_false_iff.mpr
    fun hfinite => ((isFinite_expMinus1_iff hfmt hinput).mp hfinite).not_ge hrange
  obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  have hpositive : 0 < argument := by
    rw [← Rat.cast_pos (K := ℝ), ← hreal, ← Real.one_lt_exp_iff]
    linarith [one_lt_overflowThreshold hfmt]
  rw [expMinus1_eq_expMinus1Rat hdecode hpositive.ne'] at hnonfinite ⊢
  rw [expMinus1Rat_eq_nativeOverflow hfmt hnonfinite, decide_eq_false hpositive.not_gt]

/--
The logarithm of a finite positive input is the infinity with the sign of its exact result when that
result is at or above the overflow threshold in magnitude.
-/
theorem log_eq_nativeOverflow (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hpositive : 0 < toReal input)
    (hrange : Certified.overflowThreshold fmt ≤ |Real.log (toReal input)|)
    {budget : Certified.Budget} :
    log input budget = nativeOverflow fmt (decide (toReal input < 1)) := by
  have hnonfinite : isFinite (log input budget) = false := Bool.eq_false_iff.mpr
    fun hfinite => ((isFinite_log_iff hfmt hinput hpositive).mp hfinite).not_ge hrange
  obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  have hargument : 0 < argument := by exact_mod_cast hreal ▸ hpositive
  rw [log_eq_logRat hdecode hargument] at hnonfinite ⊢
  rw [logRat_eq_nativeOverflow hfmt hargument hnonfinite, hreal]
  exact congrArg _ (decide_eq_decide.mpr (by norm_cast))

/--
`logPlus1` of a finite input above `-1` is the infinity with the sign of its exact result when that
result is at or above the overflow threshold in magnitude.
-/
theorem logPlus1_eq_nativeOverflow (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hdomain : -1 < toReal input)
    (hrange : Certified.overflowThreshold fmt ≤ |Real.log (1 + toReal input)|)
    {budget : Certified.Budget} :
    logPlus1 input budget = nativeOverflow fmt (decide (toReal input < 0)) := by
  have hnonfinite : isFinite (logPlus1 input budget) = false := Bool.eq_false_iff.mpr
    fun hfinite => ((isFinite_logPlus1_iff hfmt hinput hdomain).mp hfinite).not_ge hrange
  obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  have hzero : argument ≠ 0 := by
    rintro rfl
    rw [logPlus1_of_isZero (isZero_of_toRat?_eq_some_zero hdecode)] at hnonfinite
    simp [hinput] at hnonfinite
  have hpositive := one_add_pos_of_neg_one_lt hreal hdomain
  rw [logPlus1_eq_logRat hdecode hzero hpositive] at hnonfinite ⊢
  rw [logRat_eq_nativeOverflow hfmt hpositive hnonfinite, hreal]
  exact congrArg _ (decide_eq_decide.mpr (by rw [add_lt_iff_neg_left]; norm_cast))

/--
The weighted exponential of finite operands is the infinity with the sign of the weight when its
exact result is at or above the overflow threshold in magnitude.
-/
theorem expMul_eq_nativeOverflow (hfmt : fmt.isIEEE = true) {input weight : Model fmt}
    (hinput : isFinite input = true) (hweight : isFinite weight = true)
    (hrange : Certified.overflowThreshold fmt ≤ |Real.exp (toReal input) * toReal weight|)
    {budget : Certified.Budget} :
    expMul input weight budget = nativeOverflow fmt (signBit weight) := by
  have hnonfinite : isFinite (expMul input weight budget) = false := Bool.eq_false_iff.mpr
    fun hfinite => ((isFinite_expMul_iff hfmt hinput hweight).mp hfinite).not_ge hrange
  cases hzero : isZero weight
  · obtain ⟨argument, hdecode, -⟩ := Algebraic.exists_toRat?_of_isFinite hinput
    obtain ⟨factor, hfactor, hnonzero, -⟩ := exists_toDyadic?_eq hweight hzero
    rw [expMul_eq_expMulRat hdecode hfactor hnonzero] at hnonfinite ⊢
    rw [expMulRat_eq_nativeOverflow hfmt hnonfinite, sign_eq_signBit_of_toDyadic?_some hfactor]
  · rw [expMul_of_isZero hinput hzero] at hnonfinite
    simp [isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt _)] at hnonfinite

/-- A finite logarithm of a finite input comes from a positive input. -/
theorem toReal_pos_of_isFinite_log (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) {budget : Certified.Budget}
    (hfinite : isFinite (log input budget) = true) : 0 < toReal input := by
  have hencoding := FloatFormat.encoding_eq_ieee_of_isIEEE fmt hfmt
  obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  rw [hreal]
  by_contra hnonpositive
  have hargument : ¬0 < argument := fun h => hnonpositive (by exact_mod_cast h)
  by_cases hzero : isZero input = true
  · simp [log, isNaN_eq_false_of_isFinite_eq_true input hinput,
      isInf_eq_false_of_isFinite_eq_true input hinput, hzero,
      isFinite_nativeOverflow hfmt] at hfinite
  · simp [log, isNaN_eq_false_of_isFinite_eq_true input hinput,
      isInf_eq_false_of_isFinite_eq_true input hinput, hzero, hdecode, hargument, invalidResult,
      hencoding, isFinite_canonicalNaN hencoding] at hfinite

/-- A finite `logPlus1` of a finite input comes from an input above `-1`. -/
theorem neg_one_lt_toReal_of_isFinite_logPlus1 (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) {budget : Certified.Budget}
    (hfinite : isFinite (logPlus1 input budget) = true) : -1 < toReal input := by
  have hencoding := FloatFormat.encoding_eq_ieee_of_isIEEE fmt hfmt
  obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  rw [hreal]
  by_contra houtside
  have hargument : ¬0 < 1 + argument :=
    fun h => houtside (by exact_mod_cast (by linarith : (-1 : ℚ) < argument))
  have hzero : isZero input = false :=
    isZero_eq_false_of_toRat?_eq_some hdecode (fun h => hargument (by rw [h]; norm_num))
  by_cases hone : argument = -1
  · simp [logPlus1, isNaN_eq_false_of_isFinite_eq_true input hinput,
      isInf_eq_false_of_isFinite_eq_true input hinput, hzero, hdecode, hone,
      isFinite_nativeOverflow hfmt] at hfinite
  · simp [logPlus1, isNaN_eq_false_of_isFinite_eq_true input hinput,
      isInf_eq_false_of_isFinite_eq_true input hinput, hzero, hdecode, hargument, hone,
      invalidResult, hencoding, isFinite_canonicalNaN hencoding] at hfinite

/-! ## Mixed error bounds -/

/--
For a finite input `x` with `exp x` below the overflow threshold, the exponential differs from
`exp x` by at most `unitRoundoffAt fmt * |exp x| + underflowErrorAt fmt`.
-/
theorem abs_toReal_exp_sub_le (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true)
    (hrange : Real.exp (toReal input) < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} :
    |toReal (exp input budget) - Real.exp (toReal input)| ≤
      unitRoundoffAt fmt * |Real.exp (toReal input)| + underflowErrorAt fmt := by
  rw [toReal_exp_eq_roundAt hfmt hinput hrange]
  exact abs_roundAt_sub_le_unitRoundoffAt fmt _

/--
For a finite input `x` with `exp x - 1` below the overflow threshold, `expMinus1` differs from
`exp x - 1` by at most `unitRoundoffAt fmt * |exp x - 1| + underflowErrorAt fmt`.
-/
theorem abs_toReal_expMinus1_sub_le (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true)
    (hrange : Real.exp (toReal input) - 1 < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} :
    |toReal (expMinus1 input budget) - (Real.exp (toReal input) - 1)| ≤
      unitRoundoffAt fmt * |Real.exp (toReal input) - 1| + underflowErrorAt fmt := by
  rw [toReal_expMinus1_eq_roundAt hfmt hinput hrange]
  exact abs_roundAt_sub_le_unitRoundoffAt fmt _

/--
For a finite positive input `x` with `|log x|` below the overflow threshold, the logarithm differs
from `log x` by at most `unitRoundoffAt fmt * |log x| + underflowErrorAt fmt`.
-/
theorem abs_toReal_log_sub_le (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hpositive : 0 < toReal input)
    (hrange : |Real.log (toReal input)| < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} :
    |toReal (log input budget) - Real.log (toReal input)| ≤
      unitRoundoffAt fmt * |Real.log (toReal input)| + underflowErrorAt fmt := by
  rw [toReal_log_eq_roundAt hfmt hinput hpositive hrange]
  exact abs_roundAt_sub_le_unitRoundoffAt fmt _

/--
For a finite input `x > -1` with `|log (1 + x)|` below the overflow threshold, `logPlus1` differs
from `log (1 + x)` by at most `unitRoundoffAt fmt * |log (1 + x)| + underflowErrorAt fmt`.
-/
theorem abs_toReal_logPlus1_sub_le (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hdomain : -1 < toReal input)
    (hrange : |Real.log (1 + toReal input)| < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} :
    |toReal (logPlus1 input budget) - Real.log (1 + toReal input)| ≤
      unitRoundoffAt fmt * |Real.log (1 + toReal input)| + underflowErrorAt fmt := by
  rw [toReal_logPlus1_eq_roundAt hfmt hinput hdomain hrange]
  exact abs_roundAt_sub_le_unitRoundoffAt fmt _

/--
For finite `x` and `w` with `|exp x * w|` below the overflow threshold, the weighted exponential
differs from `exp x * w` by at most `unitRoundoffAt fmt * |exp x * w| + underflowErrorAt fmt`.
-/
theorem abs_toReal_expMul_sub_le (hfmt : fmt.isIEEE = true) {input weight : Model fmt}
    (hinput : isFinite input = true) (hweight : isFinite weight = true)
    (hrange : |Real.exp (toReal input) * toReal weight| < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} :
    |toReal (expMul input weight budget) - Real.exp (toReal input) * toReal weight| ≤
      unitRoundoffAt fmt * |Real.exp (toReal input) * toReal weight| + underflowErrorAt fmt := by
  rw [toReal_expMul_eq_roundAt hfmt hinput hweight hrange]
  exact abs_roundAt_sub_le_unitRoundoffAt fmt _

/-! ## Signs -/

/-- A finite nonzero input is at least the least subnormal, `2 * underflowErrorAt fmt`, in size. -/
private theorem two_mul_underflowErrorAt_le_abs_toReal {input : Model fmt}
    (hinput : isFinite input = true) (hzero : toReal input ≠ 0) :
    2 * underflowErrorAt fmt ≤ |toReal input| := by
  rw [two_mul_underflowErrorAt]
  exact bpow_minSubnormalExponent_le_abs_toReal hinput hzero

/-- Half the least subnormal of every descriptor is at most `1 / 4`. -/
private theorem underflowErrorAt_le_quarter : underflowErrorAt fmt ≤ 1 / 4 := by
  rw [underflowErrorAt_eq, show (1 / 4 : ℝ) = 2 ^ (-2 : ℤ) by norm_num]
  refine zpow_le_zpow_right₀ (by norm_num) ?_
  have := fmt.exponentBias_pos
  have := fmt.fracWidth_pos
  simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
    Int.ofNat_eq_natCast]
  omega

/--
The exponential never has a negative real value: a NaN or an overflow has real value zero,
`exp (-∞)` is zero and `exp ∞` overflows, so no premise on the input is needed.
-/
theorem toReal_exp_nonneg (hfmt : fmt.isIEEE = true) (input : Model fmt)
    {budget : Certified.Budget} : 0 ≤ toReal (exp input budget) := by
  cases hfinite : isFinite (exp input budget)
  · rw [toReal_eq_zero_of_isFinite_eq_false hfinite]
  by_cases hinput : isFinite input = true
  · rw [toReal_exp_of_isFinite hfmt hinput hfinite]
    exact roundAt_nonneg fmt (Real.exp_pos _).le
  unfold exp at hfinite ⊢
  split_ifs at hfinite ⊢ with hnan hinf
  · rw [isFinite_quietNaN] at hfinite
    exact absurd hfinite hinput
  · simp
  · exact toReal_nativeOverflow_false_nonneg fmt
  · exact absurd (isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false input
      (by simpa using hnan) (by simpa using hinf)) hinput

/--
The exponential of a finite input is positive when its exact result exceeds `underflowErrorAt fmt`
and is below the overflow threshold.
-/
theorem toReal_exp_pos (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true)
    (hrange : Real.exp (toReal input) < Certified.overflowThreshold fmt)
    (hlarge : underflowErrorAt fmt < Real.exp (toReal input)) {budget : Certified.Budget} :
    0 < toReal (exp input budget) := by
  rw [toReal_exp_eq_roundAt hfmt hinput hrange]
  exact roundAt_pos fmt hlarge

/-- `expMinus1` of a finite negative input is negative. -/
theorem toReal_expMinus1_lt_zero (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hnegative : toReal input < 0)
    {budget : Certified.Budget} : toReal (expMinus1 input budget) < 0 := by
  have hexp : Real.exp (toReal input) < 1 := Real.exp_lt_one_iff.mpr hnegative
  rw [toReal_expMinus1_eq_roundAt hfmt hinput (by linarith [one_lt_overflowThreshold hfmt])]
  refine roundAt_lt_zero fmt ?_
  -- With `t = 2 * underflowErrorAt fmt ≤ 1 / 2`, `1 - exp (-t) ≥ t * exp (-t) > t / 2`.
  set t := 2 * underflowErrorAt fmt
  have ht : 0 < t := mul_pos two_pos (underflowErrorAt_pos fmt)
  have hhalf : t ≤ 1 / 2 := by linarith [underflowErrorAt_le_quarter (fmt := fmt)]
  have hle : toReal input ≤ -t := by
    have h := two_mul_underflowErrorAt_le_abs_toReal hinput hnegative.ne
    rw [abs_of_neg hnegative] at h
    linarith
  have hlower : 1 / 2 < Real.exp (-t) := by
    linarith [Real.add_one_lt_exp (neg_ne_zero.mpr ht.ne')]
  have hinv : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hmono := Real.exp_le_exp.mpr hle
  nlinarith [Real.add_one_le_exp t, Real.exp_pos (-t), mul_pos ht (sub_pos.mpr hlower)]

/--
`expMinus1` of a finite positive input is positive when its exact result is below the overflow
threshold.
-/
theorem toReal_expMinus1_pos (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hpositive : 0 < toReal input)
    (hrange : Real.exp (toReal input) - 1 < Certified.overflowThreshold fmt)
    {budget : Certified.Budget} : 0 < toReal (expMinus1 input budget) := by
  have h := two_mul_underflowErrorAt_le_abs_toReal hinput hpositive.ne'
  rw [abs_of_pos hpositive] at h
  rw [toReal_expMinus1_eq_roundAt hfmt hinput hrange]
  exact roundAt_pos fmt (by linarith [Real.add_one_le_exp (toReal input), underflowErrorAt_pos fmt])

/-- The exponential of a finite nonpositive input is finite. -/
theorem isFinite_exp_of_nonpos (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hnonpos : toReal input ≤ 0)
    {budget : Certified.Budget} : isFinite (exp input budget) = true :=
  isFinite_exp hfmt hinput
    ((Real.exp_le_one_iff.mpr hnonpos).trans_lt (one_lt_overflowThreshold hfmt))

/-- `expMinus1` of a finite nonpositive input is finite. -/
theorem isFinite_expMinus1_of_nonpos (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hnonpos : toReal input ≤ 0)
    {budget : Certified.Budget} : isFinite (expMinus1 input budget) = true :=
  isFinite_expMinus1 hfmt hinput
    (by linarith [Real.exp_le_one_iff.mpr hnonpos, one_lt_overflowThreshold hfmt])

/-- `logPlus1` of a finite nonnegative input is finite. -/
theorem isFinite_logPlus1_of_nonneg (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hnonneg : 0 ≤ toReal input)
    {budget : Certified.Budget} : isFinite (logPlus1 input budget) = true := by
  have hbelow := abs_lt_overflowThreshold_of_toReal_eq_roundAt hfmt hinput
    (roundAt_toReal_eq input hinput).symm
  rw [abs_of_nonneg hnonneg] at hbelow
  refine isFinite_logPlus1 hfmt hinput (by linarith) ?_
  rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
  linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + toReal input)]

/-- `logPlus1` of a finite positive input is positive. -/
theorem toReal_logPlus1_pos (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (hpositive : 0 < toReal input)
    {budget : Certified.Budget} : 0 < toReal (logPlus1 input budget) := by
  have h := two_mul_underflowErrorAt_le_abs_toReal hinput hpositive.ne'
  rw [abs_of_pos hpositive] at h
  have hη := underflowErrorAt_pos fmt
  have hquarter := underflowErrorAt_le_quarter (fmt := fmt)
  have hshift : 0 < 1 + toReal input := by linarith
  rw [toReal_logPlus1_of_isFinite hfmt hinput (by linarith)
    (isFinite_logPlus1_of_nonneg hfmt hinput hpositive.le)]
  refine roundAt_pos fmt (lt_of_lt_of_le ?_ (Real.one_sub_inv_le_log_of_pos hshift))
  rw [show 1 - (1 + toReal input)⁻¹ = toReal input / (1 + toReal input) by field_simp; ring,
    lt_div_iff₀ hshift]
  nlinarith

/-- The weighted exponential of finite operands with a nonnegative weight is nonnegative. -/
theorem toReal_expMul_nonneg (hfmt : fmt.isIEEE = true) {input weight : Model fmt}
    (hinput : isFinite input = true) (hweight : isFinite weight = true)
    (hnonneg : 0 ≤ toReal weight) {budget : Certified.Budget} :
    0 ≤ toReal (expMul input weight budget) := by
  cases hfinite : isFinite (expMul input weight budget)
  · rw [toReal_eq_zero_of_isFinite_eq_false hfinite]
  · rw [toReal_expMul_of_isFinite hfmt hinput hweight hfinite]
    simpa using roundAt_mono fmt (mul_nonneg (Real.exp_pos _).le hnonneg)

/-- The weighted exponential of finite operands with a nonpositive weight is nonpositive. -/
theorem toReal_expMul_nonpos (hfmt : fmt.isIEEE = true) {input weight : Model fmt}
    (hinput : isFinite input = true) (hweight : isFinite weight = true)
    (hnonpos : toReal weight ≤ 0) {budget : Certified.Budget} :
    toReal (expMul input weight budget) ≤ 0 := by
  cases hfinite : isFinite (expMul input weight budget)
  · rw [toReal_eq_zero_of_isFinite_eq_false hfinite]
  · rw [toReal_expMul_of_isFinite hfmt hinput hweight hfinite]
    simpa using roundAt_mono fmt (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hnonpos)

/--
The weighted exponential of finite operands is positive when its exact result exceeds
`underflowErrorAt fmt` and is below the overflow threshold.
-/
theorem toReal_expMul_pos (hfmt : fmt.isIEEE = true) {input weight : Model fmt}
    (hinput : isFinite input = true) (hweight : isFinite weight = true)
    (hrange : |Real.exp (toReal input) * toReal weight| < Certified.overflowThreshold fmt)
    (hlarge : underflowErrorAt fmt < Real.exp (toReal input) * toReal weight)
    {budget : Certified.Budget} : 0 < toReal (expMul input weight budget) := by
  rw [toReal_expMul_eq_roundAt hfmt hinput hweight hrange]
  exact roundAt_pos fmt hlarge

/--
The weighted exponential of finite operands is negative when its exact result is below
`-underflowErrorAt fmt` and above minus the overflow threshold.
-/
theorem toReal_expMul_lt_zero (hfmt : fmt.isIEEE = true) {input weight : Model fmt}
    (hinput : isFinite input = true) (hweight : isFinite weight = true)
    (hrange : |Real.exp (toReal input) * toReal weight| < Certified.overflowThreshold fmt)
    (hlarge : Real.exp (toReal input) * toReal weight < -underflowErrorAt fmt)
    {budget : Certified.Budget} : toReal (expMul input weight budget) < 0 := by
  rw [toReal_expMul_eq_roundAt hfmt hinput hweight hrange]
  exact roundAt_lt_zero fmt hlarge

/-! ## Agreement with the certified search -/

/-- The exponential returns the certified result whenever the certified search does. -/
theorem exp_eq_of_certified_exp_eq_ok {input result : Model fmt} {budget : Certified.Budget}
    (hresult : Certified.exp input budget = .ok result) : exp input budget = result := by
  unfold Certified.exp at hresult
  split at hresult
  · simp at hresult
  · cases hdecode : toRat? input with
    | none => simp [hdecode] at hresult
    | some argument =>
        rw [hdecode] at hresult
        rw [exp_eq_expRat hdecode, expRat_eq_of_certified_expRat_eq_ok hresult]

/-- `expMinus1` returns the certified result whenever the certified search does. -/
theorem expMinus1_eq_of_certified_expMinus1_eq_ok {input result : Model fmt}
    {budget : Certified.Budget} (hresult : Certified.expMinus1 input budget = .ok result) :
    expMinus1 input budget = result := by
  unfold Certified.expMinus1 at hresult
  split at hresult
  · simp at hresult
  · split at hresult
    · rename_i hzero
      cases Except.ok.inj hresult
      exact expMinus1_of_isZero hzero budget
    · rename_i hzero
      cases hdecode : toRat? input with
      | none => simp [hdecode] at hresult
      | some argument =>
          rw [hdecode] at hresult
          have hargument : argument ≠ 0 := by
            rintro rfl
            exact hzero (isZero_of_toRat?_eq_some_zero hdecode)
          rw [expMinus1_eq_expMinus1Rat hdecode hargument,
            expMinus1Rat_eq_of_certified_expMinus1Rat_eq_ok hresult]

private theorem signBit_roundEndpoint (hfmt : fmt.isIEEE = true) (value : ℚ) (scale : ℤ) :
    signBit (Enclosure.roundEndpoint fmt value scale) = decide (value < 0) := by
  have hround (sign : Bool) (num den : Nat) (exponent : Int) (hden : den ≠ 0) :
      signBit (ieeeRoundRatScaled fmt sign num den exponent hfmt) = sign := by
    unfold ieeeRoundRatScaled
    simp only [beq_iff_eq, hden, ite_false]
    split_ifs <;> (try split) <;> simp_all
  rw [Enclosure.roundEndpoint, roundRatScaled, dite_eq_left hfmt, hround _ _ _ _ value.den_nz]

/-- An accepted enclosure gives the sign of the value it contains, also to a zero result. -/
private theorem signBit_of_round?_eq_some (hfmt : fmt.isIEEE = true)
    {interval : RationalInterval} {target : ℝ} {result : Model fmt}
    (hcontains : interval.Contains target) (hresult : Enclosure.round? fmt interval = some result) :
    signBit result = decide (target < 0) := by
  obtain ⟨-, -, hlo, hhi⟩ := Enclosure.accepted hresult
  by_cases hnegative : target < 0
  · rw [← hlo, signBit_roundEndpoint hfmt, decide_eq_true hnegative]
    exact decide_eq_true (by exact_mod_cast hcontains.1.trans_lt hnegative)
  · have hupper : (0 : ℝ) ≤ interval.hi := (le_of_not_gt hnegative).trans hcontains.2
    rw [← hhi, signBit_roundEndpoint hfmt, decide_eq_false hnegative]
    exact decide_eq_false (not_lt.mpr (by exact_mod_cast hupper))

/-- A zero from exact-comparison rounding carries the requested sign. -/
private theorem signBit_round_of_toReal_eq_zero (hfmt : fmt.isIEEE = true) {sign : Bool}
    {compare : ℚ → Ordering} {target : ℝ} (hnonneg : 0 ≤ target)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (hfinite : isFinite (AlgebraicRounding.round fmt sign compare) = true)
    (hzero : toReal (AlgebraicRounding.round fmt sign compare) = 0) :
    signBit (AlgebraicRounding.round fmt sign compare) = sign := by
  have hround := AlgebraicRounding.toReal_round_eq_roundAt fmt hfmt sign compare target hnonneg
    hcompare hfinite
  rw [hzero] at hround
  have hsmall : target ≤ underflowErrorAt fmt := by
    have h := abs_le_underflowErrorAt_of_roundAt_eq_zero fmt hround.symm
    cases sign <;> simpa [abs_of_nonneg hnonneg] using h
  have hbranch :
      compare (AlgebraicRounding.powerOfTwo (AlgebraicRounding.lowerExponent fmt)) ≠ .gt := by
    rw [hcompare, AlgebraicRounding.cast_powerOfTwo, ne_eq, cmp_eq_gt_iff]
    exact not_lt.mpr hsmall
  rw [AlgebraicRounding.round, ite_eq_left hbranch, signBit_zero,
    FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt, Bool.and_true]

/-- Finite values with the same real value, and the same sign when it is zero, are equal. -/
private theorem eq_of_toReal_eq {x y : Model fmt} (hx : isFinite x = true)
    (hy : isFinite y = true) (hvalue : toReal x = toReal y)
    (hsign : toReal x = 0 → signBit x = signBit y) : x = y := by
  by_cases hzero : toReal x = 0
  · have hxzero := (isZero_eq_true_iff_toReal_eq_zero x hx).mpr hzero
    have hyzero := (isZero_eq_true_iff_toReal_eq_zero y hy).mpr (hvalue ▸ hzero)
    have hdecode := toDyadic?_eq_zero_of_isZero_eq_true y hyzero
    rw [← hsign hzero] at hdecode
    exact eq_of_toDyadic?_eq_some (toDyadic?_eq_zero_of_isZero_eq_true x hxzero) hdecode
  · exact eq_of_toReal_eq_of_nonzero hvalue hzero

private theorem exists_enclosure_of_certified_logRat_eq_ok {argument : ℚ}
    {budget : Certified.Budget} {result : Model fmt}
    (hresult : Certified.logRat fmt argument budget = .ok result) :
    ∃ interval : RationalInterval, interval.Contains (Real.log argument) ∧
      Enclosure.round? fmt interval = some result := by
  rw [Certified.logRat] at hresult
  split at hresult
  · simp at hresult
  · split at hresult
    · simp at hresult
    · rename_i hpositive
      split at hresult
      · rename_i hone
        exact ⟨RationalInterval.point 0,
          by simpa [hone] using RationalInterval.contains_point (0 : ℚ),
          Certified.accept_eq_ok.mp hresult⟩
      · obtain ⟨degree, precision, haccept⟩ :=
          RationalInterval.exists_of_refine_eq_some (Certified.accept_eq_ok.mp hresult)
        exact ⟨_, FloatLib.Numerics.Enclosure.BinaryGrid.contains_log argument degree precision
          (lt_of_not_ge hpositive), haccept⟩

private theorem isIEEE_of_certified_logRat_eq_ok {argument : ℚ} {budget : Certified.Budget}
    {result : Model fmt} (hresult : Certified.logRat fmt argument budget = .ok result) :
    fmt.isIEEE = true := by
  by_contra hfmt
  simp [Certified.logRat, Bool.eq_false_iff.mpr hfmt] at hresult

/-- `logRat` returns the certified logarithm whenever the certified search does. -/
theorem logRat_eq_of_certified_logRat_eq_ok {argument : ℚ} (hpositive : 0 < argument)
    {budget : Certified.Budget} {result : Model fmt}
    (hresult : Certified.logRat fmt argument budget = .ok result) :
    logRat fmt argument hpositive budget = result := by
  have hfmt := isIEEE_of_certified_logRat_eq_ok hresult
  obtain ⟨interval, hcontains, haccept⟩ := exists_enclosure_of_certified_logRat_eq_ok hresult
  have hfinite := Enclosure.isFinite_of_round?_eq_some haccept
  have hvalue := Enclosure.toReal_eq_roundAt_of_round?_eq_some hcontains haccept
  have hrange := abs_lt_overflowThreshold_of_toReal_eq_roundAt hfmt hfinite hvalue
  have hfinite' := isFinite_logRat hfmt hpositive hrange budget
  refine eq_of_toReal_eq hfinite' hfinite ((toReal_logRat hfmt hpositive hfinite').trans
    hvalue.symm) fun hzero => ?_
  rw [signBit_of_round?_eq_some hfmt hcontains haccept]
  cases hsearch : logSearch fmt argument budget with
  | some found =>
      obtain ⟨interval', hcontains', haccept'⟩ :=
        exists_enclosure_of_logSearch_eq_some hpositive hsearch
      simp only [logRat, hsearch]
      exact signBit_of_round?_eq_some hfmt hcontains' haccept'
  | none =>
      simp only [logRat, hsearch] at hfinite' hzero ⊢
      rw [signBit_round_of_toReal_eq_zero hfmt (abs_nonneg _)
        (compareAbsLog_eq_real argument hpositive) hfinite' hzero]
      have hiff : Real.log (argument : ℝ) < 0 ↔ argument < 1 := by
        rw [Real.log_neg_iff (by exact_mod_cast hpositive)]
        exact_mod_cast Iff.rfl
      exact decide_eq_decide.mpr hiff.symm

/-- The logarithm returns the certified result whenever the certified search does. -/
theorem log_eq_of_certified_log_eq_ok {input result : Model fmt} {budget : Certified.Budget}
    (hresult : Certified.log input budget = .ok result) : log input budget = result := by
  unfold Certified.log at hresult
  split at hresult
  · simp at hresult
  · cases hdecode : toRat? input with
    | none => simp [hdecode] at hresult
    | some argument =>
        rw [hdecode] at hresult
        have hpositive : 0 < argument := by
          by_contra hnonpositive
          simp [Certified.logRat, isIEEE_of_certified_logRat_eq_ok hresult,
            le_of_not_gt hnonpositive] at hresult
        rw [log_eq_logRat hdecode hpositive, logRat_eq_of_certified_logRat_eq_ok hpositive hresult]

/-- `logPlus1` returns the certified result whenever the certified search does. -/
theorem logPlus1_eq_of_certified_logPlus1_eq_ok {input result : Model fmt}
    {budget : Certified.Budget} (hresult : Certified.logPlus1 input budget = .ok result) :
    logPlus1 input budget = result := by
  unfold Certified.logPlus1 at hresult
  split at hresult
  · simp at hresult
  · split at hresult
    · rename_i hzero
      cases Except.ok.inj hresult
      exact logPlus1_of_isZero hzero budget
    · rename_i hzero
      cases hdecode : toRat? input with
      | none => simp [hdecode] at hresult
      | some argument =>
          rw [hdecode] at hresult
          have hargument : argument ≠ 0 := by
            rintro rfl
            exact hzero (isZero_of_toRat?_eq_some_zero hdecode)
          have hpositive : 0 < 1 + argument := by
            by_contra hnonpositive
            simp [Certified.logPlus1Rat, Certified.logRat,
              isIEEE_of_certified_logRat_eq_ok hresult, le_of_not_gt hnonpositive] at hresult
          rw [logPlus1_eq_logRat hdecode hargument hpositive,
            logRat_eq_of_certified_logRat_eq_ok hpositive hresult]

/-! ## Contracts -/

/--
The exponential is correctly rounded on every finite input whose exact result is below the overflow
threshold.
-/
theorem exp_correctlyRoundedCertificateOn (hfmt : fmt.isIEEE = true)
    (budget : Certified.Budget) :
    Contract.CorrectlyRoundedCertificateOn fmt Real.exp (fun input => exp input budget)
      (fun input => Real.exp (toReal input) < Certified.overflowThreshold fmt) :=
  ⟨fun _ hinput hrange => isFinite_exp hfmt hinput hrange,
    fun _ hinput hrange => toReal_exp_eq_roundAt hfmt hinput hrange⟩

/--
`expMinus1` is correctly rounded on every finite input whose exact result is below the overflow
threshold.
-/
theorem expMinus1_correctlyRoundedCertificateOn (hfmt : fmt.isIEEE = true)
    (budget : Certified.Budget) :
    Contract.CorrectlyRoundedCertificateOn fmt (fun x => Real.exp x - 1)
      (fun input => expMinus1 input budget)
      (fun input => Real.exp (toReal input) - 1 < Certified.overflowThreshold fmt) :=
  ⟨fun _ hinput hrange => isFinite_expMinus1 hfmt hinput hrange,
    fun _ hinput hrange => toReal_expMinus1_eq_roundAt hfmt hinput hrange⟩

/--
The logarithm is correctly rounded on every finite positive input whose exact result is below the
overflow threshold in magnitude.
-/
theorem log_correctlyRoundedCertificateOn (hfmt : fmt.isIEEE = true)
    (budget : Certified.Budget) :
    Contract.CorrectlyRoundedCertificateOn fmt Real.log (fun input => log input budget)
      (fun input => 0 < toReal input ∧
        |Real.log (toReal input)| < Certified.overflowThreshold fmt) :=
  ⟨fun _ hinput hdomain => isFinite_log hfmt hinput hdomain.1 hdomain.2,
    fun _ hinput hdomain => toReal_log_eq_roundAt hfmt hinput hdomain.1 hdomain.2⟩

/--
`logPlus1` is correctly rounded on every finite input above `-1` whose exact result is below the
overflow threshold in magnitude.
-/
theorem logPlus1_correctlyRoundedCertificateOn (hfmt : fmt.isIEEE = true)
    (budget : Certified.Budget) :
    Contract.CorrectlyRoundedCertificateOn fmt (fun x => Real.log (1 + x))
      (fun input => logPlus1 input budget)
      (fun input => -1 < toReal input ∧
        |Real.log (1 + toReal input)| < Certified.overflowThreshold fmt) :=
  ⟨fun _ hinput hdomain => isFinite_logPlus1 hfmt hinput hdomain.1 hdomain.2,
    fun _ hinput hdomain => toReal_logPlus1_eq_roundAt hfmt hinput hdomain.1 hdomain.2⟩

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.CorrectlyRounded
