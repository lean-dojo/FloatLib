/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.Directed
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError.Attribute
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.CorrectlyRounded.Proof
public import FloatLib.Numerics.MixedError.Elementary

/-!
# `exp x - 1 - x`, correctly rounded in every rounding attribute

`expm1x x` is `exp x - 1 - x`, the exponential without the first two terms of its series, rounded
once. The name is that of the function in R's package DPQ (M. Maechler, `expm1x`: "accurate
`exp(x) - 1 - x`, notably for small `|x|`"); the GNU Scientific Library has the scaled form
`gsl_sf_exprel_2 x = 2 (exp x - 1 - x) / x ^ 2`, and exponential integrators call
`(exp x - 1 - x) / x ^ 2` the function `φ₂`. Near zero the three terms cancel: for `x = 2⁻³⁰` in
binary64 the expression `exp x - 1 - x` loses every digit, where the value is `x² / 2` to first
order. The function serves formulations that are sums of nonnegative terms, such as the relative
entropy `∑ p i * (exp s i - 1 - s i)` with `s i = log (q i / p i)`.

The rounding is decided by exact comparisons of `exp x` with rational candidates
(`ElementaryComparison.compareExp`), never by subtracting rounded values, so no cancellation
occurs at any argument. For a nonzero rational `x` the value is irrational, so no candidate
equals it and both nearest attributes round alike.

* `expm1x input mode` returns, for a finite nonzero input, the rounding in `mode` of the real
  value: `AlgebraicRounding.round` for the two nearest attributes, `roundDown` for `down` and
  `towardZero`, and `roundUp` for `up` and `away` (the value is positive).
* `toReal_expm1x_of_isFinite`: for an IEEE descriptor, a finite input and a finite result whose
  real value is below `2 ^ (emax + 1)`, the result is `roundAt fmt (exp x - 1 - x) mode`, in
  every one of the six attributes.
* `isFinite_expm1x`: the result is finite in the nearest and the downward attributes when the
  real value is below the overflow threshold.
* `isFinite_expm1x_of_le_posMaxFinite`, `toReal_expm1x_eq_roundAt_of_le_posMaxFinite`: when the
  real value is at most the largest finite value, the result is finite and correctly rounded in
  every one of the six attributes. An upward rounding of a value between the largest finite
  value and the overflow threshold is `+∞`, so the two upward attributes need this range.
* `mixedError_toReal_expm1x`: the result has the mixed error of one rounding in its attribute,
  `unitRoundoffIn fmt mode` and `underflowErrorIn fmt mode`.
* `toReal_expm1x_nonneg`: the result is never negative, for any input and attribute.

The function of this module has no enclosure search before its comparisons, unlike `exp` and
`expm1`: it is correct at every precision and slower than they are.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.CorrectlyRounded

open FloatLib.Numerics FloatLib.Floats.Formats.Flocq

variable {fmt : FloatFormat}

/-! ## The real function -/

/-- `exp q - 1 - q` is irrational for a nonzero rational `q`. -/
theorem irrational_exp_sub_one_sub (q : ℚ) (hq : q ≠ 0) :
    Irrational (Real.exp (q : ℝ) - 1 - q) := by
  have h := (Enclosure.irrational_exp_ratCast q hq).sub_ratCast (q := 1 + q)
  rwa [show Real.exp (q : ℝ) - ((1 + q : ℚ) : ℝ) = Real.exp (q : ℝ) - 1 - q by
    push_cast; ring] at h

/-! ## Rounding off the rationals -/

/-- A value of the format is rational. -/
private theorem exists_ratCast_of_genericFormat {x : ℝ}
    (hx : GenericRepresentable binaryRadix (fexpOf fmt) x) : ∃ q : ℚ, x = q := by
  obtain ⟨n, hn⟩ := exists_int_mul_bpow_cexp_of_generic hx
  refine ⟨n * (2 : ℚ) ^ cexp binaryRadix (fexpOf fmt) x, hn.trans ?_⟩
  simp [Flocq.bpow, binaryRadix, Radix.toReal]

/-- Off the rationals the two nearest attributes round alike: a tie is the midpoint of two values
of the format, which is rational. -/
theorem roundAt_nearestAway_eq_of_irrational (fmt : FloatFormat) {t : ℝ} (ht : Irrational t) :
    roundAt fmt t .nearestAway = roundAt fmt t .nearest := by
  have haway := round_toNearest_error_le (β := binaryRadix) (fexp := fexpOf fmt)
    (nearestChoice nearestAwayChoice) nearestEven t
  have heven := round_toNearest_error_le (β := binaryRadix) (fexp := fexpOf fmt)
    nearestEven (nearestChoice nearestAwayChoice) t
  change round (β := binaryRadix) (fexp := fexpOf fmt) (nearestChoice nearestAwayChoice) t =
    round (β := binaryRadix) (fexp := fexpOf fmt) nearestEven t
  rcases abs_eq_abs.mp (le_antisymm haway heven) with hsame | hopposite
  · linarith
  · -- The two roundings are on opposite sides at one distance: `t` is their midpoint.
    obtain ⟨a, ha⟩ := exists_ratCast_of_genericFormat (fmt := fmt)
      (genericRepresentable_round (nearestChoice nearestAwayChoice) t)
    obtain ⟨b, hb⟩ := exists_ratCast_of_genericFormat (fmt := fmt)
      (genericRepresentable_round nearestEven t)
    exact absurd ⟨(a + b) / 2, by push_cast; rw [← ha, ← hb]; linarith⟩ ht

/-! ## Rational arguments -/

/-- Compare `exp argument - 1 - argument` with a rational boundary: a comparison of
`exp argument` with `boundary + 1 + argument`. -/
def compareExpm1x (argument boundary : ℚ) : Ordering :=
  ElementaryComparison.compareExp argument (boundary + 1 + argument)

/-- The comparison of `compareExpm1x` is that of the real value with the boundary. -/
theorem compareExpm1x_eq_real (argument boundary : ℚ) :
    compareExpm1x argument boundary =
      cmp (Real.exp (argument : ℝ) - 1 - argument) (boundary : ℝ) := by
  rw [compareExpm1x, ElementaryComparison.compareExp_eq_real]
  have hlt : Real.exp (argument : ℝ) < ((boundary + 1 + argument : ℚ) : ℝ) ↔
      Real.exp (argument : ℝ) - 1 - argument < boundary := by
    push_cast
    constructor <;> intro h <;> linarith
  have hgt : ((boundary + 1 + argument : ℚ) : ℝ) < Real.exp (argument : ℝ) ↔
      (boundary : ℝ) < Real.exp (argument : ℝ) - 1 - argument := by
    push_cast
    constructor <;> intro h <;> linarith
  simp only [cmp, cmpUsing, hlt, hgt]

/-- Round `exp argument - 1 - argument` in the attribute `mode`, for a nonzero rational: nearest
rounding for the two nearest attributes, and the downward or upward rounding of the positive
value for the directed ones. -/
def expm1xRat (fmt : FloatFormat) (argument : ℚ) (mode : IEEERoundingMode := .nearest) :
    Model fmt :=
  match mode with
  | .nearest | .nearestAway => AlgebraicRounding.round fmt false (compareExpm1x argument)
  | .towardZero | .down => AlgebraicRounding.roundDown fmt (compareExpm1x argument)
  | .up | .away => AlgebraicRounding.roundUp fmt (compareExpm1x argument)

/-- A finite `expm1xRat` of a nonzero rational whose value is below `2 ^ (emax + 1)` is the
rounding of the real value in its attribute. -/
theorem toReal_expm1xRat (hfmt : fmt.isIEEE = true) {argument : ℚ} (hargument : argument ≠ 0)
    (mode : IEEERoundingMode) (hfinite : isFinite (expm1xRat fmt argument mode) = true)
    (hrange : Real.exp (argument : ℝ) - 1 - argument <
      Flocq.bpow binaryRadix (fmt.maxNormalExponent + 1)) :
    toReal (expm1xRat fmt argument mode) =
      roundAt fmt (Real.exp (argument : ℝ) - 1 - argument) mode := by
  have hreal : (argument : ℝ) ≠ 0 := by exact_mod_cast hargument
  have hpos := exp_sub_one_sub_pos hreal
  have hcompare := compareExpm1x_eq_real argument
  have hnearest : isFinite (AlgebraicRounding.round fmt false (compareExpm1x argument)) = true →
      toReal (AlgebraicRounding.round fmt false (compareExpm1x argument)) =
        roundAt fmt (Real.exp (argument : ℝ) - 1 - argument) := fun hround => by
    simpa using AlgebraicRounding.toReal_round_eq_roundAt fmt hfmt false _ _ hpos.le hcompare
      hround
  have hdown := AlgebraicRounding.toReal_roundDown_eq_roundAt fmt hfmt _ _ hpos hcompare hrange
  have hup := AlgebraicRounding.roundUp_eq_posInf_or_finite_roundAt fmt hfmt _ _ hpos hcompare
  have hinfinity := isFinite_posInf fmt (FloatFormat.supportsInfinity_eq_true_of_isIEEE fmt hfmt)
  cases mode with
  | nearest => exact hnearest hfinite
  | nearestAway =>
      rw [roundAt_nearestAway_eq_of_irrational fmt (irrational_exp_sub_one_sub argument hargument)]
      exact hnearest hfinite
  | towardZero =>
      rw [roundAt_of_nonneg fmt (by decide) (by decide) hpos.le]
      exact hdown
  | down => exact hdown
  | up =>
      rcases hup with hinf | ⟨-, hround⟩
      · simp [expm1xRat, hinf, hinfinity] at hfinite
      · exact hround
  | away =>
      rw [roundAt_of_nonneg fmt (by decide) (by decide) hpos.le]
      rcases hup with hinf | ⟨-, hround⟩
      · simp [expm1xRat, hinf, hinfinity] at hfinite
      · exact hround

/-- `expm1xRat` is finite in the nearest and the downward attributes when the real value is
below the overflow threshold. -/
theorem isFinite_expm1xRat (hfmt : fmt.isIEEE = true) (argument : ℚ) {mode : IEEERoundingMode}
    (hmode : mode.roundsAwayFromZero false = false)
    (hrange : Real.exp (argument : ℝ) - 1 - argument < Certified.overflowThreshold fmt) :
    isFinite (expm1xRat fmt argument mode) = true := by
  have hnearest := AlgebraicRounding.isFinite_round_of_lt_overflow fmt hfmt false _ _
    (compareExpm1x_eq_real argument) (cast_overflowThreshold fmt ▸ hrange)
  cases mode with
  | nearest => exact hnearest
  | nearestAway => exact hnearest
  | towardZero => exact AlgebraicRounding.isFinite_roundDown fmt _
  | down => exact AlgebraicRounding.isFinite_roundDown fmt _
  | up => simp [IEEERoundingMode.roundsAwayFromZero] at hmode
  | away => simp [IEEERoundingMode.roundsAwayFromZero] at hmode

/-- A real at most the largest finite value is below the overflow threshold. -/
theorem lt_overflowThreshold_of_le_posMaxFinite (hfmt : fmt.isIEEE = true) {t : ℝ}
    (ht : t ≤ toReal (posMaxFinite fmt)) : t < Certified.overflowThreshold fmt := by
  by_contra hge
  have hthreshold := roundAt_mono fmt (not_lt.mp hge)
  have hmaximum := roundAt_mono fmt ht
  rw [roundAt_overflowThreshold hfmt] at hthreshold
  rw [roundAt_of_genericFormat fmt
    (toReal_genericFormat_of_isFinite _ (isFinite_posMaxFinite fmt))] at hmaximum
  exact absurd (hthreshold.trans hmaximum) (not_le.mpr (toReal_posMaxFinite_lt_bpow fmt))

/-- `expm1xRat` of a nonzero rational is finite in every attribute when the real value is at most
the largest finite value. -/
theorem isFinite_expm1xRat_of_le_posMaxFinite (hfmt : fmt.isIEEE = true) {argument : ℚ}
    (hargument : argument ≠ 0) (mode : IEEERoundingMode)
    (hrange : Real.exp (argument : ℝ) - 1 - argument ≤ toReal (posMaxFinite fmt)) :
    isFinite (expm1xRat fmt argument mode) = true := by
  have hreal : (argument : ℝ) ≠ 0 := by exact_mod_cast hargument
  have hlt := lt_overflowThreshold_of_le_posMaxFinite hfmt hrange
  have hup := (AlgebraicRounding.roundUp_finite_roundAt_of_le_posMaxFinite fmt _ _
    (exp_sub_one_sub_pos hreal) (compareExpm1x_eq_real argument) hrange).1
  cases mode with
  | nearest => exact isFinite_expm1xRat hfmt argument rfl hlt
  | nearestAway => exact isFinite_expm1xRat hfmt argument rfl hlt
  | towardZero => exact isFinite_expm1xRat hfmt argument rfl hlt
  | down => exact isFinite_expm1xRat hfmt argument rfl hlt
  | up => exact hup
  | away => exact hup

/-! ## Encoded inputs -/

/-- `exp x - 1 - x` with one rounding in the attribute `mode`, correctly rounded for every finite
input of an IEEE descriptor, at every precision.

NaNs are quieted, both infinities give `+∞`, and either zero gives `+0`. -/
def expm1x {fmt : FloatFormat} (input : Model fmt) (mode : IEEERoundingMode := .nearest) :
    Model fmt :=
  if isNaN input then quietNaN input
  else if isInfinite input then nativeOverflow fmt false
  else if isZero input then zero fmt false
  else
    match toRat? input with
    | some argument => expm1xRat fmt argument mode
    | none => invalidResult fmt

/-- `expm1x` of a zero is the positive zero. -/
@[simp] theorem expm1x_of_isZero {input : Model fmt} (hzero : isZero input = true)
    (mode : IEEERoundingMode) : expm1x input mode = zero fmt false := by
  have hfinite := isFinite_eq_true_of_isZero_eq_true input hzero
  simp [expm1x, isNaN_eq_false_of_isFinite_eq_true input hfinite,
    isInfinite_eq_false_of_isFinite_eq_true input hfinite, hzero]

/-- `expm1x` of a finite nonzero input is `expm1xRat` at its exact value. -/
theorem expm1x_eq_expm1xRat {input : Model fmt} {argument : ℚ}
    (hinput : toRat? input = some argument) (hzero : isZero input = false)
    (mode : IEEERoundingMode) : expm1x input mode = expm1xRat fmt argument mode := by
  have hfinite := Algebraic.isFinite_of_toRat?_eq_some hinput
  simp [expm1x, isNaN_eq_false_of_isFinite_eq_true input hfinite,
    isInfinite_eq_false_of_isFinite_eq_true input hfinite, hzero, hinput]

/-- A finite input is a zero, or it decodes to a nonzero rational. -/
private theorem isZero_or_exists_toRat? {input : Model fmt} (hinput : isFinite input = true) :
    (isZero input = true ∧ toReal input = 0) ∨
      ∃ argument : ℚ, toRat? input = some argument ∧ toReal input = argument ∧
        argument ≠ 0 ∧ isZero input = false := by
  obtain ⟨argument, hdecode, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hinput
  by_cases hzero : isZero input = true
  · exact Or.inl ⟨hzero, toReal_eq_zero_of_isZero input hzero⟩
  · refine Or.inr ⟨argument, hdecode, hreal, fun hargument => hzero ?_, by simpa using hzero⟩
    exact (isZero_eq_true_iff_toReal_eq_zero input hinput).mpr (by rw [hreal, hargument]; simp)

/-- A finite `expm1x` of a finite input whose real value is below `2 ^ (emax + 1)` is the
rounding of `exp x - 1 - x` in its attribute, in every one of the six attributes. -/
theorem toReal_expm1x_of_isFinite (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (mode : IEEERoundingMode)
    (hfinite : isFinite (expm1x input mode) = true)
    (hrange : Real.exp (toReal input) - 1 - toReal input <
      Flocq.bpow binaryRadix (fmt.maxNormalExponent + 1)) :
    toReal (expm1x input mode) =
      roundAt fmt (Real.exp (toReal input) - 1 - toReal input) mode := by
  rcases isZero_or_exists_toRat? hinput with ⟨hzero, hreal⟩ | ⟨argument, hdecode, hreal, hne, hz⟩
  · rw [expm1x_of_isZero hzero, hreal]
    simp
  · rw [expm1x_eq_expm1xRat hdecode hz] at hfinite ⊢
    rw [hreal] at hrange ⊢
    exact toReal_expm1xRat hfmt hne mode hfinite hrange

/-- `expm1x` of a finite input is finite in the nearest and the downward attributes when the real
value is below the overflow threshold. -/
theorem isFinite_expm1x (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) {mode : IEEERoundingMode}
    (hmode : mode.roundsAwayFromZero false = false)
    (hrange : Real.exp (toReal input) - 1 - toReal input < Certified.overflowThreshold fmt) :
    isFinite (expm1x input mode) = true := by
  rcases isZero_or_exists_toRat? hinput with ⟨hzero, -⟩ | ⟨argument, hdecode, hreal, -, hz⟩
  · rw [expm1x_of_isZero hzero]
    exact isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt false)
  · rw [expm1x_eq_expm1xRat hdecode hz]
    exact isFinite_expm1xRat hfmt argument hmode (hreal ▸ hrange)

/-- The overflow threshold is below `2 ^ (emax + 1)`. -/
theorem overflowThreshold_lt_bpow (fmt : FloatFormat) :
    (Certified.overflowThreshold fmt : ℝ) < Flocq.bpow binaryRadix (fmt.maxNormalExponent + 1) := by
  rw [cast_overflowThreshold]
  linarith [Flocq.bpow.pos binaryRadix (fmt.maxNormalExponent - fmt.fracWidth - 1)]

/-- `expm1x` of a finite input is correctly rounded in the nearest and the downward attributes
when the real value is below the overflow threshold. -/
theorem toReal_expm1x_eq_roundAt (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) {mode : IEEERoundingMode}
    (hmode : mode.roundsAwayFromZero false = false)
    (hrange : Real.exp (toReal input) - 1 - toReal input < Certified.overflowThreshold fmt) :
    toReal (expm1x input mode) =
      roundAt fmt (Real.exp (toReal input) - 1 - toReal input) mode :=
  toReal_expm1x_of_isFinite hfmt hinput mode (isFinite_expm1x hfmt hinput hmode hrange)
    (hrange.trans (overflowThreshold_lt_bpow fmt))

/-- `expm1x` of a finite input is finite in every attribute when the real value is at most the
largest finite value. -/
theorem isFinite_expm1x_of_le_posMaxFinite (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (mode : IEEERoundingMode)
    (hrange : Real.exp (toReal input) - 1 - toReal input ≤ toReal (posMaxFinite fmt)) :
    isFinite (expm1x input mode) = true := by
  rcases isZero_or_exists_toRat? hinput with ⟨hzero, -⟩ | ⟨argument, hdecode, hreal, hne, hz⟩
  · rw [expm1x_of_isZero hzero]
    exact isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt false)
  · rw [expm1x_eq_expm1xRat hdecode hz]
    exact isFinite_expm1xRat_of_le_posMaxFinite hfmt hne mode (hreal ▸ hrange)

/-- `expm1x` of a finite input is correctly rounded in every attribute when the real value is at
most the largest finite value. -/
theorem toReal_expm1x_eq_roundAt_of_le_posMaxFinite (hfmt : fmt.isIEEE = true)
    {input : Model fmt} (hinput : isFinite input = true) (mode : IEEERoundingMode)
    (hrange : Real.exp (toReal input) - 1 - toReal input ≤ toReal (posMaxFinite fmt)) :
    toReal (expm1x input mode) =
      roundAt fmt (Real.exp (toReal input) - 1 - toReal input) mode :=
  toReal_expm1x_of_isFinite hfmt hinput mode
    (isFinite_expm1x_of_le_posMaxFinite hfmt hinput mode hrange)
    (hrange.trans_lt (toReal_posMaxFinite_lt_bpow fmt))

/-- A finite `expm1x` of a finite input whose real value is below `2 ^ (emax + 1)` has the mixed
error of one rounding in its attribute. -/
theorem mixedError_toReal_expm1x (hfmt : fmt.isIEEE = true) {input : Model fmt}
    (hinput : isFinite input = true) (mode : IEEERoundingMode)
    (hfinite : isFinite (expm1x input mode) = true)
    (hrange : Real.exp (toReal input) - 1 - toReal input <
      Flocq.bpow binaryRadix (fmt.maxNormalExponent + 1)) :
    MixedError (toReal (expm1x input mode)) (Real.exp (toReal input) - 1 - toReal input)
      (unitRoundoffIn fmt mode) (underflowErrorIn fmt mode) :=
  mixedError_toReal_of_eq_roundAt_mode
    (toReal_expm1x_of_isFinite hfmt hinput mode hfinite hrange)

/-- `expm1x` never has a negative real value, for any input and in any attribute: a NaN or an
infinity has real value zero, and every rounding of a nonnegative value is nonnegative. -/
theorem toReal_expm1x_nonneg (hfmt : fmt.isIEEE = true) (input : Model fmt)
    (mode : IEEERoundingMode) : 0 ≤ toReal (expm1x input mode) := by
  unfold expm1x
  split_ifs with hnan hinf hzero
  · cases hfinite : isFinite (quietNaN input)
    · rw [toReal_eq_zero_of_isFinite_eq_false hfinite]
    · rw [isFinite_quietNaN] at hfinite
      exact absurd hnan (by simp [isNaN_eq_false_of_isFinite_eq_true input hfinite])
  · exact toReal_nativeOverflow_false_nonneg fmt
  · simp
  · split
    · rename_i argument _
      have hnearest :
          0 ≤ toReal (AlgebraicRounding.round fmt false (compareExpm1x argument)) := by
        cases hfinite : isFinite (AlgebraicRounding.round fmt false (compareExpm1x argument))
        · rw [toReal_eq_zero_of_isFinite_eq_false hfinite]
        · have h := AlgebraicRounding.toReal_round_eq_roundAt fmt hfmt false _ _
            (exp_sub_one_sub_nonneg (argument : ℝ)) (compareExpm1x_eq_real argument) hfinite
          rw [h]
          simpa using roundAt_nonneg fmt (exp_sub_one_sub_nonneg (argument : ℝ))
      cases mode with
      | nearest => exact hnearest
      | nearestAway => exact hnearest
      | towardZero => exact AlgebraicRounding.toReal_roundDown_nonneg fmt _
      | down => exact AlgebraicRounding.toReal_roundDown_nonneg fmt _
      | up => exact AlgebraicRounding.toReal_roundUp_nonneg fmt _
      | away => exact AlgebraicRounding.toReal_roundUp_nonneg fmt _
    · rw [toReal_eq_zero_of_isFinite_eq_false (isFinite_invalidResult hfmt)]

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.CorrectlyRounded
