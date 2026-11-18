/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rounded

/-!
# The unit roundoff of each rounding attribute

A rounding to a nearest value misses by at most half a unit in the last place, and a directed
rounding by at most a whole one. `Model.unitRoundoffIn fmt mode` and `Model.underflowErrorIn fmt
mode` are the relative and the absolute error of one rounding in the attribute `mode`:
`unitRoundoffAt fmt` and `underflowErrorAt fmt` for `nearest` and `nearestAway`, and twice those
for `towardZero`, `up`, `down` and `away`. `Model.mixedError_roundAt_mode` is the mixed error of
`roundAt fmt t mode` for every attribute, from the standard model of the valid roundings
(`round_standardModel`, `round_standardModel_of_nearest`).

A rounding misses by at most `halfUlps` half units in the last place
(`abs_roundAt_sub_le_halfUlps_mul`). At or above the least normal magnitude the absolute part is
not needed (`abs_roundAt_sub_le_mode_of_normal`), and a sum of two grid points never needs it
(`abs_roundAt_add_sub_le_mode`): below the normal range such a sum is itself a grid point.

A sum, a difference, a product or a fused multiply-add of the model in the attribute `mode` is
one such rounding of the exact result when that result is within the largest finite magnitude
(`DirectedSemantics.Rounded`). `add_rounding_mode`, `sub_rounding_mode`, `mul_rounding_mode` and
`fma_rounding_mode` state its mixed error for every attribute: relative `unitRoundoffIn fmt
mode`, with no absolute part for a sum or a difference and `underflowErrorIn fmt mode` for a
product or a fused multiply-add. `abs_toReal_add_sub_le_mode` and its `sub`, `mul` and `fma`
forms state the same bounds as inequalities.

`roundoff` has these theorems among its rules (`FloatLib.Tactic.Roundoff.Rules`). A rounding in
the default attribute keeps `unitRoundoffAt fmt`, and a rounding in another attribute states its
own.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics FloatLib.Floats.Formats.Flocq

namespace IEEERoundingMode

/-- The largest error of one rounding in this attribute, in half units in the last place: one for
the two attributes that round to a nearest value, two for the four directed ones. -/
def halfUlps : IEEERoundingMode → ℕ
  | .nearest | .nearestAway => 1
  | .towardZero | .up | .down | .away => 2

/-- A rounding misses by at least half a unit in the last place in the worst case. -/
theorem halfUlps_pos (mode : IEEERoundingMode) : 0 < mode.halfUlps := by
  cases mode <;> decide

end IEEERoundingMode

variable {fmt : FloatFormat}

/-- The unit roundoff of `fmt` under the rounding attribute `mode`: `unitRoundoffAt fmt` for the
two attributes that round to a nearest value, and twice that for a directed attribute. -/
noncomputable def unitRoundoffIn (fmt : FloatFormat) (mode : IEEERoundingMode) : ℝ :=
  mode.halfUlps * unitRoundoffAt fmt

/-- The underflow allowance of `fmt` under the rounding attribute `mode`: `underflowErrorAt fmt`
for the two attributes that round to a nearest value, and twice that, the subnormal spacing, for
a directed attribute. -/
noncomputable def underflowErrorIn (fmt : FloatFormat) (mode : IEEERoundingMode) : ℝ :=
  mode.halfUlps * underflowErrorAt fmt

/-- Nearest-even rounding has the unit roundoff of the format. -/
@[simp] theorem unitRoundoffIn_nearest (fmt : FloatFormat) :
    unitRoundoffIn fmt .nearest = unitRoundoffAt fmt := by
  simp [unitRoundoffIn, IEEERoundingMode.halfUlps]

/-- Nearest-even rounding has the underflow allowance of the format. -/
@[simp] theorem underflowErrorIn_nearest (fmt : FloatFormat) :
    underflowErrorIn fmt .nearest = underflowErrorAt fmt := by
  simp [underflowErrorIn, IEEERoundingMode.halfUlps]

/-- The unit roundoff of every attribute is positive. -/
theorem unitRoundoffIn_pos (fmt : FloatFormat) (mode : IEEERoundingMode) :
    0 < unitRoundoffIn fmt mode :=
  mul_pos (Nat.cast_pos.mpr mode.halfUlps_pos) (unitRoundoffAt_pos fmt)

/-- Rounding in any attribute has the mixed error of that attribute: relative
`unitRoundoffIn fmt mode` and absolute `underflowErrorIn fmt mode`. -/
theorem mixedError_roundAt_mode (fmt : FloatFormat) (t : ℝ) (mode : IEEERoundingMode) :
    MixedError (roundAt fmt t mode) t (unitRoundoffIn fmt mode) (underflowErrorIn fmt mode) := by
  apply MixedError.of_standardModel
  rw [roundAt_eq_round]
  cases mode with
  | nearest =>
      obtain ⟨δ, η, h, hδ, hη, -⟩ := round_standardModel_of_nearest fmt nearestEven t
      exact ⟨δ, η, h, by simpa using hδ, by simpa using hη⟩
  | nearestAway =>
      obtain ⟨δ, η, h, hδ, hη, -⟩ :=
        round_standardModel_of_nearest fmt (nearestChoice nearestAwayChoice) t
      exact ⟨δ, η, h, by simpa [unitRoundoffIn, IEEERoundingMode.halfUlps] using hδ,
        by simpa [underflowErrorIn, IEEERoundingMode.halfUlps] using hη⟩
  | towardZero =>
      obtain ⟨δ, η, h, hδ, hη, -⟩ := round_standardModel fmt truncRound t
      exact ⟨δ, η, h, by simpa [unitRoundoffIn, IEEERoundingMode.halfUlps] using hδ,
        by simpa [underflowErrorIn, IEEERoundingMode.halfUlps] using hη⟩
  | up =>
      obtain ⟨δ, η, h, hδ, hη, -⟩ := round_standardModel fmt ceilRound t
      exact ⟨δ, η, h, by simpa [unitRoundoffIn, IEEERoundingMode.halfUlps] using hδ,
        by simpa [underflowErrorIn, IEEERoundingMode.halfUlps] using hη⟩
  | down =>
      obtain ⟨δ, η, h, hδ, hη, -⟩ := round_standardModel fmt floorRound t
      exact ⟨δ, η, h, by simpa [unitRoundoffIn, IEEERoundingMode.halfUlps] using hδ,
        by simpa [underflowErrorIn, IEEERoundingMode.halfUlps] using hη⟩
  | away =>
      obtain ⟨δ, η, h, hδ, hη, -⟩ := round_standardModel fmt awayRound t
      exact ⟨δ, η, h, by simpa [unitRoundoffIn, IEEERoundingMode.halfUlps] using hδ,
        by simpa [underflowErrorIn, IEEERoundingMode.halfUlps] using hη⟩

/-- A value equal to the rounding of `t` in a rounding attribute has the mixed error of that
attribute. Applied to a function that is correctly rounded in every attribute, this gives its
implementation contract. -/
theorem mixedError_toReal_of_eq_roundAt_mode {v : Model fmt} {t : ℝ} {mode : IEEERoundingMode}
    (h : toReal v = roundAt fmt t mode) :
    MixedError (toReal v) t (unitRoundoffIn fmt mode) (underflowErrorIn fmt mode) :=
  h ▸ mixedError_roundAt_mode fmt t mode

/-- Rounding in any attribute changes a real by at most the relative and the absolute error of
that attribute. -/
theorem abs_roundAt_sub_le_mode (fmt : FloatFormat) (t : ℝ) (mode : IEEERoundingMode) :
    |roundAt fmt t mode - t| ≤ unitRoundoffIn fmt mode * |t| + underflowErrorIn fmt mode :=
  (mixedError_roundAt_mode fmt t mode).bound

/-- A rounding in any attribute misses by at most the half units in the last place of that
attribute: one for the two attributes that round to a nearest value, two for a directed one. -/
theorem abs_roundAt_sub_le_halfUlps_mul (fmt : FloatFormat) (t : ℝ) (mode : IEEERoundingMode) :
    |roundAt fmt t mode - t| ≤ mode.halfUlps * (ulpAt fmt t / 2) := by
  have hdirected : |roundAt fmt t mode - t| ≤ ((2 : ℕ) : ℝ) * (ulpAt fmt t / 2) := by
    rw [Nat.cast_ofNat, two_mul, add_halves, roundAt_eq_round, ulpAt]
    exact round_abs_error_le_ulp (roundingFunction mode) t
  cases mode with
  | nearest =>
      rw [show ((IEEERoundingMode.nearest.halfUlps : ℕ) : ℝ) = 1 from Nat.cast_one, one_mul,
        roundAt_eq_round, ulpAt]
      exact error_bound_ulp (β := Numerics.binaryRadix) (fexp := fexpOf fmt) nearestEven t
  | nearestAway =>
      rw [show ((IEEERoundingMode.nearestAway.halfUlps : ℕ) : ℝ) = 1 from Nat.cast_one, one_mul,
        roundAt_eq_round, ulpAt]
      exact error_bound_ulp (β := Numerics.binaryRadix) (fexp := fexpOf fmt)
        (nearestChoice nearestAwayChoice) t
  | towardZero => exact hdirected
  | up => exact hdirected
  | down => exact hdirected
  | away => exact hdirected

/-- A rounding in any attribute of a real at or above the least normal magnitude has only the
relative error of that attribute. -/
theorem abs_roundAt_sub_le_mode_of_normal (fmt : FloatFormat) {t : ℝ}
    (hnormal : minNormalAt fmt ≤ |t|) (mode : IEEERoundingMode) :
    |roundAt fmt t mode - t| ≤ unitRoundoffIn fmt mode * |t| := by
  have hhalf : ulpAt fmt t / 2 ≤ unitRoundoffAt fmt * |t| := by
    rw [div_le_iff₀ two_pos, mul_comm, ← mul_assoc, two_mul_unitRoundoffAt]
    exact ulpAt_le_of_minNormalAt_le fmt hnormal
  rw [unitRoundoffIn, mul_assoc]
  exact (abs_roundAt_sub_le_halfUlps_mul fmt t mode).trans
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg _))

/-- Rounding a sum of two grid points in any attribute has the relative error of that attribute
and no underflow term: below the normal range the sum is itself a grid point. -/
theorem abs_roundAt_add_sub_le_mode (fmt : FloatFormat) {x y : ℝ}
    (hx : GenericRepresentable Numerics.binaryRadix (fexpOf fmt) x)
    (hy : GenericRepresentable Numerics.binaryRadix (fexpOf fmt) y) (mode : IEEERoundingMode) :
    |roundAt fmt (x + y) mode - (x + y)| ≤ unitRoundoffIn fmt mode * |x + y| := by
  by_cases hnormal : minNormalAt fmt ≤ |x + y|
  · exact abs_roundAt_sub_le_mode_of_normal fmt hnormal mode
  · have hsum := genericFormat_add_of_abs_lt_minNormalAt fmt hx hy (not_le.mp hnormal)
    have hexact : roundAt fmt (x + y) mode = x + y := by
      rw [roundAt_eq_round]
      exact round_preserves_generic (roundingFunction mode) (x + y) hsum
    rw [hexact, sub_self, abs_zero]
    exact mul_nonneg (unitRoundoffIn_pos fmt mode).le (abs_nonneg _)

section Operations

variable {x y z : Model fmt} {mode : IEEERoundingMode}

/-- For an IEEE descriptor and every rounding attribute, the sum of finite operands whose exact
sum is within the largest finite magnitude has the relative error of that attribute against the
exact sum, and no absolute part. -/
theorem add_rounding_mode (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hrange : |toReal x + toReal y| ≤ toReal (posMaxFinite fmt)) :
    MixedError (toReal (add x y (mode := mode))) (toReal x + toReal y)
      (unitRoundoffIn fmt mode) 0 := by
  rw [(add_finite_roundAt hfmt hx hy hrange).2]
  exact MixedError.of_abs_sub_le_mul (unitRoundoffIn_pos fmt mode).le
    (abs_roundAt_add_sub_le_mode fmt (toReal_genericFormat_of_isFinite x hx)
      (toReal_genericFormat_of_isFinite y hy) mode)

/-- For an IEEE descriptor and every rounding attribute, the difference of finite operands whose
exact difference is within the largest finite magnitude has the relative error of that attribute
against the exact difference, and no absolute part. -/
theorem sub_rounding_mode (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hrange : |toReal x - toReal y| ≤ toReal (posMaxFinite fmt)) :
    MixedError (toReal (sub x y (mode := mode))) (toReal x - toReal y)
      (unitRoundoffIn fmt mode) 0 := by
  rw [(sub_finite_roundAt hfmt hx hy hrange).2, sub_eq_add_neg]
  exact MixedError.of_abs_sub_le_mul (unitRoundoffIn_pos fmt mode).le
    (abs_roundAt_add_sub_le_mode fmt (toReal_genericFormat_of_isFinite x hx)
      (genericRepresentable_neg _ (toReal_genericFormat_of_isFinite y hy)) mode)

/-- For an IEEE descriptor and every rounding attribute, the product of finite operands whose
exact product is within the largest finite magnitude has the mixed error of one rounding in that
attribute. -/
theorem mul_rounding_mode (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hrange : |toReal x * toReal y| ≤ toReal (posMaxFinite fmt)) :
    MixedError (toReal (mul x y (mode := mode))) (toReal x * toReal y)
      (unitRoundoffIn fmt mode) (underflowErrorIn fmt mode) :=
  mixedError_toReal_of_eq_roundAt_mode (mul_finite_roundAt hfmt hx hy hrange).2

/-- For an IEEE descriptor and every rounding attribute, the fused multiply-add of finite
operands whose exact `x * y + z` is within the largest finite magnitude has the mixed error of
one rounding in that attribute. -/
theorem fma_rounding_mode (hfmt : fmt.isIEEE = true) (hx : isFinite x = true)
    (hy : isFinite y = true) (hz : isFinite z = true)
    (hrange : |toReal x * toReal y + toReal z| ≤ toReal (posMaxFinite fmt)) :
    MixedError (toReal (fma x y z (mode := mode))) (toReal x * toReal y + toReal z)
      (unitRoundoffIn fmt mode) (underflowErrorIn fmt mode) :=
  mixedError_toReal_of_eq_roundAt_mode (fma_finite_roundAt hfmt hx hy hz hrange).2

/-- For an IEEE descriptor and every rounding attribute, the sum of finite operands whose exact
sum is within the largest finite magnitude is within the relative error of that attribute of
the exact sum. -/
theorem abs_toReal_add_sub_le_mode (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hrange : |toReal x + toReal y| ≤ toReal (posMaxFinite fmt)) :
    |toReal (add x y (mode := mode)) - (toReal x + toReal y)| ≤
      unitRoundoffIn fmt mode * |toReal x + toReal y| :=
  (add_rounding_mode hfmt hx hy hrange).bound.trans_eq (add_zero _)

/-- For an IEEE descriptor and every rounding attribute, the difference of finite operands
whose exact difference is within the largest finite magnitude is within the relative error of
that attribute of the exact difference. -/
theorem abs_toReal_sub_sub_le_mode (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hrange : |toReal x - toReal y| ≤ toReal (posMaxFinite fmt)) :
    |toReal (sub x y (mode := mode)) - (toReal x - toReal y)| ≤
      unitRoundoffIn fmt mode * |toReal x - toReal y| :=
  (sub_rounding_mode hfmt hx hy hrange).bound.trans_eq (add_zero _)

/-- For an IEEE descriptor and every rounding attribute, the product of finite operands whose
exact product is within the largest finite magnitude is within the relative and the absolute
error of that attribute of the exact product. -/
theorem abs_toReal_mul_sub_le_mode (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hrange : |toReal x * toReal y| ≤ toReal (posMaxFinite fmt)) :
    |toReal (mul x y (mode := mode)) - toReal x * toReal y| ≤
      unitRoundoffIn fmt mode * |toReal x * toReal y| + underflowErrorIn fmt mode :=
  (mul_rounding_mode hfmt hx hy hrange).bound

/-- For an IEEE descriptor and every rounding attribute, the fused multiply-add of finite
operands whose exact `x * y + z` is within the largest finite magnitude is within the relative
and the absolute error of that attribute of the exact value. -/
theorem abs_toReal_fma_sub_le_mode (hfmt : fmt.isIEEE = true) (hx : isFinite x = true)
    (hy : isFinite y = true) (hz : isFinite z = true)
    (hrange : |toReal x * toReal y + toReal z| ≤ toReal (posMaxFinite fmt)) :
    |toReal (fma x y z (mode := mode)) - (toReal x * toReal y + toReal z)| ≤
      unitRoundoffIn fmt mode * |toReal x * toReal y + toReal z| + underflowErrorIn fmt mode :=
  (fma_rounding_mode hfmt hx hy hz hrange).bound

end Operations

end FloatLib.Floats.Formats.BinaryInterchange.Model
