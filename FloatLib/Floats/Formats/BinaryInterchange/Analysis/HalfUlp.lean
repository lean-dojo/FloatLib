/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel

import FloatLib.Numerics.ErrorBound.Algebra

/-!
# Half an ulp as the error of one nearest rounding

`abs_roundAt_sub_le` bounds the error of nearest-even rounding by `halfUlpAt fmt x`, half the
spacing of the grid of `fmt` at `x`. The standard model keeps only its consequence
`u * |x| + η`. Sharp bounds for a few operations, such as the `√5 u` bound of a complex product,
compare the half-ulps of several intermediate values instead. This module has the facts such an
argument uses, for every descriptor `fmt`:

* `halfUlpAt_le`: half an ulp is at most `u * |x| + η`, with `u * |x|` alone in the normal range
  and `η` exactly below it.
* `halfUlpAt_mono`: it is monotone in `|x|`.
* `two_mul_halfUlpAt_le_of_lt`: half-ulps are powers of two, so a smaller one is at most half a
  larger one.
* `halfUlpAt_le_halfUlpAt_roundAt`: rounding does not decrease it.
* `roundAt_sub_eq_of_halfUlpAt_le`: a difference of two grid points whose half-ulp is at most
  that of each operand is a grid point, so rounding it is exact.
* `abs_roundAt_sub_le_abs_sub`: the rounded value is at least as close as any grid point, and
  `exists_genericFormat_between` finds a grid point between two nonnegative reals with
  different half-ulps.
* `one_add_mul_abs_roundAt_sub_le`: in the normal range the relative error is at most
  `u / (1 + u)`, stated as `(1 + u) * |round x - x| ≤ u * |x|`.
* `abs_roundAt_add_sub_le_of_genericFormat`: a sum or difference of two grid points rounds with
  relative error `u` and no underflow term.
* `NoUnderflowAt fmt t` says that `t` is zero or in the normal range. Such a rounding, and the
  rounding of a sum of grid points, multiplies by a factor in `[1 - u, 1 + u]`
  (`exists_roundAt_eq_mul`, `exists_roundAt_add_eq_mul`).

## References

- R. P. Brent, C. Percival and P. Zimmermann, "Error bounds on complex floating-point
  multiplication," Math. Comp. 76 (2007), 1469–1481, which argues with ulps in this way.
- C.-P. Jeannerod and S. M. Rump, "On relative errors of floating-point operations: optimal
  bounds and applications," Math. Comp. 87 (2018), 803–819, for the bound `u / (1 + u)`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics (binaryRadix)

variable (fmt : FloatFormat)

/-- The precision of every descriptor is positive. -/
private theorem precision_pos : (0 : ℤ) < Int.ofNat (fmt.fracWidth + 1) :=
  Int.natCast_pos.mpr (Nat.succ_pos fmt.fracWidth)

/-- One ulp at zero is the subnormal spacing. -/
theorem ulpAt_zero : ulpAt fmt 0 = Flocq.bpow binaryRadix fmt.minSubnormalExponent :=
  ulp_zero_flt (β := binaryRadix) fmt.minSubnormalExponent (Int.ofNat (fmt.fracWidth + 1))
    (precision_pos fmt)

/-- One ulp is a power of two at or above the subnormal spacing. -/
theorem exists_ulpAt_eq_bpow (x : ℝ) :
    ∃ e : ℤ, fmt.minSubnormalExponent ≤ e ∧ ulpAt fmt x = Flocq.bpow binaryRadix e := by
  by_cases hx : x = 0
  · subst hx
    exact ⟨fmt.minSubnormalExponent, le_rfl, ulpAt_zero fmt⟩
  · refine ⟨cexp binaryRadix (fexpOf fmt) x, ?_, ulp.of_ne_zero _ _ x hx⟩
    simp only [cexp, fexpOf, fltExp]
    exact le_max_right _ _

/-- In the normal range half an ulp is at most `u * |x|`. -/
theorem halfUlpAt_le_of_minNormalAt_le {x : ℝ} (hx : minNormalAt fmt ≤ |x|) :
    halfUlpAt fmt x ≤ unitRoundoffAt fmt * |x| := by
  have h := ulpAt_le_of_minNormalAt_le fmt hx
  rw [← two_mul_unitRoundoffAt] at h
  change ulpAt fmt x / 2 ≤ _
  linarith

/-- Below the normal range half an ulp is the underflow allowance `η`. -/
theorem halfUlpAt_eq_of_abs_lt_minNormalAt {x : ℝ} (hx : |x| < minNormalAt fmt) :
    halfUlpAt fmt x = underflowErrorAt fmt := by
  have h := ulpAt_eq_of_abs_lt_minNormalAt fmt hx
  rw [← two_mul_underflowErrorAt] at h
  change ulpAt fmt x / 2 = _
  rw [h]
  simp

/-- Half an ulp is at most `u * |x| + η`. -/
theorem halfUlpAt_le (x : ℝ) :
    halfUlpAt fmt x ≤ unitRoundoffAt fmt * |x| + underflowErrorAt fmt := by
  by_cases hnormal : minNormalAt fmt ≤ |x|
  · linarith [halfUlpAt_le_of_minNormalAt_le fmt hnormal, underflowErrorAt_pos fmt]
  · rw [halfUlpAt_eq_of_abs_lt_minNormalAt fmt (not_le.mp hnormal)]
    linarith [mul_nonneg (unitRoundoffAt_pos fmt).le (abs_nonneg x)]

/-- One ulp is monotone in the magnitude of its argument. -/
theorem ulpAt_mono {x y : ℝ} (hxy : |x| ≤ |y|) : ulpAt fmt x ≤ ulpAt fmt y := by
  by_cases hx : x = 0
  · subst hx
    obtain ⟨e, he, hy⟩ := exists_ulpAt_eq_bpow fmt y
    rw [hy, ulpAt_zero]
    exact (bpow_le_bpow_iff _ _ _).mpr he
  · have h := ulp_mono_pos (β := binaryRadix) (fexp := fexpOf fmt) (abs_pos.mpr hx) hxy
    rwa [ulp_abs, ulp_abs] at h

/-- Half an ulp is monotone in the magnitude of its argument. -/
theorem halfUlpAt_mono {x y : ℝ} (hxy : |x| ≤ |y|) : halfUlpAt fmt x ≤ halfUlpAt fmt y := by
  have h := ulpAt_mono fmt hxy
  change ulpAt fmt x / 2 ≤ ulpAt fmt y / 2
  exact div_le_div_of_nonneg_right h (by norm_num)

/-- Half-ulps are powers of two: a smaller one is at most half a larger one. -/
theorem two_mul_halfUlpAt_le_of_lt {x y : ℝ} (h : halfUlpAt fmt x < halfUlpAt fmt y) :
    2 * halfUlpAt fmt x ≤ halfUlpAt fmt y := by
  obtain ⟨ex, -, hx⟩ := exists_ulpAt_eq_bpow fmt x
  obtain ⟨ey, -, hy⟩ := exists_ulpAt_eq_bpow fmt y
  have h' : ulpAt fmt x < ulpAt fmt y := by
    have : ulpAt fmt x / 2 < ulpAt fmt y / 2 := h
    linarith
  rw [hx, hy, bpow_lt_bpow_iff] at h'
  have hle : Flocq.bpow binaryRadix (ex + 1) ≤ Flocq.bpow binaryRadix ey :=
    (bpow_le_bpow_iff _ _ _).mpr (by omega)
  have h2 : Flocq.bpow binaryRadix (ex + 1) = 2 * Flocq.bpow binaryRadix ex := by
    rw [bpow.add_exp]
    simp [Flocq.bpow, binaryRadix, Numerics.Radix.toReal, mul_comm]
  change 2 * (ulpAt fmt x / 2) ≤ ulpAt fmt y / 2
  rw [hx, hy]
  linarith

/-- A difference of two grid points whose half-ulp is at most that of each operand is a grid
point: both operands are multiples of its ulp. -/
theorem genericFormat_sub_of_halfUlpAt_le {f g : ℝ}
    (hf : GenericRepresentable binaryRadix (fexpOf fmt) f)
    (hg : GenericRepresentable binaryRadix (fexpOf fmt) g)
    (h1 : halfUlpAt fmt (f - g) ≤ halfUlpAt fmt f)
    (h2 : halfUlpAt fmt (f - g) ≤ halfUlpAt fmt g) :
    GenericRepresentable binaryRadix (fexpOf fmt) (f - g) := by
  by_cases hf0 : f = 0
  · subst hf0
    simpa using genericRepresentable_neg g hg
  by_cases hg0 : g = 0
  · subst hg0
    simpa using hf
  by_cases hd : f - g = 0
  · rw [hd]
    exact genericRepresentable_zero
  have hcexp : ∀ {t : ℝ}, t ≠ 0 → halfUlpAt fmt (f - g) ≤ halfUlpAt fmt t →
      cexp binaryRadix (fexpOf fmt) (f - g) ≤ cexp binaryRadix (fexpOf fmt) t := by
    intro t ht h
    have h' : ulpAt fmt (f - g) ≤ ulpAt fmt t := by
      have : ulpAt fmt (f - g) / 2 ≤ ulpAt fmt t / 2 := h
      linarith
    rw [ulpAt, ulpAt, ulp.of_ne_zero _ _ _ hd, ulp.of_ne_zero _ _ _ ht] at h'
    exact (bpow_le_bpow_iff _ _ _).mp h'
  obtain ⟨mf, hmf⟩ := exists_int_mul_bpow_of_le_cexp hf (hcexp hf0 h1)
  obtain ⟨mg, hmg⟩ := exists_int_mul_bpow_of_le_cexp hg (hcexp hg0 h2)
  refine genericRepresentable_of_toReal_of_cexp_le
    ({ mantissa := mf - mg, exponent := cexp binaryRadix (fexpOf fmt) (f - g) } :
      FloatRep binaryRadix) _ ?_ le_rfl
  change f - g =
    ((mf - mg : ℤ) : ℝ) * Flocq.bpow binaryRadix (cexp binaryRadix (fexpOf fmt) (f - g))
  push_cast
  linear_combination hmf - hmg

/-- Rounding a difference of two grid points is exact when its half-ulp is at most that of each
operand. -/
theorem roundAt_sub_eq_of_halfUlpAt_le {f g : ℝ}
    (hf : GenericRepresentable binaryRadix (fexpOf fmt) f)
    (hg : GenericRepresentable binaryRadix (fexpOf fmt) g)
    (h1 : halfUlpAt fmt (f - g) ≤ halfUlpAt fmt f)
    (h2 : halfUlpAt fmt (f - g) ≤ halfUlpAt fmt g) :
    roundAt fmt (f - g) = f - g :=
  round_preserves_generic nearestEven _ (genericFormat_sub_of_halfUlpAt_le fmt hf hg h1 h2)

/-- The rounded value is at least as close to `x` as any grid point. -/
theorem abs_roundAt_sub_le_abs_sub {f : ℝ} (hf : GenericRepresentable binaryRadix (fexpOf fmt) f)
    (x : ℝ) : |roundAt fmt x - x| ≤ |f - x| :=
  (round_nearestEven_point (β := binaryRadix) (fexp := fexpOf fmt) x).2 f hf

/-- A power of two at or above the subnormal spacing is a grid point. -/
theorem genericFormat_bpow {e : ℤ} (he : fmt.minSubnormalExponent ≤ e) :
    GenericRepresentable binaryRadix (fexpOf fmt) (Flocq.bpow binaryRadix e) := by
  apply genericRepresentable_bpow
  have := precision_pos fmt
  simp only [fexpOf, fltExp, Int.ofNat_eq_natCast] at this ⊢
  exact max_le (by omega) he

/-- Rounding does not decrease the half-ulp: the rounded value stays in the binade of `x` or
reaches the next one. -/
theorem halfUlpAt_le_halfUlpAt_roundAt (x : ℝ) :
    halfUlpAt fmt x ≤ halfUlpAt fmt (roundAt fmt x) := by
  have hprec := precision_pos fmt
  by_cases hsmall : x = 0 ∨ magnitude binaryRadix x ≤ fmt.minSubnormalExponent
  · -- The ulp of `x` is the subnormal spacing, the least one.
    have hx : ulpAt fmt x = Flocq.bpow binaryRadix fmt.minSubnormalExponent := by
      rcases hsmall with rfl | hmag
      · exact ulpAt_zero fmt
      · by_cases hx0 : x = 0
        · subst hx0
          exact ulpAt_zero fmt
        · rw [ulpAt, ulp.of_ne_zero _ _ x hx0]
          congr 1
          simp only [cexp, fexpOf, fltExp, Int.ofNat_eq_natCast] at hprec ⊢
          exact max_eq_right (by omega)
    obtain ⟨e, he, hr⟩ := exists_ulpAt_eq_bpow fmt (roundAt fmt x)
    change ulpAt fmt x / 2 ≤ ulpAt fmt (roundAt fmt x) / 2
    rw [hx, hr]
    have := (bpow_le_bpow_iff binaryRadix _ _).mpr he
    exact div_le_div_of_nonneg_right this (by norm_num)
  · obtain ⟨hx0, _⟩ := not_or.mp hsmall
    -- The power of two at the bottom of the binade of `x` is a grid point with the ulp of `x`.
    set σ := Flocq.bpow binaryRadix (magnitude binaryRadix x - 1) with hσ
    have hσpos : 0 < σ := bpow.pos _ _
    have hσle : σ ≤ |x| := bpow_magnitude_sub_one_le binaryRadix x hx0
    have hσfmt : GenericRepresentable binaryRadix (fexpOf fmt) σ :=
      genericFormat_bpow fmt (by omega)
    have hσulp : halfUlpAt fmt σ = halfUlpAt fmt x := by
      change ulpAt fmt σ / 2 = ulpAt fmt x / 2
      rw [ulpAt, ulpAt, hσ, ulp_bpow, ulp.of_ne_zero _ _ x hx0, cexp, sub_add_cancel]
    have hround : σ ≤ |roundAt fmt x| := by
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · have h := roundAt_mono fmt (x := x) (y := -σ) (by
          rw [abs_of_neg hneg] at hσle
          linarith)
        rw [show roundAt fmt (-σ) = -σ from
          round_preserves_generic nearestEven _ (genericRepresentable_neg σ hσfmt)] at h
        rw [abs_of_nonpos (by linarith)]
        exact le_neg_of_le_neg h
      · have h := roundAt_mono fmt (x := σ) (y := x) (by rwa [abs_of_pos hpos] at hσle)
        rw [show roundAt fmt σ = σ from round_preserves_generic nearestEven _ hσfmt] at h
        rw [abs_of_nonneg (hσpos.le.trans h)]
        exact h
    rw [← hσulp]
    exact halfUlpAt_mono fmt (by rwa [abs_of_pos hσpos])

/-- Between two nonnegative reals with different half-ulps there is a grid point: the power of
two at the top of the binade of the smaller one. -/
theorem exists_genericFormat_between {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : halfUlpAt fmt x < halfUlpAt fmt y) :
    ∃ b, GenericRepresentable binaryRadix (fexpOf fmt) b ∧ x < b ∧ b ≤ y := by
  have hprec := precision_pos fmt
  have hlt : ulpAt fmt x < ulpAt fmt y := by
    have : ulpAt fmt x / 2 < ulpAt fmt y / 2 := h
    linarith
  -- The exponent of the candidate: the magnitude of `x`, raised to the subnormal floor.
  obtain ⟨e, he, hxe, hulp⟩ : ∃ e : ℤ, fmt.minSubnormalExponent ≤ e ∧ x < Flocq.bpow binaryRadix e ∧
      ∀ t : ℝ, 0 ≤ t → t < Flocq.bpow binaryRadix e → ulpAt fmt t ≤ ulpAt fmt x := by
    by_cases hx0 : x = 0
    · subst hx0
      refine ⟨fmt.minSubnormalExponent, le_rfl, bpow.pos _ _, fun t ht0 ht => ?_⟩
      have hnormal : |t| < minNormalAt fmt := by
        rw [abs_of_nonneg ht0]
        refine ht.trans_le ((bpow_le_bpow_iff _ _ _).mpr ?_)
        have := minSubnormalExponent_add_precision_sub_one fmt
        simp only [Int.ofNat_eq_natCast] at this hprec
        omega
      rw [ulpAt_eq_of_abs_lt_minNormalAt fmt hnormal, ulpAt_zero]
    · refine ⟨max (magnitude binaryRadix x) fmt.minSubnormalExponent, le_max_right _ _, ?_,
        fun t ht0 ht => ?_⟩
      · have := abs_lt_bpow_magnitude binaryRadix x
        rw [abs_of_nonneg hx] at this
        exact this.trans_le ((bpow_le_bpow_iff _ _ _).mpr (le_max_left _ _))
      · by_cases ht : t = 0
        · subst ht
          exact ulpAt_mono fmt (by simp)
        · have hmag := magnitude_le_of_abs_lt_bpow binaryRadix t _ ht
            (by rwa [abs_of_nonneg ht0])
          rw [ulpAt, ulpAt, ulp.of_ne_zero _ _ t ht, ulp.of_ne_zero _ _ x hx0,
            bpow_le_bpow_iff]
          simp only [cexp, fexpOf, fltExp, Int.ofNat_eq_natCast] at hprec ⊢
          refine max_le ?_ (le_max_right _ _)
          rcases le_max_iff.mp hmag with hle | hle
          · exact le_max_of_le_left (by omega)
          · exact le_max_of_le_right (by omega)
  refine ⟨Flocq.bpow binaryRadix e, genericFormat_bpow fmt he, hxe, ?_⟩
  by_contra hy'
  exact absurd (hulp y hy (not_le.mp hy')) (not_le.mpr hlt)

/-- In the normal range the relative error of nearest rounding is at most `u / (1 + u)`:
`(1 + u) * |round x - x| ≤ u * |x|`. The bound `u` is attained only in the limit, because a
real within `u` of the bottom of its binade rounds to that power of two. -/
theorem one_add_mul_abs_roundAt_sub_le {x : ℝ} (hnormal : minNormalAt fmt ≤ |x|) :
    (1 + unitRoundoffAt fmt) * |roundAt fmt x - x| ≤ unitRoundoffAt fmt * |x| := by
  have hprec := precision_pos fmt
  have hu := unitRoundoffAt_pos fmt
  have hx0 : x ≠ 0 := abs_pos.mp ((bpow.pos _ _).trans_le hnormal)
  -- The magnitude of `x` is above the least normal exponent.
  have hmag : fmt.minNormalExponent < magnitude binaryRadix x :=
    (bpow_lt_bpow_iff binaryRadix _ _).mp
      (hnormal.trans_lt (abs_lt_bpow_magnitude binaryRadix x))
  have hexp := minSubnormalExponent_add_precision_sub_one fmt
  set σ := Flocq.bpow binaryRadix (magnitude binaryRadix x - 1) with hσ
  have hσle : σ ≤ |x| := bpow_magnitude_sub_one_le binaryRadix x hx0
  have hσfmt : GenericRepresentable binaryRadix (fexpOf fmt) σ :=
    genericFormat_bpow fmt (by simp only [Int.ofNat_eq_natCast] at hexp hprec; omega)
  -- Half an ulp is `u` times the bottom of the binade.
  have hhalf : halfUlpAt fmt x = unitRoundoffAt fmt * σ := by
    have hulp : ulpAt fmt x = Flocq.bpow binaryRadix (1 - Int.ofNat (fmt.fracWidth + 1)) * σ := by
      rw [ulpAt, ulp.of_ne_zero _ _ x hx0, hσ, ← bpow.add_exp]
      congr 1
      simp only [cexp, fexpOf, fltExp, Int.ofNat_eq_natCast] at hexp hprec ⊢
      rw [max_eq_left (by omega)]
      omega
    change ulpAt fmt x / 2 = _
    rw [hulp, ← two_mul_unitRoundoffAt]
    ring
  have herr : |roundAt fmt x - x| ≤ unitRoundoffAt fmt * σ := by
    rw [← hhalf]
    exact abs_roundAt_sub_le fmt x
  -- The bottom of the binade, with the sign of `x`, is a grid point at distance `|x| - σ`.
  have hnear : |roundAt fmt x - x| ≤ |x| - σ := by
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · have h := abs_roundAt_sub_le_abs_sub fmt (genericRepresentable_neg σ hσfmt) x
      rw [abs_of_neg hneg] at hσle ⊢
      rw [abs_of_nonneg (by linarith : 0 ≤ -σ - x)] at h
      linarith
    · have h := abs_roundAt_sub_le_abs_sub fmt hσfmt x
      rw [abs_of_pos hpos] at hσle ⊢
      rw [abs_of_nonpos (by linarith : σ - x ≤ 0)] at h
      simpa only [neg_sub] using h
  by_cases hcase : (1 + unitRoundoffAt fmt) * σ ≤ |x|
  · calc (1 + unitRoundoffAt fmt) * |roundAt fmt x - x|
        ≤ (1 + unitRoundoffAt fmt) * (unitRoundoffAt fmt * σ) :=
          mul_le_mul_of_nonneg_left herr (by positivity)
      _ = unitRoundoffAt fmt * ((1 + unitRoundoffAt fmt) * σ) := mul_left_comm _ _ _
      _ ≤ unitRoundoffAt fmt * |x| := mul_le_mul_of_nonneg_left hcase hu.le
  · calc (1 + unitRoundoffAt fmt) * |roundAt fmt x - x|
        ≤ (1 + unitRoundoffAt fmt) * (|x| - σ) :=
          mul_le_mul_of_nonneg_left hnear (by positivity)
      _ ≤ unitRoundoffAt fmt * |x| := by linarith

/-- The refined relative bound with gradual underflow:
`(1 + u) * |round x - x| ≤ u * |x| + (1 + u) * η`. -/
theorem one_add_mul_abs_roundAt_sub_le_add (x : ℝ) :
    (1 + unitRoundoffAt fmt) * |roundAt fmt x - x| ≤
      unitRoundoffAt fmt * |x| + (1 + unitRoundoffAt fmt) * underflowErrorAt fmt := by
  have hu := unitRoundoffAt_pos fmt
  by_cases hnormal : minNormalAt fmt ≤ |x|
  · have := one_add_mul_abs_roundAt_sub_le fmt hnormal
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + unitRoundoffAt fmt)
      (underflowErrorAt_pos fmt).le
    linarith
  · have herr := abs_roundAt_sub_le fmt x
    rw [halfUlpAt_eq_of_abs_lt_minNormalAt fmt (not_le.mp hnormal)] at herr
    have := mul_le_mul_of_nonneg_left herr (by linarith : (0 : ℝ) ≤ 1 + unitRoundoffAt fmt)
    have := mul_nonneg hu.le (abs_nonneg x)
    linarith

/-- A sum of two grid points rounds with relative error `u` and no underflow term. -/
theorem abs_roundAt_add_sub_le_of_genericFormat {f g : ℝ}
    (hf : GenericRepresentable binaryRadix (fexpOf fmt) f)
    (hg : GenericRepresentable binaryRadix (fexpOf fmt) g) :
    |roundAt fmt (f + g) - (f + g)| ≤ unitRoundoffAt fmt * |f + g| := by
  obtain ⟨δ, hround, hδ⟩ := roundAt_add_eq_mul_one_add fmt hf hg
  rw [hround, mul_add, mul_one, add_sub_cancel_left, mul_comm]
  exact Numerics.Backward.abs_mul_le_mul hδ le_rfl

/-- A difference of two grid points rounds with relative error `u` and no underflow term. -/
theorem abs_roundAt_sub_sub_le_of_genericFormat {f g : ℝ}
    (hf : GenericRepresentable binaryRadix (fexpOf fmt) f)
    (hg : GenericRepresentable binaryRadix (fexpOf fmt) g) :
    |roundAt fmt (f - g) - (f - g)| ≤ unitRoundoffAt fmt * |f - g| := by
  simpa [sub_eq_add_neg] using
    abs_roundAt_add_sub_le_of_genericFormat fmt hf (genericRepresentable_neg g hg)

/-! ## Roundings without an underflow error, as factors -/

/-- `t` rounds without an underflow error: it is zero or in the normal range of `fmt`. -/
def NoUnderflowAt (t : ℝ) : Prop :=
  t = 0 ∨ minNormalAt fmt ≤ |t|

/-- A real that is zero or in the normal range rounds with relative error `u` and no underflow
term. -/
theorem abs_roundAt_sub_le_of_noUnderflowAt {t : ℝ} (h : NoUnderflowAt fmt t) :
    |roundAt fmt t - t| ≤ unitRoundoffAt fmt * |t| := by
  rcases h with rfl | h
  · simp
  · exact (abs_roundAt_sub_le fmt t).trans (halfUlpAt_le_of_minNormalAt_le fmt h)

/-- A value within relative error `u` of `t` is `t` times a factor in `[1 - u, 1 + u]`. -/
theorem exists_eq_mul_of_abs_sub_le {r t u : ℝ} (hu : 0 ≤ u) (h : |r - t| ≤ u * |t|) :
    ∃ f, r = t * f ∧ 1 - u ≤ f ∧ f ≤ 1 + u := by
  by_cases ht : t = 0
  · subst ht
    have hr : r = 0 := by simpa using h
    exact ⟨1, by simp [hr], sub_le_self _ hu, le_add_of_nonneg_right hu⟩
  · have hdiv : |r / t - 1| ≤ u := by
      rw [div_sub_one ht, abs_div, div_le_iff₀ (abs_pos.mpr ht)]
      exact h
    exact ⟨r / t, by rw [mul_comm, div_mul_cancel₀ _ ht], sub_le_of_abs_sub_le_left hdiv,
      (sub_le_iff_le_add').mp (abs_le.mp hdiv).2⟩

/-- A rounding without an underflow error multiplies by a factor in `[1 - u, 1 + u]`. -/
theorem exists_roundAt_eq_mul {t : ℝ} (h : NoUnderflowAt fmt t) :
    ∃ f, roundAt fmt t = t * f ∧ 1 - unitRoundoffAt fmt ≤ f ∧ f ≤ 1 + unitRoundoffAt fmt :=
  exists_eq_mul_of_abs_sub_le (unitRoundoffAt_pos fmt).le
    (abs_roundAt_sub_le_of_noUnderflowAt fmt h)

/-- Rounding a sum of two grid points multiplies it by a factor in `[1 - u, 1 + u]`. -/
theorem exists_roundAt_add_eq_mul {f g : ℝ} (hf : GenericRepresentable binaryRadix (fexpOf fmt) f)
    (hg : GenericRepresentable binaryRadix (fexpOf fmt) g) :
    ∃ k, roundAt fmt (f + g) = (f + g) * k ∧
      1 - unitRoundoffAt fmt ≤ k ∧ k ≤ 1 + unitRoundoffAt fmt :=
  exists_eq_mul_of_abs_sub_le (unitRoundoffAt_pos fmt).le
    (abs_roundAt_add_sub_le_of_genericFormat fmt hf hg)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
