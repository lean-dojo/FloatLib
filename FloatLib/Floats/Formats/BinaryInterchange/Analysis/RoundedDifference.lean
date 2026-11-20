/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.HalfUlp
public import FloatLib.Numerics.ErrorBound.Algebra

/-!
# The rounded difference of two rounded reals

`roundedSubError fmt p q` is the error of `round (round p - round q)` against `p - q`: three
nearest-even roundings onto the grid of `fmt`. With `p` and `q` two products it is the real or
the imaginary part of a complex product, a 2 by 2 determinant, or a dot product of length two.
A rounded sum is the same thing at `(p, -q)`, because nearest-even rounding commutes with
negation.

Three bounds hold for every descriptor `fmt`, with `u = unitRoundoffAt fmt` and
`η = underflowErrorAt fmt`. The underflow term comes from the two inner roundings only: the outer
one rounds a difference of two grid points, which has none.

* `roundedSubError_le`: `(2u + u²)(|p| + |q|) + (2 + 2u) η` for all `p` and `q`. This is what the
  standard model gives.
* `roundedSubError_le_of_mul_nonpos`: `2u (|p| + |q|) + 4 η` when `p` and `q` have opposite
  signs, so that nothing cancels. The `u²` term is gone: either the outer rounding has the
  half-ulp of the exact sum, or a power of two lies between the exact and the computed sum and
  the outer rounding cannot move further than the inner ones did.
* `roundedSubError_cases`: when `p` and `q` have the same sign, with `m` the larger and `n` the
  smaller magnitude, one of
  `u (2m - n) + 2u² (m + n) + (2 + 4u) η`, `7/4 (u m + η)` and `u (m + n) + 2 η` holds. The cases
  compare the half-ulps of `p`, `q` and the computed difference. When the difference has the
  smallest one the subtraction is exact.

`abs_roundAt_add_roundAt_sub_le` is the fused form, with one inner rounding:
`|round (p + round q) - (p + q)| ≤ u |p + q| + u |q| + 3 η`.

The second and third bounds are the two halves of the proof of Theorem 1 of Brent, Percival and
Zimmermann,
"Error bounds on complex floating-point multiplication," Math. Comp. 76 (2007), 1469–1481:
their cases I1 and I2, and R1 to R4 with R2 and R3 merged. Here the grid has gradual underflow,
which adds the `η` terms, and the inputs are any reals. The fused form gives the bound `2u` of
the product with fused multiply-adds, the constant of Jeannerod, Kornerup, Louvet and Muller,
"Error bounds on complex floating-point multiplication with an FMA," Math. Comp. 86 (2017),
881–898, who prove it without underflow for `β ^ (p - 1) ≥ 24`. The proof here uses the relative
error `u / (1 + u)` of one rounding and needs no bound on the precision.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics (binaryRadix)

variable (fmt : FloatFormat)

/-- Nearest-even rounding commutes with negation. -/
theorem roundAt_neg_nearest (x : ℝ) : roundAt fmt (-x) = -roundAt fmt x := by
  rw [roundAt_neg]
  rfl

/-- The error of the rounded difference of two rounded reals against their exact difference. -/
noncomputable def roundedSubError (p q : ℝ) : ℝ :=
  |roundAt fmt (roundAt fmt p - roundAt fmt q) - (p - q)|

/-- Exchanging the operands negates the difference and keeps the error. -/
theorem roundedSubError_comm (p q : ℝ) : roundedSubError fmt p q = roundedSubError fmt q p := by
  unfold roundedSubError
  rw [← neg_sub (roundAt fmt q) (roundAt fmt p), roundAt_neg_nearest, ← abs_neg]
  congr 1
  ring

/-- Negating both operands keeps the error. -/
theorem roundedSubError_neg (p q : ℝ) :
    roundedSubError fmt (-p) (-q) = roundedSubError fmt p q := by
  unfold roundedSubError
  rw [roundAt_neg_nearest, roundAt_neg_nearest,
    show -roundAt fmt p - -roundAt fmt q = -(roundAt fmt p - roundAt fmt q) by ring,
    roundAt_neg_nearest, ← abs_neg]
  congr 1
  ring

/-- The error of a rounded sum of two rounded reals is `roundedSubError` at `(p, -q)`. -/
theorem abs_roundAt_add_sub_eq_roundedSubError (p q : ℝ) :
    |roundAt fmt (roundAt fmt p + roundAt fmt q) - (p + q)| = roundedSubError fmt p (-q) := by
  unfold roundedSubError
  rw [roundAt_neg_nearest, sub_neg_eq_add, sub_neg_eq_add]

/-- The outer rounding of a rounded difference has relative error `u` and no underflow term. -/
private theorem abs_outer_le (p q : ℝ) :
    |roundAt fmt (roundAt fmt p - roundAt fmt q) - (roundAt fmt p - roundAt fmt q)| ≤
      unitRoundoffAt fmt * |roundAt fmt p - roundAt fmt q| :=
  abs_roundAt_sub_sub_le_of_genericFormat fmt (genericFormat_roundAt fmt p)
    (genericFormat_roundAt fmt q)

/-- The error of a rounded difference is at most the three rounding errors. -/
private theorem roundedSubError_le_add (p q : ℝ) :
    roundedSubError fmt p q ≤
      |roundAt fmt (roundAt fmt p - roundAt fmt q) - (roundAt fmt p - roundAt fmt q)| +
        (|roundAt fmt p - p| + |roundAt fmt q - q|) := by
  unfold roundedSubError
  simpa only [add_comm] using Numerics.sub_error (le_refl |roundAt fmt p - p|)
    (le_refl |roundAt fmt q - q|)
    (le_refl |roundAt fmt (roundAt fmt p - roundAt fmt q) - (roundAt fmt p - roundAt fmt q)|)

/--
The standard-model bound for the rounded difference of two rounded reals:
`(2u + u²)(|p| + |q|) + (2 + 2u) η`, for all reals and every descriptor.
-/
theorem roundedSubError_le (p q : ℝ) :
    roundedSubError fmt p q ≤
      (2 * unitRoundoffAt fmt + unitRoundoffAt fmt ^ 2) * (|p| + |q|) +
        (2 + 2 * unitRoundoffAt fmt) * underflowErrorAt fmt := by
  have hu := (unitRoundoffAt_pos fmt).le
  have hp := abs_roundAt_sub_le_unitRoundoffAt fmt p
  have hq := abs_roundAt_sub_le_unitRoundoffAt fmt q
  have hdiff : |roundAt fmt p - roundAt fmt q| ≤
      |p| + |q| + (|roundAt fmt p - p| + |roundAt fmt q - q|) := by
    simpa only [sub_zero] using Numerics.compose_error
      (Numerics.Backward.sub (le_refl |roundAt fmt p - p|) (le_refl |roundAt fmt q - q|))
      (show |p - q - 0| ≤ |p| + |q| by simpa using abs_sub p q)
  have houter := (abs_outer_le fmt p q).trans (mul_le_mul_of_nonneg_left hdiff hu)
  have h1 := mul_le_mul_of_nonneg_left hp hu
  have h2 := mul_le_mul_of_nonneg_left hq hu
  have := roundedSubError_le_add fmt p q
  linarith

/--
Without cancellation the `u²` term disappears: for nonnegative `s` and `t`,
`|round (round s + round t) - (s + t)| ≤ 2u (s + t) + 4 η`.
-/
theorem abs_roundAt_add_sub_le_of_nonneg {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |roundAt fmt (roundAt fmt s + roundAt fmt t) - (s + t)| ≤
      2 * unitRoundoffAt fmt * (s + t) + 4 * underflowErrorAt fmt := by
  have hη := (underflowErrorAt_pos fmt).le
  have hS := roundAt_nonneg fmt hs
  have hT := roundAt_nonneg fmt ht
  have hes : |roundAt fmt s - s| ≤ unitRoundoffAt fmt * s + underflowErrorAt fmt := by
    simpa [abs_of_nonneg hs] using (abs_roundAt_sub_le fmt s).trans (halfUlpAt_le fmt s)
  have het : |roundAt fmt t - t| ≤ unitRoundoffAt fmt * t + underflowErrorAt fmt := by
    simpa [abs_of_nonneg ht] using (abs_roundAt_sub_le fmt t).trans (halfUlpAt_le fmt t)
  set σ := roundAt fmt s + roundAt fmt t
  have hσ0 : 0 ≤ σ := add_nonneg hS hT
  have hw0 : 0 ≤ s + t := add_nonneg hs ht
  -- The computed sum is within the two inner errors of the exact one.
  have hσw : |σ - (s + t)| ≤
      unitRoundoffAt fmt * s + underflowErrorAt fmt +
        (unitRoundoffAt fmt * t + underflowErrorAt fmt) :=
    Numerics.Backward.add hes het
  by_cases hcase : halfUlpAt fmt σ ≤ halfUlpAt fmt (s + t)
  · -- The outer rounding has at most the half-ulp of the exact sum.
    have houter : |roundAt fmt σ - σ| ≤ unitRoundoffAt fmt * (s + t) + underflowErrorAt fmt := by
      have h := ((abs_roundAt_sub_le fmt σ).trans hcase).trans (halfUlpAt_le fmt (s + t))
      rwa [abs_of_nonneg hw0] at h
    have := Numerics.compose_error houter hσw
    linarith
  · -- A grid point lies between the exact and the computed sum, and it is no closer to the
    -- computed sum than the rounded value.
    obtain ⟨b, hb, hwb, hbσ⟩ := exists_genericFormat_between fmt hw0 hσ0 (not_le.mp hcase)
    have houter : |roundAt fmt σ - σ| ≤ |σ - (s + t)| := by
      have h := abs_roundAt_sub_le_abs_sub fmt hb σ
      rw [abs_of_nonpos (by linarith : b - σ ≤ 0)] at h
      rw [abs_of_nonneg (by linarith : 0 ≤ σ - (s + t))]
      linarith
    have := Numerics.compose_error houter hσw
    linarith

/--
Without cancellation, for operands of opposite signs:
`roundedSubError fmt p q ≤ 2u (|p| + |q|) + 4 η`.
-/
theorem roundedSubError_le_of_mul_nonpos {p q : ℝ} (hpq : p * q ≤ 0) :
    roundedSubError fmt p q ≤
      2 * unitRoundoffAt fmt * (|p| + |q|) + 4 * underflowErrorAt fmt := by
  have key : ∀ {p q : ℝ}, 0 ≤ p → q ≤ 0 → roundedSubError fmt p q ≤
      2 * unitRoundoffAt fmt * (|p| + |q|) + 4 * underflowErrorAt fmt := by
    intro p q hp hq
    have h := abs_roundAt_add_sub_le_of_nonneg fmt hp (neg_nonneg.mpr hq)
    rw [abs_roundAt_add_sub_eq_roundedSubError, show - -q = q from _root_.neg_neg q] at h
    rwa [abs_of_nonneg hp, abs_of_nonpos hq]
  rcases mul_nonpos_iff.mp hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact key hp hq
  · have h := key (p := -p) (q := -q) (neg_nonneg.mpr hp) (neg_nonpos.mpr hq)
    rwa [roundedSubError_neg, abs_neg, abs_neg] at h

/--
With cancellation, for `0 ≤ q ≤ p`, one of three bounds holds for the rounded difference, by
the half-ulps of `p`, `q` and the computed difference `d = round p - round q`.

* `halfUlp p ≤ halfUlp d`: `u (2p - q) + 2u² (p + q) + (2 + 4u) η`.
* `halfUlp d < halfUlp p` and not both `halfUlp d ≤ halfUlp q = halfUlp p`: `7/4 (u p + η)`.
* `halfUlp d ≤ halfUlp q = halfUlp p`: the subtraction is exact, and `u (p + q) + 2 η`.
-/
theorem roundedSubError_cases_of_le {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) :
    roundedSubError fmt p q ≤
        unitRoundoffAt fmt * (2 * p - q) + 2 * unitRoundoffAt fmt ^ 2 * (p + q) +
          (2 + 4 * unitRoundoffAt fmt) * underflowErrorAt fmt ∨
      roundedSubError fmt p q ≤ 7 / 4 * (unitRoundoffAt fmt * p + underflowErrorAt fmt) ∨
      roundedSubError fmt p q ≤ unitRoundoffAt fmt * (p + q) + 2 * underflowErrorAt fmt := by
  have hu := (unitRoundoffAt_pos fmt).le
  have hp : 0 ≤ p := hq.trans hqp
  set P := roundAt fmt p
  set Q := roundAt fmt q
  have hQP : Q ≤ P := roundAt_mono fmt hqp
  have hd0 : 0 ≤ P - Q := sub_nonneg.mpr hQP
  -- The two inner errors, by half-ulps and in the mixed form.
  have hep : |P - p| ≤ halfUlpAt fmt p := abs_roundAt_sub_le fmt p
  have heq : |Q - q| ≤ halfUlpAt fmt q := abs_roundAt_sub_le fmt q
  have hhp : halfUlpAt fmt p ≤ unitRoundoffAt fmt * p + underflowErrorAt fmt := by
    simpa [abs_of_nonneg hp] using halfUlpAt_le fmt p
  have hhq : halfUlpAt fmt q ≤ unitRoundoffAt fmt * q + underflowErrorAt fmt := by
    simpa [abs_of_nonneg hq] using halfUlpAt_le fmt q
  have hsum : roundedSubError fmt p q ≤
      |roundAt fmt (P - Q) - (P - Q)| + (|P - p| + |Q - q|) := roundedSubError_le_add fmt p q
  by_cases h1 : halfUlpAt fmt p ≤ halfUlpAt fmt (P - Q)
  · -- The difference has the largest half-ulp: it bounds the error of `p` and its own.
    left
    have hd : halfUlpAt fmt (P - Q) ≤ unitRoundoffAt fmt * (P - Q) + underflowErrorAt fmt := by
      simpa [abs_of_nonneg hd0] using halfUlpAt_le fmt (P - Q)
    have houter : |roundAt fmt (P - Q) - (P - Q)| ≤ unitRoundoffAt fmt * (P - Q) := by
      have h : |roundAt fmt (P - Q) - (P - Q)| ≤ unitRoundoffAt fmt * |P - Q| :=
        abs_outer_le fmt p q
      rwa [abs_of_nonneg hd0] at h
    have hPQ : P - Q ≤ (p - q) + (halfUlpAt fmt p + halfUlpAt fmt q) := by
      have := (abs_le.mp hep).2
      have := (abs_le.mp heq).1
      linarith
    have hmul := mul_le_mul_of_nonneg_left (hPQ.trans (add_le_add le_rfl (add_le_add hhp hhq))) hu
    linarith
  · have h1' := two_mul_halfUlpAt_le_of_lt fmt (not_le.mp h1)
    right
    by_cases h2 : halfUlpAt fmt (P - Q) ≤ halfUlpAt fmt q
    · -- The difference has the smallest half-ulp: the subtraction is exact.
      have hexact : roundAt fmt (P - Q) = P - Q :=
        roundAt_sub_eq_of_halfUlpAt_le fmt (genericFormat_roundAt fmt p)
          (genericFormat_roundAt fmt q)
          ((not_le.mp h1).le.trans (halfUlpAt_le_halfUlpAt_roundAt fmt p))
          (h2.trans (halfUlpAt_le_halfUlpAt_roundAt fmt q))
      rw [hexact, sub_self, abs_zero, zero_add] at hsum
      by_cases h3 : halfUlpAt fmt q < halfUlpAt fmt p
      · left
        have := two_mul_halfUlpAt_le_of_lt fmt h3
        linarith
      · right
        linarith [not_lt.mp h3]
    · left
      have h2' := two_mul_halfUlpAt_le_of_lt fmt (not_le.mp h2)
      have houter := abs_roundAt_sub_le fmt (P - Q)
      linarith

/--
With cancellation, for operands of the same sign, with `m` the larger and `n` the smaller of
`|p|` and `|q|`, one of three bounds holds for the rounded difference:
`u (2m - n) + 2u² (m + n) + (2 + 4u) η`, `7/4 (u m + η)` or `u (m + n) + 2 η`.
-/
theorem roundedSubError_cases {p q : ℝ} (hpq : 0 ≤ p * q) :
    roundedSubError fmt p q ≤
        unitRoundoffAt fmt * (2 * max |p| |q| - min |p| |q|) +
          2 * unitRoundoffAt fmt ^ 2 * (max |p| |q| + min |p| |q|) +
          (2 + 4 * unitRoundoffAt fmt) * underflowErrorAt fmt ∨
      roundedSubError fmt p q ≤
        7 / 4 * (unitRoundoffAt fmt * max |p| |q| + underflowErrorAt fmt) ∨
      roundedSubError fmt p q ≤
        unitRoundoffAt fmt * (max |p| |q| + min |p| |q|) + 2 * underflowErrorAt fmt := by
  -- Both operands may be taken nonnegative, and then the first one the larger.
  have habs : roundedSubError fmt p q = roundedSubError fmt |p| |q| := by
    rcases mul_nonneg_iff.mp hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rw [abs_of_nonneg hp, abs_of_nonneg hq]
    · rw [abs_of_nonpos hp, abs_of_nonpos hq, roundedSubError_neg]
  rw [habs]
  rcases le_total |q| |p| with h | h
  · rw [max_eq_left h, min_eq_right h]
    exact roundedSubError_cases_of_le fmt (abs_nonneg q) h
  · rw [max_eq_right h, min_eq_left h, roundedSubError_comm]
    exact roundedSubError_cases_of_le fmt (abs_nonneg p) h

/--
One rounded operand and one rounding of the sum, as a fused multiply-add computes `a * c + q`
with `q` a rounded product: `|round (p + round q) - (p + q)| ≤ u |p + q| + u |q| + 3 η`.

There is no `u²` term, because the relative error of each rounding is at most `u / (1 + u)`
(`one_add_mul_abs_roundAt_sub_le`).
-/
theorem abs_roundAt_add_roundAt_sub_le (p q : ℝ) :
    |roundAt fmt (p + roundAt fmt q) - (p + q)| ≤
      unitRoundoffAt fmt * |p + q| + unitRoundoffAt fmt * |q| + 3 * underflowErrorAt fmt := by
  have hu := (unitRoundoffAt_pos fmt).le
  have hη := (underflowErrorAt_pos fmt).le
  have hv : (0 : ℝ) < 1 + unitRoundoffAt fmt := by positivity
  set u := unitRoundoffAt fmt
  set η := underflowErrorAt fmt
  set e₁ := |roundAt fmt q - q|
  set e₂ := |roundAt fmt (p + roundAt fmt q) - (p + roundAt fmt q)|
  have h₁ : (1 + u) * e₁ ≤ u * |q| + (1 + u) * η := one_add_mul_abs_roundAt_sub_le_add fmt q
  have h₂ : (1 + u) * e₂ ≤ u * |p + roundAt fmt q| + (1 + u) * η :=
    one_add_mul_abs_roundAt_sub_le_add fmt (p + roundAt fmt q)
  have ht : |p + roundAt fmt q| ≤ |p + q| + e₁ := by
    simpa only [sub_self, abs_zero, zero_add, add_sub_add_left_eq_sub, sub_zero] using
      Numerics.compose_error (Numerics.Backward.add (le_refl |p - p|)
        (le_refl |roundAt fmt q - q|)) (le_refl |p + q - 0|)
  have htotal : |roundAt fmt (p + roundAt fmt q) - (p + q)| ≤ e₂ + e₁ := by
    simpa only [sub_self, abs_zero, zero_add, add_comm] using
      Numerics.add_error (le_refl |p - p|) (le_refl |roundAt fmt q - q|)
        (le_refl |roundAt fmt (p + roundAt fmt q) - (p + roundAt fmt q)|)
  have hq0 := abs_nonneg q
  have hpq0 := abs_nonneg (p + q)
  -- Multiply by `(1 + u)²` and use each refined bound once.
  refine le_of_mul_le_mul_left ?_ (pow_pos hv 2)
  have a₀ := mul_le_mul_of_nonneg_left htotal (pow_pos hv 2).le
  have a₁ := mul_le_mul_of_nonneg_left h₂ hv.le
  have a₂ := mul_le_mul_of_nonneg_left h₁ hv.le
  have a₃ := mul_le_mul_of_nonneg_left ht (mul_nonneg hv.le hu)
  have a₄ := mul_le_mul_of_nonneg_left h₁ hu
  have b₁ := mul_nonneg (mul_nonneg hu hu) hpq0
  have b₃ := mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hq0
  have b₄ := mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hpq0
  have b₅ := mul_nonneg hu hη
  linarith

end Model
end FloatLib.Floats.Formats.BinaryInterchange
