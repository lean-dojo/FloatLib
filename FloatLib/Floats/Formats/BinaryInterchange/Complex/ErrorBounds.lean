/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.RoundedDifference
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Semantics

/-!
# Error bounds for whole complex operations

`Complex.Semantics` says which roundings each operation of `ExecComplex` performs. This module
bounds the error of the whole operation against the exact operation in `ℂ`, for every descriptor
and nearest-even rounding, with `u = unitRoundoffAt fmt` and `η = underflowErrorAt fmt`. A bound
is stated twice: for the rounded expression at any complex arguments (`roundedMul` and its
peers, every `FloatFormat`), and for the executable operation on an IEEE descriptor under the
finiteness premise of its semantic theorem.

* Addition and subtraction are componentwise relatively accurate: each component has error at
  most `u` times its exact value, with no underflow term, so the normwise relative error is at
  most `u` (`abs_toComplex_add_sub_le`, `norm_toComplex_add_sub_le` and the two for
  subtraction).
* The conventional product `x * y` (four products, one difference and one sum):
  * componentwise, the error of the real part is at most
    `(2u + u²)(|a c| + |b d|) + (2 + 2u) η`, and that of the imaginary part the same with
    `|a d| + |b c|` (`abs_roundedMul_sub_le`). No bound relative to `|a c - b d|` holds,
    because the difference can cancel.
  * normwise, `‖fl(x y) - x y‖ ≤ √5 u ‖x y‖ + 5 η` for formats with at least five bits of
    precision (`norm_roundedMul_sub_le`, `norm_toComplex_mul_sub_le`). This is Theorem 1 of
    Brent, Percival and Zimmermann with their hypothesis `u ≤ 2⁻⁵`. They assume that no
    underflow occurs; here an underflow of a product costs at most `5 η` in all.
* The product with fused multiply-adds `mulFma`:
  `‖fl(x y) - x y‖ ≤ 2 u ‖x y‖ + 5 η` for every descriptor (`norm_roundedMulFma_sub_le`,
  `norm_toComplex_mulFma_sub_le`). This is the constant `2u` of Jeannerod, Kornerup, Louvet and
  Muller for the product that uses one fused multiply-add per component. They prove it for
  precisions with `β ^ (p - 1) ≥ 24` when no underflow occurs; the statement here has no
  precision premise and has the underflow term.

* Division by the ratio formula (Smith's formula, the one `ExecComplex.div` runs):
  `‖fl(x / y) - x / y‖ ≤ √2 ((1 + u)⁴ / (1 - u)³ - 1) ‖x / y‖` when no product or quotient
  underflows (`norm_roundedDiv_sub_le`, `norm_toComplex_div_sub_le`, premise `DivNormal`). The
  constant is at most `√2 γ₇` with `γ₇ = 7u / (1 - 7u)`, in the notation of Higham's book
  (`pow_four_div_pow_three_sub_one_le`). We know of no published proof of a normwise bound for
  this formula, so the constant is what this proof gives: four roundings in each numerator
  and three in the denominator. Here underflow is a premise and not an absolute term: an
  underflow error `η`
  of the product in the denominator is a relative error `η / |c|` of the denominator, so no
  bound of the form `C u ‖x / y‖ + C' η` holds for divisors near the subnormal range.
* Magnitude by scaling: `|fl(|z|) - |z|| ≤ ((1 + u)⁴ - 1) |z| + η` when the inner roundings do
  not underflow (`abs_roundedMagnitude_sub_le`, `abs_toReal_magnitude_sub_le`, premise
  `MagnitudeNormal`). We found no published bound for this seven-rounding algorithm; the
  constant is what the factor count gives.

The constants `√5` and `2` are the published ones. The underflow constants `5` and the
constants of the division and of the magnitude are what these proofs give and are not claimed
sharp.

## References

- R. P. Brent, C. Percival and P. Zimmermann, "Error bounds on complex floating-point
  multiplication," Math. Comp. 76 (2007), 1469–1481, Theorem 1.
  https://doi.org/10.1090/S0025-5718-07-01931-X
- C.-P. Jeannerod, P. Kornerup, N. Louvet and J.-M. Muller, "Error bounds on complex
  floating-point multiplication with an FMA," Math. Comp. 86 (2017), 881–898.
  https://doi.org/10.1090/mcom/3123
- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, second edition, SIAM, 2002,
  Section 3.6, for the analysis of complex arithmetic under the standard model and the
  notation `γₙ = n u / (1 - n u)`. https://doi.org/10.1137/1.9780898718027
- R. L. Smith, "Algorithm 116: Complex division," Comm. ACM 5 (1962), 435, for the ratio
  formula. https://doi.org/10.1145/368637.368661
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

noncomputable section

open Model (unitRoundoffAt underflowErrorAt roundAt roundedSubError)

/-! ## From components to the norm -/

/-- A complex number whose squared components sum to at most `B ^ 2` has norm at most `B`. -/
private theorem norm_le_of_sq_add_sq_le {z : ℂ} {B : ℝ} (hB : 0 ≤ B)
    (h : z.re ^ 2 + z.im ^ 2 ≤ B ^ 2) : ‖z‖ ≤ B := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sqrt_le_iff]
  exact ⟨hB, h⟩

/-- The squared norm is the sum of the squared components. -/
private theorem sq_norm_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq]

/-- Componentwise relative error `u` gives normwise relative error `u`. -/
private theorem norm_sub_le_of_componentwise {z w : ℂ} {u : ℝ} (hu : 0 ≤ u)
    (h : |z.re - w.re| ≤ u * |w.re| ∧ |z.im - w.im| ≤ u * |w.im|) : ‖z - w‖ ≤ u * ‖w‖ := by
  refine norm_le_of_sq_add_sq_le (mul_nonneg hu (norm_nonneg w)) ?_
  have hre := pow_le_pow_left₀ (abs_nonneg _) h.1 2
  have him := pow_le_pow_left₀ (abs_nonneg _) h.2 2
  rw [sq_abs, mul_pow, sq_abs] at hre him
  rw [Complex.sub_re, Complex.sub_im, mul_pow, sq_norm_eq]
  simpa only [mul_add] using add_le_add hre him

/-! ## Addition and subtraction -/

/-- Complex addition is componentwise relatively accurate: each component of a finite sum is
within `u` times the exact component, with no underflow term. -/
theorem abs_toComplex_add_sub_le {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (hout : isFinite (x + y) = true) :
    |(toComplex (x + y)).re - (toComplex x + toComplex y).re| ≤
        unitRoundoffAt fmt * |(toComplex x + toComplex y).re| ∧
      |(toComplex (x + y)).im - (toComplex x + toComplex y).im| ≤
        unitRoundoffAt fmt * |(toComplex x + toComplex y).im| := by
  obtain ⟨hore, hoim⟩ := (isFinite_eq_true_iff (x + y)).1 hout
  exact ⟨Model.abs_toReal_add_sub_le_unitRoundoffAt x.re y.re hfmt hore,
    Model.abs_toReal_add_sub_le_unitRoundoffAt x.im y.im hfmt hoim⟩

/-- The normwise relative error of a finite complex sum is at most `u`. -/
theorem norm_toComplex_add_sub_le {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (hout : isFinite (x + y) = true) :
    ‖toComplex (x + y) - (toComplex x + toComplex y)‖ ≤
      unitRoundoffAt fmt * ‖toComplex x + toComplex y‖ :=
  norm_sub_le_of_componentwise (Model.unitRoundoffAt_pos fmt).le
    (abs_toComplex_add_sub_le x y hfmt hout)

/-- Complex subtraction is componentwise relatively accurate: each component of a finite
difference is within `u` times the exact component, with no underflow term. -/
theorem abs_toComplex_sub_sub_le {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (hout : isFinite (x - y) = true) :
    |(toComplex (x - y)).re - (toComplex x - toComplex y).re| ≤
        unitRoundoffAt fmt * |(toComplex x - toComplex y).re| ∧
      |(toComplex (x - y)).im - (toComplex x - toComplex y).im| ≤
        unitRoundoffAt fmt * |(toComplex x - toComplex y).im| := by
  obtain ⟨hore, hoim⟩ := (isFinite_eq_true_iff (x - y)).1 hout
  exact ⟨Model.abs_toReal_sub_sub_le_unitRoundoffAt x.re y.re hfmt hore,
    Model.abs_toReal_sub_sub_le_unitRoundoffAt x.im y.im hfmt hoim⟩

/-- The normwise relative error of a finite complex difference is at most `u`. -/
theorem norm_toComplex_sub_sub_le {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (hout : isFinite (x - y) = true) :
    ‖toComplex (x - y) - (toComplex x - toComplex y)‖ ≤
      unitRoundoffAt fmt * ‖toComplex x - toComplex y‖ :=
  norm_sub_le_of_componentwise (Model.unitRoundoffAt_pos fmt).le
    (abs_toComplex_sub_sub_le x y hfmt hout)

/-! ## The conventional product, componentwise -/

variable (fmt : FloatFormat)

/-- The real part of the error of the conventional product is a rounded difference of two
rounded products. -/
private theorem abs_roundedMul_re_sub (x y : ℂ) :
    |(roundedMul fmt x y - x * y).re| = roundedSubError fmt (x.re * y.re) (x.im * y.im) := by
  rw [Complex.sub_re, Complex.mul_re]
  rfl

/-- The imaginary part of the error of the conventional product is a rounded sum of two rounded
products. -/
private theorem abs_roundedMul_im_sub (x y : ℂ) :
    |(roundedMul fmt x y - x * y).im| = roundedSubError fmt (x.re * y.im) (-(x.im * y.re)) := by
  rw [Complex.sub_im, Complex.mul_im, ← Model.abs_roundAt_add_sub_eq_roundedSubError]
  rfl

/--
The componentwise bound of the conventional product, for every descriptor and all complex
arguments: with `x = a + b i` and `y = c + d i`, the real part is within
`(2u + u²)(|a c| + |b d|) + (2 + 2u) η` of `a c - b d`, and the imaginary part within
`(2u + u²)(|a d| + |b c|) + (2 + 2u) η` of `a d + b c`.

The bounds are relative to the sums of magnitudes, not to the components of the exact product:
`a c - b d` can cancel.
-/
theorem abs_roundedMul_sub_le (x y : ℂ) :
    |(roundedMul fmt x y).re - (x * y).re| ≤
        (2 * unitRoundoffAt fmt + unitRoundoffAt fmt ^ 2) * (|x.re * y.re| + |x.im * y.im|) +
          (2 + 2 * unitRoundoffAt fmt) * underflowErrorAt fmt ∧
      |(roundedMul fmt x y).im - (x * y).im| ≤
        (2 * unitRoundoffAt fmt + unitRoundoffAt fmt ^ 2) * (|x.re * y.im| + |x.im * y.re|) +
          (2 + 2 * unitRoundoffAt fmt) * underflowErrorAt fmt := by
  constructor
  · rw [← Complex.sub_re, abs_roundedMul_re_sub]
    exact Model.roundedSubError_le fmt _ _
  · rw [← Complex.sub_im, abs_roundedMul_im_sub]
    simpa using Model.roundedSubError_le fmt (x.re * y.im) (-(x.im * y.re))

/-! ## The conventional product, normwise -/

/-- The unit roundoff of a format with at least five bits of precision is at most `2⁻⁵`. -/
private theorem unitRoundoffAt_le (hprec : 4 ≤ fmt.fracWidth) : unitRoundoffAt fmt ≤ 1 / 32 := by
  rw [Model.unitRoundoffAt_eq]
  calc (2 : ℝ) ^ (-((fmt.fracWidth : ℤ) + 1)) ≤ (2 : ℝ) ^ (-5 : ℤ) :=
        zpow_le_zpow_right₀ (one_le_two) (by omega)
    _ = 1 / 32 := by norm_num

/--
The inequality behind the `√5 u` bound. `m ≥ n ≥ 0` are the magnitudes of the two products that
cancel and `s, t ≥ 0` those of the two that add, so `m n = s t`. `D` is the error of the
cancelling component, under one of the three bounds of `roundedSubError_cases`, and `E` that of
the other, at most `2u (s + t) + 4 η`. Then
`D² + E² ≤ (√5 u √((m - n)² + (s + t)²) + 5 η)²` when `u ≤ 2⁻⁵`.

The three cases use the identities of Brent, Percival and Zimmermann: with `N² = (m - n)² +
(s + t)²`, `(2m - n)² + 4 (s + t)² ≤ 32/7 N²`, `(7/4 m)² + 4 (s + t)² ≤ 1024/207 N²` and
`(m + n)² + 4 (s + t)² ≤ 5 N²`.
-/
private theorem sq_add_sq_le_of_cases {m n s t u η D E : ℝ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (hmn : m * n = s * t) (hu : 0 ≤ u) (hu' : u ≤ 1 / 32)
    (hη : 0 ≤ η) (hD : 0 ≤ D) (hE : 0 ≤ E) (hE' : E ≤ 2 * u * (s + t) + 4 * η)
    (hD' : D ≤ u * (2 * m - n) + 2 * u ^ 2 * (m + n) + (2 + 4 * u) * η ∨
      D ≤ 7 / 4 * (u * m + η) ∨ D ≤ u * (m + n) + 2 * η) :
    D ^ 2 + E ^ 2 ≤ (√5 * u * √((m - n) ^ 2 + (s + t) ^ 2) + 5 * η) ^ 2 := by
  have hm : 0 ≤ m := hn.trans hnm
  have hNsq0 : 0 ≤ (m - n) ^ 2 + (s + t) ^ 2 := by positivity
  set Nsq := (m - n) ^ 2 + (s + t) ^ 2 with hNsq
  set K := √5 * √Nsq with hK
  have hKsq : K ^ 2 = 5 * Nsq := by
    rw [hK, mul_pow, Real.sq_sqrt (Nat.ofNat_nonneg' 5 : (0 : ℝ) ≤ 5), Real.sq_sqrt hNsq0]
  -- An amplification factor `A` and an underflow count `c` for each case.
  obtain ⟨A, c, _, hc0, hc, hDA, hA⟩ : ∃ A c : ℝ, 0 ≤ A ∧ 0 ≤ c ∧ c ≤ 17 / 8 ∧
      D ≤ u * A + c * η ∧ A ^ 2 + 4 * (s + t) ^ 2 ≤ 5 * Nsq := by
    rcases hD' with h | h | h
    · refine ⟨2 * m - n + 2 * u * (m + n), 2 + 4 * u, ?_, by linarith, by linarith,
        h.trans (le_of_eq (by ring)), ?_⟩
      · have := mul_nonneg hu (add_nonneg hm hn)
        linarith
      · have h1 : (2 * m - n) ^ 2 + 4 * (s + t) ^ 2 ≤ 32 / 7 * Nsq := by
          rw [hNsq]
          linarith [sq_nonneg (s - t), sq_nonneg (2 * m - 5 * n)]
        have h2 : (m + n) ^ 2 ≤ Nsq := by
          rw [hNsq]
          linarith [sq_nonneg (s - t)]
        have h3 : (2 * m - n) * (m + n) ≤ 2 * (m + n) ^ 2 := by
          linarith [mul_nonneg hn (add_nonneg hm hn)]
        have h4 : 8 * u + 4 * u ^ 2 ≤ 3 / 7 := by
          linarith [mul_le_mul_of_nonneg_left hu' hu]
        have e1 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 4 * u)
        have e2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 8 * u + 4 * u ^ 2)
        have e3 := mul_le_mul_of_nonneg_right h4 hNsq0
        linarith
    · refine ⟨7 / 4 * m, 7 / 4, by positivity, by norm_num, by norm_num,
        h.trans (le_of_eq (by ring)), ?_⟩
      rw [hNsq]
      linarith [sq_nonneg (s - t), sq_nonneg (79 * m - 128 * n)]
    · refine ⟨m + n, 2, by positivity, by norm_num, by norm_num, h, ?_⟩
      rw [hNsq]
      linarith [sq_nonneg (s - t), sq_nonneg (m - n)]
  -- The two components, squared.
  have hX : D ^ 2 ≤ (u * A + c * η) ^ 2 := pow_le_pow_left₀ hD hDA 2
  have hY : E ^ 2 ≤ (2 * u * (s + t) + 4 * η) ^ 2 := pow_le_pow_left₀ hE hE' 2
  have hc2 : c ^ 2 + 16 ≤ 25 := by linarith [mul_le_mul_of_nonneg_left hc hc0]
  -- Cauchy–Schwarz for the cross term.
  have hCS : c * A + 8 * (s + t) ≤ 5 * K := by
    have hsq : (c * A + 8 * (s + t)) ^ 2 ≤ (5 * K) ^ 2 := by
      have hcs : (c * A + 8 * (s + t)) ^ 2 ≤ (c ^ 2 + 16) * (A ^ 2 + 4 * (s + t) ^ 2) := by
        convert Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (![c, 4] : Fin 2 → ℝ) (![A, 2 * (s + t)] : Fin 2 → ℝ) using 1 <;>
          norm_num [Fin.sum_univ_two, mul_pow, ← mul_assoc]
      have hprod : (c ^ 2 + 16) * (A ^ 2 + 4 * (s + t) ^ 2) ≤ 25 * (5 * Nsq) :=
        mul_le_mul hc2 hA (by positivity) (by norm_num)
      rw [mul_pow, hKsq]
      linarith
    exact (abs_le_of_sq_le_sq' hsq (by positivity)).2
  have e1 := mul_le_mul_of_nonneg_left hA (sq_nonneg u)
  have e2 := mul_le_mul_of_nonneg_left hCS (by positivity : 0 ≤ 2 * u * η)
  have e3 := mul_le_mul_of_nonneg_left hc2 (sq_nonneg η)
  have e4 : u ^ 2 * K ^ 2 = u ^ 2 * (5 * Nsq) := by rw [hKsq]
  have hgoal : (u * A + c * η) ^ 2 + (2 * u * (s + t) + 4 * η) ^ 2 ≤ (u * K + 5 * η) ^ 2 := by
    linarith
  calc D ^ 2 + E ^ 2 ≤ (u * A + c * η) ^ 2 + (2 * u * (s + t) + 4 * η) ^ 2 := add_le_add hX hY
    _ ≤ (u * K + 5 * η) ^ 2 := hgoal
    _ = (√5 * u * √Nsq + 5 * η) ^ 2 := by rw [hK]; ac_rfl

/-- The squared difference of the larger and the smaller of two reals. -/
private theorem max_sub_min_sq (a b : ℝ) : (max a b - min a b) ^ 2 = (a - b) ^ 2 := by
  rw [max_sub_min_eq_abs, sq_abs, sub_sq_comm]

/--
**The normwise error of the conventional complex product** (Brent, Percival and Zimmermann,
Theorem 1, with gradual underflow). For every descriptor with at least five bits of precision
and all complex `x` and `y`,

`‖roundedMul fmt x y - x * y‖ ≤ √5 * u * ‖x * y‖ + 5 * η`,

where `roundedMul` rounds the four products and then the difference and the sum to nearest
even. One of the two components cancels and the other does not. The proof bounds the first by
the three cases of `roundedSubError_cases` and the second by `roundedSubError_le_of_mul_nonpos`.
-/
theorem norm_roundedMul_sub_le (hprec : 4 ≤ fmt.fracWidth) (x y : ℂ) :
    ‖roundedMul fmt x y - x * y‖ ≤
      √5 * unitRoundoffAt fmt * ‖x * y‖ + 5 * underflowErrorAt fmt := by
  have hu := (Model.unitRoundoffAt_pos fmt).le
  have hu' := unitRoundoffAt_le fmt hprec
  have hη := (Model.underflowErrorAt_pos fmt).le
  have hnorm : ‖x * y‖ =
      √((x.re * y.re - x.im * y.im) ^ 2 + (x.re * y.im + x.im * y.re) ^ 2) := by
    simpa only [Complex.mul_re, Complex.mul_im] using Complex.norm_eq_sqrt_sq_add_sq (x * y)
  refine norm_le_of_sq_add_sq_le (by positivity) ?_
  rw [← sq_abs (roundedMul fmt x y - x * y).re, ← sq_abs (roundedMul fmt x y - x * y).im,
    abs_roundedMul_re_sub, abs_roundedMul_im_sub, hnorm]
  -- The four exact products: `P Q = S T`.
  set P := x.re * y.re with hP
  set Q := x.im * y.im with hQ
  set S := x.re * y.im with hS
  set T := x.im * y.re with hT
  have hPQ : P * Q = S * T := by rw [hP, hQ, hS, hT]; ac_rfl
  have habs : |P| * |Q| = |S| * |T| := by rw [← abs_mul, ← abs_mul, hPQ]
  rcases le_or_gt 0 (P * Q) with hpos | hneg
  · -- The real part cancels and the imaginary part does not.
    have hE := Model.roundedSubError_le_of_mul_nonpos fmt (p := S) (q := -T)
      (by rw [mul_neg, ← hPQ]; linarith)
    rw [abs_neg] at hE
    have hrad : (P - Q) ^ 2 + (S + T) ^ 2 =
        (max |P| |Q| - min |P| |Q|) ^ 2 + (|S| + |T|) ^ 2 := by
      rw [max_sub_min_sq]
      linarith [sq_abs P, sq_abs Q, sq_abs S, sq_abs T]
    rw [hrad]
    exact sq_add_sq_le_of_cases (le_min (abs_nonneg P) (abs_nonneg Q))
      min_le_max (by rw [max_mul_min, habs]) hu hu' hη
      (abs_nonneg _) (abs_nonneg _) hE (Model.roundedSubError_cases fmt hpos)
  · -- The imaginary part cancels and the real part does not.
    have hE := Model.roundedSubError_le_of_mul_nonpos fmt (p := P) (q := Q) hneg.le
    have hD := Model.roundedSubError_cases fmt (p := S) (q := -T)
      (by rw [mul_neg, ← hPQ]; linarith)
    rw [abs_neg] at hD
    have hrad : (P - Q) ^ 2 + (S + T) ^ 2 =
        (max |S| |T| - min |S| |T|) ^ 2 + (|P| + |Q|) ^ 2 := by
      rw [max_sub_min_sq]
      linarith [sq_abs P, sq_abs Q, sq_abs S, sq_abs T]
    rw [hrad, add_comm (roundedSubError fmt P Q ^ 2)]
    exact sq_add_sq_le_of_cases (le_min (abs_nonneg S) (abs_nonneg T))
      min_le_max (by rw [max_mul_min, habs]) hu hu' hη
      (abs_nonneg _) (abs_nonneg _) hE hD

/--
The normwise error of the executable complex product: for an IEEE descriptor with at least five
bits of precision and finite inputs, intermediate products and result,

`‖toComplex (x * y) - toComplex x * toComplex y‖ ≤ √5 * u * ‖toComplex x * toComplex y‖ + 5 * η`.
-/
theorem norm_toComplex_mul_sub_le {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (hprec : 4 ≤ fmt.fracWidth) (h : MulFinite x y) :
    ‖toComplex (x * y) - toComplex x * toComplex y‖ ≤
      √5 * unitRoundoffAt fmt * ‖toComplex x * toComplex y‖ + 5 * underflowErrorAt fmt := by
  rw [toComplex_mul_eq_roundedMul x y hfmt h]
  exact norm_roundedMul_sub_le fmt hprec _ _

/-- The componentwise error of the executable complex product, under the premises of
`toComplex_mul_eq_roundedMul`: see `abs_roundedMul_sub_le`. -/
theorem abs_toComplex_mul_sub_le {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (h : MulFinite x y) :
    |(toComplex (x * y)).re - (toComplex x * toComplex y).re| ≤
        (2 * unitRoundoffAt fmt + unitRoundoffAt fmt ^ 2) *
            (|(toComplex x).re * (toComplex y).re| + |(toComplex x).im * (toComplex y).im|) +
          (2 + 2 * unitRoundoffAt fmt) * underflowErrorAt fmt ∧
      |(toComplex (x * y)).im - (toComplex x * toComplex y).im| ≤
        (2 * unitRoundoffAt fmt + unitRoundoffAt fmt ^ 2) *
            (|(toComplex x).re * (toComplex y).im| + |(toComplex x).im * (toComplex y).re|) +
          (2 + 2 * unitRoundoffAt fmt) * underflowErrorAt fmt := by
  rw [toComplex_mul_eq_roundedMul x y hfmt h]
  exact abs_roundedMul_sub_le fmt _ _

/-! ## The product with fused multiply-adds -/

/--
The inequality behind the `2u` bound: with `R² + I² = N²` the components of the exact product
and `β₁² + β₂² ≤ N²` the two rounded products, component errors of at most
`u R + u β₁ + 3 η` and `u I + u β₂ + 3 η` have norm at most `2 u N + 5 η`.
-/
private theorem sq_add_sq_le_fused {R I β₁ β₂ N u η D E : ℝ} (hN : 0 ≤ N)
    (hRI : R ^ 2 + I ^ 2 = N ^ 2)
    (hβ : β₁ ^ 2 + β₂ ^ 2 ≤ N ^ 2) (hu : 0 ≤ u) (hη : 0 ≤ η) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hD' : D ≤ u * R + u * β₁ + 3 * η) (hE' : E ≤ u * I + u * β₂ + 3 * η) :
    D ^ 2 + E ^ 2 ≤ (2 * u * N + 5 * η) ^ 2 := by
  have hX := pow_le_pow_left₀ hD hD' 2
  have hY := pow_le_pow_left₀ hE hE' 2
  -- Cauchy–Schwarz, and each pair of components against the norm.
  have hcross : R * β₁ + I * β₂ ≤ N ^ 2 := by
    have hsq : (R * β₁ + I * β₂) ^ 2 ≤ (N ^ 2) ^ 2 := by
      have hmul : (R ^ 2 + I ^ 2) * (β₁ ^ 2 + β₂ ^ 2) = N ^ 2 * (β₁ ^ 2 + β₂ ^ 2) := by
        rw [hRI]
      linarith [sq_nonneg (R * β₂ - I * β₁), mul_le_mul_of_nonneg_left hβ (sq_nonneg N)]
    exact (abs_le_of_sq_le_sq' hsq (sq_nonneg N)).2
  have hsum : R + I ≤ 3 / 2 * N := by
    have hsq : (R + I) ^ 2 ≤ (3 / 2 * N) ^ 2 := by
      linarith [sq_nonneg (R - I), sq_nonneg N]
    exact (abs_le_of_sq_le_sq' hsq (by positivity)).2
  have hβsum : β₁ + β₂ ≤ 3 / 2 * N := by
    have hsq : (β₁ + β₂) ^ 2 ≤ (3 / 2 * N) ^ 2 := by
      linarith [sq_nonneg (β₁ - β₂), sq_nonneg N]
    exact (abs_le_of_sq_le_sq' hsq (by positivity)).2
  have e1 := mul_le_mul_of_nonneg_left hcross (by positivity : 0 ≤ 2 * u ^ 2)
  have e2 := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 6 * u * η)
  have e3 := mul_le_mul_of_nonneg_left hβsum (by positivity : 0 ≤ 6 * u * η)
  have e4 := mul_le_mul_of_nonneg_left hβ (sq_nonneg u)
  have e5 : u ^ 2 * (R ^ 2 + I ^ 2) = u ^ 2 * N ^ 2 := by rw [hRI]
  have e6 := mul_nonneg (mul_nonneg hu hη) hN
  linarith [sq_nonneg η]

/--
**The normwise error of the complex product with fused multiply-adds** (Jeannerod, Kornerup,
Louvet and Muller, with gradual underflow). For every descriptor and all complex `x` and `y`,

`‖roundedMulFma fmt x y - x * y‖ ≤ 2 * u * ‖x * y‖ + 5 * η`,

where `roundedMulFma` rounds `b d` and `b c`, and then `a c - round (b d)` and
`a d + round (b c)`.
-/
theorem norm_roundedMulFma_sub_le (x y : ℂ) :
    ‖roundedMulFma fmt x y - x * y‖ ≤
      2 * unitRoundoffAt fmt * ‖x * y‖ + 5 * underflowErrorAt fmt := by
  have hu := (Model.unitRoundoffAt_pos fmt).le
  have hη := (Model.underflowErrorAt_pos fmt).le
  refine norm_le_of_sq_add_sq_le (by positivity) ?_
  -- Each component is one rounded product and one rounding of the sum.
  have hre : |(roundedMulFma fmt x y - x * y).re| ≤
      unitRoundoffAt fmt * |x.re * y.re - x.im * y.im| + unitRoundoffAt fmt * |x.im * y.im| +
        3 * underflowErrorAt fmt := by
    have h := Model.abs_roundAt_add_roundAt_sub_le fmt (x.re * y.re) (-(x.im * y.im))
    rw [Model.roundAt_neg_nearest, abs_neg, ← sub_eq_add_neg, ← sub_eq_add_neg] at h
    rw [Complex.sub_re, Complex.mul_re]
    exact h
  have him : |(roundedMulFma fmt x y - x * y).im| ≤
      unitRoundoffAt fmt * |x.re * y.im + x.im * y.re| + unitRoundoffAt fmt * |x.im * y.re| +
        3 * underflowErrorAt fmt := by
    rw [Complex.sub_im, Complex.mul_im]
    exact Model.abs_roundAt_add_roundAt_sub_le fmt (x.re * y.im) (x.im * y.re)
  rw [← sq_abs (roundedMulFma fmt x y - x * y).re, ← sq_abs (roundedMulFma fmt x y - x * y).im]
  refine sq_add_sq_le_fused (norm_nonneg (x * y)) ?_ ?_ hu hη (abs_nonneg _) (abs_nonneg _)
    hre him
  · rw [sq_abs, sq_abs, sq_norm_eq, Complex.mul_re, Complex.mul_im]
  · rw [sq_abs, sq_abs, sq_norm_eq, Complex.mul_re, Complex.mul_im]
    linarith [sq_nonneg (x.re * y.re), sq_nonneg (x.re * y.im)]

/--
The normwise error of the executable product with fused multiply-adds: for an IEEE descriptor
and a finite result,

`‖toComplex (mulFma x y) - toComplex x * toComplex y‖ ≤ 2 * u * ‖toComplex x * toComplex y‖ + 5 *
η`.
-/
theorem norm_toComplex_mulFma_sub_le {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (hout : isFinite (mulFma x y) = true) :
    ‖toComplex (mulFma x y) - toComplex x * toComplex y‖ ≤
      2 * unitRoundoffAt fmt * ‖toComplex x * toComplex y‖ + 5 * underflowErrorAt fmt := by
  rw [toComplex_mulFma_eq_roundedMulFma x y hfmt hout]
  exact norm_roundedMulFma_sub_le fmt _ _

/-! ## Factors of roundings without an underflow error -/

/-- A product of a factor in `[lo ^ i, hi ^ i]` and one in `[lo ^ j, hi ^ j]` is in
`[lo ^ (i + j), hi ^ (i + j)]`. -/
private theorem mul_mem_pow {lo hi x y : ℝ} {i j : ℕ} (hlo : 0 ≤ lo)
    (hx : lo ^ i ≤ x ∧ x ≤ hi ^ i) (hy : lo ^ j ≤ y ∧ y ≤ hi ^ j) :
    lo ^ (i + j) ≤ x * y ∧ x * y ≤ hi ^ (i + j) := by
  have hx0 : 0 ≤ x := (pow_nonneg hlo i).trans hx.1
  have hy0 : 0 ≤ y := (pow_nonneg hlo j).trans hy.1
  rw [pow_add, pow_add]
  exact ⟨mul_le_mul hx.1 hy.1 (pow_nonneg hlo j) hx0,
    mul_le_mul hx.2 hy.2 hy0 (hx0.trans hx.2)⟩

/-- A quotient of a numerator in `[(1 - u)⁴, (1 + u)⁴]` by a denominator in
`[(1 - u)³, (1 + u)³]` is within `(1 + u)⁴ / (1 - u)³ - 1` of one. -/
private theorem abs_div_sub_one_le {u N D : ℝ} (hu : 0 ≤ u) (hu1 : u < 1)
    (hN : (1 - u) ^ 4 ≤ N ∧ N ≤ (1 + u) ^ 4) (hD : (1 - u) ^ 3 ≤ D ∧ D ≤ (1 + u) ^ 3) :
    |N / D - 1| ≤ (1 + u) ^ 4 / (1 - u) ^ 3 - 1 := by
  have hlo : 0 < 1 - u := by positivity
  have hlo3 : 0 < (1 - u) ^ 3 := pow_pos hlo 3
  have hhi3 : 0 < (1 + u) ^ 3 := by positivity
  have hD0 : 0 < D := hlo3.trans_le hD.1
  have hN0 : 0 ≤ N := (pow_nonneg hlo.le 4).trans hN.1
  have hupper : N / D ≤ (1 + u) ^ 4 / (1 - u) ^ 3 :=
    div_le_div₀ (by positivity) hN.2 hlo3 hD.1
  have hlower : (1 - u) ^ 4 / (1 + u) ^ 3 ≤ N / D := div_le_div₀ hN0 hN.1 hD0 hD.2
  have hsum : 2 ≤ (1 - u) ^ 4 / (1 + u) ^ 3 + (1 + u) ^ 4 / (1 - u) ^ 3 := by
    have hab : 1 - u ≤ 1 + u := (sub_le_self _ hu).trans (le_add_of_nonneg_right hu)
    rw [div_add_div _ _ hhi3.ne' hlo3.ne', le_div_iff₀ (mul_pos hhi3 hlo3)]
    calc
      _ = (1 - u) ^ 4 * (1 + u) ^ 3 + (1 + u) ^ 4 * (1 - u) ^ 3 := by
        conv_lhs => rw [show (2 : ℝ) = (1 - u) + (1 + u) by ring]
        rw [add_mul, pow_succ' (1 - u) 3, pow_succ' (1 + u) 3]
        simp only [mul_assoc, mul_comm, mul_left_comm]
      _ ≤ (1 - u) ^ 4 * (1 - u) ^ 3 + (1 + u) ^ 4 * (1 + u) ^ 3 :=
        mul_add_mul_le_mul_add_mul
          (pow_le_pow_left₀ hlo.le hab 4) (pow_le_pow_left₀ hlo.le hab 3)
      _ = _ := by simp only [mul_comm]
  rw [abs_le]
  refine ⟨?_, sub_le_sub_right hupper 1⟩
  rw [neg_sub, sub_le_sub_iff]
  simpa only [one_add_one_eq_two] using hsum.trans (add_le_add hlower le_rfl)

/-- The relative constant of the ratio division is at most `γ₇ = 7u / (1 - 7u)`. -/
theorem pow_four_div_pow_three_sub_one_le {u : ℝ} (hu : 0 ≤ u) (hu7 : 7 * u < 1) :
    (1 + u) ^ 4 / (1 - u) ^ 3 - 1 ≤ 7 * u / (1 - 7 * u) := by
  have hlo : 0 < 1 - u := by linarith
  have h7 : 0 < 1 - 7 * u := by positivity
  have hone : 1 + u ≤ 1 / (1 - u) := by
    rw [le_div_iff₀ hlo]
    linarith [sq_nonneg u]
  have hbern : 1 - 7 * u ≤ (1 - u) ^ 7 := by
    simpa only [Nat.cast_ofNat, mul_neg, ← sub_eq_add_neg] using
      one_add_mul_le_pow (show -2 ≤ -u by linarith) 7
  have hkey : (1 + u) ^ 4 / (1 - u) ^ 3 ≤ 1 / (1 - 7 * u) := by
    calc
      _ ≤ (1 / (1 - u)) ^ 4 / (1 - u) ^ 3 :=
        div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hone 4) (pow_nonneg hlo.le 3)
      _ = 1 / (1 - u) ^ 7 := by rw [div_pow, one_pow, div_div, ← pow_add]
      _ ≤ _ := one_div_le_one_div_of_le h7 hbern
  calc
    _ ≤ 1 / (1 - 7 * u) - 1 := sub_le_sub_right hkey 1
    _ = _ := by rw [div_sub_one h7.ne', sub_sub_cancel]

/-! ## Division by the ratio formula -/

/--
The relative change of the denominator of the ratio formula. With `0 ≤ q` and three factors in
`[1 - u, 1 + u]`, `(1 + q f₁ f₂) / (1 + q) · f₃` is in `[(1 - u)³, (1 + u)³]`.
-/
private theorem ratio_denominator_mem {q u f₁ f₂ f₃ : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    (hu1 : u < 1) (h₁ : 1 - u ≤ f₁ ∧ f₁ ≤ 1 + u) (h₂ : 1 - u ≤ f₂ ∧ f₂ ≤ 1 + u)
    (h₃ : 1 - u ≤ f₃ ∧ f₃ ≤ 1 + u) :
    (1 - u) ^ 3 ≤ (1 + q * (f₁ * f₂)) / (1 + q) * f₃ ∧
      (1 + q * (f₁ * f₂)) / (1 + q) * f₃ ≤ (1 + u) ^ 3 := by
  have hlo : 0 < 1 - u := by positivity
  have hq1 : 0 < 1 + q := by positivity
  have p₁ : (1 - u) ^ 1 ≤ f₁ ∧ f₁ ≤ (1 + u) ^ 1 := by simpa using h₁
  have p₂ : (1 - u) ^ 1 ≤ f₂ ∧ f₂ ≤ (1 + u) ^ 1 := by simpa using h₂
  have p₃ : (1 - u) ^ 1 ≤ f₃ ∧ f₃ ≤ (1 + u) ^ 1 := by simpa using h₃
  have hg : (1 - u) ^ 2 ≤ f₁ * f₂ ∧ f₁ * f₂ ≤ (1 + u) ^ 2 := mul_mem_pow hlo.le p₁ p₂
  have hratio : (1 - u) ^ 2 ≤ (1 + q * (f₁ * f₂)) / (1 + q) ∧
      (1 + q * (f₁ * f₂)) / (1 + q) ≤ (1 + u) ^ 2 := by
    rw [le_div_iff₀ hq1, div_le_iff₀ hq1]
    have hlo2 : (1 - u) ^ 2 ≤ 1 := pow_le_one₀ hlo.le (sub_le_self _ hu)
    have hhi2 : (1 : ℝ) ≤ (1 + u) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right hu)
    constructor
    · simpa only [mul_add, mul_one, mul_comm q] using
        add_le_add hlo2 (mul_le_mul_of_nonneg_left hg.1 hq)
    · simpa only [mul_add, mul_one, mul_comm q] using
        add_le_add hhi2 (mul_le_mul_of_nonneg_left hg.2 hq)
  exact mul_mem_pow hlo.le hratio p₃

/--
One component of the ratio formula with every rounding written as a factor. With `c ≠ 0` and
six factors in `[1 - u, 1 + u]`, the computed
`((a + b r f₄) f₅ / ((c + d r f₂) f₃)) f₆`, `r = (d / c) f₁`, is within
`((1 + u)⁴ / (1 - u)³ - 1) (|a c| + |b d|) / (c² + d²)` of `(a c + b d) / (c² + d²)`.
-/
private theorem abs_ratio_component_sub_le {a b c d u f₁ f₂ f₃ f₄ f₅ f₆ : ℝ} (hc : c ≠ 0)
    (hu : 0 ≤ u) (hu1 : u < 1)
    (h₁ : 1 - u ≤ f₁ ∧ f₁ ≤ 1 + u) (h₂ : 1 - u ≤ f₂ ∧ f₂ ≤ 1 + u)
    (h₃ : 1 - u ≤ f₃ ∧ f₃ ≤ 1 + u) (h₄ : 1 - u ≤ f₄ ∧ f₄ ≤ 1 + u)
    (h₅ : 1 - u ≤ f₅ ∧ f₅ ≤ 1 + u) (h₆ : 1 - u ≤ f₆ ∧ f₆ ≤ 1 + u) :
    |(a + b * (d / c * f₁) * f₄) * f₅ / ((c + d * (d / c * f₁) * f₂) * f₃) * f₆ -
        (a * c + b * d) / (c ^ 2 + d ^ 2)| ≤
      ((1 + u) ^ 4 / (1 - u) ^ 3 - 1) * ((|a * c| + |b * d|) / (c ^ 2 + d ^ 2)) := by
  have hlo : 0 < 1 - u := by positivity
  have hlo1 : 1 - u ≤ 1 := sub_le_self _ hu
  have hhi1 : (1 : ℝ) ≤ 1 + u := le_add_of_nonneg_right hu
  set γ := (1 + u) ^ 4 / (1 - u) ^ 3 - 1
  set q := (d / c) ^ 2 with hq
  have hq0 : 0 ≤ q := sq_nonneg _
  have hcd : c ^ 2 + d ^ 2 = c ^ 2 * (1 + q) := by
    rw [hq]
    field_simp
  have hq1 : 0 < 1 + q := by positivity
  -- The factors as powers of the two ends.
  have p₁ : (1 - u) ^ 1 ≤ f₁ ∧ f₁ ≤ (1 + u) ^ 1 := by simpa using h₁
  have p₄ : (1 - u) ^ 1 ≤ f₄ ∧ f₄ ≤ (1 + u) ^ 1 := by simpa using h₄
  have p₅ : (1 - u) ^ 1 ≤ f₅ ∧ f₅ ≤ (1 + u) ^ 1 := by simpa using h₅
  have p₆ : (1 - u) ^ 1 ≤ f₆ ∧ f₆ ≤ (1 + u) ^ 1 := by simpa using h₆
  -- The relative change of the denominator is in `[(1 - u)³, (1 + u)³]`.
  set Dn := (1 + q * (f₁ * f₂)) / (1 + q) * f₃ with hDn
  have hDnb : (1 - u) ^ 3 ≤ Dn ∧ Dn ≤ (1 + u) ^ 3 :=
    ratio_denominator_mem hq0 hu hu1 h₁ h₂ h₃
  -- The two numerators: two factors and four factors.
  have hNa : (1 - u) ^ 4 ≤ f₅ * f₆ ∧ f₅ * f₆ ≤ (1 + u) ^ 4 := by
    have h : (1 - u) ^ 2 ≤ f₅ * f₆ ∧ f₅ * f₆ ≤ (1 + u) ^ 2 := mul_mem_pow hlo.le p₅ p₆
    exact ⟨(pow_le_pow_of_le_one hlo.le hlo1 (by decide)).trans h.1,
      h.2.trans (pow_le_pow_right₀ hhi1 (by decide))⟩
  have hNb : (1 - u) ^ 4 ≤ f₁ * f₄ * (f₅ * f₆) ∧ f₁ * f₄ * (f₅ * f₆) ≤ (1 + u) ^ 4 :=
    mul_mem_pow hlo.le (mul_mem_pow hlo.le p₁ p₄) (mul_mem_pow hlo.le p₅ p₆)
  have hFa := abs_div_sub_one_le hu hu1 hNa hDnb
  have hFb := abs_div_sub_one_le hu hu1 hNb hDnb
  -- The computed and the exact component over the common denominator `c (1 + q)`.
  have hf₃ : f₃ ≠ 0 := (hlo.trans_le h₃.1).ne'
  have hcomputed : (a + b * (d / c * f₁) * f₄) * f₅ / ((c + d * (d / c * f₁) * f₂) * f₃) * f₆ =
      (a * (f₅ * f₆ / Dn) + b * (d / c) * (f₁ * f₄ * (f₅ * f₆) / Dn)) / (c * (1 + q)) := by
    rw [hDn, hq]
    field_simp
  have hexact : (a * c + b * d) / (c ^ 2 + d ^ 2) = (a + b * (d / c)) / (c * (1 + q)) := by
    rw [hq]
    field_simp
  rw [hcomputed, hexact, ← sub_div,
    show a * (f₅ * f₆ / Dn) + b * (d / c) * (f₁ * f₄ * (f₅ * f₆) / Dn) - (a + b * (d / c)) =
      a * (f₅ * f₆ / Dn - 1) + b * (d / c) * (f₁ * f₄ * (f₅ * f₆) / Dn - 1) by ring,
    abs_div]
  have hnum : |a * (f₅ * f₆ / Dn - 1) + b * (d / c) * (f₁ * f₄ * (f₅ * f₆) / Dn - 1)| ≤
      γ * (|a| + |b * (d / c)|) := by
    calc _ ≤ |a| * γ + |b * (d / c)| * γ :=
          Numerics.Backward.abs_add_le_add
            (Numerics.Backward.abs_mul_le_mul le_rfl hFa)
            (Numerics.Backward.abs_mul_le_mul le_rfl hFb)
      _ = γ * (|a| + |b * (d / c)|) := by rw [← add_mul, mul_comm]
  have hdenom : |c * (1 + q)| = |c| * (1 + q) := by rw [abs_mul, abs_of_pos hq1]
  have hfinal : (|a| + |b * (d / c)|) / (|c| * (1 + q)) =
      (|a * c| + |b * d|) / (c ^ 2 + d ^ 2) := by
    have hcabs : |c| ≠ 0 := abs_ne_zero.mpr hc
    rw [hcd, abs_mul, abs_mul, abs_mul, abs_div, ← sq_abs c]
    field_simp
  calc _ ≤ γ * (|a| + |b * (d / c)|) / |c * (1 + q)| :=
        div_le_div_of_nonneg_right hnum (abs_nonneg _)
    _ = γ * ((|a * c| + |b * d|) / (c ^ 2 + d ^ 2)) := by rw [hdenom, mul_div_assoc, hfinal]

/-- The quotient of two complex numbers by components. -/
private theorem div_eq_mk {x y : ℂ} :
    x / y = ⟨(x.re * y.re + x.im * y.im) / (y.re ^ 2 + y.im ^ 2),
      (x.im * y.re + -x.re * y.im) / (y.re ^ 2 + y.im ^ 2)⟩ := by
  apply Complex.ext <;>
    simp only [Complex.div_re, Complex.div_im, Complex.normSq_apply,
      pow_two, add_div, neg_mul, neg_div, sub_eq_add_neg]

/--
The products and quotients of the ratio formula with the real component `c` of the divisor as
pivot round without an underflow error: the ratio `d / c`, the three products with the rounded
ratio and the two final quotients are each zero or in the normal range. The sums need no
premise.
-/
structure DivNormal (fmt : FloatFormat) (x y : ℂ) : Prop where
  /-- The ratio of the denominator components. -/
  ratio : Model.NoUnderflowAt fmt (y.im / y.re)
  /-- The product in the denominator. -/
  denominator_product : Model.NoUnderflowAt fmt (y.im * roundAt fmt (y.im / y.re))
  /-- The product in the real numerator. -/
  re_product : Model.NoUnderflowAt fmt (x.im * roundAt fmt (y.im / y.re))
  /-- The product in the imaginary numerator. -/
  im_product : Model.NoUnderflowAt fmt (x.re * roundAt fmt (y.im / y.re))
  /-- The real quotient. -/
  re_quotient : Model.NoUnderflowAt fmt
    (roundAt fmt (x.re + roundAt fmt (x.im * roundAt fmt (y.im / y.re))) /
      roundAt fmt (y.re + roundAt fmt (y.im * roundAt fmt (y.im / y.re))))
  /-- The imaginary quotient. -/
  im_quotient : Model.NoUnderflowAt fmt
    (roundAt fmt (x.im - roundAt fmt (x.re * roundAt fmt (y.im / y.re))) /
      roundAt fmt (y.re + roundAt fmt (y.im * roundAt fmt (y.im / y.re))))

open FloatLib.Floats.Formats.Flocq in
/--
**The normwise error of complex division by the ratio formula**, with the real component of the
divisor as pivot: for grid points `a, b, c` with `c ≠ 0`, when no product or quotient underflows
(`DivNormal`),

`‖roundedDivRealDominant fmt x y - x / y‖ ≤ √2 * ((1 + u)⁴ / (1 - u)³ - 1) * ‖x / y‖`.

The constant is at most `√2 * 7u / (1 - 7u)` (`pow_four_div_pow_three_sub_one_le`). Each
component is within `(1 + u)⁴ / (1 - u)³ - 1` times `(|a c| + |b d|) / (c² + d²)`,
respectively `(|b c| + |a d|) / (c² + d²)`, of the exact one. The bound does not use
`|d| ≤ |c|`: choosing the larger component as pivot keeps the intermediate values in range and
does not change the relative accuracy.

With underflow no bound relative to `‖x / y‖` holds: an underflow error `η` of the product in
the denominator is a relative error `η / |c|` of the denominator, which is large for a divisor
near the subnormal range.
-/
theorem norm_roundedDivRealDominant_sub_le {x y : ℂ} (hc : y.re ≠ 0)
    (hxre : GenericRepresentable Numerics.binaryRadix (Model.fexpOf fmt) x.re)
    (hxim : GenericRepresentable Numerics.binaryRadix (Model.fexpOf fmt) x.im)
    (hyre : GenericRepresentable Numerics.binaryRadix (Model.fexpOf fmt) y.re)
    (h : DivNormal fmt x y) :
    ‖Internal.roundedDivRealDominant fmt x y - x / y‖ ≤
      √2 * ((1 + unitRoundoffAt fmt) ^ 4 / (1 - unitRoundoffAt fmt) ^ 3 - 1) * ‖x / y‖ := by
  have hu := (Model.unitRoundoffAt_pos fmt).le
  have hu1 := Model.unitRoundoffAt_lt_one fmt
  set u := unitRoundoffAt fmt
  set γ := (1 + u) ^ 4 / (1 - u) ^ 3 - 1
  have hγ0 : 0 ≤ γ := by
    apply sub_nonneg.mpr
    apply (one_le_div (pow_pos (sub_pos.mpr hu1) _)).mpr
    exact (pow_le_one₀ (sub_nonneg.mpr hu1.le) (sub_le_self _ hu)).trans
      (one_le_pow₀ (le_add_of_nonneg_right hu))
  have hsq : 0 < y.re ^ 2 + y.im ^ 2 := by positivity
  -- Every rounding as a factor.
  obtain ⟨f₁, e₁, b₁⟩ := Model.exists_roundAt_eq_mul fmt h.ratio
  obtain ⟨f₂, e₂, b₂⟩ := Model.exists_roundAt_eq_mul fmt h.denominator_product
  obtain ⟨f₃, e₃, b₃⟩ := Model.exists_roundAt_add_eq_mul fmt hyre
    (Model.genericFormat_roundAt fmt (y.im * roundAt fmt (y.im / y.re)))
  obtain ⟨f₄, e₄, b₄⟩ := Model.exists_roundAt_eq_mul fmt h.re_product
  obtain ⟨f₅, e₅, b₅⟩ := Model.exists_roundAt_add_eq_mul fmt hxre
    (Model.genericFormat_roundAt fmt (x.im * roundAt fmt (y.im / y.re)))
  obtain ⟨f₆, e₆, b₆⟩ := Model.exists_roundAt_eq_mul fmt h.re_quotient
  obtain ⟨f₇, e₇, b₇⟩ := Model.exists_roundAt_eq_mul fmt h.im_product
  obtain ⟨f₈, e₈, b₈⟩ := Model.exists_roundAt_add_eq_mul fmt hxim
    (genericRepresentable_neg _ (Model.genericFormat_roundAt fmt (x.re * roundAt fmt (y.im /
      y.re))))
  obtain ⟨f₉, e₉, b₉⟩ := Model.exists_roundAt_eq_mul fmt h.im_quotient
  -- The two components of the error.
  have hre : |(Internal.roundedDivRealDominant fmt x y - x / y).re| ≤
      γ * ((|x.re * y.re| + |x.im * y.im|) / (y.re ^ 2 + y.im ^ 2)) := by
    rw [Complex.sub_re, div_eq_mk]
    change |roundAt fmt (roundAt fmt (x.re + roundAt fmt (x.im * roundAt fmt (y.im / y.re))) /
      roundAt fmt (y.re + roundAt fmt (y.im * roundAt fmt (y.im / y.re)))) - _| ≤ _
    rw [e₆, e₅, e₄, e₃, e₂, e₁]
    exact abs_ratio_component_sub_le hc hu hu1 b₁ b₂ b₃ b₄ b₅ b₆
  have him : |(Internal.roundedDivRealDominant fmt x y - x / y).im| ≤
      γ * ((|x.im * y.re| + |x.re * y.im|) / (y.re ^ 2 + y.im ^ 2)) := by
    rw [Complex.sub_im, div_eq_mk]
    change |roundAt fmt (roundAt fmt (x.im - roundAt fmt (x.re * roundAt fmt (y.im / y.re))) /
      roundAt fmt (y.re + roundAt fmt (y.im * roundAt fmt (y.im / y.re)))) - _| ≤ _
    rw [e₉, sub_eq_add_neg x.im, e₈, e₇, e₃, e₂, e₁]
    have := abs_ratio_component_sub_le (a := x.im) (b := -x.re) (d := y.im) hc hu hu1
      b₁ b₂ b₃ b₇ b₈ b₉
    simpa [neg_mul, mul_neg, abs_neg] using this
  -- From the components to the norm.
  have hnorm : ‖x / y‖ ^ 2 = (x.re ^ 2 + x.im ^ 2) / (y.re ^ 2 + y.im ^ 2) := by
    rw [Complex.norm_div, div_pow, sq_norm_eq, sq_norm_eq]
  refine norm_le_of_sq_add_sq_le (by positivity) ?_
  rw [← sq_abs (Internal.roundedDivRealDominant fmt x y - x / y).re,
    ← sq_abs (Internal.roundedDivRealDominant fmt x y - x / y).im, mul_pow, mul_pow,
    Real.sq_sqrt (zero_le_two : (0 : ℝ) ≤ 2), hnorm]
  have h1 := pow_le_pow_left₀ (abs_nonneg _) hre 2
  have h2 := pow_le_pow_left₀ (abs_nonneg _) him 2
  have hcross : (|x.re * y.re| + |x.im * y.im|) ^ 2 + (|x.im * y.re| + |x.re * y.im|) ^ 2 ≤
      2 * ((x.re ^ 2 + x.im ^ 2) * (y.re ^ 2 + y.im ^ 2)) := by
    calc
      _ ≤ 2 * (|x.re * y.re| ^ 2 + |x.im * y.im| ^ 2) +
          2 * (|x.im * y.re| ^ 2 + |x.re * y.im| ^ 2) := add_le_add add_sq_le add_sq_le
      _ = _ := by simp only [sq_abs, mul_pow]; ring
  have hscale : (|x.re * y.re| + |x.im * y.im|) ^ 2 / (y.re ^ 2 + y.im ^ 2) ^ 2 +
      (|x.im * y.re| + |x.re * y.im|) ^ 2 / (y.re ^ 2 + y.im ^ 2) ^ 2 ≤
      2 * ((x.re ^ 2 + x.im ^ 2) / (y.re ^ 2 + y.im ^ 2)) := by
    rw [← add_div, div_le_iff₀ (sq_pos_of_pos hsq)]
    calc _ ≤ 2 * ((x.re ^ 2 + x.im ^ 2) * (y.re ^ 2 + y.im ^ 2)) := hcross
      _ = _ := by field_simp
  rw [mul_pow, div_pow] at h1 h2
  have := mul_le_mul_of_nonneg_left hscale (sq_nonneg γ)
  linarith

open FloatLib.Floats.Formats.Flocq in
/--
**The normwise error of complex division**, in both branches of the ratio formula: for grid
points `a, b, c, d` with `y = c + d i ≠ 0`, when no product or quotient of the selected branch
underflows,

`‖roundedDiv fmt x y - x / y‖ ≤ √2 * ((1 + u)⁴ / (1 - u)³ - 1) * ‖x / y‖`.

When `|c| < |d|` the formula runs on the exchanged components and conjugates, which computes
`x / y` again.
-/
theorem norm_roundedDiv_sub_le {x y : ℂ} (hy : y ≠ 0)
    (hxre : GenericRepresentable Numerics.binaryRadix (Model.fexpOf fmt) x.re)
    (hxim : GenericRepresentable Numerics.binaryRadix (Model.fexpOf fmt) x.im)
    (hyre : GenericRepresentable Numerics.binaryRadix (Model.fexpOf fmt) y.re)
    (hyim : GenericRepresentable Numerics.binaryRadix (Model.fexpOf fmt) y.im)
    (h : if |y.re| < |y.im| then DivNormal fmt ⟨x.im, x.re⟩ ⟨y.im, y.re⟩ else DivNormal fmt x y) :
    ‖roundedDiv fmt x y - x / y‖ ≤
      √2 * ((1 + unitRoundoffAt fmt) ^ 4 / (1 - unitRoundoffAt fmt) ^ 3 - 1) * ‖x / y‖ := by
  unfold roundedDiv
  split
  next hlt =>
    rw [ite_eq_left hlt] at h
    -- Exchanging the components of both operands conjugates the quotient.
    have hswap : x / y = starRingEnd ℂ ((⟨x.im, x.re⟩ : ℂ) / ⟨y.im, y.re⟩) := by
      have hswap (z : ℂ) : (⟨z.im, z.re⟩ : ℂ) = Complex.I * starRingEnd ℂ z := by
        simp only [Complex.I_mul, Complex.conj_im, Complex.conj_re, neg_neg]
      rw [hswap x, hswap y, mul_div_mul_left _ _ Complex.I_ne_zero,
        ← map_div₀, Complex.conj_conj]
    have hpivot : y.im ≠ 0 := fun hzero => by
      rw [hzero, abs_zero] at hlt
      exact absurd hlt (not_lt.mpr (abs_nonneg _))
    have hbound := norm_roundedDivRealDominant_sub_le fmt (x := ⟨x.im, x.re⟩)
      (y := ⟨y.im, y.re⟩) hpivot hxim hxre hyim h
    rw [hswap, ← map_sub, Complex.norm_conj, Complex.norm_conj]
    exact hbound
  next hlt =>
    rw [ite_eq_right hlt] at h
    have hpivot : y.re ≠ 0 := fun hzero => by
      rw [hzero, abs_zero] at hlt
      have him : y.im = 0 := abs_eq_zero.mp (le_antisymm (not_lt.mp hlt) (abs_nonneg _))
      exact hy (Complex.ext hzero him)
    exact norm_roundedDivRealDominant_sub_le fmt hpivot hxre hxim hyre h

/--
The normwise error of the executable complex division: for an IEEE descriptor, under the
finiteness premise of `toComplex_div_eq_roundedDiv` and without underflow of the products and
quotients of the selected branch,

`‖toComplex (x / y) - toComplex x / toComplex y‖ ≤ √2 * ((1 + u)⁴ / (1 - u)³ - 1) * ‖toComplex x
/ toComplex y‖`.
-/
theorem norm_toComplex_div_sub_le {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (hfinite : DivFinite x y)
    (hnormal : if |(toComplex y).re| < |(toComplex y).im| then
        DivNormal fmt ⟨(toComplex x).im, (toComplex x).re⟩ ⟨(toComplex y).im, (toComplex y).re⟩
      else DivNormal fmt (toComplex x) (toComplex y)) :
    ‖toComplex (x / y) - toComplex x / toComplex y‖ ≤
      √2 * ((1 + unitRoundoffAt fmt) ^ 4 / (1 - unitRoundoffAt fmt) ^ 3 - 1) *
        ‖toComplex x / toComplex y‖ := by
  obtain ⟨hxre, hxim⟩ := (isFinite_eq_true_iff x).1 hfinite.left
  obtain ⟨hyre, hyim⟩ := (isFinite_eq_true_iff y).1 hfinite.right
  -- The pivot of the selected branch is a nonzero component of the divisor.
  have hy : toComplex y ≠ 0 := by
    intro hzero
    have hre : Model.toReal y.re = 0 := congrArg Complex.re hzero
    have him : Model.toReal y.im = 0 := congrArg Complex.im hzero
    have hbranch := hfinite.branch
    split at hbranch
    · have hpivot := hbranch.pivot_nonzero
      rw [show (Internal.swap y).re = y.im from rfl,
        (Model.isZero_eq_true_iff_toReal_eq_zero y.im hyim).2 him] at hpivot
      exact absurd hpivot (by simp)
    · have hpivot := hbranch.pivot_nonzero
      rw [(Model.isZero_eq_true_iff_toReal_eq_zero y.re hyre).2 hre] at hpivot
      exact absurd hpivot (by simp)
  rw [toComplex_div_eq_roundedDiv x y hfmt hfinite]
  exact norm_roundedDiv_sub_le fmt hy (Model.toReal_genericFormat_of_isFinite x.re hxre)
    (Model.toReal_genericFormat_of_isFinite x.im hxim)
    (Model.toReal_genericFormat_of_isFinite y.re hyre)
    (Model.toReal_genericFormat_of_isFinite y.im hyim) hnormal

/-! ## Magnitude -/

/--
The inner roundings of the scaled magnitude round without an underflow error: the two component
ratios, their squares and the square root are each zero or in the normal range. The ratio of the
larger component is `±1`. The sum of the squares needs no premise, and the final product keeps
its underflow term.
-/
structure MagnitudeNormal (fmt : FloatFormat) (z : ℂ) : Prop where
  /-- The real component over the scale. -/
  ratio_re : Model.NoUnderflowAt fmt (z.re / max |z.re| |z.im|)
  /-- The imaginary component over the scale. -/
  ratio_im : Model.NoUnderflowAt fmt (z.im / max |z.re| |z.im|)
  /-- The square of the rounded real ratio. -/
  square_re : Model.NoUnderflowAt fmt
    (roundAt fmt (z.re / max |z.re| |z.im|) * roundAt fmt (z.re / max |z.re| |z.im|))
  /-- The square of the rounded imaginary ratio. -/
  square_im : Model.NoUnderflowAt fmt
    (roundAt fmt (z.im / max |z.re| |z.im|) * roundAt fmt (z.im / max |z.re| |z.im|))
  /-- The square root of the rounded sum of squares. -/
  root : Model.NoUnderflowAt fmt (√(roundedNormSq fmt
    ⟨roundAt fmt (z.re / max |z.re| |z.im|), roundAt fmt (z.im / max |z.re| |z.im|)⟩))

/--
The scaled magnitude before its last rounding, with the six inner roundings written as factors
in `[1 - u, 1 + u]`: it is between `(1 - u)³ √(a² + b²)` and `(1 + u)³ √(a² + b²)`.
-/
private theorem scaled_magnitude_bounds {a b s u f₁ f₂ g₁ g₂ g₃ g₄ : ℝ} (hs : 0 < s)
    (hu : 0 ≤ u) (hu1 : u < 1)
    (h₁ : 1 - u ≤ f₁ ∧ f₁ ≤ 1 + u) (h₂ : 1 - u ≤ f₂ ∧ f₂ ≤ 1 + u)
    (k₁ : 1 - u ≤ g₁ ∧ g₁ ≤ 1 + u) (k₂ : 1 - u ≤ g₂ ∧ g₂ ≤ 1 + u)
    (k₃ : 1 - u ≤ g₃ ∧ g₃ ≤ 1 + u) (k₄ : 1 - u ≤ g₄ ∧ g₄ ≤ 1 + u) :
    (1 - u) ^ 3 * √(a ^ 2 + b ^ 2) ≤
        s * (√((a / s * f₁ * (a / s * f₁) * g₁ + b / s * f₂ * (b / s * f₂) * g₂) * g₃) * g₄) ∧
      s * (√((a / s * f₁ * (a / s * f₁) * g₁ + b / s * f₂ * (b / s * f₂) * g₂) * g₃) * g₄) ≤
        (1 + u) ^ 3 * √(a ^ 2 + b ^ 2) := by
  have hlo : 0 < 1 - u := by positivity
  have hhi : 0 < 1 + u := by positivity
  have p₁ : (1 - u) ^ 1 ≤ f₁ ∧ f₁ ≤ (1 + u) ^ 1 := by simpa using h₁
  have p₂ : (1 - u) ^ 1 ≤ f₂ ∧ f₂ ≤ (1 + u) ^ 1 := by simpa using h₂
  have q₁ : (1 - u) ^ 1 ≤ g₁ ∧ g₁ ≤ (1 + u) ^ 1 := by simpa using k₁
  have q₂ : (1 - u) ^ 1 ≤ g₂ ∧ g₂ ≤ (1 + u) ^ 1 := by simpa using k₂
  have q₃ : (1 - u) ^ 1 ≤ g₃ ∧ g₃ ≤ (1 + u) ^ 1 := by simpa using k₃
  -- Each rounded square, and their rounded sum, against the exact scaled squares.
  have hA : (1 - u) ^ 4 ≤ f₁ * f₁ * g₁ * g₃ ∧ f₁ * f₁ * g₁ * g₃ ≤ (1 + u) ^ 4 :=
    mul_mem_pow hlo.le (mul_mem_pow hlo.le (mul_mem_pow hlo.le p₁ p₁) q₁) q₃
  have hB : (1 - u) ^ 4 ≤ f₂ * f₂ * g₂ * g₃ ∧ f₂ * f₂ * g₂ * g₃ ≤ (1 + u) ^ 4 :=
    mul_mem_pow hlo.le (mul_mem_pow hlo.le (mul_mem_pow hlo.le p₂ p₂) q₂) q₃
  set M := (a ^ 2 + b ^ 2) / s ^ 2 with hM
  have hsum : (a / s * f₁ * (a / s * f₁) * g₁ + b / s * f₂ * (b / s * f₂) * g₂) * g₃ =
      (a / s) ^ 2 * (f₁ * f₁ * g₁ * g₃) + (b / s) ^ 2 * (f₂ * f₂ * g₂ * g₃) := by
    rw [add_mul, sq, sq]
    ac_rfl
  have hMsplit : M = (a / s) ^ 2 + (b / s) ^ 2 := by
    rw [hM, add_div, div_pow, div_pow]
  have hlower : (1 - u) ^ 4 * M ≤
      (a / s * f₁ * (a / s * f₁) * g₁ + b / s * f₂ * (b / s * f₂) * g₂) * g₃ := by
    rw [hsum, hMsplit, mul_add]
    exact add_le_add (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hA.1 (sq_nonneg _))
      (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hB.1 (sq_nonneg _))
  have hupper : (a / s * f₁ * (a / s * f₁) * g₁ + b / s * f₂ * (b / s * f₂) * g₂) * g₃ ≤
      (1 + u) ^ 4 * M := by
    rw [hsum, hMsplit, mul_add]
    exact add_le_add (by rw [mul_comm ((1 + u) ^ 4)]; exact
      mul_le_mul_of_nonneg_left hA.2 (sq_nonneg _))
      (by rw [mul_comm ((1 + u) ^ 4)]; exact mul_le_mul_of_nonneg_left hB.2 (sq_nonneg _))
  -- Square roots.
  have hsqrtM : s * √M = √(a ^ 2 + b ^ 2) := by
    rw [hM, Real.sqrt_div' _ (sq_nonneg s), Real.sqrt_sq hs.le]
    exact mul_div_cancel₀ _ hs.ne'
  have hsqrt : ∀ {v : ℝ}, 0 ≤ v → √(v ^ 4 * M) = v ^ 2 * √M := by
    intro v hv
    rw [Real.sqrt_mul (pow_nonneg hv 4), show v ^ 4 = (v ^ 2) ^ 2 by rw [← pow_mul],
      Real.sqrt_sq (pow_nonneg hv 2)]
  have hroot_lower : (1 - u) ^ 2 * √M ≤
      √((a / s * f₁ * (a / s * f₁) * g₁ + b / s * f₂ * (b / s * f₂) * g₂) * g₃) :=
    (hsqrt hlo.le).symm.trans_le (Real.sqrt_le_sqrt hlower)
  have hroot_upper : √((a / s * f₁ * (a / s * f₁) * g₁ + b / s * f₂ * (b / s * f₂) * g₂) * g₃) ≤
      (1 + u) ^ 2 * √M :=
    (Real.sqrt_le_sqrt hupper).trans_eq (hsqrt hhi.le)
  set r := √((a / s * f₁ * (a / s * f₁) * g₁ + b / s * f₂ * (b / s * f₂) * g₂) * g₃)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  constructor
  · calc (1 - u) ^ 3 * √(a ^ 2 + b ^ 2) = s * ((1 - u) ^ 2 * √M * (1 - u)) := by
          rw [← hsqrtM]; ac_rfl
      _ ≤ s * (r * g₄) := mul_le_mul_of_nonneg_left
          (mul_le_mul hroot_lower k₄.1 hlo.le hr0) hs.le
  · calc s * (r * g₄) ≤ s * ((1 + u) ^ 2 * √M * (1 + u)) := mul_le_mul_of_nonneg_left
          (mul_le_mul hroot_upper k₄.2 (hlo.le.trans k₄.1) (hr0.trans hroot_upper)) hs.le
      _ = (1 + u) ^ 3 * √(a ^ 2 + b ^ 2) := by rw [← hsqrtM, pow_succ (1 + u) 2]; ac_rfl

/--
**The error of the scaled magnitude.** For every descriptor and every complex `z` whose inner
roundings do not underflow (`MagnitudeNormal`),

`|roundedMagnitude fmt z - ‖z‖| ≤ ((1 + u)⁴ - 1) * ‖z‖ + η`,

where `roundedMagnitude` divides both components by the larger magnitude, squares, adds, takes
the square root and multiplies by the scale, rounding seven times. The term `η` is the
underflow of the last product. The relative constant is `4u + O(u²)`; it is not claimed sharp.
-/
theorem abs_roundedMagnitude_sub_le (z : ℂ) (h : MagnitudeNormal fmt z) :
    |roundedMagnitude fmt z - ‖z‖| ≤
      ((1 + unitRoundoffAt fmt) ^ 4 - 1) * ‖z‖ + underflowErrorAt fmt := by
  have hu := (Model.unitRoundoffAt_pos fmt).le
  have hu1 := Model.unitRoundoffAt_lt_one fmt
  have hη := (Model.underflowErrorAt_pos fmt).le
  have hnorm : ‖z‖ = √(z.re ^ 2 + z.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    ring
  unfold roundedMagnitude
  dsimp only
  split
  next hzero =>
    -- Both components are zero.
    have hre : z.re = 0 := abs_eq_zero.mp
      (le_antisymm ((le_max_left _ _).trans hzero.le) (abs_nonneg _))
    have him : z.im = 0 := abs_eq_zero.mp
      (le_antisymm ((le_max_right _ _).trans hzero.le) (abs_nonneg _))
    rw [hnorm, hre, him]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Real.sqrt_zero,
      sub_self, abs_zero, mul_zero, zero_add, ge_iff_le]
    exact hη
  next hzero =>
    have hs0 : 0 < max |z.re| |z.im| :=
      lt_of_le_of_ne ((abs_nonneg _).trans (le_max_left _ _)) (Ne.symm hzero)
    obtain ⟨hratio_re, hratio_im, hsquare_re, hsquare_im, hroot⟩ := h
    simp only [roundedNormSq] at hroot ⊢
    generalize max |z.re| |z.im| = s at *
    set u := unitRoundoffAt fmt
    obtain ⟨f₁, e₁, b₁⟩ := Model.exists_roundAt_eq_mul fmt hratio_re
    obtain ⟨f₂, e₂, b₂⟩ := Model.exists_roundAt_eq_mul fmt hratio_im
    obtain ⟨g₁, d₁, c₁⟩ := Model.exists_roundAt_eq_mul fmt hsquare_re
    obtain ⟨g₂, d₂, c₂⟩ := Model.exists_roundAt_eq_mul fmt hsquare_im
    obtain ⟨g₃, d₃, c₃⟩ := Model.exists_roundAt_add_eq_mul fmt
      (Model.genericFormat_roundAt fmt (roundAt fmt (z.re / s) * roundAt fmt (z.re / s)))
      (Model.genericFormat_roundAt fmt (roundAt fmt (z.im / s) * roundAt fmt (z.im / s)))
    obtain ⟨g₄, d₄, c₄⟩ := Model.exists_roundAt_eq_mul fmt hroot
    rw [d₄, d₃, d₁, d₂, e₁, e₂, hnorm]
    set N := √(z.re ^ 2 + z.im ^ 2)
    have hN0 : 0 ≤ N := Real.sqrt_nonneg _
    obtain ⟨hlow, hhigh⟩ := scaled_magnitude_bounds (a := z.re) (b := z.im) hs0 hu hu1
      b₁ b₂ c₁ c₂ c₃ c₄
    set t := s * (√((z.re / s * f₁ * (z.re / s * f₁) * g₁ +
      z.im / s * f₂ * (z.im / s * f₂) * g₂) * g₃) * g₄)
    have ht0 : 0 ≤ t := (mul_nonneg (pow_nonneg (by linarith) 3) hN0).trans hlow
    -- The last rounding, with its underflow term.
    have hlast := Model.abs_roundAt_sub_le_unitRoundoffAt fmt t
    rw [abs_of_nonneg ht0] at hlast
    have hlast' := abs_le.mp hlast
    have h2 : 2 * N ≤ ((1 - u) ^ 4 + (1 + u) ^ 4) * N := by
      have := pow_nonneg hu 2
      have := pow_nonneg hu 4
      exact mul_le_mul_of_nonneg_right (by linarith) hN0
    have h3 := mul_le_mul_of_nonneg_left hhigh (by linarith : (0 : ℝ) ≤ 1 + u)
    have h4 := mul_le_mul_of_nonneg_left hlow (by linarith : (0 : ℝ) ≤ 1 - u)
    rw [abs_le]
    constructor <;> linarith

/--
The error of the executable magnitude: for an IEEE descriptor, under the finiteness premise of
`toReal_magnitude_eq_roundedMagnitude` and without underflow of the inner roundings,

`|toReal (magnitude z) - ‖toComplex z‖| ≤ ((1 + u)⁴ - 1) * ‖toComplex z‖ + η`.
-/
theorem abs_toReal_magnitude_sub_le {fmt : FloatFormat} (z : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (hfinite : MagnitudeFinite z)
    (hnormal : MagnitudeNormal fmt (toComplex z)) :
    |Model.toReal (magnitude z) - ‖toComplex z‖| ≤
      ((1 + unitRoundoffAt fmt) ^ 4 - 1) * ‖toComplex z‖ + underflowErrorAt fmt := by
  rw [toReal_magnitude_eq_roundedMagnitude z hfmt hfinite]
  exact abs_roundedMagnitude_sub_le fmt _ hnormal

end
end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
