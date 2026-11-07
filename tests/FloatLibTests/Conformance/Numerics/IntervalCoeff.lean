/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Automation.Interval
public import FloatLib.Numerics.Packed.Literal

/-!
# Bounds over a whole domain by `interval`

Each goal here bounds a series over its whole domain, so `interval` proves it from the
coefficients and never splits a box.

## Main statements

* Trigonometric polynomials on the circle. `exact_min` is `1/2 + cos u + 1/2 cos (2u)`, which is
  `(cos u + 1/2)² - 1/4`, so the factor `[1, 1, 1]` proves the minimum `-1/4` exactly, here as a
  sum block and as monomials. `sine_ball`, `free_sine` and `ramp_ball` are bounds from the
  coefficients alone, with no certificate. `sine_exact` is `1 + sin u = |1 - i z|² / 2`, whose
  factor needs an imaginary part, and `difference` bounds one polynomial by another.
* `mixed_abs`: a polynomial with 24 cosine and 24 sine coefficients below `2 ^ 40`, decaying like
  `1.15 ^ (-k)`, drawn by Python's `random` with seed `20261107`. Its maximum on the circle is
  `2.97980661e12`, and two certificates with complex factors from
  `scripts/coeff_cert.py MixedCos.txt --sin MixedSin.txt --abs auto --slack 1e-7` prove
  `|S(u)| ≤ 2.9798074e12`, while the `l1` norm is `7.27e12`.
* `row_bound`: a cosine polynomial with 200 integer coefficients below `2 ^ 80` that decay like
  `1.04 ^ (-k)`, read by `packed_row` from `IntervalCoeffRow.txt`. Its maximum is
  `4.72552689e24` and its `l1` norm `1.632e25`, 3.45 times larger; two certificates prove
  `|R(u)| ≤ 4.7255286e24`, within `4e-7` of the maximum.
* Chebyshev series on `[-1, 1]` and, in the variable `(x - 4) / 2`, on `[2, 6]`.
* Polynomials in the power basis on an interval, through Horner's rule in the kernel:
  `power_exact` is `x² - x ≥ -1/4` on `[0, 1]` from the coefficients alone, and `power_lower` a
  degree-9 polynomial with coefficients `k / 2 ^ (j + 3)` on `[-1, 3]` whose minimum
  `-191.528808594` the certificate proves up to `-191.52881`. `power_boxes` is a bound that the
  coefficients do not give, which the boxes then prove.
* Norms of polynomials on the unit circle of `ℂ`: `norm_ball` from the coefficients alone, and
  `norm_upper` and `norm_lower` for a degree-8 polynomial with Gaussian-integer coefficients below
  `2 ^ 10` (and `6000` added to the constant), whose norm ranges over `[2608.2352, 8996.4255]` on
  the circle.
* Negative controls. `interval` refuses a wrong factor, a bound above the minimum, a bound that the
  coefficients alone do not give, a Chebyshev point outside `[-1, 1]` (where the boxes fail too,
  since they cannot read a list), a strict bound at an attained minimum and a certificate on a goal
  that is not a series. In the kernel, `exact_min_check` and
  `complex_check` refuse wrong factors, `wrong_link` a coefficient list that does not match its
  row, and `wrong_horner` a power row that is not the composed one.

## Implementation notes

Every proof runs with `(maxHeartbeats := B)` for its kernel checks at about three times what they
need, so the build fails if their kernel cost grows. Most of these checks need under 16,000
heartbeats, the 48-term mixed polynomial under 64,000 and the 200-term row under 200,000, because
the kernel's big-number arithmetic hardly counts against the budget. We found each budget by
trying a ladder of values and keeping the smallest that passed.

The certificate files were written by `scripts/coeff_cert.py` and are untrusted data. Each one
starts with comment lines that record the bound, the scale and the exact check the script ran.

## References

* Lipót Fejér, *Über trigonometrische Polynome*, J. Reine Angew. Math. 146 (1916), 53–82,
  <https://doi.org/10.1515/crll.1916.146.53>, for why a certificate exists below every minimum.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.IntervalCoeff

open FloatLib.Numerics.Packed FloatLib.Numerics.Coeff Finset

/-! ## Trigonometric polynomials -/

/-- The minimum of `1/2 + cos u + 1/2 cos (2u)`, attained at `cos u = -1/2`. -/
theorem exact_min : ∀ u : ℝ,
    -1/4 ≤ ∑ k ∈ range 3, (([1/2, 1, 1/2] : List ℚ).getD k 0 : ℝ) * Real.cos (k * u) := by
  interval (lower := [1, 1, 1]) (maxHeartbeats := 50)

/-- The same minimum, written with monomials. -/
theorem exact_min_monomials : ∀ u : ℝ, -1/4 ≤ 1/2 + Real.cos u + Real.cos (2 * u) / 2 := by
  interval (lower := [1, 1, 1]) (maxHeartbeats := 50)

/-- The bound of the coefficients alone on `2 sin u - sin (2u)`. -/
theorem sine_ball : ∀ u : ℝ,
    |∑ k ∈ range 3, (([0, 2, -1] : List ℚ).getD k 0 : ℝ) * Real.sin (k * u)| ≤ 3 := by
  interval (maxHeartbeats := 50)

/-- The same bound at a free variable, which the boxes cannot bound. -/
theorem free_sine (u : ℝ) :
    |∑ k ∈ range 3, (([0, 2, -1] : List ℚ).getD k 0 : ℝ) * Real.sin (k * u)| ≤ 3 := by
  interval (maxHeartbeats := 50)

/-- The bound of the coefficients alone on `∑ k < 5, k cos (k u)`. -/
theorem ramp_ball : ∀ u : ℝ, ∑ k ∈ range 5, ((k : ℤ) : ℝ) * Real.cos (k * u) ≤ 10 := by
  interval (maxHeartbeats := 50)

/-- Cancellation has a zero bound over the whole circle. -/
theorem zero_bounds : (∀ u : ℝ, Real.cos u ≤ Real.cos u) ∧
    ∀ u : ℝ, |Real.sin u - Real.sin u| ≤ 0 :=
  ⟨by interval, by interval⟩

/-- Empty coefficient lists may be hidden behind truncation or a nonempty sum range. -/
theorem empty_power_rows :
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      (∑ k ∈ range 0, (([1] : List ℚ).getD k 0 : ℝ) * x ^ k) ≤ 0) ∧
    ∀ x ∈ Set.Icc (-2 : ℝ) 3,
      (∑ k ∈ range 5, ((([1, 2] : List ℚ).take 0).getD k 0 : ℝ) * x ^ k) ≤ 0 :=
  ⟨by interval, by interval⟩

/-- Whole-interval goals outside the coefficient families still use the box evaluator. -/
theorem elementary_boxes : (∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3) ∧
    ∀ x ∈ Set.Icc (1 : ℝ) 4, Real.sqrt x ≤ 2 :=
  ⟨by interval, by interval⟩

/-- `1 + sin u = |1 - i z|² / 2`: a sine term needs a factor with an imaginary part. -/
theorem sine_exact : ∀ u : ℝ, 0 ≤ 1 + Real.sin u := by
  interval (lower := ([1, 0], [0, -1])) (maxHeartbeats := 50)

/-- One polynomial below another, read as `0 ≤ 2 - cos u - cos (2u)`, and a strict bound. -/
theorem difference : (∀ u : ℝ, Real.cos u ≤ 2 - Real.cos (2 * u)) ∧
    ∀ u : ℝ, Real.cos u - Real.sin (3 * u) < 2.5 :=
  ⟨by interval (maxHeartbeats := 50), by interval (maxHeartbeats := 50)⟩

/-- The 24 cosine coefficients. -/
def mixedCos : List ℚ := [
    142063823435, -228885300033, 511691014908, -506228883985, 135816329610, -280054396895,
    -268524943921, -354351131968, 41080568816, -272149532413, -155887829947, -200873204151,
    199566421704, -111892891964, -103370934590, -71377635122, -49734437668, 57682189616,
    -13125496834, 19979567484, 60406090598, 36401845766, 27215810552, -37499894765]

/-- The 24 sine coefficients. -/
def mixedSin : List ℚ := [
    0, 241774221839, -445426236358, 488594875908, -550466506857, -80459159331,
    18116736252, -43819502676, -249598837558, 312130100659, -197976063878, 7668398363,
    194578947767, 54459895033, 70982878134, 123373693673, 6640280004, 101029937648,
    56483068368, 17410198909, -39501527896, -50755987303, -1629018514, -34772770019]

/-- The two-sided bound on the mixed polynomial, from two complex factors. -/
theorem mixed_abs : ∀ u : ℝ,
    |∑ k ∈ range 24, (mixedCos.getD k 0 : ℝ) * Real.cos (k * u) +
      ∑ k ∈ range 24, (mixedSin.getD k 0 : ℝ) * Real.sin (k * u)| ≤ 2979807400000 := by
  interval (lower := ("IntervalCoeffMixed_lower.txt", "IntervalCoeffMixed_lower_im.txt"))
    (upper := ("IntervalCoeffMixed_upper.txt", "IntervalCoeffMixed_upper_im.txt"))
    (maxHeartbeats := 200)

/-- The 200 integer coefficients. -/
packed_row row (width := 96) from "IntervalCoeffRow.txt"

/-- The sharp two-sided bound on the 200-term polynomial. -/
theorem row_bound : ∀ u : ℝ,
    |∑ k ∈ range 200, (entry 96 k row : ℝ) * Real.cos (k * u)| ≤ 4725528600000000000000000 := by
  interval (lower := "IntervalCoeffRow_lower.txt") (upper := "IntervalCoeffRow_upper.txt")
    (maxHeartbeats := 600)

/-! ## Chebyshev series and polynomials on an interval -/

/-- The minimum of `1/2 + x + 1/2 T₂(x)` on `[-1, 1]`, from the same factor as `exact_min`. -/
theorem chebyshev_min : ∀ x ∈ Set.Icc (-1 : ℝ) 1, -1/4 ≤
    ∑ k ∈ range 3, (([1/2, 1, 1/2] : List ℚ).getD k 0 : ℝ) *
      (Polynomial.Chebyshev.T ℝ k).eval x := by
  interval (lower := [1, 1, 1]) (maxHeartbeats := 50)

/-- The bound of the coefficients alone on the Chebyshev series in `(x - 4) / 2`, on `[2, 6]`. -/
theorem chebyshev_ball : ∀ x ∈ Set.Icc (2 : ℝ) 6,
    ∑ k ∈ range 3, (([1/2, 1, 1/2] : List ℚ).getD k 0 : ℝ) *
      (Polynomial.Chebyshev.T ℝ k).eval ((x - 4) / 2) ≤ 2 := by
  interval (maxHeartbeats := 50)

/-- `x² - x = cos (2 u) / 8 - 1/8` at `x = (1 + cos u) / 2`, so the coefficients alone give the
minimum `-1/4` on `[0, 1]`. -/
theorem power_exact : ∀ x ∈ Set.Icc (0 : ℝ) 1, -1/4 ≤ x ^ 2 - x := by
  interval (maxHeartbeats := 50)

/-- The ten coefficients of the degree-9 polynomial. -/
def power : List ℚ := [
    2/8, 25/16, 17/32, 28/64, 55/128, -59/256, 10/512, 31/1024, 8/2048, -62/4096]

/-- The minimum of the degree-9 polynomial on `[-1, 3]`, up to `5e-6`. -/
theorem power_lower : ∀ x ∈ Set.Icc (-1 : ℝ) 3,
    -191.52881 ≤ ∑ k ∈ range 10, (power.getD k 0 : ℝ) * x ^ k := by
  interval (lower := "IntervalCoeffPower.txt") (maxHeartbeats := 100)

/-- The coefficients alone give `x - x² - x³ / 4 ∈ [-1/4, 11/32]` on `[0, 1]`, which is not enough
for `0.3`, while the maximum is about `0.225`; the boxes prove the bound. -/
theorem power_boxes : ∀ x ∈ Set.Icc (0 : ℝ) 1, x - x ^ 2 - x ^ 3 / 4 ≤ 0.3 := by
  interval (maxHeartbeats := 600)

/-! ## Norms on the unit circle -/

/-- Norm bounds from the coefficients alone, with real and Gaussian coefficients. -/
theorem norm_ball : (∀ z : ℂ, ‖z‖ = 1 → ‖1 + z‖ ≤ 2) ∧ (∀ z : ℂ, ‖z‖ = 1 → 1 ≤ ‖2 + z‖) ∧
    ∀ z : ℂ, ‖z‖ = 1 → ‖z + 2 * Complex.I‖ < 3.5 :=
  ⟨by interval (maxHeartbeats := 100), by interval (maxHeartbeats := 100),
    by interval (maxHeartbeats := 100)⟩

/-- The real parts of the nine coefficients. -/
def normRe : List ℚ := [4992, -5, -240, -79, -364, 830, 706, -495, 31]

/-- The imaginary parts of the nine coefficients. -/
def normIm : List ℚ := [-89, 802, -1014, -611, -986, 217, 350, 53, -764]

/-- The maximum of the norm, up to `1.3e-3`. -/
theorem norm_upper : ∀ z : ℂ, ‖z‖ = 1 →
    ‖∑ k ∈ range 9, (normRe.getD k 0 : ℂ) * z ^ k +
      Complex.I * ∑ k ∈ range 9, (normIm.getD k 0 : ℂ) * z ^ k‖ ≤ 8996.4268 := by
  interval (upper := ("IntervalCoeffNormUpper.txt", "IntervalCoeffNormUpper_im.txt"))
    (maxHeartbeats := 100)

/-- The minimum of the norm, up to `1.4e-3`: the polynomial has no zero on the circle. -/
theorem norm_lower : ∀ z : ℂ, ‖z‖ = 1 → 2608.2339 ≤
    ‖∑ k ∈ range 9, (normRe.getD k 0 : ℂ) * z ^ k +
      Complex.I * ∑ k ∈ range 9, (normIm.getD k 0 : ℂ) * z ^ k‖ := by
  interval (lower := ("IntervalCoeffNormLower.txt", "IntervalCoeffNormLower_im.txt"))
    (maxHeartbeats := 100)

/-! ## Negative controls -/

/-- error: interval: the certificate fails: the centre entry 0 of the defect is below the sum 4
of the absolute values of the others -/
#guard_msgs (error, whitespace := lax) in
example : ∀ u : ℝ,
    -1/4 ≤ ∑ k ∈ range 3, (([1/2, 1, 1/2] : List ℚ).getD k 0 : ℝ) * Real.cos (k * u) := by
  interval (lower := [1, 1, 2])

/-- error: interval: the certificate fails: the centre entry 2 of the defect is below the sum 6
of the absolute values of the others -/
#guard_msgs (error, whitespace := lax) in
example : ∀ u : ℝ,
    -0.2 ≤ ∑ k ∈ range 3, (([1/2, 1, 1/2] : List ℚ).getD k 0 : ℝ) * Real.cos (k * u) := by
  interval (lower := [1, 1, 1])

/-- error: interval: the coefficients alone give the range [-3, 3] for the polynomial, which
does not prove the goal; a sharp bound takes a sum-of-squares certificate `(lower := h)`, which
`scripts/coeff_cert.py` finds -/
#guard_msgs (error, whitespace := lax) in
example : ∀ u : ℝ,
    |∑ k ∈ range 3, (([0, 2, -1] : List ℚ).getD k 0 : ℝ) * Real.sin (k * u)| ≤ 2.9 := by
  interval

/-- error: interval: could not prove that x - 1 lies in [-1, 1]
The boxes did not prove it either: interval needs a rational lower bound for
↑([1 / 2, 1, 1 / 2].getD 0 0) -/
#guard_msgs (error, whitespace := lax) in
example : ∀ x ∈ Set.Icc (0 : ℝ) 3,
    ∑ k ∈ range 3, (([1/2, 1, 1/2] : List ℚ).getD k 0 : ℝ) *
      (Polynomial.Chebyshev.T ℝ k).eval (x - 1) ≤ 2 := by
  interval

/-- error: interval: the certificate proves the bound with equality somewhere, so not the strict
bound -/
#guard_msgs (error, whitespace := lax) in
example : ∀ u : ℝ, 0 < 1 + Real.sin u := by
  interval (lower := ([1, 0], [0, -1]))

/-- error: interval: `lower` and `upper` are certificates for a bound on a polynomial or series
over its whole domain, and this goal is not one -/
#guard_msgs (error, whitespace := lax) in
example (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : x ≤ 1 := by
  interval (lower := [1])

/-- The check behind `exact_min`, written out: the cosine row `[1, 2, 2, 2, 1]` of the coefficients
at the denominator `2`, `kT = 4`, `kc = 4` and `kH = 4`, so that `4 T + 4 - 4 |h|² = 0` for
`h = [1, 1, 1]`. The kernel accepts that factor and refuses `[1, 1, 2]`. -/
theorem exact_min_check :
    sosCheck 16 3 2 3 3 0 4 4 4 (ofInt 16 5 (unfold 16 3 (pack 16 [1, 2, 1]))) (ofInt 16 5 0)
        (pack 16 [1, 1, 1]) 0 = true ∧
      sosCheck 16 3 2 3 3 0 4 4 4 (ofInt 16 5 (unfold 16 3 (pack 16 [1, 2, 1]))) (ofInt 16 5 0)
        (pack 16 [1, 1, 2]) 0 = false := by
  decide +kernel

/-- The check behind `sine_exact`: `2 (1 + sin u) - |1 - i z|² = 0`. The kernel accepts the factor
`[1, 0] + i [0, -1]` and refuses its conjugate `[1, 0] + i [0, 1]`, whose square is
`2 - 2 sin u`. -/
theorem complex_check :
    sosCheck 8 2 1 2 2 2 1 0 1 (ofInt 8 3 (shift 8 1 (unfold 8 1 (pack 8 [1]))))
        (ofInt 8 3 (unfold 8 2 (pack 8 [0, 1]) true)) (pack 8 [1, 0]) (pack 8 [0, -1]) = true ∧
      sosCheck 8 2 1 2 2 2 1 0 1 (ofInt 8 3 (shift 8 1 (unfold 8 1 (pack 8 [1]))))
        (ofInt 8 3 (unfold 8 2 (pack 8 [0, 1]) true)) (pack 8 [1, 0]) (pack 8 [0, 1]) = false := by
  decide +kernel

/-- The kernel refuses a link whose last coefficient is changed from `1/2` to `1/3`. -/
theorem wrong_link : rowCheck 8 2 3 2 (pack 8 [1, 2, 1]) [1/2, 1, 1/3] = false := by
  decide +kernel

/-- Horner's rule for `x²` on `[0, 1]`, where `x = (1 + cos u) / 2`, builds the row
`[1, 4, 6, 4, 1]` of `16 x² = (z⁻¹ + 2 + z)²`; the kernel refuses `[1, 4, 6, 4, 2]` as that row. -/
theorem wrong_horner :
    entries 16 5 (ofInt 16 5 (horner 16 3 (shift 16 1 4) (Int.add 1 (Int.add (shift 16 1 2)
        (shift 16 2 1))) (pack 16 [0, 0, 1]))) = [1, 4, 6, 4, 1] ∧
      entries 16 5 (ofInt 16 5 (horner 16 3 (shift 16 1 4) (Int.add 1 (Int.add (shift 16 1 2)
        (shift 16 2 1))) (pack 16 [0, 0, 1]))) ≠ [1, 4, 6, 4, 2] := by
  decide +kernel

end FloatLibTests.Conformance.Numerics.IntervalCoeff
