/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Coeff.Wiener
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Inverses and inverse square roots from a defect

A certificate cannot store `1 / f` or `f ^ (-1/2)` for a function `f` on the circle: their
coefficients never end. It stores an approximation `v` or `g`, found by an untrusted program, and
the kernel computes the defect `d = 1 - v f` or `d = 1 - x g²` exactly, as a finite row, and its
norm `δ = ‖d‖` with one `Packed.absSum`. The lemmas here turn a small defect into the exact
inverse or inverse square root, up to an error that `δ` bounds, in any complete normed
commutative algebra with `‖1‖ = 1` and in particular in the Wiener algebra.

For example, `f = 2 + cos u` is `ofRow [1, 4, 1] 1 / 2`. The row `v = [-2, 7, -2] / 12`, centred
at lane `1`, has `v f = (-2, -1, 24, -1, -2) / 24`, so `‖1 - v f‖ = 6 / 24 = 1/4`, and
`inv_of_defect` gives `‖f⁻¹ - v‖ ≤ (11/12) (1/4) / (3/4) = 11/36` for the exact inverse
`1 / (2 + cos u)` in the Wiener algebra. With 25 coefficients at `2 ^ (-40)` the defect drops to
`1.0e-7`, as in the conformance test.

## Main definitions

* `invSqrtCoeff n`: the coefficient `C(2n, n) / 4ⁿ` of `tⁿ` in `(1 - t) ^ (-1/2)`, written as
  Mathlib's `Ring.choose (n - 1/2) n`.
* `invSqrtOneSub d`: `(1 - d) ^ (-1/2)` as the binomial series `∑ n, invSqrtCoeff n • dⁿ`.

## Main statements

* `inv_of_defect`: if `‖1 - v f‖ ≤ δ < 1`, then `f` is a unit and
  `‖f⁻¹ - v‖ ≤ ‖v‖ δ / (1 - δ)`. This is the Neumann series of `v f = 1 - d`.
* `invSqrtOneSub_sq_mul` and `norm_invSqrtOneSub_sub_one_le`: `(1 - d) ^ (-1/2)` squares to
  `(1 - d)⁻¹`, and `‖(1 - d) ^ (-1/2) - 1‖ ≤ δ / (2 (1 - δ))`. The proof passes through
  `(1 - δ) ^ (-1/2) - 1`, the same series at `δ`, since every coefficient is positive.
* `invSqrt_of_defect`: if `‖1 - x g²‖ ≤ δ < 1`, then `r = g (1 - d) ^ (-1/2)` satisfies
  `r² x = 1` and `‖r - g‖ ≤ ‖g‖ δ / (2 (1 - δ))`. With `x = qᵏ` this is `q ^ (-k/2)`.
* `Wiener.eval_invSqrt_of_defect`: on the circle, `r` is the function `1 / √(x u)` when `x` and
  `g` are real there and `g (0) > 0`. The inverse needs nothing extra, because evaluation is an
  algebra map.
* `Wiener.norm_one_sub_ofRow_mul_le`: the norm of a defect from packed rows, by one Kronecker
  product, one subtraction and one `absSum`.

## Implementation notes

The positivity of the binomial coefficients is what makes the inverse square root as easy as the
inverse. With every `cₙ > 0`, the bound `‖∑ cₙ dⁿ‖ ≤ ∑ cₙ δⁿ` holds term by term, so
`‖(1 - d) ^ (-1/2) - 1‖` is at most the same series at `t = δ`, which has the closed form
`(1 - δ) ^ (-1/2) - 1`. No Lipschitz estimate or second certificate is needed. That the square of
the series is the geometric series is the Chu–Vandermonde identity at `-1/2 + -1/2 = -1`
(`sum_antidiagonal_invSqrtCoeff`), which Mathlib has as `Ring.add_choose_eq`.

On the circle, the sign of `g` is the one thing a norm bound cannot see: `g` and `-g` have the same
defect. The proof of `Wiener.eval_invSqrt_of_defect` rules out a sign change with the intermediate
value theorem, because `x g² ≥ 1 - δ > 0` everywhere, so one sample `g (0) > 0` fixes the sign.

The idea of an a posteriori inverse square root in a Fourier algebra comes from PlasmaLean's
`InvSqrtApprox`, which bounds `x ^ (-1/2) - V₀` linearly in the defect in a weighted strip algebra.
The statements here are for any Banach algebra and are proved from Mathlib's Neumann series and
binomial series, with no code taken from PlasmaLean.

## References

* Siegfried M. Rump, *Verification methods: rigorous results using floating-point arithmetic*,
  Acta Numerica 19 (2010), 287–449, <https://doi.org/10.1017/S096249291000005X>.
* Siddhartha Gadgil, PlasmaLean, `PlasmaLean/Theory/KAM/InvSqrtApprox.lean`,
  <https://github.com/siddhartha-gadgil/PlasmaLean>.

## Tags

Neumann series, binomial series, inverse square root, a posteriori bound, Banach algebra
-/

@[expose] public section

namespace FloatLib.Numerics.Coeff

open Complex Finset

/-! ### The preconditioned inverse -/

section Inverse

variable {A : Type*} [NormedCommRing A] [CompleteSpace A] [NormOneClass A]

/-- An approximate inverse with a small defect gives the exact inverse: if `‖1 - v f‖ ≤ δ < 1`,
then `f` is a unit and `‖f⁻¹ - v‖ ≤ ‖v‖ δ / (1 - δ)`. -/
theorem inv_of_defect {f v : A} {δ : ℝ} (h : ‖1 - v * f‖ ≤ δ) (hδ : δ < 1) :
    IsUnit f ∧ ‖Ring.inverse f - v‖ ≤ ‖v‖ * δ / (1 - δ) := by
  set d := 1 - v * f with hd_def
  have hd : ‖d‖ < 1 := h.trans_lt hδ
  set s := ∑' n : ℕ, d ^ n
  have hs : s * (1 - d) = 1 := geom_series_mul_neg d hd
  have hvf : v * f = 1 - d := by rw [hd_def]; ring
  have hfs : f * (s * v) = 1 := by
    calc f * (s * v) = s * (v * f) := by ring
      _ = 1 := by rw [hvf, hs]
  have hfu : IsUnit f := isUnit_iff_exists_inv.mpr ⟨_, hfs⟩
  refine ⟨hfu, ?_⟩
  -- `f⁻¹ = s v`, so `f⁻¹ - v = (s - 1) v = s d v`, and `‖s‖ ≤ 1 / (1 - δ)` by the geometric series
  have hinv : Ring.inverse f = s * v := by
    calc Ring.inverse f = Ring.inverse f * (f * (s * v)) := by rw [hfs, mul_one]
      _ = s * v := by rw [← mul_assoc, Ring.inverse_mul_cancel f hfu, one_mul]
  have hsd : Ring.inverse f - v = s * d * v := by
    rw [hinv]
    linear_combination v * hs
  have hsn : ‖s‖ ≤ (1 - δ)⁻¹ := by
    have hsum : Summable fun n : ℕ => ‖d‖ ^ n := summable_geometric_of_lt_one (norm_nonneg _) hd
    calc ‖s‖ ≤ ∑' n : ℕ, ‖d‖ ^ n :=
          (norm_tsum_le_tsum_norm (hsum.of_nonneg_of_le (fun _ => norm_nonneg _)
            fun n => norm_pow_le d n)).trans
            (Summable.tsum_le_tsum (fun n => norm_pow_le d n)
              (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => norm_pow_le d n) hsum)
      _ = (1 - ‖d‖)⁻¹ := tsum_geometric_of_lt_one (norm_nonneg _) hd
      _ ≤ (1 - δ)⁻¹ := by
          have : 0 < 1 - δ := by linarith
          gcongr
  have h1 : 0 < 1 - δ := by linarith
  rw [hsd]
  calc ‖s * d * v‖ ≤ ‖s‖ * ‖d‖ * ‖v‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ (1 - δ)⁻¹ * δ * ‖v‖ := by gcongr
    _ = ‖v‖ * δ / (1 - δ) := by field_simp

end Inverse

/-! ### The binomial series of `(1 - t) ^ (-1/2)` -/

/-- The coefficient of `tⁿ` in `(1 - t) ^ (-1/2)`: the binomial coefficient `(n - 1/2 choose n)`,
which is `C(2n, n) / 4ⁿ`, so `1, 1/2, 3/8, 5/16, …`. -/
noncomputable def invSqrtCoeff (n : ℕ) : ℝ := Ring.choose ((n : ℝ) - 1 / 2) n

/-- Every coefficient of the binomial series of `(1 - t) ^ (-1/2)` is positive. -/
theorem invSqrtCoeff_pos (n : ℕ) : 0 < invSqrtCoeff n := by
  rw [invSqrtCoeff, Ring.choose_eq_smul, smul_eq_mul, ← Polynomial.aeval_eq_smeval,
    ← Polynomial.eval_map_algebraMap, algebraMap_int_eq, descPochhammer_map]
  have : (n : ℝ) - 1 < n - 1 / 2 := by linarith
  have := descPochhammer_pos this
  positivity

/-- The binomial series: `∑ n, invSqrtCoeff n * tⁿ = 1 / √(1 - t)` for `|t| < 1`. -/
theorem hasSum_invSqrtCoeff {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n => invSqrtCoeff n * t ^ n) (√(1 - t))⁻¹ := by
  have ht' : ‖t‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_eq_abs]
    simpa using ht
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2)).hasSum (y := t)
    (by rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]; exact_mod_cast ht')
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at h
  convert h using 2 with n
  · rw [invSqrtCoeff, show (n : ℝ) - 1 / 2 = 1 / 2 + n - 1 by ring]
  · rw [Real.sqrt_eq_rpow, one_div, one_div]

/-- The square of the binomial series of `(1 - t) ^ (-1/2)` is the geometric series: for every
`n`, `∑ i + j = n, cᵢ cⱼ = 1`. This is the Chu–Vandermonde identity for `-1/2 + -1/2 = -1`. -/
theorem sum_antidiagonal_invSqrtCoeff (n : ℕ) :
    ∑ ij ∈ antidiagonal n, invSqrtCoeff ij.1 * invSqrtCoeff ij.2 = 1 := by
  have hc : ∀ k : ℕ, invSqrtCoeff k = (-1) ^ k * Ring.choose (-(1 / 2 : ℝ)) k := by
    intro k
    rw [Ring.choose_neg, Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow, invSqrtCoeff]
    rw [show (1 / 2 : ℝ) + k - 1 = k - 1 / 2 by ring, ← mul_assoc, zpow_natCast, ← mul_pow]
    norm_num
  have hv := Ring.add_choose_eq (r := -(1 / 2 : ℝ)) (s := -(1 / 2)) n (Commute.refl _)
  have hm : Ring.choose (-(1 / 2 : ℝ) + -(1 / 2)) n = (-1) ^ n := by
    rw [show -(1 / 2 : ℝ) + -(1 / 2) = -1 by norm_num, Ring.choose_neg, Units.smul_def,
      zsmul_eq_mul, Int.cast_negOnePow, show (1 : ℝ) + n - 1 = (n : ℕ) by ring,
      Ring.choose_natCast, Nat.choose_self, zpow_natCast]
    simp
  calc ∑ ij ∈ antidiagonal n, invSqrtCoeff ij.1 * invSqrtCoeff ij.2
      = ∑ ij ∈ antidiagonal n, (-1) ^ n *
          (Ring.choose (-(1 / 2 : ℝ)) ij.1 * Ring.choose (-(1 / 2)) ij.2) := by
        refine Finset.sum_congr rfl fun ij hij => ?_
        rw [hc, hc, ← mem_antidiagonal.mp hij, pow_add]
        ring
    _ = (-1) ^ n * (-1) ^ n := by rw [← Finset.mul_sum, ← hv, hm]
    _ = 1 := by rw [← mul_pow]; norm_num

/-! ### `(1 - d) ^ (-1/2)` in a Banach algebra -/

section InvSqrt

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

/-- `(1 - d) ^ (-1/2)` as the binomial series `∑ n, invSqrtCoeff n • dⁿ`, which converges when
`‖d‖ < 1`. -/
noncomputable def invSqrtOneSub (d : A) : A := ∑' n, invSqrtCoeff n • d ^ n

omit [CompleteSpace A] in
private theorem norm_invSqrtCoeff_smul_le (d : A) (n : ℕ) :
    ‖invSqrtCoeff n • d ^ n‖ ≤ invSqrtCoeff n * ‖d‖ ^ n := by
  rw [norm_smul, Real.norm_of_nonneg (invSqrtCoeff_pos n).le]
  exact mul_le_mul_of_nonneg_left (norm_pow_le d n) (invSqrtCoeff_pos n).le

private theorem summable_invSqrtCoeff {t : ℝ} (ht : |t| < 1) :
    Summable fun n => invSqrtCoeff n * t ^ n :=
  (hasSum_invSqrtCoeff ht).summable

omit [CompleteSpace A] in
private theorem summable_norm_invSqrtOneSub {d : A} (hd : ‖d‖ < 1) :
    Summable fun n => ‖invSqrtCoeff n • d ^ n‖ :=
  (summable_invSqrtCoeff (by rwa [abs_norm])).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_invSqrtCoeff_smul_le d)

private theorem summable_invSqrtOneSub {d : A} (hd : ‖d‖ < 1) :
    Summable fun n => invSqrtCoeff n • d ^ n :=
  .of_norm (summable_norm_invSqrtOneSub hd)

/-- Continuous algebra maps commute with `(1 - d) ^ (-1/2)`. -/
theorem map_invSqrtOneSub {B : Type*} [NormedCommRing B] [NormedAlgebra ℝ B] (φ : A →ₐ[ℝ] B)
    (hφ : Continuous φ) {d : A} (hd : ‖d‖ < 1) :
    φ (invSqrtOneSub d) = invSqrtOneSub (φ d) := by
  unfold invSqrtOneSub
  rw [(summable_invSqrtOneSub hd).map_tsum φ hφ]
  simp only [map_smul, map_pow]

/-- `(1 - d) ^ (-1/2)` squares to the inverse of `1 - d`. -/
theorem invSqrtOneSub_sq_mul {d : A} (hd : ‖d‖ < 1) : invSqrtOneSub d ^ 2 * (1 - d) = 1 := by
  have hs := summable_norm_invSqrtOneSub hd
  rw [sq, invSqrtOneSub, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hs hs]
  have h : ∀ n : ℕ, ∑ k ∈ range (n + 1), invSqrtCoeff k • d ^ k * invSqrtCoeff (n - k) • d ^ (n - k)
      = d ^ n := by
    intro n
    have e : ∀ k ∈ range (n + 1), invSqrtCoeff k • d ^ k * invSqrtCoeff (n - k) • d ^ (n - k) =
        (invSqrtCoeff k * invSqrtCoeff (n - k)) • d ^ n := by
      intro k hk
      rw [smul_mul_smul, ← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (mem_range.mp hk))]
    rw [Finset.sum_congr rfl e, ← Finset.sum_smul,
      ← Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun ij => invSqrtCoeff ij.1 * invSqrtCoeff ij.2),
      sum_antidiagonal_invSqrtCoeff, one_smul]
  simp only [h]
  exact geom_series_mul_neg d hd

private theorem inv_sqrt_sub_one_le {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) :
    (√(1 - δ))⁻¹ - 1 ≤ δ / (2 * (1 - δ)) := by
  have hy : 0 < √(1 - δ) := Real.sqrt_pos.mpr (by linarith)
  have hy2 : √(1 - δ) ^ 2 = 1 - δ := Real.sq_sqrt (by linarith)
  have hy1 : √(1 - δ) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  generalize √(1 - δ) = y at hy hy2 hy1 ⊢
  obtain rfl : δ = 1 - y ^ 2 := by linarith
  rw [inv_eq_one_div, div_sub_one hy.ne', div_le_div_iff₀ hy (by nlinarith)]
  nlinarith [mul_nonneg hy.le (sq_nonneg (1 - y))]

/-- The distance of `(1 - d) ^ (-1/2)` from `1` is at most `δ / (2 (1 - δ))` when `‖d‖ ≤ δ < 1`.
The proof bounds it by `(1 - δ) ^ (-1/2) - 1` first, the same series at `δ`. -/
theorem norm_invSqrtOneSub_sub_one_le {d : A} {δ : ℝ} (hd : ‖d‖ ≤ δ) (hδ : δ < 1) :
    ‖invSqrtOneSub d - 1‖ ≤ δ / (2 * (1 - δ)) := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hd
  have hδa : |δ| < 1 := by rwa [abs_of_nonneg hδ0]
  have hs := summable_norm_invSqrtOneSub (hd.trans_lt hδ)
  have hsδ := hasSum_invSqrtCoeff hδa
  have hc0 : invSqrtCoeff 0 = 1 := by simp [invSqrtCoeff]
  have htail : invSqrtOneSub d - 1 = ∑' n : ℕ, invSqrtCoeff (n + 1) • d ^ (n + 1) := by
    rw [invSqrtOneSub, (summable_invSqrtOneSub (hd.trans_lt hδ)).tsum_eq_zero_add, hc0, pow_zero,
      one_smul,
      add_sub_cancel_left]
  have hδtail : ∑' n : ℕ, invSqrtCoeff (n + 1) * δ ^ (n + 1) = (√(1 - δ))⁻¹ - 1 := by
    rw [← hsδ.tsum_eq, hsδ.summable.tsum_eq_zero_add, hc0, pow_zero, mul_one, add_sub_cancel_left]
  have hsum : Summable fun n : ℕ => invSqrtCoeff (n + 1) * δ ^ (n + 1) :=
    (summable_nat_add_iff (f := fun n => invSqrtCoeff n * δ ^ n) 1).mpr hsδ.summable
  have hs1 : Summable fun n : ℕ => ‖invSqrtCoeff (n + 1) • d ^ (n + 1)‖ :=
    (summable_nat_add_iff (f := fun n => ‖invSqrtCoeff n • d ^ n‖) 1).mpr hs
  -- termwise: `‖cₙ dⁿ‖ ≤ cₙ δⁿ` because `cₙ > 0`, and the series at `δ` has a closed form
  rw [htail]
  refine (norm_tsum_le_tsum_norm hs1).trans ((Summable.tsum_le_tsum (fun n =>
    (norm_invSqrtCoeff_smul_le d (n + 1)).trans ?_) hs1 hsum).trans ?_)
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd _)
      (invSqrtCoeff_pos _).le
  · rw [hδtail]
    exact inv_sqrt_sub_one_le hδ0 hδ

/-- An approximate inverse square root with a small defect gives the exact one: if
`‖1 - x g²‖ ≤ δ < 1`, then `r = g (1 - d) ^ (-1/2)` with `d = 1 - x g²`, which is
`g (x g²) ^ (-1/2)`, satisfies `r² x = 1`, and `‖r - g‖ ≤ ‖g‖ δ / (2 (1 - δ))`. -/
theorem invSqrt_of_defect {x g : A} {δ : ℝ} (h : ‖1 - x * g ^ 2‖ ≤ δ) (hδ : δ < 1) :
    (g * invSqrtOneSub (1 - x * g ^ 2)) ^ 2 * x = 1 ∧
      ‖g * invSqrtOneSub (1 - x * g ^ 2) - g‖ ≤ ‖g‖ * (δ / (2 * (1 - δ))) := by
  have hsq := invSqrtOneSub_sq_mul (h.trans_lt hδ)
  refine ⟨?_, ?_⟩
  · calc (g * invSqrtOneSub (1 - x * g ^ 2)) ^ 2 * x
        = invSqrtOneSub (1 - x * g ^ 2) ^ 2 * (1 - (1 - x * g ^ 2)) := by ring
      _ = 1 := hsq
  · rw [show g * invSqrtOneSub (1 - x * g ^ 2) - g = g * (invSqrtOneSub (1 - x * g ^ 2) - 1) by
      ring]
    exact (norm_mul_le _ _).trans (by gcongr; exact norm_invSqrtOneSub_sub_one_le h hδ)

end InvSqrt

/-! ### On the circle -/

namespace Wiener

open Packed

/-- At a point where `d` is real, `(1 - d) ^ (-1/2)` is the real number `1 / √(1 - d u)`. -/
theorem eval_invSqrtOneSub {d : Wiener} (hd : ‖d‖ < 1) {u : ℝ} (hre : (eval u d).im = 0) :
    eval u (invSqrtOneSub d) = ((√(1 - (eval u d).re))⁻¹ : ℝ) := by
  set t := (eval u d).re
  have ht : |t| < 1 := (abs_re_le_norm _).trans_lt ((norm_eval_le u d).trans_lt hd)
  have hd' : eval u d = ofRealAm t := Complex.ext (by simp [t]) (by simp [hre])
  have h1 := map_invSqrtOneSub ((eval u).restrictScalars ℝ) (continuous_eval u) hd
  have h2 := map_invSqrtOneSub ofRealAm continuous_ofReal (d := t) (by simpa using ht)
  have h3 : invSqrtOneSub t = (√(1 - t))⁻¹ := by
    unfold invSqrtOneSub
    simp only [smul_eq_mul]
    exact (hasSum_invSqrtCoeff ht).tsum_eq
  rw [AlgHom.coe_restrictScalars', hd', ← h2, h3] at h1
  exact h1

/-- The inverse square root on the circle. If `x` and `g` are real on the circle,
`‖1 - x g²‖ ≤ δ < 1` and `g (0) > 0`, then `x` is positive on the circle and
`g (1 - (1 - x g²)) ^ (-1/2)` is the function `1 / √(x u)`. -/
theorem eval_invSqrt_of_defect {x g : Wiener} {δ : ℝ} (hx : ∀ u, (eval u x).im = 0)
    (hg : ∀ u, (eval u g).im = 0) (h : ‖1 - x * g ^ 2‖ ≤ δ) (hδ : δ < 1)
    (hg0 : 0 < (eval 0 g).re) (u : ℝ) :
    0 < (eval u x).re ∧
      eval u (g * invSqrtOneSub (1 - x * g ^ 2)) = ((√(eval u x).re)⁻¹ : ℝ) := by
  have hd : ∀ v, eval v (1 - x * g ^ 2) = ((1 - (eval v x).re * (eval v g).re ^ 2 : ℝ) : ℂ) :=
    fun v => Complex.ext (by simp [sq, hx v, hg v]) (by simp [sq, hx v, hg v])
  have hpos : ∀ v, 0 < (eval v x).re * (eval v g).re ^ 2 := by
    intro v
    have h1 := (norm_eval_le v (1 - x * g ^ 2)).trans_lt (h.trans_lt hδ)
    rw [hd, norm_real, Real.norm_eq_abs] at h1
    linarith [abs_lt.mp h1]
  have hgne : ∀ v, (eval v g).re ≠ 0 := fun v h0 => by
    have := hpos v
    rw [h0] at this
    simp at this
  -- `g` never vanishes on the circle, so it keeps the sign it has at `0`
  have hgpos : 0 < (eval u g).re := by
    by_contra hneg
    have hlt : (eval u g).re < 0 := lt_of_le_of_ne (not_lt.mp hneg) (hgne u)
    obtain ⟨v, hv⟩ := intermediate_value_univ u 0
      (Complex.continuous_re.comp (continuous_eval_apply g)) ⟨hlt.le, hg0.le⟩
    exact hgne v hv
  have hxpos : 0 < (eval u x).re := (mul_pos_iff_of_pos_right (pow_pos hgpos 2)).mp (hpos u)
  refine ⟨hxpos, ?_⟩
  have hs := eval_invSqrtOneSub (d := 1 - x * g ^ 2) (h.trans_lt hδ) (u := u)
    (by rw [hd u, ofReal_im])
  rw [hd u, ofReal_re, sub_sub_cancel, Real.sqrt_mul hxpos.le, Real.sqrt_sq hgpos.le] at hs
  rw [map_mul, hs]
  apply Complex.ext
  · simp only [mul_re, ofReal_re, ofReal_im, hg u, mul_zero, sub_zero]
    field_simp
  · simp [mul_im, hg u]

/-- The defect of a product of packed rows against the constant `2 ^ K`, by one Kronecker product,
one subtraction and one `absSum`: with the rows centred at lanes `c` and `d`,
`‖1 - (u v) / 2 ^ K‖ ≤ absSum (2 ^ K δ - u v) / 2 ^ K`. The range checks and
`2 ^ K + n 2 ^ gx (m 2 ^ gy) < 2 ^ (w - 1)` make every lane of the defect fit. -/
theorem norm_one_sub_ofRow_mul_le {w gx gy n m u v K c d : ℕ} (hu : guard w gx n u = true)
    (hv : guard w gy m v = true) (hroom : 2 ^ K + n * 2 ^ gx * (m * 2 ^ gy) < 2 ^ (w - 1))
    (hn : 0 < n) (hm : 0 < m) (hcd : c + d < n + m - 1) :
    ‖1 - ((2 : ℂ) ^ K)⁻¹ • (ofRow (entries w n u) c * ofRow (entries w m v) d)‖ ≤
      (absSum w (n + m - 1) (shift w (c + d) (2 ^ K) - toInt w n u * toInt w m v) : ℝ) / 2 ^ K := by
  obtain ⟨hgw, hu', hub⟩ := guard_sound hu
  obtain ⟨-, hv', hvb⟩ := guard_sound hv
  have hw : 1 ≤ w := by omega
  set U := entries w n u with hU
  set V := entries w m v with hV
  set S : List ℤ := List.replicate (c + d) 0 ++ [2 ^ K] with hS
  obtain ⟨D, hD⟩ : ∃ D, D = Packed.sub S (Packed.conv U V) := ⟨_, rfl⟩
  have hUl : U.length = n := length_entries w n u
  have hVl : V.length = m := length_entries w m v
  have hconvl : (Packed.conv U V).length = n + m - 1 := by
    rw [length_conv (List.length_pos_iff.mp (by omega)) (List.length_pos_iff.mp (by omega)), hUl,
      hVl]
  have hDl : D.length = n + m - 1 := by
    rw [hD, Packed.sub, length_add, smul, List.length_map, hconvl, hS, List.length_append,
      List.length_replicate, List.length_singleton]
    exact Nat.max_eq_right (by omega)
  have hl1 : l1 D < 2 ^ (w - 1) := by
    have h1 := l1_le_of_bound hub
    have h2 := l1_le_of_bound hvb
    rw [hUl] at h1
    rw [hVl] at h2
    have h3 := l1_conv_le U V
    have h4 := l1_sub_le S (Packed.conv U V)
    rw [← hD] at h4
    have hS : l1 S = 2 ^ K := by
      simp only [S, l1, List.map_append, List.map_replicate, List.sum_append, List.sum_replicate]
      simp
    have := Nat.mul_le_mul h1 h2
    omega
  have hval : shift w (c + d) (2 ^ K) - toInt w n u * toInt w m v = Packed.eval (2 ^ w) D := by
    rw [hD, hU, hV, ← eval_entries hw hu', ← eval_entries hw hv', ← eval_conv, eval_sub,
      ← shift_eval]
    simp [Packed.eval]
  have hone : (1 : Wiener) = ((2 : ℂ) ^ K)⁻¹ • ofRow S (c + d : ℕ) := by
    rw [ofRow_single, Int.cast_pow, Int.cast_ofNat, ← map_ofNat (algebraMap ℂ Wiener) 2, ← map_pow,
      Algebra.smul_def, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), map_one]
  have hprod : ofRow U c * ofRow V d = ofRow (Packed.conv U V) (c + d : ℕ) := by
    rw [Nat.cast_add, ofRow_conv]
  rw [hone, hprod, ← smul_sub, ← ofRow_sub, ← hD, norm_smul, hval,
    absSum_eval hw (le_of_eq hDl) hl1,
    norm_inv, norm_pow, Complex.norm_ofNat, inv_mul_eq_div]
  gcongr
  exact norm_ofRow_le D _

end Wiener

end FloatLib.Numerics.Coeff
