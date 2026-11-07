/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Coeff.Defect
public import FloatLib.Numerics.Coeff.Trig
public import FloatLib.Numerics.Packed.Literal

/-!
# An inverse and an inverse square root on the circle from kernel-checked defects

`f = 2 + cos u` is `(z⁻¹ + 4 + z) / 2` on the circle, the row `[1, 4, 1]` over `2`.

## Main statements

* Its inverse has the coefficients `(√3 - 2) ^ |n| / √3`. The row `v` keeps `|n| ≤ 12`, rounded
  to `2 ^ (-40)`. The kernel computes the defect `1 - v f` with one Kronecker product and one
  `absSum`: `‖1 - v f‖ ≤ 220528 / 2 ^ 41 ≈ 1.0e-7`. `inv_of_defect` then gives
  `|1 / (2 + cos u) - v u| ≤ 1.003e-7` for every `u`.
* Its inverse square root has the half row `g₀ / 2, g₁, …, g₁₆` of the cosine coefficients of
  `(2 + cos u) ^ (-1/2)`, computed by the trapezoid rule on 512 points and rounded to
  `2 ^ (-40)`. The kernel unfolds the half row, squares it and computes `1 - f g²`:
  `‖1 - f g²‖ ≤ 383809488572480 / 2 ^ 81 ≈ 1.6e-10`. `Wiener.eval_invSqrt_of_defect` then gives
  `|1 / √(2 + cos u) - g u| ≤ 8e-11` for every `u`.

The rows are untrusted data from Python with mpmath. With a wrong row the defect is large and the
bounds no longer follow; `wrong_inverse` shows the kernel refusing the bound for a perturbed `v`.

## Implementation notes

Every check runs under `set_option maxHeartbeats` at about three times the heartbeats it uses, so
the build fails if its kernel cost grows.

The inverse coefficients come from a closed form: `1 / (2 + cos u)` has the Fourier coefficients
`(√3 - 2) ^ |n| / √3`, which shrink by a factor `2 + √3 ≈ 3.7` per step, so keeping `|n| ≤ 12`
leaves a defect of about `10⁻⁷`, which is what the kernel measures.

## References

* Siegfried M. Rump, *Verification methods: rigorous results using floating-point arithmetic*,
  Acta Numerica 19 (2010), 287–449, <https://doi.org/10.1017/S096249291000005X>.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.Wiener

open FloatLib.Numerics.Packed FloatLib.Numerics.Coeff FloatLib.Numerics.Coeff.Wiener Complex

/-- The half row `[2, 1]` of `2 + cos u`, doubled. -/
packed_row fHalf (width := 128) := [2, 1]

/-- The row of `1 / (2 + cos u)` for `|n| ≤ 12`, times `2 ^ 40`. -/
packed_row vRow (width := 128) := [86950, -324501, 1211055, -4519717, 16867815, -62951541,
    234938350, -876801858, 3272269083, -12212274474, 45576828811, -170095040771, 634803334274,
    -170095040771, 45576828811, -12212274474, 3272269083, -876801858, 234938350, -62951541,
    16867815, -4519717, 1211055, -324501, 86950]

/-- The half row of `(2 + cos u) ^ (-1/2)`, times `2 ^ 40`, with the constant term halved. -/
packed_row gHalf (width := 128) := [409979951429, -110876799227, 22351496986, -4998710818,
    1173082101, -283072391, 69559701, -17313026, 4350224, -1101115, 280339, -71713, 18417,
    -4746, 1226, -318, 82]

/-- The row `[1, 4, 1]` of `2 (2 + cos u)`. -/
noncomputable def fRow : ℕ := ofInt 128 3 (unfold 128 2 fHalf)

/-- The row of `2 ^ 40 g`. -/
noncomputable def gRow : ℕ := ofInt 128 33 (unfold 128 17 gHalf)

/-- The row of `2 ^ 80 g²`. -/
noncomputable def gSq : ℕ := ofInt 128 65 (toInt 128 33 gRow * toInt 128 33 gRow)

/-- `2 + cos u`. -/
noncomputable def f : Wiener := (2 : ℂ)⁻¹ • ofRow (entries 128 3 fRow) 1

/-- The approximate inverse. -/
noncomputable def v : Wiener := ((2 : ℂ) ^ 40)⁻¹ • ofRow (entries 128 25 vRow) 12

/-- The approximate inverse square root. -/
noncomputable def g : Wiener := ((2 : ℂ) ^ 40)⁻¹ • ofRow (entries 128 33 gRow) 16

set_option maxHeartbeats 2000 in
/-- All the kernel work: range checks, the two defects, two `l1` norms and the value `g(0)`, whose
sign one `sum` reads. -/
theorem check :
    guard 128 2 2 fHalf = true ∧ guard 128 3 3 fRow = true ∧ guard 128 40 25 vRow = true ∧
      guard 128 39 17 gHalf = true ∧ guard 128 40 33 gRow = true ∧ guard 128 80 65 gSq = true ∧
      absSum 128 27 (shift 128 13 (2 ^ 41) - toInt 128 25 vRow * toInt 128 3 fRow) ≤ 220528 ∧
      absSum 128 25 (toInt 128 25 vRow) ≤ 1099511564126 ∧
      absSum 128 67 (shift 128 33 (2 ^ 81) - toInt 128 3 fRow * toInt 128 65 gSq) ≤
        383809488572480 ∧
      absSum 128 33 (toInt 128 33 gRow) ≤ 1099511627718 ∧
      0 < sum 128 17 (toInt 128 17 gHalf) := by
  decide +kernel

/-- `f` is `2 + cos u` on the circle. -/
theorem eval_f (u : ℝ) : eval u f = ((2 + Real.cos u : ℝ) : ℂ) := by
  have h : entries 128 3 fRow = mirror [2, 1] := by decide +kernel
  have hl := laurent_mirror [2, 1] u
  norm_num [Finset.sum_range_succ] at hl
  rw [f, map_smul, eval_ofRow, h, hl, smul_eq_mul]
  push_cast
  ring

/-- The defect of the approximate inverse. -/
theorem defect_inv : ‖1 - v * f‖ ≤ 220528 / 2 ^ 41 := by
  have h := norm_one_sub_ofRow_mul_le (K := 41) (c := 12) (d := 1) check.2.2.1 check.2.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e : v * f = ((2 : ℂ) ^ 41)⁻¹ •
      (ofRow (entries 128 25 vRow) 12 * ofRow (entries 128 3 fRow) 1) := by
    rw [v, f, smul_mul_smul, ← mul_inv, ← pow_succ]
  rw [e]
  refine h.trans ?_
  gcongr
  exact_mod_cast check.2.2.2.2.2.2.1

/-- The norm of the approximate inverse. -/
theorem norm_v : ‖v‖ ≤ 1099511564126 / 2 ^ 40 := by
  rw [v, norm_smul, norm_inv, norm_pow, Complex.norm_ofNat, inv_mul_eq_div]
  gcongr
  refine (norm_ofRow_le _ _).trans ?_
  rw [← absSum_toInt check.2.2.1 (by norm_num)]
  exact_mod_cast check.2.2.2.2.2.2.2.1

/-- The inverse of `2 + cos u` is within `1.003e-7` of `v` on the whole circle. -/
theorem inverse_bound (u : ℝ) : ‖((2 + Real.cos u : ℝ) : ℂ)⁻¹ - eval u v‖ ≤ 1.003e-7 := by
  obtain ⟨hunit, hnorm⟩ := inv_of_defect defect_inv (by norm_num)
  have he : eval u (Ring.inverse f) = (eval u f)⁻¹ := by
    obtain ⟨U, hU⟩ := hunit
    rw [← hU, Ring.inverse_unit, map_units_inv]
  rw [← eval_f, ← he, ← map_sub]
  refine (norm_eval_le u _).trans (hnorm.trans ?_)
  have hn := norm_v
  calc ‖v‖ * (220528 / 2 ^ 41) / (1 - 220528 / 2 ^ 41) ≤
      1099511564126 / 2 ^ 40 * (220528 / 2 ^ 41) / (1 - 220528 / 2 ^ 41) := by gcongr
    _ ≤ 1.003e-7 := by norm_num

/-- `g` is the cosine polynomial of its half row on the circle. -/
theorem eval_g (u : ℝ) : eval u g = (((2 ^ 40)⁻¹ *
    (2 * ∑ k ∈ Finset.range 17, (entry 128 k gHalf : ℝ) * Real.cos (k * u)) : ℝ) : ℂ) := by
  have hG : entries 128 33 gRow = mirror (entries 128 17 gHalf) :=
    entries_ofInt_unfold check.2.2.2.1 (by norm_num) false
  have hl := laurent_mirror (entries 128 17 gHalf) u
  rw [sum_getD_entries, length_entries] at hl
  rw [g, map_smul, eval_ofRow, hG, show (16 : ℤ) = ((17 - 1 : ℕ) : ℤ) by norm_num, hl, smul_eq_mul]
  push_cast
  ring

/-- The norm of the approximate inverse square root. -/
theorem norm_g : ‖g‖ ≤ 1099511627718 / 2 ^ 40 := by
  rw [g, norm_smul, norm_inv, norm_pow, Complex.norm_ofNat, inv_mul_eq_div]
  gcongr
  refine (norm_ofRow_le _ _).trans ?_
  rw [← absSum_toInt check.2.2.2.2.1 (by norm_num)]
  exact_mod_cast check.2.2.2.2.2.2.2.2.2.1

/-- The defect of the approximate inverse square root, from `g² = gSq / 2 ^ 80`. -/
theorem defect_invSqrt : ‖1 - f * g ^ 2‖ ≤ 383809488572480 / 2 ^ 81 := by
  have hP : entries 128 65 gSq = conv (entries 128 33 gRow) (entries 128 33 gRow) :=
    entries_mul check.2.2.2.2.1 check.2.2.2.2.1 (by norm_num) (by norm_num) (by norm_num)
  have e : f * g ^ 2 = ((2 : ℂ) ^ 81)⁻¹ •
      (ofRow (entries 128 3 fRow) 1 * ofRow (entries 128 65 gSq) 32) := by
    rw [hP, show (32 : ℤ) = 16 + 16 by norm_num, ofRow_conv, f, g, sq, smul_mul_smul,
      smul_mul_smul, ← mul_inv, ← mul_inv, ← pow_add, ← pow_succ']
  have h := norm_one_sub_ofRow_mul_le (K := 81) (c := 1) (d := 32) check.2.1
    check.2.2.2.2.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [e]
  refine h.trans ?_
  gcongr
  exact_mod_cast check.2.2.2.2.2.2.2.2.1

/-- The inverse square root of `2 + cos u` is within `8e-11` of `g` on the whole circle. -/
theorem invSqrt_bound (u : ℝ) : ‖((√(2 + Real.cos u))⁻¹ : ℂ) - eval u g‖ ≤ 8e-11 := by
  have hx : ∀ u, (eval u f).im = 0 := fun u => by rw [eval_f, ofReal_im]
  have hg : ∀ u, (eval u g).im = 0 := fun u => by rw [eval_g, ofReal_im]
  have hg0 : 0 < (eval 0 g).re := by
    have h := check.2.2.2.2.2.2.2.2.2.2
    rw [sum_toInt check.2.2.2.1 (by norm_num)] at h
    have h' : (0 : ℝ) < ∑ k ∈ Finset.range 17, (entry 128 k gHalf : ℝ) := by
      exact_mod_cast (show (entries 128 17 gHalf).sum = ∑ k ∈ Finset.range 17, entry 128 k gHalf
        from rfl) ▸ h
    rw [eval_g, ofReal_re]
    simp only [mul_zero, Real.cos_zero, mul_one]
    positivity
  obtain ⟨-, hr⟩ := eval_invSqrt_of_defect hx hg defect_invSqrt (by norm_num) hg0 u
  obtain ⟨-, hnorm⟩ := invSqrt_of_defect defect_invSqrt (by norm_num)
  rw [eval_f, ofReal_re] at hr
  rw [show ((√(2 + Real.cos u))⁻¹ : ℂ) = (((√(2 + Real.cos u))⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    ← hr, ← map_sub]
  refine (norm_eval_le u _).trans (hnorm.trans ?_)
  have hδ : (0 : ℝ) ≤ 383809488572480 / 2 ^ 81 / (2 * (1 - 383809488572480 / 2 ^ 81)) := by
    norm_num
  calc _ ≤ 1099511627718 / 2 ^ 40 * (383809488572480 / 2 ^ 81 /
        (2 * (1 - 383809488572480 / 2 ^ 81))) := mul_le_mul_of_nonneg_right norm_g hδ
    _ ≤ 8e-11 := by norm_num

set_option maxHeartbeats 2000 in
/-- A perturbed inverse: the last coefficient of `v` changed by `2 ^ 20` makes the defect larger
than the bound above, and the kernel refuses it. -/
theorem wrong_inverse :
    220528 < absSum 128 27 (shift 128 13 (2 ^ 41) - toInt 128 25 (vRow + 2 ^ (128 * 24 + 20)) *
      toInt 128 3 fRow) := by
  decide +kernel

end FloatLibTests.Conformance.Numerics.Wiener
