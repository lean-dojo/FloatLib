/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.MixedError.Elementary
public import FloatLibTests.Conformance.BinaryInterchange.BoundaryCases

/-!
# Mixed error bounds in binary32 and bfloat16

These examples apply the mixed-error theorems to concrete binary32 and bfloat16 values, with
finiteness and the stored values checked by kernel reduction. The left-to-right sum of `0.1`,
`0.2` and `0.3` has relative error at most `(1 + 2⁻²⁴) ^ 2 - 1`, both over a list and with
`Fin.foldl`, and so does `1 + 2⁻²⁵ + 2⁻²⁵`, whose small terms are both absorbed. Against the
decimals they store, the three literals sum with relative error at most `(1 + 2⁻²⁴) ^ 3 - 1`, each
literal's error weighted by its own value. In `1 + 2⁻²⁵ - 1` cancellation loses the exact sum,
which stays within the absolute bound. In `0.1 * 0.2 + 0.3` the only absolute term is the
underflow allowance of the product.

Sterbenz subtraction, `x - x`, subtraction from zero and multiplication by `-1` are exact. A
one-hot vector of any length sums to exactly `-1` in binary32 and bfloat16. `log (1 + s)` keeps
the relative error of a nonnegative sum and takes negative arguments above `-1/2`, and `exp x - 1`
takes arguments of either sign near zero.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.MixedError

open FloatLib.Numerics
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model

/-- Binary32 one. -/
private def one : Model FloatFormat.binary32 := ofNatBits 0x3f800000
/-- Binary32 `1.5`. -/
private def threeHalves : Model FloatFormat.binary32 := ofNatBits 0x3fc00000
/-- Binary32 `2⁻²⁵`, a quarter of the spacing of binary32 values just above one. -/
private def tiny : Model FloatFormat.binary32 := ofNatBits 0x33000000
/-- Binary32 `0.1`, rounded once from the decimal literal. -/
private def tenth : Model FloatFormat.binary32 := ofNatBits 0x3dcccccd
/-- Binary32 `0.2`, rounded once from the decimal literal. -/
private def fifth : Model FloatFormat.binary32 := ofNatBits 0x3e4ccccd
/-- Binary32 `0.3`, rounded once from the decimal literal. -/
private def threeTenths : Model FloatFormat.binary32 := ofNatBits 0x3e99999a
/-- Binary32 positive zero, the seed of these sums. -/
private def seed : Model FloatFormat.binary32 := Model.zero _ false

/-- The stored value of `one`. -/
private theorem toReal_one : toReal one = 1 := by
  rw [Algebraic.toReal_of_toRat?_eq_some (q := 1) (by decide +kernel)]
  norm_num

/-- The stored value of `threeHalves`. -/
private theorem toReal_threeHalves : toReal threeHalves = 3 / 2 := by
  rw [Algebraic.toReal_of_toRat?_eq_some (q := 3 / 2) (by decide +kernel)]
  norm_num

/-- The stored value of `tiny`. -/
private theorem toReal_tiny : toReal tiny = 2 ^ (-25 : ℤ) := by
  rw [Algebraic.toReal_of_toRat?_eq_some (q := 2⁻¹ ^ 25) (by decide +kernel)]
  norm_num

/-! ## Sums of positive values -/

/-- The values `0.1`, `0.2` and `0.3`. -/
private def tenths : List (Model FloatFormat.binary32) := [tenth, fifth, threeTenths]

/-- Every partial sum of `tenths` is finite. -/
private theorem tenths_finite :
    ∀ v ∈ tenths.scanl (fun acc v => add acc v) seed, isFinite v = true := by
  simp only [tenths, tenth, fifth, threeTenths, seed, List.scanl_cons, List.scanl_nil,
    Proof.add_eq_spec]
  decide +kernel

/-- The stored values of `tenths` are nonnegative. -/
private theorem tenths_nonneg : ∀ v ∈ tenths, 0 ≤ toReal v := fun v hv =>
  toReal_nonneg_of_signBit_eq_false ((by decide : ∀ v ∈ tenths, signBit v = false) v hv)

/--
The left-to-right sum of `0.1`, `0.2` and `0.3` from zero rounds twice. Its relative error
against the exact sum of the three stored values is at most `(1 + 2⁻²⁴) ^ 2 - 1`.
-/
example :
    |toReal (tenths.foldl (fun acc v => add acc v) seed) - (tenths.map toReal).sum| ≤
      ((1 + 2 ^ (-24 : ℤ)) ^ 2 - 1) * (tenths.map toReal).sum := by
  have h := mixedError_toReal_foldl_add_of_toReal_eq_zero (term := fun v => v)
    (term₀ := toReal) (err := fun _ => 0) (by decide) (toReal_zero _ _) tenths_finite
    (by decide) (fun v _ => MixedError.refl _) le_rfl tenths_nonneg
  have hS : 0 ≤ (tenths.map toReal).sum := List.sum_nonneg (by simpa using tenths_nonneg)
  have hlen : tenths.length - 1 = 2 := rfl
  have hzero : (tenths.map fun _ => (0 : ℝ)).sum = 0 := by simp
  have hb := h.bound
  rw [hlen, hzero, BoundaryCases.binary32_unitRoundoffAt, abs_of_nonneg hS, add_zero, mul_one,
    mul_zero, add_zero] at hb
  exact hb

/-- The binary32 roundings of `0.1`, `0.2` and `0.3` as a function on `Fin 3`. -/
private def tenthsFin : Fin 3 → Model FloatFormat.binary32 := ![tenth, fifth, threeTenths]

/--
The same sum computed by `Fin.foldl`. Its partial sums are finite because the result is, so
the only finiteness check is on the result.
-/
example :
    |toReal (Fin.foldl 3 (fun acc i => add acc (tenthsFin i)) seed) - ∑ i, toReal (tenthsFin i)| ≤
      ((1 + 2 ^ (-24 : ℤ)) ^ 2 - 1) * ∑ i, toReal (tenthsFin i) := by
  have hsum : isFinite (Fin.foldl 3 (fun acc i => add acc (tenthsFin i)) seed) = true := by
    simp only [Fin.foldl_succ, Fin.foldl_zero, tenthsFin, tenth, fifth, threeTenths, seed,
      Proof.add_eq_spec]
    decide +kernel
  have hnonneg (i : Fin 3) : 0 ≤ toReal (tenthsFin i) :=
    toReal_nonneg_of_signBit_eq_false (by revert i; decide)
  have h := mixedError_toReal_fin_foldl_add_of_toReal_eq_zero (seed := seed)
    (term₀ := fun i => toReal (tenthsFin i)) (err := fun _ => 0) (by decide) (toReal_zero _ _)
    (fun _ => isFinite_of_mem_finRange_scanl_add (by decide) hsum) (fun i => by revert i; decide)
    (fun _ => MixedError.refl _) le_rfl hnonneg
  have hS : 0 ≤ ∑ i, toReal (tenthsFin i) := Finset.sum_nonneg fun i _ => hnonneg i
  simpa [BoundaryCases.binary32_unitRoundoffAt, abs_of_nonneg hS] using h.bound

/-- The values `1`, `2⁻²⁵` and `2⁻²⁵`. -/
private def absorbed : List (Model FloatFormat.binary32) := [one, tiny, tiny]

/-- Each small term is absorbed, and the sum rounds back to one. -/
private theorem absorbed_sum : absorbed.foldl (fun acc v => add acc v) seed = one := by
  simp only [absorbed, one, tiny, seed, List.foldl_cons, List.foldl_nil, Proof.add_eq_spec]
  decide +kernel

/--
The absorbed terms cost a relative error of about `2⁻²⁴`, within the bound for the sum. The
partial sums are finite because the result is.
-/
example :
    |toReal (absorbed.foldl (fun acc v => add acc v) seed) - (1 + 2 ^ (-24 : ℤ))| ≤
      ((1 + 2 ^ (-24 : ℤ)) ^ 2 - 1) * (1 + 2 ^ (-24 : ℤ)) := by
  have hsum : isFinite (absorbed.foldl (fun acc v => add acc v) seed) = true := by
    rw [absorbed_sum]
    decide
  have hfinite : ∀ v ∈ absorbed.scanl (fun acc v => add acc v) seed, isFinite v = true :=
    fun _ => isFinite_of_mem_scanl_add (by decide) hsum
  have h := mixedError_toReal_foldl_add_of_toReal_eq_zero (term := fun v => v)
    (term₀ := toReal) (err := fun _ => 0) (by decide) (toReal_zero _ _) hfinite (by decide)
    (fun v _ => MixedError.refl _) le_rfl fun v hv =>
      toReal_nonneg_of_signBit_eq_false ((by decide : ∀ v ∈ absorbed, signBit v = false) v hv)
  have hS : (absorbed.map toReal).sum = 1 + 2 ^ (-24 : ℤ) := by
    simp only [absorbed, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, toReal_one,
      toReal_tiny]
    norm_num
  have hlen : absorbed.length - 1 = 2 := rfl
  have hzero : (absorbed.map fun _ => (0 : ℝ)).sum = 0 := by simp
  have hb := h.bound
  rw [hlen, hzero, hS, BoundaryCases.binary32_unitRoundoffAt,
    abs_of_pos (by positivity : (0 : ℝ) < 1 + 2 ^ (-24 : ℤ)), add_zero, mul_one, mul_zero,
    add_zero] at hb
  exact hb

/-- The decimals `0.1`, `0.2` and `0.3`, whose binary32 roundings `tenthsFin` stores. -/
private noncomputable def decimals : Fin 3 → ℝ := ![1 / 10, 1 / 5, 3 / 10]

/-- Each stored literal is within relative error `2⁻²⁴` of its decimal. -/
private theorem mixedError_tenthsFin (i : Fin 3) :
    MixedError (toReal (tenthsFin i)) (decimals i) (2 ^ (-24 : ℤ)) 0 := by
  refine MixedError.of_abs_sub_le_mul (by positivity) ?_
  fin_cases i
  · show |toReal tenth - 1 / 10| ≤ _ * |1 / 10|
    rw [Algebraic.toReal_of_toRat?_eq_some (q := 13421773 / 134217728) (by decide +kernel)]
    norm_num
  · show |toReal fifth - 1 / 5| ≤ _ * |1 / 5|
    rw [Algebraic.toReal_of_toRat?_eq_some (q := 13421773 / 67108864) (by decide +kernel)]
    norm_num
  · show |toReal threeTenths - 3 / 10| ≤ _ * |3 / 10|
    rw [Algebraic.toReal_of_toRat?_eq_some (q := 5033165 / 16777216) (by decide +kernel)]
    norm_num

/--
The sum of the stored literals approximates the decimal sum `3/5`. Its two roundings and the
literals' own errors, each weighted by its decimal, give relative error at most
`(1 + 2⁻²⁴) ^ 3 - 1`.
-/
example :
    |toReal (Fin.foldl 3 (fun acc i => add acc (tenthsFin i)) seed) - 3 / 5| ≤
      ((1 + 2 ^ (-24 : ℤ)) ^ 3 - 1) * (3 / 5) := by
  have hsum : isFinite (Fin.foldl 3 (fun acc i => add acc (tenthsFin i)) seed) = true := by
    simp only [Fin.foldl_succ, Fin.foldl_zero, tenthsFin, tenth, fifth, threeTenths, seed,
      Proof.add_eq_spec]
    decide +kernel
  have h := mixedError_toReal_fin_foldl_add_weighted_of_toReal_eq_zero (seed := seed)
    (rel := fun _ => 2 ^ (-24 : ℤ)) (err := fun _ => 0) (by decide) (toReal_zero _ _)
    (fun _ => isFinite_of_mem_finRange_scanl_add (by decide) hsum) (fun i => by revert i; decide)
    mixedError_tenthsFin fun i => by fin_cases i <;> norm_num [decimals]
  have hS : ∑ i, decimals i = 3 / 5 := by
    simp [decimals, Fin.sum_univ_three]
    norm_num
  have hb := h.bound
  simp only [add_zero, ← Finset.mul_sum, hS, BoundaryCases.binary32_unitRoundoffAt] at hb
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)] at hb
  calc _ ≤ _ := hb
    _ = _ := by ring

/-! ## A sum with cancellation -/

/-- The values `1`, `2⁻²⁵` and `-1`. -/
private def cancelling : List (Model FloatFormat.binary32) := [one, tiny, negOne _]

/-- The small term is absorbed, and the sum is zero. -/
private theorem cancelling_sum : cancelling.foldl (fun acc v => add acc v) seed = seed := by
  simp only [cancelling, one, tiny, seed, List.foldl_cons, List.foldl_nil, Proof.add_eq_spec]
  decide +kernel

/--
The exact sum `2⁻²⁵` is lost entirely: the computed sum is zero, so the relative error is exactly
one and no relative bound below one holds. The pure absolute bound, about `2 * 2⁻²⁴` times the sum
`2 + 2⁻²⁵` of the magnitudes, does.
-/
example :
    |toReal (cancelling.foldl (fun acc v => add acc v) seed) - 2 ^ (-25 : ℤ)| ≤
      ((1 + 2 ^ (-24 : ℤ)) ^ 2 - 1) * (2 + 2 ^ (-25 : ℤ)) := by
  have hsum : isFinite (cancelling.foldl (fun acc v => add acc v) seed) = true := by
    rw [cancelling_sum]
    decide
  have h := mixedError_toReal_foldl_add_absolute_of_toReal_eq_zero (term := fun v => v)
    (term₀ := toReal) (rel := fun _ => 0) (err := fun _ => 0) (by decide) (toReal_zero _ _)
    (fun _ => isFinite_of_mem_scanl_add (by decide) hsum) (by decide) fun v _ => MixedError.refl _
  have hS : (cancelling.map toReal).sum = 2 ^ (-25 : ℤ) := by
    simp [cancelling, toReal_one, toReal_tiny, toReal_negOne]
  have habs : (cancelling.map fun v => |toReal v|).sum = 2 + 2 ^ (-25 : ℤ) := by
    simp [cancelling, toReal_one, toReal_tiny, toReal_negOne]
    ring
  have hlen : cancelling.length - 1 = 2 := rfl
  have hb := h.bound
  simp only [hS, habs, hlen, zero_mul, zero_add, add_zero, List.map_const', List.sum_replicate,
    smul_zero, mul_zero, BoundaryCases.binary32_unitRoundoffAt] at hb
  exact hb

/-! ## A product followed by a sum -/

/--
`0.1 * 0.2 + 0.3` with a rounded product and a rounded sum. The underflow allowance of the
product is the only absolute term, and the sum of positive values keeps the relative error.
-/
example :
    MixedError (toReal (add (mul tenth fifth) threeTenths))
      (toReal tenth * toReal fifth + toReal threeTenths)
      ((1 + 2 ^ (-24 : ℤ)) * 2 ^ (-24 : ℤ) + 2 ^ (-24 : ℤ))
      ((1 + 2 ^ (-24 : ℤ)) * 2 ^ (-150 : ℤ)) := by
  have hmul := mixedError_toReal_mul (by decide)
    (by simp only [tenth, fifth, Proof.mul_eq_spec]; decide +kernel)
    (MixedError.refl (toReal tenth)) (MixedError.refl (toReal fifth))
  have hadd := mixedError_toReal_add_of_mul_nonneg (by decide)
    (by
      simp only [tenth, fifth, threeTenths, Proof.mul_eq_spec, Proof.add_eq_spec]
      decide +kernel)
    hmul (MixedError.refl (toReal threeTenths)) (by
      have h₁ := toReal_nonneg_of_signBit_eq_false (x := tenth) (by decide)
      have h₂ := toReal_nonneg_of_signBit_eq_false (x := fifth) (by decide)
      have h₃ := toReal_nonneg_of_signBit_eq_false (x := threeTenths) (by decide)
      positivity)
  rw [BoundaryCases.binary32_unitRoundoffAt, BoundaryCases.binary32_underflowErrorAt] at hadd
  refine hadd.mono (le_of_eq ?_) (le_of_eq ?_) <;> norm_num

/-! ## Exact operations -/

/-- `1.5 - 1` satisfies the Sterbenz condition, so the subtraction does not round. -/
example : toReal (sub threeHalves one) = 1 / 2 := by
  have h := mixedError_toReal_sub_of_sterbenz (x := threeHalves) (y := one) (by decide)
    (by decide) (by decide) (MixedError.refl _) (MixedError.refl _)
    (by rw [toReal_threeHalves, toReal_one]; norm_num)
    (by rw [toReal_threeHalves, toReal_one]; norm_num)
    (by rw [toReal_threeHalves, toReal_one]; norm_num)
  simp only [zero_mul, add_zero, mixedError_zero_zero_iff] at h
  rw [h, toReal_threeHalves, toReal_one]
  norm_num

/-- Subtracting a value from itself is exact. -/
example : toReal (sub tenth tenth) = 0 :=
  toReal_sub_self (by decide) (by decide)

/-- Subtracting from a zero and multiplying by `-1` are exact negations. -/
example : toReal (sub seed tenth) = -toReal tenth ∧
    toReal (mul tenth (negOne _)) = -toReal tenth := by
  refine ⟨toReal_sub_of_isZero_left _ _ (by decide) (by decide) (by decide), ?_⟩
  rw [toReal_mul_of_abs_toReal_eq_one_right _ _ (by decide) (by decide) (by decide)
    (by rw [toReal_negOne, abs_neg, abs_one]), toReal_negOne, mul_neg_one]

/-- A binary32 one-hot vector of any length, with `-1` at `j`, sums to exactly `-1`. -/
theorem oneHot_sum_binary32 (n : ℕ) (j : Fin n) :
    toRat? (Fin.foldl n (fun acc i => add acc (if i = j then negOne _ else zero _ false))
      (zero FloatFormat.binary32 false)) = some (-1) :=
  toRat?_fin_foldl_add_eq_single (by decide) (by decide +kernel)
    (by rw [ite_eq_left rfl]; decide +kernel) fun i hi => by rw [ite_eq_right hi]; decide +kernel

/-- A bfloat16 one-hot vector of any length, with `-1` at `j`, sums to exactly `-1`. -/
theorem oneHot_sum_bfloat16 (n : ℕ) (j : Fin n) :
    toRat? (Fin.foldl n (fun acc i => add acc (if i = j then negOne _ else zero _ false))
      (zero FloatFormat.bfloat16 false)) = some (-1) :=
  toRat?_fin_foldl_add_eq_single (by decide) (by decide +kernel)
    (by rw [ite_eq_left rfl]; decide +kernel) fun i hi => by rw [ite_eq_right hi]; decide +kernel

/-- `0.1 - 0.1` decodes to `0`, and so does its product with `0.3`. -/
example : toRat? (mul (sub tenth tenth) threeTenths) = some 0 :=
  toRat?_mul_of_toRat?_eq_some_zero_left (by decide) (toRat?_sub_self (by decide) (by decide))
    (by decide)

/-- Multiplying the bfloat16 value `0.1`, stored as `205/2048`, by `-1` is exact. -/
example : toRat? (mul (ofNatBits (fmt := FloatFormat.bfloat16) 0x3dcd) (negOne _)) =
    some (-(205 / 2048)) := by
  simpa using toRat?_mul_of_abs_eq_one_right (x := ofNatBits 0x3dcd) (y := negOne _)
    (p := 205 / 2048) (q := -1) (by decide) (by decide +kernel) (by decide +kernel) (by norm_num)

/-- The configured theorems apply to `Binary32` arithmetic written with `+`. -/
example (x y : Binary32) (hxy : (x + y).isFinite = true) :
    MixedError (x + y).toReal (x.toReal + y.toReal) (unitRoundoffAt FloatFormat.binary32) 0 := by
  simpa using ExecFloat.Binary.mixedError_toReal_add hxy
    (MixedError.refl _) (MixedError.refl _)

namespace ThroughputPlan

open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput

/-- They hold under every planning policy, so `+` planned for throughput is covered too. -/
example (x y : Binary32) (hxy : (x + y).isFinite = true) :
    MixedError (x + y).toReal (x.toReal + y.toReal) (unitRoundoffAt FloatFormat.binary32) 0 := by
  simpa using ExecFloat.Binary.mixedError_toReal_add hxy
    (MixedError.refl _) (MixedError.refl _)

end ThroughputPlan

/-! ## Logarithms of sums -/

/-- On a nonnegative sum, `log (1 + s)` keeps the relative error of `s`. -/
example {s s₀ : ℝ} (h : MixedError s s₀ (2⁻¹ ^ 23) 0) (hs₀ : 0 ≤ s₀) (hs : 0 ≤ s) :
    |Real.log (1 + s) - Real.log (1 + s₀)| ≤ 2⁻¹ ^ 23 * Real.log (1 + s₀) := by
  have hb := (h.log_one_add hs₀ hs).bound
  rwa [abs_of_nonneg (Real.log_nonneg (by linarith)), add_zero] at hb

/-- Above `-1/2`, `log (1 + s)` at most doubles the error of `s`, whatever its sign. -/
example {s s₀ : ℝ} (h : MixedError s s₀ 0 (2⁻¹ ^ 24)) (hs : -1 / 2 ≤ s) (hs₀ : -1 / 2 ≤ s₀) :
    |Real.log (1 + s) - Real.log (1 + s₀)| ≤ 2 * 2⁻¹ ^ 24 := by
  have hb := (h.log_one_add_of_le (m := 1 / 2) (by norm_num) (by linarith) (by linarith)).bound
  norm_num at hb ⊢
  linarith

/-- On `|x₀| ≤ 1`, `exp x - 1` turns a relative error `r ≤ 1/2` into at most `4 * r`. -/
example {x x₀ r : ℝ} (h : MixedError x x₀ r 0) (hr : r ≤ 1 / 2) (hx₀ : |x₀| ≤ 1) :
    MixedError (Real.exp x - 1) (Real.exp x₀ - 1) (4 * r) 0 := by
  have hr₀ := h.r_nonneg
  refine (h.exp_sub_one_of_abs_le hx₀).mono ?_ (by simp)
  -- `exp r * (1 - r) ≤ exp r * exp (-r) = 1`, so `exp r ≤ 2`.
  have hinv : Real.exp (r * 1 + 0) * Real.exp (-(r * 1 + 0)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hexp : Real.exp (r * 1 + 0) ≤ 2 := by
    nlinarith [Real.add_one_le_exp (-(r * 1 + 0)), Real.exp_pos (r * 1 + 0)]
  nlinarith

end FloatLibTests.Conformance.BinaryInterchange.MixedError
