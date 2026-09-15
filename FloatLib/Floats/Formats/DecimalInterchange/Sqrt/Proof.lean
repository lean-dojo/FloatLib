/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.GridProof
public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.ScaleProof
public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Proof

/-!
# Decimal square-root value, range, and error

Carry normalization preserves the rounded root, and preferred-cohort selection
preserves its value. The numerical bound compares the returned rational datum
with the mathematical real square root. Inexactness is tested by an exact
squaring equality.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

theorem sqrtRound_le_coefficientBound (f : Format) (mode : RoundingMode)
    {x : ℚ} (hx : 0 ≤ x) :
    mode.sqrtRound (x / (10 : ℚ) ^ (2 * sqrtQuantum f x)) ≤ f.coefficientBound := by
  have hu : 0 < (10 : ℚ) ^ (2 * sqrtQuantum f x) := zpow_pos (by norm_num) _
  have hf : ⌊x / (10 : ℚ) ^ (2 * sqrtQuantum f x)⌋₊ < f.coefficientBound ^ 2 :=
    (Nat.floor_lt (div_nonneg hx hu.le)).mpr (by
      exact_mod_cast div_sqrtQuantum_lt f hx)
  have hs := Nat.sqrt_lt'.mpr hf
  exact (mode.sqrtRound_le_floor_add_one _).trans (by unfold sqrtFloor; omega)

theorem sqrtPair_coefficient_lt (f : Format) (mode : RoundingMode)
    {x : ℚ} (hx : 0 ≤ x) : (sqrtPair f mode x).1 < f.coefficientBound := by
  exact f.carry_coefficient_lt (sqrtRound_le_coefficientBound f mode hx) _

theorem sqrtPair_quantum_ge_min (f : Format) (mode : RoundingMode) (x : ℚ) :
    f.minQuantum ≤ (sqrtPair f mode x).2 := by
  exact (sqrtQuantum_ge_min f x).trans (f.le_carry_quantum _ _)

/-- Decimal carry normalization does not change the rounded numerical root. -/
theorem sqrtPair_value (f : Format) (mode : RoundingMode) (x : ℚ) :
    ((sqrtPair f mode x).1 : ℚ) * (10 : ℚ) ^ (sqrtPair f mode x).2 =
      (mode.sqrtRound (x / (10 : ℚ) ^ (2 * sqrtQuantum f x)) : ℚ) *
        (10 : ℚ) ^ sqrtQuantum f x := by
  exact Numerics.RadixText.carry_value 10 (by decide) _ _ _

theorem sqrtMagnitude_valid (f : Format) (mode : RoundingMode)
    {x : ℚ} (hx : 0 ≤ x) (preferred : Int) :
    (sqrtMagnitude f mode x preferred).value.Valid f := by
  simp only [sqrtMagnitude]
  split
  · split
    · trivial
    · exact f.maxFinite_valid false
  · rename_i hq
    have hv : (Datum.finite false (sqrtPair f mode x).1
        (sqrtPair f mode x).2).Valid f :=
      (Datum.valid_quantum_iff ..).mpr ⟨sqrtPair_coefficient_lt f mode hx,
        sqrtPair_quantum_ge_min f mode x, le_of_not_gt hq⟩
    split
    · exact hv
    · exact preferredCohort_valid f false _ _ _ hv

theorem Arithmetic.sqrt_valid (f : Format) (mode : RoundingMode) (x : Datum) :
    (sqrt f mode x).value.Valid f := by
  cases x with
  | nan s t p => exact nanResult_valid ..
  | infinity s =>
    simp only [sqrt]
    split <;> first | exact invalidResult_valid f | trivial
  | finite s c q =>
    simp only [sqrt]
    split
    · exact projectMagnitude_valid f mode s (by rfl) _
    · split
      · exact invalidResult_valid f
      · exact sqrtMagnitude_valid f mode
          (mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num) q).le) _

theorem sqrtMagnitude_overflow_iff (f : Format) (mode : RoundingMode)
    (x : ℚ) (preferred : Int) :
    (sqrtMagnitude f mode x preferred).status.overflow = true ↔
      f.maxQuantum < (sqrtPair f mode x).2 := by
  by_cases h : f.maxQuantum < (sqrtPair f mode x).2 <;> simp [sqrtMagnitude, h]

theorem sqrtMagnitude_value (f : Format) (mode : RoundingMode)
    (x : ℚ) (preferred : Int) (hq : (sqrtPair f mode x).2 ≤ f.maxQuantum) :
    (sqrtMagnitude f mode x preferred).value.toRat? =
      some ((mode.sqrtRound (x / (10 : ℚ) ^ (2 * sqrtQuantum f x)) : ℚ) *
        (10 : ℚ) ^ sqrtQuantum f x) := by
  simp only [sqrtMagnitude, ite_eq_right (not_lt.mpr hq)]
  have hv := sqrtPair_value f mode x
  split
  · simp only [Datum.toRat?_eq, Bool.false_eq_true, ↓reduceIte, one_mul, hv]
  · rw [preferredCohort_toRat?]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, hv]

/-- Scaling by a decimal quantum commutes with the nonnegative mathematical square root. -/
theorem sqrt_scaled (x : ℚ) (q : Int) :
    Real.sqrt ((x / (10 : ℚ) ^ (2 * q) : ℚ) : ℝ) * (10 : ℝ) ^ q =
      Real.sqrt (x : ℝ) := by
  have hu : 0 < (10 : ℝ) ^ q := zpow_pos (by norm_num) _
  have he : (10 : ℝ) ^ (2 * q) = ((10 : ℝ) ^ q) ^ 2 := by
    rw [mul_comm 2 q, zpow_mul]
    norm_num
  rw [Rat.cast_div, Rat.cast_zpow, Rat.cast_ofNat, he,
    Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hu.le, div_mul_cancel₀ _ hu.ne']

/-- The actual returned datum is within half a grid unit of the mathematical root. -/
theorem sqrtMagnitude_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (sqrtMagnitude f mode x preferred).status.overflow = false) :
    ∃ value : ℚ, (sqrtMagnitude f mode x preferred).value.toRat? = some value ∧
      |(value : ℝ) - Real.sqrt (x : ℝ)| ≤ (10 : ℝ) ^ sqrtQuantum f x / 2 := by
  have hq : (sqrtPair f mode x).2 ≤ f.maxQuantum := by
    apply le_of_not_gt
    intro h
    have ht := (sqrtMagnitude_overflow_iff f mode x preferred).mpr h
    simp [hfinite] at ht
  refine ⟨_, sqrtMagnitude_value f mode x preferred hq, ?_⟩
  let q := sqrtQuantum f x
  have hu : 0 < (10 : ℝ) ^ q := zpow_pos (by norm_num) _
  have hx' : 0 ≤ x / (10 : ℚ) ^ (2 * q) :=
    div_nonneg hx (zpow_pos (by norm_num) _).le
  have h := sqrtRound_error_le_half mode hm hx'
  have he :
      (((mode.sqrtRound (x / (10 : ℚ) ^ (2 * q)) : Nat) : ℝ) * (10 : ℝ) ^ q -
          Real.sqrt (x : ℝ)) =
        (((mode.sqrtRound (x / (10 : ℚ) ^ (2 * q)) : Nat) : ℝ) -
          Real.sqrt ((x / (10 : ℚ) ^ (2 * q) : ℚ) : ℝ)) * (10 : ℝ) ^ q := by
    rw [sub_mul, sqrt_scaled]
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_zpow, Rat.cast_ofNat]
  rw [he, abs_mul, abs_of_pos hu]
  exact (mul_le_mul_of_nonneg_right h hu.le).trans_eq (by ring)

/-- Squared equality tests real numerical exactness, including irrational roots. -/
theorem sqrtMagnitude_inexact_iff (f : Format) (mode : RoundingMode)
    {x : ℚ} (hx : 0 ≤ x) (value : ℚ) (preferred : Int)
    (hq : (sqrtPair f mode x).2 ≤ f.maxQuantum)
    (hv : (sqrtMagnitude f mode x preferred).value.toRat? = some value) :
    (sqrtMagnitude f mode x preferred).status.inexact = true ↔
      (value : ℝ) ≠ Real.sqrt (x : ℝ) := by
  have he := sqrtMagnitude_value f mode x preferred hq
  rw [hv] at he
  have hv' := Option.some.inj he
  have hvnonneg : 0 ≤ value := by
    rw [hv']
    exact mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  have hexact : value ^ 2 = x ↔ (value : ℝ) = Real.sqrt (x : ℝ) := by
    constructor
    · intro h
      apply Eq.symm
      apply (Real.sqrt_eq_iff_eq_sq (by exact_mod_cast hx)
        (by exact_mod_cast hvnonneg)).mpr
      exact_mod_cast h.symm
    · intro h
      have hsq := Real.sq_sqrt (show 0 ≤ (x : ℝ) by exact_mod_cast hx)
      rw [← h] at hsq
      exact_mod_cast hsq
  simp only [sqrtMagnitude, ite_eq_right (not_lt.mpr hq), decide_eq_true_eq]
  rw [sqrtPair_value, ← hv']
  exact not_congr hexact

end FloatLib.Floats.Formats.DecimalInterchange
