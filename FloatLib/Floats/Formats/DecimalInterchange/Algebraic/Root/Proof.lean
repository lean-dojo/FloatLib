/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Root.GridProof
public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Root.ScaleProof
public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Proof

/-!
# Integer-degree root values and rounding guarantees

The delivered datum represents the signed, rounded coefficient. Carry and exact
cohort selection preserve its value. Numerical bounds compare it with the real
root, and power equality decides exactness without approximating an irrational
result.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- On the grid `rootQuantum` selects, the rounded root coefficient is at most the coefficient
bound, so only a carry can reach `10 ^ precision`. -/
theorem rootRound_le_coefficientBound (f : Format) (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) :
    mode.rootRound s degree (x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x)) ≤
      f.coefficientBound := by
  have hu : 0 < (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x) :=
    zpow_pos (by norm_num) _
  have hf : ⌊x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x)⌋₊ <
      f.coefficientBound ^ degree :=
    (Nat.floor_lt (div_nonneg hx hu.le)).mpr (by
      exact_mod_cast div_rootQuantum_lt f (Nat.pos_of_ne_zero hn) x)
  have hs := (Nat.nthRoot_lt_iff hn).mpr hf
  exact (mode.rootRound_le_floor_add_one s degree _).trans (by
    rw [rootFloor_eq_nthRoot]
    omega)

/-- After the power-of-ten carry, the rounded root coefficient fits the format's precision. -/
theorem rootPair_coefficient_lt (f : Format) (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) :
    (rootPair f mode s degree x).1 < f.coefficientBound :=
  f.carry_coefficient_lt (rootRound_le_coefficientBound f mode s hn hx) _

/-- The quantum of a rounded root is never below the format's least quantum. -/
theorem rootPair_quantum_ge_min (f : Format) (mode : RoundingMode) (s : Bool)
    (degree : Nat) (x : ℚ) : f.minQuantum ≤ (rootPair f mode s degree x).2 :=
  (rootQuantum_ge_min f degree x).trans (f.le_carry_quantum _ _)

/-- The power-of-ten carry preserves the value of the rounded root: the pair still represents the
grid-rounded root times the selected grid unit. -/
theorem rootPair_value (f : Format) (mode : RoundingMode) (s : Bool)
    (degree : Nat) (x : ℚ) :
    ((rootPair f mode s degree x).1 : ℚ) * (10 : ℚ) ^ (rootPair f mode s degree x).2 =
      (mode.rootRound s degree
        (x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x)) : ℚ) *
          (10 : ℚ) ^ rootQuantum f degree x :=
  Numerics.RadixText.carry_value 10 (by decide) _ _ _

/-- For a positive degree and a nonnegative radicand, the root rounder delivers a valid datum of the
format, overflow results included. -/
theorem rootMagnitude_valid (f : Format) (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int) :
    (rootMagnitude f mode s degree x preferred).value.Valid f := by
  simp only [rootMagnitude]
  split
  · split
    · trivial
    · exact f.maxFinite_valid s
  · rename_i hq
    have hv : (Datum.finite s (rootPair f mode s degree x).1
        (rootPair f mode s degree x).2).Valid f :=
      (Datum.valid_quantum_iff ..).mpr ⟨rootPair_coefficient_lt f mode s hn hx,
        rootPair_quantum_ge_min f mode s degree x, le_of_not_gt hq⟩
    split
    · exact hv
    · exact preferredCohort_valid f s _ _ _ hv

/-- Degree zero always delivers an invalid result, including quiet and signaling NaNs. -/
@[simp] theorem Arithmetic.rootN_degree_zero (f : Format) (mode : RoundingMode) (x : Datum) :
    rootN f mode x 0 = invalidResult := by
  cases x <;> simp [rootN]

/-- Every integer-degree root, including NaN, invalid, pole, infinite and overflowed results, is a
valid datum of the format. -/
theorem Arithmetic.rootN_valid (f : Format) (mode : RoundingMode) (x : Datum) (n : Int) :
    (rootN f mode x n).value.Valid f := by
  cases x with
  | nan s t p =>
    simp only [rootN]
    split
    · exact invalidResult_valid f
    · exact nanResult_valid ..
  | infinity s =>
    simp only [rootN]
    repeat first
      | exact invalidResult_valid f
      | exact projectMagnitude_valid f mode _ (by rfl) _
      | trivial
      | split
  | finite s c q =>
    simp only [rootN]
    split
    · exact invalidResult_valid f
    · rename_i hn
      split
      · split
        · trivial
        · exact projectMagnitude_valid f mode _ (by rfl) _
      · split
        · exact invalidResult_valid f
        · apply rootMagnitude_valid f mode _ (Int.natAbs_ne_zero.mpr hn)
          split
          · exact inv_nonneg.mpr
              (mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num) q).le)
          · exact mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num) q).le

/-- The root rounder raises overflow exactly when the rounded quantum exceeds the format's largest
quantum. -/
theorem rootMagnitude_overflow_iff (f : Format) (mode : RoundingMode) (s : Bool)
    (degree : Nat) (x : ℚ) (preferred : Int) :
    (rootMagnitude f mode s degree x preferred).status.overflow = true ↔
      f.maxQuantum < (rootPair f mode s degree x).2 := by
  by_cases h : f.maxQuantum < (rootPair f mode s degree x).2 <;>
    simp [rootMagnitude, h]

/-- Without overflow, the quantum of the rounded root is at most the format's largest quantum. -/
theorem rootMagnitude_quantum_le_of_no_overflow (f : Format) (mode : RoundingMode)
    (s : Bool) (degree : Nat) (x : ℚ) (preferred : Int)
    (hfinite : (rootMagnitude f mode s degree x preferred).status.overflow = false) :
    (rootPair f mode s degree x).2 ≤ f.maxQuantum := by
  apply le_of_not_gt
  intro h
  have ht := (rootMagnitude_overflow_iff f mode s degree x preferred).mpr h
  simp [hfinite] at ht

/-- Without overflow, the delivered root is finite and has the signed value of the grid-rounded
root, whichever cohort member is selected. -/
theorem rootMagnitude_value (f : Format) (mode : RoundingMode) (s : Bool)
    (degree : Nat) (x : ℚ) (preferred : Int)
    (hq : (rootPair f mode s degree x).2 ≤ f.maxQuantum) :
    (rootMagnitude f mode s degree x preferred).value.toRat? =
      some ((if s then -1 else 1) *
        (mode.rootRound s degree
          (x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x)) : ℚ) *
            (10 : ℚ) ^ rootQuantum f degree x) := by
  simp only [rootMagnitude, ite_eq_right (not_lt.mpr hq)]
  have hv := rootPair_value f mode s degree x
  split
  · simp only [Datum.toRat?_eq, mul_assoc, hv]
  · rw [preferredCohort_toRat?]
    simp only [mul_assoc, hv]

/-- Multiplication by a positive decimal quantum commutes with the real root. -/
theorem realRoot_scaled {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x)
    (q : Int) :
    realRoot degree ((x / (10 : ℚ) ^ ((degree : Int) * q) : ℚ) : ℝ) *
        (10 : ℝ) ^ q = realRoot degree (x : ℝ) := by
  have hu : 0 < (10 : ℝ) ^ q := zpow_pos (by norm_num) _
  have hx' : 0 ≤ ((x / (10 : ℚ) ^ ((degree : Int) * q) : ℚ) : ℝ) := by
    exact_mod_cast div_nonneg hx (zpow_pos (by norm_num : (0 : ℚ) < 10) _).le
  apply (pow_left_inj₀ (mul_nonneg (realRoot_nonneg degree hx') hu.le)
    (realRoot_nonneg degree (by exact_mod_cast hx)) hn).mp
  rw [mul_pow, realRoot_pow hn hx', realRoot_pow hn (by exact_mod_cast hx),
    Rat.cast_div, Rat.cast_zpow, Rat.cast_ofNat]
  have he : (10 : ℝ) ^ ((degree : Int) * q) = ((10 : ℝ) ^ q) ^ degree := by
    rw [mul_comm (degree : Int), zpow_mul, zpow_natCast]
  rw [he, div_mul_cancel₀ _ (pow_ne_zero _ hu.ne')]

/-- An overflowing root of a nonnegative rational has an exact root strictly above the greatest
finite magnitude. -/
theorem maxFinite_lt_realRoot_of_overflow (f : Format) (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x)
    (h : f.maxQuantum < (rootPair f mode s degree x).2) :
    ((f.coefficientBound - 1 : Nat) : ℝ) * (10 : ℝ) ^ f.maxQuantum < realRoot degree (x : ℝ) := by
  have hu : (0 : ℚ) < (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x) :=
    zpow_pos (by norm_num) _
  have hy := div_nonneg hx hu.le
  have hlt := f.maxFinite_lt_of_carry_overflow
    (mode.rootRound s degree (x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x)))
    (rootQuantum f degree x)
    (realRoot degree ((x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x) : ℚ) : ℝ))
    (rootRound_error_lt_one mode s hn hy)
    (fun hq => (le_realRoot_iff hn (by exact_mod_cast hy) (Nat.cast_nonneg _)).mpr
      (by exact_mod_cast payloadBound_pow_le_div_rootQuantum f hq)) h
  rwa [realRoot_scaled hn hx] at hlt

/-- Without overflow, the delivered root is finite, and its error is the error of the integer root
rounding at the scaled radicand, with the result's sign, times the grid unit. -/
theorem rootMagnitude_value_sub_realRoot (f : Format) (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (rootMagnitude f mode s degree x preferred).status.overflow = false) :
    ∃ value : ℚ, (rootMagnitude f mode s degree x preferred).value.toRat? = some value ∧
      (value : ℝ) - (if s then -1 else 1) * realRoot degree (x : ℝ) =
        (if s then -1 else 1) *
          ((mode.rootRound s degree
              (x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x)) : ℝ) -
            realRoot degree ((x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x) : ℚ) :
              ℝ)) * (10 : ℝ) ^ rootQuantum f degree x := by
  have hq := rootMagnitude_quantum_le_of_no_overflow f mode s degree x preferred hfinite
  refine ⟨_, rootMagnitude_value f mode s degree x preferred hq, ?_⟩
  rw [← realRoot_scaled hn hx (rootQuantum f degree x)]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] <;> ring

/-- Without overflow, the absolute error of the delivered root is the integer rounding error at the
scaled radicand times the grid unit; the result's sign does not matter. -/
private theorem rootMagnitude_abs_value_sub_realRoot (f : Format) (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (rootMagnitude f mode s degree x preferred).status.overflow = false) :
    ∃ value : ℚ, (rootMagnitude f mode s degree x preferred).value.toRat? = some value ∧
      |(value : ℝ) - (if s then -1 else 1) * realRoot degree (x : ℝ)| =
        |(mode.rootRound s degree
            (x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x)) : ℝ) -
          realRoot degree ((x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x) : ℚ) : ℝ)| *
        (10 : ℝ) ^ rootQuantum f degree x := by
  obtain ⟨value, hv, he⟩ := rootMagnitude_value_sub_realRoot f mode s hn hx preferred hfinite
  refine ⟨value, hv, ?_⟩
  have hsign : |(if s then -1 else 1 : ℝ)| = 1 := by cases s <;> simp
  rw [he, abs_mul, abs_mul, hsign, one_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 10) _)]

/-- In both nearest modes, a nonoverflowing rounded root of a nonnegative rational is finite and
within half a grid unit of the signed real root. -/
theorem rootMagnitude_error_le_half (f : Format) (mode : RoundingMode) (s : Bool)
    (hm : mode = .nearest ∨ mode = .nearestAway)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (rootMagnitude f mode s degree x preferred).status.overflow = false) :
    ∃ value : ℚ, (rootMagnitude f mode s degree x preferred).value.toRat? = some value ∧
      |(value : ℝ) - (if s then -1 else 1) * realRoot degree (x : ℝ)| ≤
        (10 : ℝ) ^ rootQuantum f degree x / 2 := by
  obtain ⟨value, hv, he⟩ := rootMagnitude_abs_value_sub_realRoot f mode s hn hx preferred hfinite
  refine ⟨value, hv, he ▸ ?_⟩
  have h := rootRound_error_le_half mode s hm hn
    (div_nonneg hx (zpow_pos (by norm_num : (0 : ℚ) < 10)
      ((degree : Int) * rootQuantum f degree x)).le)
  exact (mul_le_mul_of_nonneg_right h (zpow_pos (by norm_num : (0 : ℝ) < 10) _).le).trans_eq
    (by ring)

/-- In every rounding direction, a nonoverflowing rounded root of a nonnegative rational is finite
and less than one grid unit from the signed real root. -/
theorem rootMagnitude_error_lt_one (f : Format) (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (rootMagnitude f mode s degree x preferred).status.overflow = false) :
    ∃ value : ℚ, (rootMagnitude f mode s degree x preferred).value.toRat? = some value ∧
      |(value : ℝ) - (if s then -1 else 1) * realRoot degree (x : ℝ)| <
        (10 : ℝ) ^ rootQuantum f degree x := by
  obtain ⟨value, hv, he⟩ := rootMagnitude_abs_value_sub_realRoot f mode s hn hx preferred hfinite
  refine ⟨value, hv, he ▸ ?_⟩
  have h := rootRound_error_lt_one mode s hn
    (div_nonneg hx (zpow_pos (by norm_num : (0 : ℚ) < 10)
      ((degree : Int) * rootQuantum f degree x)).le)
  exact (mul_lt_mul_of_pos_right h (zpow_pos (by norm_num : (0 : ℝ) < 10) _)).trans_eq
    (one_mul _)

/-- Without overflow, the root rounder raises inexact exactly when the delivered value differs from
the signed real root; the rounder decides this by an exact power equality. -/
theorem rootMagnitude_inexact_iff (f : Format) (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x)
    (value : ℚ) (preferred : Int)
    (hfinite : (rootMagnitude f mode s degree x preferred).status.overflow = false)
    (hv : (rootMagnitude f mode s degree x preferred).value.toRat? = some value) :
    (rootMagnitude f mode s degree x preferred).status.inexact = true ↔
      (value : ℝ) ≠ (if s then -1 else 1) * realRoot degree (x : ℝ) := by
  have hq := rootMagnitude_quantum_le_of_no_overflow f mode s degree x preferred hfinite
  have he := rootMagnitude_value f mode s degree x preferred hq
  rw [hv] at he
  have hv' := Option.some.inj he
  let magnitude : ℚ := (mode.rootRound s degree
    (x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x)) : ℚ) *
      (10 : ℚ) ^ rootQuantum f degree x
  have hm : 0 ≤ magnitude :=
    mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  have hexact : magnitude ^ degree = x ↔ (magnitude : ℝ) = realRoot degree (x : ℝ) := by
    rw [← pow_left_inj₀ (by exact_mod_cast hm)
      (realRoot_nonneg degree (by exact_mod_cast hx)) hn, realRoot_pow hn
        (by exact_mod_cast hx)]
    exact_mod_cast Iff.rfl
  have hsign : (value : ℝ) = (if s then -1 else 1) * realRoot degree (x : ℝ) ↔
      (magnitude : ℝ) = realRoot degree (x : ℝ) := by
    rw [hv']
    cases s <;> simp [magnitude]
  simp only [rootMagnitude, ite_eq_right (not_lt.mpr hq), decide_eq_true_eq]
  rw [rootPair_value]
  exact not_congr (hexact.trans hsign.symm)

/-- Underflow uses the exact root's magnitude, before rounding; an overflowing root is never tiny.
-/
theorem rootMagnitude_underflow_iff (f : Format) (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int) :
    (rootMagnitude f mode s degree x preferred).status.underflow = true ↔
      realRoot degree (x : ℝ) < (f.minNormal : ℝ) ∧
        (rootMagnitude f mode s degree x preferred).status.inexact = true := by
  by_cases hq : (rootPair f mode s degree x).2 ≤ f.maxQuantum
  swap
  · have hq' := lt_of_not_ge hq
    have hlt := maxFinite_lt_realRoot_of_overflow f mode s hn hx hq'
    have hmin : ((f.minNormal : ℚ) : ℝ) ≤
        ((f.coefficientBound - 1 : Nat) : ℝ) * (10 : ℝ) ^ f.maxQuantum := by
      simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_zpow, Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr f.minNormal_le_maxFinite
    simp only [rootMagnitude, hq', ↓reduceIte, Bool.false_eq_true, false_iff, not_and]
    exact fun h => absurd h (not_lt.mpr (hmin.trans hlt.le))
  have hp : (0 : ℚ) < f.minNormal :=
    mul_pos (pow_pos (by norm_num) _) (zpow_pos (by norm_num) _)
  have he : realRoot degree (x : ℝ) < (f.minNormal : ℝ) ↔
      x < f.minNormal ^ degree := by
    rw [realRoot_lt_iff hn (by exact_mod_cast hx) (by exact_mod_cast hp.le)]
    exact_mod_cast Iff.rfl
  simp [rootMagnitude, not_lt.mpr hq, he]

end FloatLib.Floats.Formats.DecimalInterchange
