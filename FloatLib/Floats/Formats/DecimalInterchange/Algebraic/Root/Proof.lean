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

theorem rootRound_le_coefficientBound (f : Format) (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) :
    mode.rootRound s degree (x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x)) ≤
      f.coefficientBound := by
  have hu : 0 < (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x) :=
    zpow_pos (by norm_num) _
  have hf : ⌊x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x)⌋₊ <
      f.coefficientBound ^ degree :=
    (Nat.floor_lt (div_nonneg hx hu.le)).mpr (by
      exact_mod_cast div_rootQuantum_lt f (Nat.pos_of_ne_zero hn) hx)
  have hs := (Nat.nthRoot_lt_iff hn).mpr hf
  exact (mode.rootRound_le_floor_add_one s degree _).trans (by
    rw [rootFloor_eq_nthRoot]
    omega)

theorem rootPair_coefficient_lt (f : Format) (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) :
    (rootPair f mode s degree x).1 < f.coefficientBound :=
  f.carry_coefficient_lt (rootRound_le_coefficientBound f mode s hn hx) _

theorem rootPair_quantum_ge_min (f : Format) (mode : RoundingMode) (s : Bool)
    (degree : Nat) (x : ℚ) : f.minQuantum ≤ (rootPair f mode s degree x).2 :=
  (rootQuantum_ge_min f degree x).trans (f.le_carry_quantum _ _)

theorem rootPair_value (f : Format) (mode : RoundingMode) (s : Bool)
    (degree : Nat) (x : ℚ) :
    ((rootPair f mode s degree x).1 : ℚ) * (10 : ℚ) ^ (rootPair f mode s degree x).2 =
      (mode.rootRound s degree
        (x / (10 : ℚ) ^ ((degree : Int) * rootQuantum f degree x)) : ℚ) *
          (10 : ℚ) ^ rootQuantum f degree x :=
  Numerics.RadixText.carry_value 10 (by decide) _ _ _

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

theorem Arithmetic.rootN_valid (f : Format) (mode : RoundingMode) (x : Datum) (n : Int) :
    (rootN f mode x n).value.Valid f := by
  cases x with
  | nan s t p => exact nanResult_valid ..
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

theorem rootMagnitude_overflow_iff (f : Format) (mode : RoundingMode) (s : Bool)
    (degree : Nat) (x : ℚ) (preferred : Int) :
    (rootMagnitude f mode s degree x preferred).status.overflow = true ↔
      f.maxQuantum < (rootPair f mode s degree x).2 := by
  by_cases h : f.maxQuantum < (rootPair f mode s degree x).2 <;>
    simp [rootMagnitude, h]

theorem rootMagnitude_quantum_le_of_no_overflow (f : Format) (mode : RoundingMode)
    (s : Bool) (degree : Nat) (x : ℚ) (preferred : Int)
    (hfinite : (rootMagnitude f mode s degree x preferred).status.overflow = false) :
    (rootPair f mode s degree x).2 ≤ f.maxQuantum := by
  apply le_of_not_gt
  intro h
  have ht := (rootMagnitude_overflow_iff f mode s degree x preferred).mpr h
  simp [hfinite] at ht

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

theorem rootMagnitude_error_le_half (f : Format) (mode : RoundingMode) (s : Bool)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (rootMagnitude f mode s degree x preferred).status.overflow = false) :
    ∃ value : ℚ, (rootMagnitude f mode s degree x preferred).value.toRat? = some value ∧
      |(value : ℝ) - (if s then -1 else 1) * realRoot degree (x : ℝ)| ≤
        (10 : ℝ) ^ rootQuantum f degree x / 2 := by
  have hq := rootMagnitude_quantum_le_of_no_overflow f mode s degree x preferred hfinite
  refine ⟨_, rootMagnitude_value f mode s degree x preferred hq, ?_⟩
  let q := rootQuantum f degree x
  have hu : 0 < (10 : ℝ) ^ q := zpow_pos (by norm_num) _
  have hx' : 0 ≤ x / (10 : ℚ) ^ ((degree : Int) * q) :=
    div_nonneg hx (zpow_pos (by norm_num) _).le
  have h := rootRound_error_le_half mode s hm hn hx'
  have hs := mul_le_mul_of_nonneg_right h hu.le
  rw [← abs_of_pos hu, ← abs_mul, sub_mul, realRoot_scaled hn hx] at hs
  have hs' : |(mode.rootRound s degree
        (x / (10 : ℚ) ^ ((degree : Int) * q)) : ℝ) * (10 : ℝ) ^ q -
      realRoot degree (x : ℝ)| ≤ (10 : ℝ) ^ q / 2 := by
    simpa only [abs_of_pos hu, div_eq_mul_inv, one_mul, mul_comm (2 : ℝ)⁻¹] using hs
  cases s <;>
    simpa only [Bool.false_eq_true, ↓reduceIte, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one, one_mul,
      neg_one_mul, neg_mul, neg_sub_neg, abs_sub_comm] using hs'

theorem rootMagnitude_error_lt_one (f : Format) (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (rootMagnitude f mode s degree x preferred).status.overflow = false) :
    ∃ value : ℚ, (rootMagnitude f mode s degree x preferred).value.toRat? = some value ∧
      |(value : ℝ) - (if s then -1 else 1) * realRoot degree (x : ℝ)| <
        (10 : ℝ) ^ rootQuantum f degree x := by
  have hq := rootMagnitude_quantum_le_of_no_overflow f mode s degree x preferred hfinite
  refine ⟨_, rootMagnitude_value f mode s degree x preferred hq, ?_⟩
  let q := rootQuantum f degree x
  have hu : 0 < (10 : ℝ) ^ q := zpow_pos (by norm_num) _
  have hx' : 0 ≤ x / (10 : ℚ) ^ ((degree : Int) * q) :=
    div_nonneg hx (zpow_pos (by norm_num) _).le
  have h := rootRound_error_lt_one mode s hn hx'
  have hs := mul_lt_mul_of_pos_right h hu
  rw [← abs_of_pos hu, ← abs_mul, sub_mul, realRoot_scaled hn hx, abs_of_pos hu,
    one_mul] at hs
  cases s <;>
    simpa only [Bool.false_eq_true, ↓reduceIte, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one, one_mul,
      neg_one_mul, neg_mul, neg_sub_neg, abs_sub_comm] using hs

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

/-- Underflow uses the exact root's magnitude, before rounding. -/
theorem rootMagnitude_underflow_iff (f : Format) (mode : RoundingMode) (s : Bool)
    {degree : Nat} (hn : degree ≠ 0) {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hfinite : (rootMagnitude f mode s degree x preferred).status.overflow = false) :
    (rootMagnitude f mode s degree x preferred).status.underflow = true ↔
      realRoot degree (x : ℝ) < (f.minNormal : ℝ) ∧
        (rootMagnitude f mode s degree x preferred).status.inexact = true := by
  have hq := rootMagnitude_quantum_le_of_no_overflow f mode s degree x preferred hfinite
  have hp : (0 : ℚ) < f.minNormal :=
    mul_pos (pow_pos (by norm_num) _) (zpow_pos (by norm_num) _)
  have he : realRoot degree (x : ℝ) < (f.minNormal : ℝ) ↔
      x < f.minNormal ^ degree := by
    rw [realRoot_lt_iff hn (by exact_mod_cast hx) (by exact_mod_cast hp.le)]
    exact_mod_cast Iff.rfl
  simp [rootMagnitude, not_lt.mpr hq, he]

end FloatLib.Floats.Formats.DecimalInterchange
