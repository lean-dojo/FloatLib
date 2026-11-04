/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.ScaleProof
public import FloatLib.Floats.Formats.DecimalInterchange.Rounding.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Cohort.Proof

/-!
# Value, range, and error of rational projection

Rounding to precision can carry at most once. In decimal32, `9999999.5` rounds to `10000000`,
which needs an eighth digit until it is renormalized to `1000000e1`. Carry normalization and
preferred-cohort selection keep the exact value, and every result is representable in its
destination format, a directed overflow result included.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Rounding a zero magnitude gives coefficient zero at the least quantum, in every mode and for
either sign. -/
theorem roundedPair_zero (f : Format) (mode : RoundingMode) (s : Bool) :
    roundedPair f mode s 0 = (0, f.minQuantum) := by
  have hb := Nat.ne_of_gt f.coefficientBound_pos
  have hz : mode.roundMagnitude s 0 = 0 := mode.roundMagnitude_natCast s 0
  simp [roundedPair, f.carry_eq, RoundingMode.roundAt, roundingQuantum_zero, hz, hb.symm]

/-- Direct zero delivery agrees with precision rounding, cohort selection and all flags. -/
theorem projectMagnitude_eq (f : Format) (mode : RoundingMode) (s : Bool)
    (x : ℚ) (preferred : Int) :
    projectMagnitude f mode s x preferred =
      let result := roundedPair f mode s x
      if f.maxQuantum < result.2 then
        { value := if mode.overflowToInfinity s then .infinity s else f.maxFinite s
          status := { overflow := true, inexact := true } }
      else
        let inexact := decide ((result.1 : ℚ) * (10 : ℚ) ^ result.2 ≠ x)
        { value := if inexact then .finite s result.1 result.2
            else preferredCohort f s result.1 result.2 preferred
          status :=
            { inexact := inexact
              underflow := decide (x < f.minNormal) && inexact } } := by
  by_cases hx : x = 0
  · subst x
    simp [projectMagnitude, roundedPair_zero, not_lt.mpr f.minQuantum_le_maxQuantum]
  · simp only [projectMagnitude, ite_eq_right hx]

/-- On the grid `roundingQuantum` selects, the rounded coefficient is at most the coefficient bound,
so only a carry can reach `10 ^ precision`. -/
theorem roundAt_le_coefficientBound (f : Format) (mode : RoundingMode) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) :
    mode.roundAt s x (roundingQuantum f x) ≤ f.coefficientBound := by
  have hu : 0 < (10 : ℚ) ^ roundingQuantum f x := zpow_pos (by norm_num) _
  have hf := (Nat.floor_lt (div_nonneg hx hu.le)).mpr (div_roundingQuantum_lt f x)
  exact (mode.roundMagnitude_le_floor_add_one s _).trans (by omega)

/-- After the power-of-ten carry, the rounded coefficient fits the format's precision. -/
theorem roundedPair_coefficient_lt (f : Format) (mode : RoundingMode) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) :
    (roundedPair f mode s x).1 < f.coefficientBound := by
  exact f.carry_coefficient_lt (roundAt_le_coefficientBound f mode s hx) _

/-- The quantum of a rounded pair is never below the format's least quantum. -/
theorem roundedPair_quantum_ge_min (f : Format) (mode : RoundingMode) (s : Bool) (x : ℚ) :
    f.minQuantum ≤ (roundedPair f mode s x).2 := by
  exact (roundingQuantum_ge_min f x).trans (f.le_carry_quantum _ _)

/-- Carry normalization leaves the computed value unchanged. -/
theorem roundedPair_value (f : Format) (mode : RoundingMode) (s : Bool) (x : ℚ) :
    ((roundedPair f mode s x).1 : ℚ) * (10 : ℚ) ^ (roundedPair f mode s x).2 =
      (mode.roundAt s x (roundingQuantum f x) : ℚ) *
        (10 : ℚ) ^ roundingQuantum f x := by
  exact Numerics.RadixText.carry_value 10 (by decide) _ _ _

/-- The greatest finite datum of either sign is valid in the format. -/
theorem Format.maxFinite_valid (f : Format) (s : Bool) : (f.maxFinite s).Valid f := by
  rw [Format.maxFinite, Datum.valid_quantum_iff]
  have hb := f.coefficientBound_pos
  have hq := f.minQuantum_le_maxQuantum
  exact ⟨by omega, hq, le_rfl⟩

/-- The least normal magnitude is at most the greatest finite magnitude. -/
theorem Format.minNormal_le_maxFinite (f : Format) :
    f.minNormal ≤ ((f.coefficientBound - 1 : Nat) : ℚ) * (10 : ℚ) ^ f.maxQuantum := by
  have hp : ((10 ^ (f.precision - 1) : Nat) : ℚ) ≤ ((f.coefficientBound - 1 : Nat) : ℚ) := by
    exact_mod_cast f.payloadBound_eq ▸ f.payloadBound_le_coefficientBound_sub_one
  rw [Format.minNormal]
  push_cast at hp
  exact mul_le_mul hp (zpow_le_zpow_right₀ (by norm_num) f.minQuantum_le_maxQuantum)
    (zpow_pos (by norm_num) _).le (Nat.cast_nonneg _)

/-- A rounded coefficient whose carry overflows the largest quantum comes from an exact value above
the greatest finite magnitude. Here `c` is within one unit of the exact scaled value `y` on the grid
`q`, and `y` has a full leading digit whenever `q` is above the least quantum. -/
theorem Format.maxFinite_lt_of_carry_overflow {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (f : Format) (c : Nat) (q : Int) (y : K)
    (hc : |(c : K) - y| < 1) (hfull : f.minQuantum < q → (f.payloadBound : K) ≤ y)
    (h : f.maxQuantum < (Numerics.RadixText.carry 10 ⟨f.precision, f.precision_pos⟩ c q).2) :
    ((f.coefficientBound - 1 : Nat) : K) * (10 : K) ^ f.maxQuantum < y * (10 : K) ^ q := by
  have hb : 1 ≤ f.coefficientBound := f.coefficientBound_pos
  have hcast : ((f.coefficientBound - 1 : Nat) : K) = (f.coefficientBound : K) - 1 := by
    rw [Nat.cast_sub hb, Nat.cast_one]
  rw [f.carry_eq] at h
  split_ifs at h with hcb
  · have hq : f.maxQuantum ≤ q := by simp only at h; omega
    have hy : (f.coefficientBound : K) - 1 < y := by
      rw [← hcb]
      linarith [(abs_lt.mp hc).2]
    rw [hcast]
    calc ((f.coefficientBound : K) - 1) * (10 : K) ^ f.maxQuantum
        ≤ ((f.coefficientBound : K) - 1) * (10 : K) ^ q :=
          mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hq)
            (by rw [← hcast]; exact Nat.cast_nonneg _)
      _ < y * (10 : K) ^ q := mul_lt_mul_of_pos_right hy (zpow_pos (by norm_num) _)
  · have hq : f.maxQuantum < q := h
    have hy := hfull (lt_of_le_of_lt f.minQuantum_le_maxQuantum hq)
    have hpos : (0 : K) < (10 : K) ^ f.maxQuantum := zpow_pos (by norm_num) _
    calc ((f.coefficientBound - 1 : Nat) : K) * (10 : K) ^ f.maxQuantum
        < (f.coefficientBound : K) * (10 : K) ^ f.maxQuantum := by
          rw [hcast]
          exact mul_lt_mul_of_pos_right (by linarith) hpos
      _ = (f.payloadBound : K) * (10 : K) ^ (f.maxQuantum + 1) := by
          rw [zpow_add_one₀ (by norm_num), Format.coefficientBound, Nat.cast_mul]
          push_cast
          ring
      _ ≤ (f.payloadBound : K) * (10 : K) ^ q :=
          mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) (by omega))
            (Nat.cast_nonneg _)
      _ ≤ y * (10 : K) ^ q := mul_le_mul_of_nonneg_right hy (zpow_pos (by norm_num) _).le

/-- An overflowing projection of a nonnegative magnitude starts strictly above the greatest finite
magnitude. -/
theorem maxFinite_lt_of_roundedPair_overflow (f : Format) (mode : RoundingMode) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (h : f.maxQuantum < (roundedPair f mode s x).2) :
    ((f.coefficientBound - 1 : Nat) : ℚ) * (10 : ℚ) ^ f.maxQuantum < x := by
  have hu : 0 < (10 : ℚ) ^ roundingQuantum f x := zpow_pos (by norm_num) _
  have hlt := f.maxFinite_lt_of_carry_overflow (mode.roundAt s x (roundingQuantum f x))
    (roundingQuantum f x) (x / (10 : ℚ) ^ roundingQuantum f x)
    (mode.roundMagnitude_error_lt_one s (div_nonneg hx hu.le))
    (payloadBound_le_div_roundingQuantum f) h
  rwa [div_mul_cancel₀ _ hu.ne'] at hlt

/-- Every rational projection produces a valid datum, including underflow and overflow. -/
theorem projectMagnitude_valid (f : Format) (mode : RoundingMode) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (preferred : Int) :
    (projectMagnitude f mode s x preferred).value.Valid f := by
  simp only [projectMagnitude_eq]
  split
  · split
    · trivial
    · exact f.maxFinite_valid s
  · rename_i hq
    have hv : (Datum.finite s (roundedPair f mode s x).1
        (roundedPair f mode s x).2).Valid f :=
      (Datum.valid_quantum_iff ..).mpr ⟨roundedPair_coefficient_lt f mode s hx,
        roundedPair_quantum_ge_min f mode s x, le_of_not_gt hq⟩
    split
    · exact hv
    · exact preferredCohort_valid f s _ _ _ hv

/-- The signed public entry point is valid for every rational input. -/
theorem project_valid (f : Format) (mode : RoundingMode) (x : ℚ)
    (preferred : Int) (negativeZero : Bool) :
    (project f mode x preferred negativeZero).value.Valid f :=
  projectMagnitude_valid f mode _ (abs_nonneg x) preferred

/-- On the finite path, the datum denotes the rounded coefficient-grid value. -/
theorem projectMagnitude_value (f : Format) (mode : RoundingMode) (s : Bool)
    (x : ℚ) (preferred : Int)
    (hq : (roundedPair f mode s x).2 ≤ f.maxQuantum) :
    (projectMagnitude f mode s x preferred).value.toRat? =
      some ((if s then -1 else 1) * (mode.roundAt s x (roundingQuantum f x) : ℚ) *
        (10 : ℚ) ^ roundingQuantum f x) := by
  simp only [projectMagnitude_eq, ite_eq_right (not_lt.mpr hq)]
  have hv := roundedPair_value f mode s x
  split
  · simp only [Datum.toRat?_eq, mul_assoc, hv]
  · rw [preferredCohort_toRat?]
    simp only [mul_assoc, hv]

/-- The finite result has at most half a decimal grid unit of error in either nearest mode. -/
theorem projectMagnitude_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearest ∨ mode = .nearestAway) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hq : (roundedPair f mode s x).2 ≤ f.maxQuantum) :
    ∃ value, (projectMagnitude f mode s x preferred).value.toRat? = some value ∧
      |value - (if s then -x else x)| ≤ (10 : ℚ) ^ roundingQuantum f x / 2 := by
  refine ⟨_, projectMagnitude_value f mode s x preferred hq, ?_⟩
  have h := mode.roundAt_error_le_half hm s hx (roundingQuantum f x)
  cases s <;> simpa [neg_add_eq_sub, abs_sub_comm] using h

end FloatLib.Floats.Formats.DecimalInterchange
