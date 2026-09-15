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

The precision rounder can produce at most one carry. Carry normalization and
preferred-cohort selection preserve its exact value. Every result, including a
directed overflow result, is representable in its destination format.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

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

theorem roundAt_le_coefficientBound (f : Format) (mode : RoundingMode) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) :
    mode.roundAt s x (roundingQuantum f x) ≤ f.coefficientBound := by
  have hu : 0 < (10 : ℚ) ^ roundingQuantum f x := zpow_pos (by norm_num) _
  have hf := (Nat.floor_lt (div_nonneg hx hu.le)).mpr (div_roundingQuantum_lt f hx)
  exact (mode.roundMagnitude_le_floor_add_one s _).trans (by omega)

theorem roundedPair_coefficient_lt (f : Format) (mode : RoundingMode) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) :
    (roundedPair f mode s x).1 < f.coefficientBound := by
  exact f.carry_coefficient_lt (roundAt_le_coefficientBound f mode s hx) _

theorem roundedPair_quantum_ge_min (f : Format) (mode : RoundingMode) (s : Bool) (x : ℚ) :
    f.minQuantum ≤ (roundedPair f mode s x).2 := by
  exact (roundingQuantum_ge_min f x).trans (f.le_carry_quantum _ _)

/-- Carry normalization preserves the computed value exactly. -/
theorem roundedPair_value (f : Format) (mode : RoundingMode) (s : Bool) (x : ℚ) :
    ((roundedPair f mode s x).1 : ℚ) * (10 : ℚ) ^ (roundedPair f mode s x).2 =
      (mode.roundAt s x (roundingQuantum f x) : ℚ) *
        (10 : ℚ) ^ roundingQuantum f x := by
  exact Numerics.RadixText.carry_value 10 (by decide) _ _ _

theorem Format.maxFinite_valid (f : Format) (s : Bool) : (f.maxFinite s).Valid f := by
  rw [Format.maxFinite, Datum.valid_quantum_iff]
  have hb := f.coefficientBound_pos
  have hq := f.minQuantum_le_maxQuantum
  exact ⟨by omega, hq, le_rfl⟩

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

/-- On the finite path, the datum denotes exactly the rounded coefficient-grid value. -/
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
    (hm : mode = .nearestEven ∨ mode = .nearestAway) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hq : (roundedPair f mode s x).2 ≤ f.maxQuantum) :
    ∃ value, (projectMagnitude f mode s x preferred).value.toRat? = some value ∧
      |value - (if s then -x else x)| ≤ (10 : ℚ) ^ roundingQuantum f x / 2 := by
  refine ⟨_, projectMagnitude_value f mode s x preferred hq, ?_⟩
  have h := mode.roundAt_error_le_half hm s hx (roundingQuantum f x)
  cases s <;> simpa [neg_add_eq_sub, abs_sub_comm] using h

end FloatLib.Floats.Formats.DecimalInterchange
