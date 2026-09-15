/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Direction
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Zero

/-!
# Integer-to-decimal numerical contracts

Integer sources are converted from their exact value, with preferred quantum
zero. Every integer representable in the destination remains exact, including
integers whose decimal representation requires a positive exponent. Other
nonoverflowing results satisfy the decimal grid's error and direction bounds.

Custom descriptors may exclude quantum zero. Zero then takes the nearest
allowed quantum, and a coarse minimum quantum can make a nonzero integer
underflow. The standard presets satisfy the optional `HasQuantumZero` assumption.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer

theorem convertFromInt_valid (destination : Format) (mode : RoundingMode) (source : Int) :
    (convertFromInt destination mode source).value.Valid destination :=
  project_valid destination mode (source : ℚ) 0 false

/-- Integer zero is exact and positive, with its preferred exponent clamped to the
destination interval. This includes custom descriptors that exclude quantum zero. -/
theorem convertFromInt_zero_clamped (destination : Format) (mode : RoundingMode) :
    convertFromInt destination mode 0 =
      { value := .finite false 0
          (max destination.minQuantum (min 0 destination.maxQuantum)) } := by
  simpa [convertFromInt] using project_zero destination mode false 0

/-- When quantum zero is available, integer zero keeps that exponent and raises no flags. -/
@[simp] theorem convertFromInt_zero (destination : Format) [destination.HasQuantumZero]
    (mode : RoundingMode) :
    convertFromInt destination mode 0 = { value := .finite false 0 0 } := by
  rw [convertFromInt_zero_clamped, min_eq_left destination.maxQuantum_nonneg,
    max_eq_right destination.minQuantum_nonpos]

private theorem magnitude_of_integer_representation (source : Int) (s : Bool)
    (c : Nat) (q : Int) (hs : (Datum.finite s c q).toRat? = some (source : ℚ)) :
    |(source : ℚ)| = (c : ℚ) * (10 : ℚ) ^ q := by
  simp only [Datum.toRat?_eq] at hs
  have hm : 0 ≤ (c : ℚ) * (10 : ℚ) ^ q :=
    mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num) _).le
  have he := congrArg abs (Option.some.inj hs)
  cases s <;> simpa [abs_mul, abs_of_nonneg hm] using he.symm

/-- Representability suffices for exact conversion; no coefficient-size restriction is
imposed on the integer itself. Changing its cohort does not raise an exception. -/
theorem convertFromInt_exact (destination : Format) (mode : RoundingMode) (source : Int)
    (s : Bool) (c : Nat) (q : Int) (hvalid : (Datum.finite s c q).Valid destination)
    (hs : (Datum.finite s c q).toRat? = some (source : ℚ)) :
    (convertFromInt destination mode source).value.toRat? = some (source : ℚ) ∧
      (convertFromInt destination mode source).status = {} := by
  let negative := if (source : ℚ) = 0 then false else decide ((source : ℚ) < 0)
  have hmag := magnitude_of_integer_representation source s c q hs
  have hv : (Datum.finite negative c q).Valid destination := by
    simpa only [Datum.valid_quantum_iff] using hvalid
  change (projectMagnitude destination mode negative |(source : ℚ)| 0).value.toRat? =
      some (source : ℚ) ∧
    (projectMagnitude destination mode negative |(source : ℚ)| 0).status = {}
  rw [hmag]
  constructor
  · rw [projectMagnitude_exact destination mode negative c q 0 hv]
    have hn := signed_abs (source : ℚ) false
    change (if negative then -|(source : ℚ)| else |(source : ℚ)|) = (source : ℚ) at hn
    rw [hmag] at hn
    simp only [Datum.toRat?_eq]
    congr 1
    cases he : negative <;> simpa [he, mul_assoc] using hn
  · exact projectMagnitude_exact_status destination mode negative c q 0 hv

/-- A nearest conversion incurs at most half a unit on the selected decimal grid. -/
theorem convertFromInt_error_le_half (destination : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway) (source : Int)
    (hfinite : (convertFromInt destination mode source).status.overflow = false) :
    ∃ value, (convertFromInt destination mode source).value.toRat? = some value ∧
      |value - (source : ℚ)| ≤ (10 : ℚ) ^ roundingQuantum destination |(source : ℚ)| / 2 :=
  project_error_le_half destination mode hm (source : ℚ) 0 false hfinite

theorem convertFromInt_error_lt_one (destination : Format) (mode : RoundingMode)
    (source : Int)
    (hfinite : (convertFromInt destination mode source).status.overflow = false) :
    ∃ value, (convertFromInt destination mode source).value.toRat? = some value ∧
      |value - (source : ℚ)| < (10 : ℚ) ^ roundingQuantum destination |(source : ℚ)| :=
  project_error_lt_one destination mode (source : ℚ) 0 false hfinite

theorem le_convertFromInt_towardPositive (destination : Format) (source : Int)
    (hfinite : (convertFromInt destination .towardPositive source).status.overflow = false) :
    ∃ value, (convertFromInt destination .towardPositive source).value.toRat? = some value ∧
      (source : ℚ) ≤ value :=
  le_project_towardPositive destination (source : ℚ) 0 false hfinite

theorem convertFromInt_towardNegative_le (destination : Format) (source : Int)
    (hfinite : (convertFromInt destination .towardNegative source).status.overflow = false) :
    ∃ value, (convertFromInt destination .towardNegative source).value.toRat? = some value ∧
      value ≤ (source : ℚ) :=
  project_towardNegative_le destination (source : ℚ) 0 false hfinite

theorem abs_convertFromInt_towardZero_le (destination : Format) (source : Int)
    (hfinite : (convertFromInt destination .towardZero source).status.overflow = false) :
    ∃ value, (convertFromInt destination .towardZero source).value.toRat? = some value ∧
      |value| ≤ |(source : ℚ)| :=
  abs_project_towardZero_le destination (source : ℚ) 0 false hfinite

/-- Inexact reports a numerical change, never a change of exponent alone. -/
theorem convertFromInt_inexact_iff (destination : Format) (mode : RoundingMode)
    (source : Int) (value : ℚ)
    (hfinite : (convertFromInt destination mode source).status.overflow = false)
    (hv : (convertFromInt destination mode source).value.toRat? = some value) :
    (convertFromInt destination mode source).status.inexact = true ↔ value ≠ (source : ℚ) :=
  project_inexact_iff destination mode (source : ℚ) value 0 false hfinite hv

/-- For an arbitrary descriptor, underflow means a tiny exact integer input together
with a numerical change. Coarse custom formats can therefore underflow on integers. -/
theorem convertFromInt_underflow_iff (destination : Format) (mode : RoundingMode)
    (source : Int) (value : ℚ)
    (hfinite : (convertFromInt destination mode source).status.overflow = false)
    (hv : (convertFromInt destination mode source).value.toRat? = some value) :
    (convertFromInt destination mode source).status.underflow = true ↔
      |(source : ℚ)| < destination.minNormal ∧ value ≠ (source : ℚ) := by
  rw [show (convertFromInt destination mode source).status.underflow = true ↔
      |(source : ℚ)| < destination.minNormal ∧
        (convertFromInt destination mode source).status.inexact = true from
    project_underflow_iff destination mode (source : ℚ) 0 false hfinite,
    convertFromInt_inexact_iff destination mode source value hfinite hv]

private theorem minNormal_le_coefficientBound (destination : Format)
    [destination.HasQuantumZero] :
    destination.minNormal ≤ (destination.coefficientBound : ℚ) := by
  have he : (10 : ℚ) ^ destination.minQuantum ≤ 1 := by
    simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 10)
      destination.minQuantum_nonpos
  calc
    _ ≤ (10 : ℚ) ^ (destination.precision - 1) :=
      mul_le_of_le_one_right (by positivity) he
    _ ≤ (10 : ℚ) ^ destination.precision :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    _ = (destination.coefficientBound : ℚ) := by
      rw [Format.coefficientBound_eq]
      norm_cast

/-- When quantum zero is available, integer sources cannot underflow: every integer
below the normal range is exactly representable as an integer coefficient. Larger
integers are not tiny. The least normal value need not be at most one. -/
@[simp] theorem convertFromInt_underflow (destination : Format) [destination.HasQuantumZero]
    (mode : RoundingMode) (source : Int) :
    (convertFromInt destination mode source).status.underflow = false := by
  by_cases htiny : |(source : ℚ)| < destination.minNormal
  · have hc : source.natAbs < destination.coefficientBound := by
      have h := htiny.trans_le (minNormal_le_coefficientBound destination)
      rw [← Nat.cast_lt (α := Int), Int.natCast_natAbs]
      exact_mod_cast h
    have hv : (Datum.finite (decide (source < 0)) source.natAbs 0).Valid destination :=
      (Datum.valid_quantum_iff ..).mpr
        ⟨hc, destination.minQuantum_nonpos, destination.maxQuantum_nonneg⟩
    have hs : (Datum.finite (decide (source < 0)) source.natAbs 0).toRat? =
        some (source : ℚ) := by
      cases source <;> simp [Datum.toRat?_eq]
    have he := (convertFromInt_exact destination mode source _ _ _ hv hs).2
    rw [he]
  · simp only [convertFromInt, project, projectMagnitude_eq, htiny, decide_false, Bool.false_and]
    split_ifs <;> rfl

end FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer
