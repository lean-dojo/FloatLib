/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Binary.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Format.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Classification

/-!
# Binary-to-decimal conversion guarantees

Finite decoding feeds one exact rational projection. The proofs transfer its
error bounds, directed inequalities and exception conditions to the returned
decimal datum. Neither the binary storage width nor the decimal encoding
choice occurs in the numerical argument.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion

open FloatLib.Floats.Formats.BinaryInterchange

/-- A successfully decoded binary value is projected once, with preferred quantum zero. -/
theorem fromBinary_eq_project {fmt : FloatFormat} (f : Format) (mode : RoundingMode)
    (x : Model fmt) (a : ℚ) (hx : Model.toRat? x = some a) :
    fromBinary f mode x = project f mode a 0 (Model.signBit x) := by
  simp [fromBinary, hx]

/-- Binary conversion always returns a valid destination datum. -/
theorem fromBinary_valid {fmt : FloatFormat} (f : Format) (mode : RoundingMode)
    (x : Model fmt) : (fromBinary f mode x).value.Valid f := by
  simp only [fromBinary]
  split
  · exact project_valid ..
  · split
    · exact Arithmetic.nanResult_valid ..
    · trivial

/-- A source NaN is quieted, preserves a fitting diagnostic payload, and reports signaling. -/
theorem fromBinary_nan {fmt : FloatFormat} (f : Format) (mode : RoundingMode)
    (x : Model fmt) (hx : Model.isNaN x = true) :
    fromBinary f mode x =
      { value := .nan (Model.signBit x) false
          (if binaryPayload x < f.payloadBound then binaryPayload x else 0)
        status := { invalid := Model.isSNaN x } } := by
  have hd := Model.toDyadic?_eq_none_of_isNaN hx
  simp [fromBinary, Model.toRat?, hd, hx, Arithmetic.nanResult]

/-- An infinite source retains its sign and raises no exception. -/
theorem fromBinary_infinity {fmt : FloatFormat} (f : Format) (mode : RoundingMode)
    (x : Model fmt) (hx : Model.isInf x = true) :
    fromBinary f mode x = { value := .infinity (Model.signBit x) } := by
  have hd : Model.toDyadic? x = none := by
    cases h : Model.toDyadic? x with
    | none => rfl
    | some d =>
        have hn := Model.isInf_eq_false_of_toDyadic?_some h
        simp [hx] at hn
  have hn : Model.isNaN x = false := by
    cases he : fmt.encoding <;> simp [Model.isInf, he] at hx
    simp only [Model.isNaN, he, Model.IEEE.isNaN]
    simp [Model.IEEE.isInf] at hx
    simp [hx.2]
  simp [fromBinary, Model.toRat?, hd, hn]

/-- Both binary zeros retain their sign, with preferred quantum zero clamped to
the destination quantum range. -/
theorem fromBinary_zero_clamped {fmt : FloatFormat} (f : Format) (mode : RoundingMode)
    (x : Model fmt) (hx : Model.isZero x = true) :
    fromBinary f mode x =
      { value := .finite (Model.signBit x) 0 (max f.minQuantum (min 0 f.maxQuantum)) } := by
  have hd := Model.toDyadic?_eq_zero_of_isZero_eq_true x hx
  have hr : Model.toRat? x = some 0 := by
    simp [Model.toRat?, hd, FloatLib.Numerics.Dyadic.toRat,
      FloatLib.Numerics.Dyadic.signedSignificand]
  rw [fromBinary_eq_project f mode x 0 hr, project_zero]

/-- When quantum zero is available, both binary zeros convert to it with the same sign. -/
theorem fromBinary_zero {fmt : FloatFormat} (f : Format) [f.HasQuantumZero]
    (mode : RoundingMode) (x : Model fmt) (hx : Model.isZero x = true) :
    fromBinary f mode x = { value := .finite (Model.signBit x) 0 0 } := by
  rw [fromBinary_zero_clamped f mode x hx]
  simp [min_eq_left f.maxQuantum_nonneg, max_eq_right f.minQuantum_nonpos]

/-- Both nearest conversions bound the error of the returned decimal value by half a grid unit. -/
theorem fromBinary_error_le_half {fmt : FloatFormat} (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (x : Model fmt) (a : ℚ) (hx : Model.toRat? x = some a)
    (hfinite : (fromBinary f mode x).status.overflow = false) :
    ∃ value, (fromBinary f mode x).value.toRat? = some value ∧
      |value - a| ≤ (10 : ℚ) ^ roundingQuantum f |a| / 2 := by
  rw [fromBinary_eq_project f mode x a hx] at hfinite ⊢
  exact project_error_le_half f mode hm a 0 _ hfinite

/-- All five conversion directions have less than one grid unit of nonoverflowing error. -/
theorem fromBinary_error_lt_one {fmt : FloatFormat} (f : Format) (mode : RoundingMode)
    (x : Model fmt) (a : ℚ) (hx : Model.toRat? x = some a)
    (hfinite : (fromBinary f mode x).status.overflow = false) :
    ∃ value, (fromBinary f mode x).value.toRat? = some value ∧
      |value - a| < (10 : ℚ) ^ roundingQuantum f |a| := by
  rw [fromBinary_eq_project f mode x a hx] at hfinite ⊢
  exact project_error_lt_one f mode a 0 _ hfinite

/-- Upward conversion bounds the exact binary input from above. -/
theorem le_fromBinary_towardPositive {fmt : FloatFormat} (f : Format)
    (x : Model fmt) (a : ℚ) (hx : Model.toRat? x = some a)
    (hfinite : (fromBinary f .towardPositive x).status.overflow = false) :
    ∃ value, (fromBinary f .towardPositive x).value.toRat? = some value ∧ a ≤ value := by
  rw [fromBinary_eq_project f .towardPositive x a hx] at hfinite ⊢
  exact le_project_towardPositive f a 0 _ hfinite

/-- Downward conversion bounds the exact binary input from below. -/
theorem fromBinary_towardNegative_le {fmt : FloatFormat} (f : Format)
    (x : Model fmt) (a : ℚ) (hx : Model.toRat? x = some a)
    (hfinite : (fromBinary f .towardNegative x).status.overflow = false) :
    ∃ value, (fromBinary f .towardNegative x).value.toRat? = some value ∧ value ≤ a := by
  rw [fromBinary_eq_project f .towardNegative x a hx] at hfinite ⊢
  exact project_towardNegative_le f a 0 _ hfinite

/-- A cohort change is not inexact; inexactness detects precisely a numerical change. -/
theorem fromBinary_inexact_iff {fmt : FloatFormat} (f : Format) (mode : RoundingMode)
    (x : Model fmt) (a value : ℚ) (hx : Model.toRat? x = some a)
    (hfinite : (fromBinary f mode x).status.overflow = false)
    (hv : (fromBinary f mode x).value.toRat? = some value) :
    (fromBinary f mode x).status.inexact = true ↔ value ≠ a := by
  rw [fromBinary_eq_project f mode x a hx] at hfinite hv ⊢
  exact project_inexact_iff f mode a value 0 _ hfinite hv

/-- Decimal conversion signals underflow precisely for an inexact tiny input. -/
theorem fromBinary_underflow_iff {fmt : FloatFormat} (f : Format) (mode : RoundingMode)
    (x : Model fmt) (a : ℚ) (hx : Model.toRat? x = some a)
    (hfinite : (fromBinary f mode x).status.overflow = false) :
    (fromBinary f mode x).status.underflow = true ↔
      |a| < f.minNormal ∧ (fromBinary f mode x).status.inexact = true := by
  rw [fromBinary_eq_project f mode x a hx] at hfinite ⊢
  exact project_underflow_iff f mode a 0 _ hfinite

end FloatLib.Floats.Formats.DecimalInterchange.Conversion
