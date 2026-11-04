/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Binary.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Format.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Classification
import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics

/-!
# Binary-to-decimal conversion guarantees

Converting a finite binary value to decimal is one exact rational projection. We decode the binary
input to a rational and project that onto the decimal format, so the proofs here carry the
projection's error bounds, directed inequalities, and exception conditions over to the returned
datum. The binary storage width and the choice of decimal encoding never enter the numerical
argument.
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
  simp [fromBinary, Model.toRat?, Model.toDyadic?_eq_none_of_isInf_eq_true hx,
    Model.isNaN_eq_false_of_isInf_eq_true x hx]

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
    (hm : mode = .nearest ∨ mode = .nearestAway)
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
theorem le_fromBinary_up {fmt : FloatFormat} (f : Format)
    (x : Model fmt) (a : ℚ) (hx : Model.toRat? x = some a)
    (hfinite : (fromBinary f .up x).status.overflow = false) :
    ∃ value, (fromBinary f .up x).value.toRat? = some value ∧ a ≤ value := by
  rw [fromBinary_eq_project f .up x a hx] at hfinite ⊢
  exact le_project_up f a 0 _ hfinite

/-- Downward conversion bounds the exact binary input from below. -/
theorem fromBinary_down_le {fmt : FloatFormat} (f : Format)
    (x : Model fmt) (a : ℚ) (hx : Model.toRat? x = some a)
    (hfinite : (fromBinary f .down x).status.overflow = false) :
    ∃ value, (fromBinary f .down x).value.toRat? = some value ∧ value ≤ a := by
  rw [fromBinary_eq_project f .down x a hx] at hfinite ⊢
  exact project_down_le f a 0 _ hfinite

/-- A cohort change is not inexact. The flag is raised if and only if a finite result changes
numerically, including an overflow to the greatest finite datum. -/
theorem fromBinary_inexact_iff {fmt : FloatFormat} (f : Format) (mode : RoundingMode)
    (x : Model fmt) (a value : ℚ) (hx : Model.toRat? x = some a)
    (hv : (fromBinary f mode x).value.toRat? = some value) :
    (fromBinary f mode x).status.inexact = true ↔ value ≠ a := by
  rw [fromBinary_eq_project f mode x a hx] at hv ⊢
  exact project_inexact_iff f mode a value 0 _ hv

/-- Decimal conversion of a finite binary value signals underflow if and only if the input is tiny
and the result inexact. An overflowing input is never tiny. -/
theorem fromBinary_underflow_iff {fmt : FloatFormat} (f : Format) (mode : RoundingMode)
    (x : Model fmt) (a : ℚ) (hx : Model.toRat? x = some a) :
    (fromBinary f mode x).status.underflow = true ↔
      |a| < f.minNormal ∧ (fromBinary f mode x).status.inexact = true := by
  rw [fromBinary_eq_project f mode x a hx]
  exact project_underflow_iff f mode a 0 _

end FloatLib.Floats.Formats.DecimalInterchange.Conversion
