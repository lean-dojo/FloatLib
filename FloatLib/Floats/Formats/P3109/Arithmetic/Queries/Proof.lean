/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Classification

/-!
# P3109 classification and adjacency facts

Positive finite code order is exact numerical order. It identifies the least positive value,
the normal/subnormal boundary, and the absence of a representable value between consecutive
magnitude codes. These facts apply to arbitrary valid descriptors, including precision one.
The imported classification facet connects all eight value queries to exact decoding and order.
The neighbor facet proves immediate adjacency and the absence of a neighbor at either endpoint,
including infinite endpoints. The additional facts here expose the positive magnitude boundary
and partition finite values into normal and subnormal cases.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Format

/-- A positive magnitude code denotes a strictly positive rational, and code zero denotes zero. -/
theorem decodePositiveFinite_toRat_pos_iff (format : Format) (bits : Nat) :
    0 < (format.decodePositiveFinite bits).toRat ↔ 0 < bits := by
  simpa using format.decodePositiveFinite_strictMono.lt_iff_lt (a := 0) (b := bits)

/-- Code one is no larger than any strictly positive finite magnitude code. -/
theorem minPositive_le_decodePositiveFinite (format : Format) (bits : Nat) (hbits : 0 < bits) :
    (format.decodePositiveFinite 1).toRat ≤ (format.decodePositiveFinite bits).toRat :=
  format.decodePositiveFinite_strictMono.monotone hbits

/-- Normal magnitude codes denote precisely values at or above the first normal value. -/
theorem minNormal_le_decodePositiveFinite_iff (format : Format) (bits : Nat) :
    (format.decodePositiveFinite (2 ^ format.trailingBits)).toRat ≤
      (format.decodePositiveFinite bits).toRat ↔ 2 ^ format.trailingBits ≤ bits :=
  format.decodePositiveFinite_strictMono.le_iff_le

/-- Subnormal positive codes denote precisely nonzero values below the first normal value. -/
theorem decodePositiveFinite_subnormal_iff (format : Format) (bits : Nat) :
    (0 < (format.decodePositiveFinite bits).toRat ∧
      (format.decodePositiveFinite bits).toRat <
        (format.decodePositiveFinite (2 ^ format.trailingBits)).toRat) ↔
      0 < bits ∧ bits < 2 ^ format.trailingBits := by
  rw [decodePositiveFinite_toRat_pos_iff, format.decodePositiveFinite_strictMono.lt_iff_lt]

/-- No finite positive magnitude code lies numerically between consecutive codes. -/
theorem no_decodePositiveFinite_between (format : Format) (bits candidate : Nat) :
    ¬ ((format.decodePositiveFinite bits).toRat <
        (format.decodePositiveFinite candidate).toRat ∧
      (format.decodePositiveFinite candidate).toRat <
        (format.decodePositiveFinite (bits + 1)).toRat) := by
  rw [format.decodePositiveFinite_strictMono.lt_iff_lt,
    format.decodePositiveFinite_strictMono.lt_iff_lt]
  omega

/-- Precision one leaves no strictly positive subnormal magnitude code. -/
theorem no_subnormal_of_precision_eq_one (format : Format) (hprecision : format.precision = 1)
    (bits : Nat) :
    ¬ (0 < bits ∧ bits < 2 ^ format.trailingBits) := by
  simp [trailingBits, hprecision]
  omega

/-- The maximum-subnormal query returns the single NaN at precision one. -/
theorem maxSubnormalOf_eq_nan (format : Format) (hprecision : format.precision = 1) :
    format.maxSubnormalOf = ExecFloat.P3109.nan := by
  simp [maxSubnormalOf, hprecision]

end FloatLib.Floats.Formats.P3109.Format

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {format : Format}

/-- A normal value is finite. -/
theorem isFinite_of_isNormal (value : ExecFloat.P3109 format)
    (h : value.isNormal = true) : value.isFinite = true := by
  simp only [isNormal, Bool.and_eq_true] at h
  exact h.1

/-- A subnormal value is finite. -/
theorem isFinite_of_isSubnormal (value : ExecFloat.P3109 format)
    (h : value.isSubnormal = true) : value.isFinite = true := by
  simp only [isSubnormal, Bool.and_eq_true] at h
  exact h.1.1

/-- Normal and subnormal classifications are disjoint. -/
theorem not_isNormal_and_isSubnormal (value : ExecFloat.P3109 format) :
    ¬ (value.isNormal = true ∧ value.isSubnormal = true) := by
  simp only [isNormal, isSubnormal, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- Every nonzero finite magnitude code is classified as either normal or subnormal. -/
theorem isNormal_or_isSubnormal (value : ExecFloat.P3109 format)
    (hfinite : value.isFinite = true) (hpositive : 0 < value.magnitudeBits) :
    value.isNormal = true ∨ value.isSubnormal = true := by
  simp only [isNormal, isSubnormal, hfinite, Bool.true_and, decide_eq_true_eq,
    Bool.and_eq_true]
  omega

/-- Precision-one formats classify no value as subnormal. -/
theorem isSubnormal_eq_false_of_precision_eq_one (value : ExecFloat.P3109 format)
    (hprecision : format.precision = 1) : value.isSubnormal = false := by
  simp [isSubnormal, Format.trailingBits, hprecision]
  omega

/-- The upper neighbor of NaN is NaN. -/
theorem nextGreaterThan_of_isNaN (value : ExecFloat.P3109 format)
    (h : value.isNaN = true) : value.nextGreaterThan = nan := by
  simp [nextGreaterThan, h]

/-- The lower neighbor of NaN is NaN. -/
theorem nextLessThan_of_isNaN (value : ExecFloat.P3109 format)
    (h : value.isNaN = true) : value.nextLessThan = nan := by
  simp [nextLessThan, h]

/-- Interior nonnegative codes advance by one under the upper-neighbor operation. -/
theorem nextGreaterThan_of_nonnegative (value : ExecFloat.P3109 format)
    (hnan : value.isNaN = false) (hsign : value.isSignMinus = false)
    (hend : value.toNatBits ≠ format.positiveInfinityBits) :
    value.nextGreaterThan = ofNatBits (value.toNatBits + 1) := by
  simp [nextGreaterThan, hnan, hsign, hend]

/-- Positive codes descend by one under the lower-neighbor operation. -/
theorem nextLessThan_of_positive (value : ExecFloat.P3109 format)
    (hnan : value.isNaN = false) (hzero : value.isZero = false)
    (hsign : value.isSignMinus = false) :
    value.nextLessThan = ofNatBits (value.toNatBits - 1) := by
  simp [nextLessThan, hnan, hzero, hsign]

end FloatLib.Floats.ExecFloat.P3109
