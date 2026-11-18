/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Classification

/-!
# P3109 classification and adjacency facts

For positive finite codes, code order is numerical order. From that we get the least positive
value, the boundary between subnormal and normal values, and the fact that nothing representable
lies between consecutive magnitude codes, for every valid descriptor, precision one included.

Two imported facets do most of the work. The classification facet connects all eight value
queries to exact decoding and order, and the neighbor facet proves immediate adjacency and the
absence of a neighbor at either endpoint, infinite endpoints included. What this file adds is the
positive magnitude boundary and the split of finite values into normal and subnormal cases.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§3.1, 4.13 and 4.16.
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

/-- A positive finite code denotes a value at or above the first normal value if and only if it is a
normal magnitude code. -/
theorem minNormal_le_decodePositiveFinite_iff (format : Format) (bits : Nat) :
    (format.decodePositiveFinite (2 ^ format.trailingBits)).toRat ≤
      (format.decodePositiveFinite bits).toRat ↔ 2 ^ format.trailingBits ≤ bits :=
  format.decodePositiveFinite_strictMono.le_iff_le

/-- A positive code is subnormal if and only if it denotes a nonzero value below the first normal
value. -/
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
  simp only [trailingBits, hprecision, tsub_self, pow_zero, Order.lt_one_iff, not_and]
  omega

/-- The maximum-subnormal query returns the single NaN at precision one. -/
theorem maxSubnormalOf_eq_nan (format : Format) (hprecision : format.precision = 1) :
    format.MaxSubnormalOf = ExecFloat.P3109.nan := by
  simp [MaxSubnormalOf, hprecision]

end FloatLib.Floats.Formats.P3109.Format

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {format : Format}

/-- A normal value is finite. -/
theorem isFinite_of_isNormal (value : ExecFloat.P3109 format)
    (h : value.IsNormal = true) : value.IsFinite = true := by
  simp only [IsNormal, Bool.and_eq_true] at h
  exact h.1

/-- A subnormal value is finite. -/
theorem isFinite_of_isSubnormal (value : ExecFloat.P3109 format)
    (h : value.IsSubnormal = true) : value.IsFinite = true := by
  simp only [IsSubnormal, Bool.and_eq_true] at h
  exact h.1.1

/-- Normal and subnormal classifications are disjoint. -/
theorem not_isNormal_and_isSubnormal (value : ExecFloat.P3109 format) :
    ¬ (value.IsNormal = true ∧ value.IsSubnormal = true) := by
  simp only [IsNormal, IsSubnormal, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- Every nonzero finite magnitude code is classified as either normal or subnormal. -/
theorem isNormal_or_isSubnormal (value : ExecFloat.P3109 format)
    (hfinite : value.IsFinite = true) (hpositive : 0 < value.magnitudeBits) :
    value.IsNormal = true ∨ value.IsSubnormal = true := by
  simp only [IsNormal, IsSubnormal, hfinite, Bool.true_and, decide_eq_true_eq,
    Bool.and_eq_true]
  omega

/-- Precision-one formats classify no value as subnormal. -/
theorem isSubnormal_eq_false_of_precision_eq_one (value : ExecFloat.P3109 format)
    (hprecision : format.precision = 1) : value.IsSubnormal = false := by
  simp only [IsSubnormal, Format.trailingBits, hprecision, tsub_self, pow_zero, Order.lt_one_iff,
    Bool.and_eq_false_imp, Bool.and_eq_true, decide_eq_true_eq, decide_eq_false_iff_not, and_imp]
  omega

/-- The upper neighbor of NaN is NaN. -/
theorem nextGreaterThan_of_isNaN (value : ExecFloat.P3109 format)
    (h : value.IsNaN = true) : value.NextGreaterThan = nan := by
  simp [NextGreaterThan, h]

/-- The lower neighbor of NaN is NaN. -/
theorem nextLessThan_of_isNaN (value : ExecFloat.P3109 format)
    (h : value.IsNaN = true) : value.NextLessThan = nan := by
  simp [NextLessThan, h]

/-- Interior nonnegative codes advance by one under the upper-neighbor operation. -/
theorem nextGreaterThan_of_nonnegative (value : ExecFloat.P3109 format)
    (hnan : value.IsNaN = false) (hsign : value.IsSignMinus = false)
    (hend : value.toNatBits ≠ format.positiveInfinityBits) :
    value.NextGreaterThan = ofNatBits (value.toNatBits + 1) := by
  simp [NextGreaterThan, hnan, hsign, hend]

/-- Positive codes descend by one under the lower-neighbor operation. -/
theorem nextLessThan_of_positive (value : ExecFloat.P3109 format)
    (hnan : value.IsNaN = false) (hzero : value.IsZero = false)
    (hsign : value.IsSignMinus = false) :
    value.NextLessThan = ofNatBits (value.toNatBits - 1) := by
  simp [NextLessThan, hnan, hzero, hsign]

end FloatLib.Floats.ExecFloat.P3109
