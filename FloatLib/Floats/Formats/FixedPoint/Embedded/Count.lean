/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Operations
public import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int

/-!
# N1169's count of nonoverflowing left shifts

WG14 N1169 (2006 TR 18037 draft), C clauses 7.18a.6.4 defines `countlsfx` by a greatest
shift, rather than by a particular word instruction. The finite search uses Mathlib's
`Nat.findGreatest`. The global maximality proof establishes that a nonzero coefficient
cannot survive a shift greater than the number of value bits. Zero returns that number,
as recommended by the document.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics FloatLib.Numerics.Representations

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.2.6.3: the signed negative endpoint and
    unsigned zero endpoint. -/
theorem Format.minValue_eq (format : Format) :
    format.integerFormat.minValue =
      if format.signed then -(2 : Int) ^ format.precision else 0 := by
  by_cases hs : format.signed
  · have hw : 0 < format.width := by simp [Format.width, hs]
    simp only [Format.integerFormat, hs, ↓reduceIte, IntegerFormat.minValue]
    rw [FixedInt.minValue_eq hw]
    simp [Format.width, hs]
  · simp [Format.integerFormat, hs, IntegerFormat.minValue]

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.2.6.3: the positive endpoint is one unit below
    `2^N`. -/
theorem Format.maxValue_eq (format : Format) :
    format.integerFormat.maxValue = (2 : Int) ^ format.precision - 1 := by
  by_cases hs : format.signed <;>
    simp [Format.integerFormat, hs, IntegerFormat.maxValue, FixedInt.maxValue_eq,
      Format.width]

/-- Every valid coefficient has magnitude at most `2^N`. -/
theorem Format.abs_le (format : Format) {coefficient : Int}
    (h : format.integerFormat.InRange coefficient) :
    |coefficient| ≤ (2 : Int) ^ format.precision := by
  change format.integerFormat.minValue ≤ coefficient ∧
    coefficient ≤ format.integerFormat.maxValue at h
  rw [format.minValue_eq, format.maxValue_eq] at h
  have hp : 0 ≤ (2 : Int) ^ format.precision := pow_nonneg (by decide) _
  rw [_root_.abs_le]
  by_cases hs : format.signed <;> simp only [hs, ↓reduceIte] at h <;> omega

/-- A nonzero coefficient cannot fit after more than `N` binary shifts. -/
theorem shift_le_precision (format : Format) {coefficient : Int} (hnonzero : coefficient ≠ 0)
    {count : Nat} (h : format.integerFormat.InRange (coefficient * (2 : Int) ^ count)) :
    count ≤ format.precision := by
  have habs : 1 ≤ |coefficient| := by
    have := abs_pos.mpr hnonzero
    omega
  have hp : 0 ≤ (2 : Int) ^ count := pow_nonneg (by decide) _
  have hb := format.abs_le h
  rw [abs_mul, abs_of_nonneg hp] at hb
  apply (pow_le_pow_iff_right₀ (by decide : (1 : Int) < 2)).mp
  have hm : (2 : Int) ^ count ≤ |coefficient| * (2 : Int) ^ count := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right habs hp
  exact hm.trans hb

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.4 and generic macro C 7.18a.6.7: greatest
    nonoverflowing shift.
Zero returns exactly the precision, the document's recommended choice. -/
def countlsfx {format : Format} (value : format.Code) : Nat :=
  if bitsfx value = 0 then format.precision
  else Nat.findGreatest
    (fun count ↦ format.integerFormat.InRange (bitsfx value * (2 : Int) ^ count))
    format.precision

/-- The recommended zero convention is independent of signedness and width. -/
theorem countlsfx_zero {format : Format} (value : format.Code) (h : bitsfx value = 0) :
    countlsfx value = format.precision := by
  simp [countlsfx, h]

/-- The reported shift itself does not overflow. -/
theorem countlsfx_in_range {format : Format} (value : format.Code) :
    format.integerFormat.InRange (bitsfx value * (2 : Int) ^ countlsfx value) := by
  unfold countlsfx
  split
  · rename_i hzero
    simpa [hzero] using IntegerFormat.zero_inRange format.integerFormat
  · apply Nat.findGreatest_spec
      (P := fun count ↦ format.integerFormat.InRange (bitsfx value * (2 : Int) ^ count))
      (m := 0) (Nat.zero_le format.precision)
    simpa only [pow_zero, mul_one] using
      (show format.integerFormat.InRange (bitsfx value) from value.2)

/-- For a nonzero input, every nonoverflowing shift is at most the reported count. -/
theorem le_countlsfx {format : Format} (value : format.Code) (hnonzero : bitsfx value ≠ 0)
    (count : Nat)
    (h : format.integerFormat.InRange (bitsfx value * (2 : Int) ^ count)) :
    count ≤ countlsfx value := by
  unfold countlsfx
  rw [ite_eq_right hnonzero]
  exact Nat.le_findGreatest (shift_le_precision format hnonzero h) h

end FloatLib.Floats.Formats.FixedPoint.Embedded
