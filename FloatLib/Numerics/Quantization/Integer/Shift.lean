/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Integer.Proof
import Mathlib.Algebra.Order.Ring.Int

/-!
# Nonoverflowing binary shifts in an integer interval

For an interval containing zero and a nonzero coefficient in that interval,
`IntegerRange.countLeftShifts` gives the greatest nonoverflowing binary shift.
It divides the endpoint magnitude by the coefficient magnitude and takes the
integer binary logarithm. The characterization holds for arbitrary endpoints,
not only two's-complement words. N1169's `countlsfx` is one application.

WG14 N1169 (2006 TR 18037 draft), §4.1.7.3, defines `countlsfx`.
-/

@[expose] public section

namespace FloatLib.Numerics.IntegerRange

/-- Endpoint magnitude available in the coefficient's direction. -/
def shiftCapacity (range : IntegerRange) (coefficient : Int) : Nat :=
  (if coefficient < 0 then -range.lower else range.upper).toNat

/-- Binary headroom from an exact integer quotient and logarithm.
Its maximality contract requires a nonzero in-range coefficient and an interval
containing zero; inputs outside that contract have no specified headroom meaning. -/
def countLeftShifts (range : IntegerRange) (coefficient : Int) : Nat :=
  (range.shiftCapacity coefficient / coefficient.natAbs).log2

/-- A binary shift fits exactly when its magnitude stays below the endpoint capacity. -/
theorem contains_mul_pow_iff (range : IntegerRange) (hzero : range.Contains 0)
    (coefficient : Int) (count : Nat) :
    range.Contains (coefficient * (2 : Int) ^ count) ↔
      coefficient.natAbs * (2 : Nat) ^ count ≤ range.shiftCapacity coefficient := by
  have hp : (0 : Int) ≤ 2 ^ count := pow_nonneg (by decide) _
  change range.lower ≤ coefficient * 2 ^ count ∧
      coefficient * 2 ^ count ≤ range.upper ↔ _
  rw [← Int.ofNat_le]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, shiftCapacity]
  by_cases hc : coefficient < 0
  · rw [ite_eq_left hc, Int.toNat_of_nonneg (neg_nonneg.mpr hzero.1),
      Int.ofNat_natAbs_of_nonpos hc.le, neg_mul]
    have hu : coefficient * (2 : Int) ^ count ≤ range.upper :=
      (mul_nonpos_of_nonpos_of_nonneg hc.le hp).trans hzero.2
    omega
  · rw [ite_eq_right hc, Int.toNat_of_nonneg hzero.2,
      Int.natAbs_of_nonneg (le_of_not_gt hc)]
    have hl : range.lower ≤ coefficient * (2 : Int) ^ count :=
      hzero.1.trans (mul_nonneg (le_of_not_gt hc) hp)
    omega

/-- The logarithm formula characterizes every nonoverflowing shift, without a width bound. -/
theorem le_countLeftShifts_iff (range : IntegerRange) (hzero : range.Contains 0)
    (coefficient : Int) (hmem : range.Contains coefficient) (hne : coefficient ≠ 0)
    (count : Nat) :
    count ≤ range.countLeftShifts coefficient ↔
      range.Contains (coefficient * (2 : Int) ^ count) := by
  have habs : 0 < coefficient.natAbs := Int.natAbs_pos.mpr hne
  have hcap : coefficient.natAbs ≤ range.shiftCapacity coefficient := by
    simpa only [pow_zero, mul_one] using
      (range.contains_mul_pow_iff hzero coefficient 0).mp (by simpa using hmem)
  have hquot : range.shiftCapacity coefficient / coefficient.natAbs ≠ 0 :=
    Nat.ne_of_gt (Nat.div_pos hcap habs)
  rw [countLeftShifts, Nat.le_log2 hquot, Nat.le_div_iff_mul_le habs,
    mul_comm, ← range.contains_mul_pow_iff hzero coefficient count]

end FloatLib.Numerics.IntegerRange
