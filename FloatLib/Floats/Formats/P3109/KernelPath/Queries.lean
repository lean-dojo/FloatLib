/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.KernelPath.Selection
public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Classification
import Mathlib.Tactic.Linarith

/-!
# The kernel P3109 queries compute the reference queries

P3109 Interim Report v4.1 (14 September 2026), §§4.13 and 4.16, an unapproved draft. The
queries of the report read a code and its descriptor:

* `isZero_eq`, `isNaN_eq`, `isInfinite_eq`, `isFinite_eq`, `isSignMinus_eq`, `isNormal_eq`,
  `isSubnormal_eq`: the classification queries are the kernel tests on the code, for every
  descriptor and every code;
* `isOne_eq`: `IsOne` is `isOne`, which compares the numerator and the denominator of the code;
* `nextGreaterThan_eq`, `nextLessThan_eq`: the neighbours store `nextUp` and `nextDown`;
* `compare_eq`: the order behind `==` and `<` on P3109 values, from `less` and `equal`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.KernelPath

open FloatLib.Numerics FloatLib.Numerics.Kernel
open FloatLib.Floats.Formats.P3109

variable {format leftFormat rightFormat : Format}

/-! ## Classification -/

/-- P3109 interim report v4.1, §4.13: `IsZero` tests the code zero. -/
theorem isZero_eq (x : ExecFloat.P3109 format) : x.IsZero = Nat.beq x.toNatBits 0 := by
  unfold ExecFloat.P3109.IsZero
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

/-- P3109 interim report v4.1, §4.13: `IsNaN` is `isNaN` on the code. -/
theorem isNaN_eq (x : ExecFloat.P3109 format) :
    x.IsNaN = isNaN format.bitWidth (sgOf format) x.toNatBits := by
  unfold ExecFloat.P3109.IsNaN isNaN
  rw [nanBits_eq, Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

/-- P3109 interim report v4.1, §4.13: `IsInfinite` is `isInfinite` on the code. -/
theorem isInfinite_eq (x : ExecFloat.P3109 format) :
    x.IsInfinite = isInfinite format.bitWidth (sgOf format) (exOf format) x.toNatBits := by
  unfold ExecFloat.P3109.IsInfinite isInfinite
  rw [positiveInfinityBits_eq, negativeInfinityBits_eq, Bool.eq_iff_iff]
  unfold sgOf exOf
  cases hs : format.signedness <;> cases hd : format.domain <;> simp

/-- P3109 interim report v4.1, §4.13: `IsFinite` is `isFinite` on the code. -/
theorem isFinite_eq (x : ExecFloat.P3109 format) :
    x.IsFinite = isFinite format.bitWidth (sgOf format) (exOf format) x.toNatBits := by
  unfold ExecFloat.P3109.IsFinite isFinite
  rw [isNaN_eq, isInfinite_eq]
  cases (isNaN format.bitWidth (sgOf format) x.toNatBits ||
    isInfinite format.bitWidth (sgOf format) (exOf format) x.toNatBits) <;> rfl

/-- P3109 interim report v4.1, §4.13: `IsSignMinus` is `isSignMinus` on the code. -/
theorem isSignMinus_eq (x : ExecFloat.P3109 format) :
    x.IsSignMinus = isSignMinus format.bitWidth (sgOf format) x.toNatBits := by
  unfold ExecFloat.P3109.IsSignMinus isSignMinus
  rw [signBoundary_eq, Bool.eq_iff_iff]
  unfold sgOf
  cases hs : format.signedness <;> simp

/-- The magnitude code of a stored code is `magnitudeBits` on the code. -/
theorem magnitudeBits_eq (x : ExecFloat.P3109 format) :
    x.magnitudeBits = magnitudeBits format.bitWidth (sgOf format) x.toNatBits := by
  unfold ExecFloat.P3109.magnitudeBits magnitudeBits
  rw [signBoundary_eq]
  kernel_notation
  unfold sgOf
  cases hs : format.signedness <;> simp

/-- P3109 interim report v4.1, §4.13: `IsNormal` is `isNormal` on the code. -/
theorem isNormal_eq (x : ExecFloat.P3109 format) :
    x.IsNormal =
      isNormal format.bitWidth format.precision (sgOf format) (exOf format) x.toNatBits := by
  unfold ExecFloat.P3109.IsNormal isNormal
  rw [isFinite_eq, magnitudeBits_eq, trailingBits_eq, Bool.eq_iff_iff]
  kernel_notation
  simp

/-- P3109 interim report v4.1, §4.13: `IsSubnormal` is `isSubnormal` on the code. -/
theorem isSubnormal_eq (x : ExecFloat.P3109 format) :
    x.IsSubnormal =
      isSubnormal format.bitWidth format.precision (sgOf format) (exOf format) x.toNatBits := by
  unfold ExecFloat.P3109.IsSubnormal isSubnormal
  rw [isFinite_eq, magnitudeBits_eq, trailingBits_eq, Bool.eq_iff_iff]
  kernel_notation
  simp [Nat.succ_le_iff]

/-- A closed value given by class, sign and ratio is one when its class is finite, its sign bit
clear and its two terms equal. -/
theorem closed_eq_one_iff (c s n d : Nat) (hs : s ≤ 1) (hd : d ≠ 0) :
    closed c s n d = NumericalValue.finite 1 ↔ c = 0 ∧ s = 0 ∧ n = d := by
  have hd' : (d : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hdpos : (0 : Rat) < (d : Rat) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
  have : (0 : Rat) ≤ (n : Rat) := Nat.cast_nonneg n
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ 3 ≤ c) with rfl | rfl | rfl | hc
  · have hB : closed 0 s n d =
        NumericalValue.finite ((if s = 0 then (n : Rat) else -(n : Rat)) / (d : Rat)) := by
      simp [closed]
    rw [hB, NumericalValue.finite.injEq, div_eq_one_iff_eq hd']
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · simp
    · constructor
      · intro h
        rw [ite_eq_right Nat.one_ne_zero] at h
        linarith
      · intro h
        omega
  · simp [closed]
  · simp [closed]
  · have h0 : ¬c = 0 := by omega
    have h1 : ¬c = 1 := by omega
    have h2 : ¬c = 2 := by omega
    simp [closed, Arithmetic.nan, h0, h1, h2]

/-- P3109 interim report v4.1, §4.13: `IsOne` is `isOne` on the code, which compares the
numerator and the denominator of a finite code with a clear sign. -/
theorem isOne_eq (x : ExecFloat.P3109 format) :
    x.IsOne = isOne format.bitWidth format.precision (sgOf format) (exOf format) x.toNatBits := by
  rw [Bool.eq_iff_iff, ExecFloat.P3109.isOne_iff_toClosedRat, toClosedRat_eq x,
    closed_eq_one_iff _ _ _ _ (signOf_le _ _ _) (denominatorOf_ne_zero _ _ _ _)]
  unfold isOne
  simp only [Bool.and_eq_true, Nat.beq_eq]

/-! ## Neighbours -/

/-- P3109 interim report v4.1, §4.16: `NextGreaterThan` stores `nextUp` of the code. -/
theorem nextGreaterThan_eq (x : ExecFloat.P3109 format) :
    x.NextGreaterThan =
      ExecFloat.P3109.ofNatBits (nextUp format.bitWidth (sgOf format) x.toNatBits) := by
  unfold ExecFloat.P3109.NextGreaterThan nextUp
  rw [isNaN_eq, isSignMinus_eq, nanBits_eq, positiveInfinityBits_eq, signBoundary_eq]
  kernel_notation
  simp only [beq_iff_eq]
  split_ifs <;> rfl

/-- P3109 interim report v4.1, §4.16: `NextLessThan` stores `nextDown` of the code. -/
theorem nextLessThan_eq (x : ExecFloat.P3109 format) :
    x.NextLessThan =
      ExecFloat.P3109.ofNatBits (nextDown format.bitWidth (sgOf format) x.toNatBits) := by
  unfold ExecFloat.P3109.NextLessThan nextDown
  rw [isNaN_eq, isSignMinus_eq, isZero_eq, nanBits_eq, negativeInfinityBits_eq, signBoundary_eq]
  kernel_notation
  unfold sgOf
  cases hs : format.signedness <;> simp only [beq_iff_eq] <;> split_ifs <;> rfl

/-! ## The order of two encodings -/

/-- The order behind `==` and `<` on P3109 values (§4.12), from `less` and `equal` on the
encodings: `none` when either value is NaN. -/
theorem compare_eq (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat) :
    ExecFloat.P3109.compare x y =
      Bool.casesOn (motive := fun _ => Option Ordering)
        (less leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          x.toNatBits y.toNatBits)
        (Bool.casesOn (motive := fun _ => Option Ordering)
          (less rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
            leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
            y.toNatBits x.toNatBits)
          (Bool.casesOn (motive := fun _ => Option Ordering)
            (equal leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
              rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
              x.toNatBits y.toNatBits)
            none (some Ordering.eq))
          (some Ordering.gt))
        (some Ordering.lt) := by
  rw [← compareLess_eq x y, ← compareLess_eq y x, ← compareEqual_eq x y]
  change (if ExecFloat.P3109.CompareLess x y = true then some Ordering.lt
    else if ExecFloat.P3109.CompareLess y x = true then some Ordering.gt
    else if ExecFloat.P3109.CompareEqual x y = true then some Ordering.eq else none) = _
  cases ExecFloat.P3109.CompareLess x y <;> cases ExecFloat.P3109.CompareLess y x <;>
    cases ExecFloat.P3109.CompareEqual x y <;> rfl

end FloatLib.Floats.Formats.P3109.KernelPath
