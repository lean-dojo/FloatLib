/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Root.Direction
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Zero
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Public integer-root semantics

For a negative degree, the exact rational magnitude is inverted before rounding.
The real specification is the signed root of that magnitude. Negative nonzero
operands require an odd degree. Zero signs and preferred exponents are specified
separately because a rational value does not retain either.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- Exact rational radicand for a signed integer degree. -/
def integerRootRadicand (n : Int) (a : ℚ) : ℚ :=
  if n < 0 then |a|⁻¹ else |a|

/-- The exact radicand of a signed-degree root, `|a|` or its reciprocal for a negative degree, is
nonnegative. -/
theorem integerRootRadicand_nonneg (n : Int) (a : ℚ) :
    0 ≤ integerRootRadicand n a := by
  unfold integerRootRadicand
  split
  · exact inv_nonneg.mpr (abs_nonneg a)
  · exact abs_nonneg a

/-- Signed real root, with inversion for negative degree. Its numeric domain
excludes degree zero and negative operands at an even degree. -/
noncomputable def integerRoot (n : Int) (a : ℝ) : ℝ :=
  (if a < 0 then -1 else 1) *
    realRoot n.natAbs (if n < 0 then |a|⁻¹ else |a|)

/-- Raising the real specification to the positive degree magnitude recovers
the input, or its reciprocal for a negative degree. -/
theorem integerRoot_pow_natAbs (n : Int) (hn : n ≠ 0) (a : ℝ)
    (hdom : a < 0 → n % 2 = 1) :
    integerRoot n a ^ n.natAbs = if n < 0 then a⁻¹ else a := by
  have hm : 0 ≤ if n < 0 then |a|⁻¹ else |a| := by
    split
    · exact inv_nonneg.mpr (abs_nonneg a)
    · exact abs_nonneg a
  by_cases ha : a < 0
  · have ho : Odd n.natAbs := Int.natAbs_odd.mpr (Int.odd_iff.mpr (hdom ha))
    rw [integerRoot, ite_eq_left ha, neg_one_mul, ho.neg_pow,
      realRoot_pow (Int.natAbs_ne_zero.mpr hn) hm]
    by_cases hneg : n < 0 <;> simp [hneg, abs_of_neg ha]
  · rw [integerRoot, ite_eq_right ha, one_mul, realRoot_pow (Int.natAbs_ne_zero.mpr hn) hm]
    simp [abs_of_nonneg (le_of_not_gt ha)]

/-- The signed real root of a rational operand is its sign times the real root of the exact rational
radicand, the form the root rounder works with. -/
theorem integerRoot_cast (n : Int) (a : ℚ) :
    (if decide (a < 0) then (-1 : ℝ) else 1) *
        realRoot n.natAbs (integerRootRadicand n a : ℝ) = integerRoot n (a : ℝ) := by
  by_cases hn : n < 0 <;> simp [integerRoot, integerRootRadicand, hn, Rat.cast_abs]

/-- The magnitude of the signed real root of a rational operand is the real root of its exact
rational radicand. -/
theorem abs_integerRoot (n : Int) (a : ℚ) :
    |integerRoot n (a : ℝ)| = realRoot n.natAbs (integerRootRadicand n a : ℝ) := by
  rw [← integerRoot_cast]
  have hp := realRoot_nonneg n.natAbs
    (show (0 : ℝ) ≤ integerRootRadicand n a by
      exact_mod_cast integerRootRadicand_nonneg n a)
  split <;> simp [abs_of_nonneg hp]

/-- Every nonzero finite operand in the real domain takes exactly one root-rounding path. -/
theorem rootN_eq_rootMagnitude (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : a ≠ 0)
    (n : Int) (hn : n ≠ 0) (hdom : a < 0 → n % 2 = 1) :
    ∃ preferred, rootN f mode x n =
      rootMagnitude f mode (decide (a < 0)) n.natAbs (integerRootRadicand n a) preferred := by
  cases x <;> simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx
  subst a
  rename_i s c q
  have hc : c ≠ 0 := by
    intro h
    simp [h] at ha
  have hm : 0 < (c : ℚ) * (10 : ℚ) ^ q :=
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hc) (zpow_pos (by norm_num) q)
  cases s
  · refine ⟨(if n < 0 then -q else q) / (n.natAbs : Int), ?_⟩
    simp [rootN, hn, hc, integerRootRadicand, abs_of_pos hm, not_lt.mpr hm.le]
  · have ho : n % 2 = 1 :=
      hdom (by simpa only [↓reduceIte, neg_mul, one_mul] using neg_neg_of_pos hm)
    refine ⟨(if n < 0 then -q else q) / (n.natAbs : Int), ?_⟩
    simp [rootN, hn, hc, ho, integerRootRadicand, neg_mul,
      abs_of_pos hm, neg_neg_of_pos hm]

/-- In both nearest modes, a nonoverflowing root of a nonzero finite datum in the real domain
(nonzero degree, odd degree for a negative operand) is finite and within half a grid unit of the
signed real root, taken of the reciprocal for a negative degree. -/
theorem rootN_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearest ∨ mode = .nearestAway)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : a ≠ 0)
    (n : Int) (hn : n ≠ 0) (hdom : a < 0 → n % 2 = 1)
    (hfinite : (rootN f mode x n).status.overflow = false) :
    ∃ value : ℚ, (rootN f mode x n).value.toRat? = some value ∧
      |(value : ℝ) - integerRoot n (a : ℝ)| ≤
        (10 : ℝ) ^ rootQuantum f n.natAbs (integerRootRadicand n a) / 2 := by
  obtain ⟨preferred, he⟩ := rootN_eq_rootMagnitude f mode x a hx ha n hn hdom
  rw [he] at hfinite ⊢
  simpa only [integerRoot_cast] using rootMagnitude_error_le_half f mode (decide (a < 0))
    hm (Int.natAbs_ne_zero.mpr hn) (integerRootRadicand_nonneg n a) preferred hfinite

/-- In every rounding direction, a nonoverflowing root of a nonzero finite datum in the real domain
is finite and less than one grid unit from the signed real root. -/
theorem rootN_error_lt_one (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : a ≠ 0)
    (n : Int) (hn : n ≠ 0) (hdom : a < 0 → n % 2 = 1)
    (hfinite : (rootN f mode x n).status.overflow = false) :
    ∃ value : ℚ, (rootN f mode x n).value.toRat? = some value ∧
      |(value : ℝ) - integerRoot n (a : ℝ)| <
        (10 : ℝ) ^ rootQuantum f n.natAbs (integerRootRadicand n a) := by
  obtain ⟨preferred, he⟩ := rootN_eq_rootMagnitude f mode x a hx ha n hn hdom
  rw [he] at hfinite ⊢
  simpa only [integerRoot_cast] using rootMagnitude_error_lt_one f mode (decide (a < 0))
    (Int.natAbs_ne_zero.mpr hn) (integerRootRadicand_nonneg n a) preferred hfinite

/-- Outside the root-rounding path (degree zero, a zero operand, or a negative operand at an even
degree), a root of a finite datum raises neither underflow nor inexact, and a finite result is the
exact zero root of a zero operand at a nonzero degree. -/
private theorem rootN_of_not_path (f : Format) (mode : RoundingMode) (x : Datum) (a : ℚ)
    (hx : x.toRat? = some a) (n : Int) (h : ¬(a ≠ 0 ∧ n ≠ 0 ∧ (a < 0 → n % 2 = 1))) :
    (rootN f mode x n).status.underflow = false ∧ (rootN f mode x n).status.inexact = false ∧
      ∀ value, (rootN f mode x n).value.toRat? = some value → value = 0 ∧ a = 0 ∧ n ≠ 0 := by
  cases x <;> simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx
  rename_i s c q
  by_cases hn : n = 0
  · simp [rootN, hn, invalidResult, Datum.toRat?_eq]
  have hp : (10 : ℚ) ^ q ≠ 0 := (zpow_pos (by norm_num) _).ne'
  by_cases hc : c = 0
  · subst hc
    have ha : a = 0 := by rw [← hx]; simp
    by_cases hneg : n < 0
    · simp [rootN, hn, hneg, Datum.toRat?_eq]
    · simp [rootN, hn, hneg, projectMagnitude_zero, Datum.toRat?_eq, ha]
  have ha : a ≠ 0 := by rw [← hx]; cases s <;> simp [hc, hp]
  push Not at h
  obtain ⟨hneg, hodd⟩ := h ha hn
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hx
    have hpos : (0 : ℚ) < (c : ℚ) * (10 : ℚ) ^ q :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hc) (zpow_pos (by norm_num) _)
    linarith
  · simp [rootN, hn, hc, show n % 2 = 0 by omega, invalidResult, Datum.toRat?_eq]

/-- Without overflow, a root of a finite datum raises inexact exactly when a finite result differs
from the signed real root. Degree zero and a negative operand at an even degree give a NaN, and a
zero operand gives an exact zero or a pole, so a finite result needs no domain premise. -/
theorem rootN_inexact_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a value : ℚ) (hx : x.toRat? = some a) (n : Int)
    (hfinite : (rootN f mode x n).status.overflow = false)
    (hv : (rootN f mode x n).value.toRat? = some value) :
    (rootN f mode x n).status.inexact = true ↔ (value : ℝ) ≠ integerRoot n (a : ℝ) := by
  by_cases hpath : a ≠ 0 ∧ n ≠ 0 ∧ (a < 0 → n % 2 = 1)
  swap
  · obtain ⟨-, hi, hval⟩ := rootN_of_not_path f mode x a hx n hpath
    obtain ⟨rfl, rfl, hn⟩ := hval value hv
    simp [hi, integerRoot, realRoot, Real.zero_rpow, hn]
  obtain ⟨ha, hn, hdom⟩ := hpath
  obtain ⟨preferred, he⟩ := rootN_eq_rootMagnitude f mode x a hx ha n hn hdom
  rw [he] at hfinite hv ⊢
  simpa only [integerRoot_cast] using rootMagnitude_inexact_iff f mode (decide (a < 0))
    (Int.natAbs_ne_zero.mpr hn) (integerRootRadicand_nonneg n a) value preferred hfinite hv

/-- A root of a finite datum raises underflow exactly when the real root is below the least normal
magnitude in absolute value and the result is inexact. Outside the real domain, at degree zero and
at a zero operand the root raises neither flag, and an overflowing root is never tiny. -/
theorem rootN_underflow_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (n : Int) :
    (rootN f mode x n).status.underflow = true ↔
      |integerRoot n (a : ℝ)| < (f.minNormal : ℝ) ∧
        (rootN f mode x n).status.inexact = true := by
  by_cases hpath : a ≠ 0 ∧ n ≠ 0 ∧ (a < 0 → n % 2 = 1)
  swap
  · obtain ⟨hu, hi, -⟩ := rootN_of_not_path f mode x a hx n hpath
    simp [hu, hi]
  obtain ⟨ha, hn, hdom⟩ := hpath
  obtain ⟨preferred, he⟩ := rootN_eq_rootMagnitude f mode x a hx ha n hn hdom
  rw [he, abs_integerRoot]
  exact rootMagnitude_underflow_iff f mode (decide (a < 0))
    (Int.natAbs_ne_zero.mpr hn) (integerRootRadicand_nonneg n a) preferred

/-- Rounding toward positive, a nonoverflowing root of a nonzero finite datum in the real domain is
finite and at least the signed real root. -/
theorem le_rootN_up (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : a ≠ 0)
    (n : Int) (hn : n ≠ 0) (hdom : a < 0 → n % 2 = 1)
    (hfinite : (rootN f .up x n).status.overflow = false) :
    ∃ value : ℚ, (rootN f .up x n).value.toRat? = some value ∧
      integerRoot n (a : ℝ) ≤ (value : ℝ) := by
  obtain ⟨preferred, he⟩ := rootN_eq_rootMagnitude f .up x a hx ha n hn hdom
  rw [he] at hfinite ⊢
  simpa only [integerRoot_cast] using le_rootMagnitude_up f (decide (a < 0))
    (Int.natAbs_ne_zero.mpr hn) (integerRootRadicand_nonneg n a) preferred hfinite

/-- Rounding toward negative, a nonoverflowing root of a nonzero finite datum in the real domain is
finite and at most the signed real root. -/
theorem rootN_down_le (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : a ≠ 0)
    (n : Int) (hn : n ≠ 0) (hdom : a < 0 → n % 2 = 1)
    (hfinite : (rootN f .down x n).status.overflow = false) :
    ∃ value : ℚ, (rootN f .down x n).value.toRat? = some value ∧
      (value : ℝ) ≤ integerRoot n (a : ℝ) := by
  obtain ⟨preferred, he⟩ := rootN_eq_rootMagnitude f .down x a hx ha n hn hdom
  rw [he] at hfinite ⊢
  simpa only [integerRoot_cast] using rootMagnitude_down_le f (decide (a < 0))
    (Int.natAbs_ne_zero.mpr hn) (integerRootRadicand_nonneg n a) preferred hfinite

/-- Rounding toward zero, a root of a nonzero finite datum in the real domain is finite and no
larger in magnitude than the signed real root, also when it overflows to the greatest finite datum.
-/
theorem abs_rootN_towardZero_le (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : a ≠ 0)
    (n : Int) (hn : n ≠ 0) (hdom : a < 0 → n % 2 = 1) :
    ∃ value : ℚ, (rootN f .towardZero x n).value.toRat? = some value ∧
      |(value : ℝ)| ≤ |integerRoot n (a : ℝ)| := by
  obtain ⟨preferred, he⟩ := rootN_eq_rootMagnitude f .towardZero x a hx ha n hn hdom
  rw [he, abs_integerRoot]
  exact abs_rootMagnitude_towardZero_le f (decide (a < 0))
    (Int.natAbs_ne_zero.mpr hn) (integerRootRadicand_nonneg n a) preferred

/-- Positive-degree zero is exact. Even degrees clear its sign; odd degrees preserve it. -/
theorem rootN_zero_pos (f : Format) (mode : RoundingMode) (s : Bool) (q n : Int)
    (hn : 0 < n) :
    rootN f mode (.finite s 0 q) n =
      { value := .finite (s && decide (n % 2 = 1)) 0
          (max f.minQuantum (min (q / (n.natAbs : Int)) f.maxQuantum)) } := by
  simp [rootN, hn.ne', not_lt.mpr hn.le, projectMagnitude_zero]

/-- Negative-degree zero is a pole with the same odd-degree sign rule. -/
theorem rootN_zero_neg (f : Format) (mode : RoundingMode) (s : Bool) (q n : Int)
    (hn : n < 0) :
    rootN f mode (.finite s 0 q) n =
      { value := .infinity (s && decide (n % 2 = 1))
        status := { divideByZero := true } } := by
  simp [rootN, hn.ne, hn]

/-- The degree-zero root of any finite datum, either zero included, is the default quiet NaN with
the invalid flag. -/
theorem rootN_degree_zero_finite (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q : Int) :
    rootN f mode (.finite s c q) 0 = invalidResult := by
  simp [rootN]

/-- The degree-zero root of either infinity is the default quiet NaN with the invalid flag. -/
theorem rootN_degree_zero_infinity (f : Format) (mode : RoundingMode) (s : Bool) :
    rootN f mode (.infinity s) 0 = invalidResult := by
  simp [rootN]

/-- A root of even degree, positive, negative or zero, of a negative nonzero finite datum is the
default quiet NaN with the invalid flag. -/
theorem rootN_negative_even (f : Format) (mode : RoundingMode) (c : Nat) (q n : Int)
    (hc : c ≠ 0) (he : n % 2 = 0) :
    rootN f mode (.finite true c q) n = invalidResult := by
  by_cases hn : n = 0
  · simp [rootN, hn]
  · simp [rootN, hc, hn, he]

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
