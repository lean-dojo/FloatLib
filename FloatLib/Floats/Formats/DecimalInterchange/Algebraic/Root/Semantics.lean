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

theorem integerRoot_cast (n : Int) (a : ℚ) :
    (if decide (a < 0) then (-1 : ℝ) else 1) *
        realRoot n.natAbs (integerRootRadicand n a : ℝ) = integerRoot n (a : ℝ) := by
  by_cases hn : n < 0 <;> simp [integerRoot, integerRootRadicand, hn, Rat.cast_abs]

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

theorem rootN_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
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

theorem rootN_inexact_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a value : ℚ) (hx : x.toRat? = some a) (ha : a ≠ 0)
    (n : Int) (hn : n ≠ 0) (hdom : a < 0 → n % 2 = 1)
    (hfinite : (rootN f mode x n).status.overflow = false)
    (hv : (rootN f mode x n).value.toRat? = some value) :
    (rootN f mode x n).status.inexact = true ↔ (value : ℝ) ≠ integerRoot n (a : ℝ) := by
  obtain ⟨preferred, he⟩ := rootN_eq_rootMagnitude f mode x a hx ha n hn hdom
  rw [he] at hfinite hv ⊢
  simpa only [integerRoot_cast] using rootMagnitude_inexact_iff f mode (decide (a < 0))
    (Int.natAbs_ne_zero.mpr hn) (integerRootRadicand_nonneg n a) value preferred hfinite hv

theorem rootN_underflow_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : a ≠ 0)
    (n : Int) (hn : n ≠ 0) (hdom : a < 0 → n % 2 = 1)
    (hfinite : (rootN f mode x n).status.overflow = false) :
    (rootN f mode x n).status.underflow = true ↔
      |integerRoot n (a : ℝ)| < (f.minNormal : ℝ) ∧
        (rootN f mode x n).status.inexact = true := by
  obtain ⟨preferred, he⟩ := rootN_eq_rootMagnitude f mode x a hx ha n hn hdom
  rw [he] at hfinite ⊢
  rw [abs_integerRoot]
  exact rootMagnitude_underflow_iff f mode (decide (a < 0))
    (Int.natAbs_ne_zero.mpr hn) (integerRootRadicand_nonneg n a) preferred hfinite

theorem le_rootN_towardPositive (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : a ≠ 0)
    (n : Int) (hn : n ≠ 0) (hdom : a < 0 → n % 2 = 1)
    (hfinite : (rootN f .towardPositive x n).status.overflow = false) :
    ∃ value : ℚ, (rootN f .towardPositive x n).value.toRat? = some value ∧
      integerRoot n (a : ℝ) ≤ (value : ℝ) := by
  obtain ⟨preferred, he⟩ := rootN_eq_rootMagnitude f .towardPositive x a hx ha n hn hdom
  rw [he] at hfinite ⊢
  simpa only [integerRoot_cast] using le_rootMagnitude_towardPositive f (decide (a < 0))
    (Int.natAbs_ne_zero.mpr hn) (integerRootRadicand_nonneg n a) preferred hfinite

theorem rootN_towardNegative_le (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : a ≠ 0)
    (n : Int) (hn : n ≠ 0) (hdom : a < 0 → n % 2 = 1)
    (hfinite : (rootN f .towardNegative x n).status.overflow = false) :
    ∃ value : ℚ, (rootN f .towardNegative x n).value.toRat? = some value ∧
      (value : ℝ) ≤ integerRoot n (a : ℝ) := by
  obtain ⟨preferred, he⟩ := rootN_eq_rootMagnitude f .towardNegative x a hx ha n hn hdom
  rw [he] at hfinite ⊢
  simpa only [integerRoot_cast] using rootMagnitude_towardNegative_le f (decide (a < 0))
    (Int.natAbs_ne_zero.mpr hn) (integerRootRadicand_nonneg n a) preferred hfinite

theorem abs_rootN_towardZero_le (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : a ≠ 0)
    (n : Int) (hn : n ≠ 0) (hdom : a < 0 → n % 2 = 1)
    (hfinite : (rootN f .towardZero x n).status.overflow = false) :
    ∃ value : ℚ, (rootN f .towardZero x n).value.toRat? = some value ∧
      |(value : ℝ)| ≤ |integerRoot n (a : ℝ)| := by
  obtain ⟨preferred, he⟩ := rootN_eq_rootMagnitude f .towardZero x a hx ha n hn hdom
  rw [he] at hfinite ⊢
  rw [abs_integerRoot]
  exact abs_rootMagnitude_towardZero_le f (decide (a < 0))
    (Int.natAbs_ne_zero.mpr hn) (integerRootRadicand_nonneg n a) preferred hfinite

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

theorem rootN_degree_zero_finite (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q : Int) :
    rootN f mode (.finite s c q) 0 = invalidResult := by
  simp [rootN]

theorem rootN_degree_zero_infinity (f : Format) (mode : RoundingMode) (s : Bool) :
    rootN f mode (.infinity s) 0 = invalidResult := by
  simp [rootN]

theorem rootN_negative_even (f : Format) (mode : RoundingMode) (c : Nat) (q n : Int)
    (hc : c ≠ 0) (hn : n ≠ 0) (he : n % 2 = 0) :
    rootN f mode (.finite true c q) n = invalidResult := by
  simp [rootN, hc, hn, he]

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
