/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Zero

/-!
# Public square-root semantics

These results cover zero's sign and preferred quantum, invalid negative inputs,
and the real numerical error of a finite nonnegative operand. The public error
bound includes zero rather than assuming the input is strictly positive.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- Square root preserves either zero sign and clamps the floored half-exponent
to the format's quantum range. -/
theorem sqrt_zero (f : Format) (mode : RoundingMode) (s : Bool) (q : Int) :
    sqrt f mode (.finite s 0 q) =
      { value := .finite s 0 (max f.minQuantum (min (q / 2) f.maxQuantum)) } := by
  simp [sqrt, projectMagnitude_zero]

/-- A negative nonzero finite operand raises invalid and returns a quiet NaN. -/
theorem sqrt_negative (f : Format) (mode : RoundingMode) (c : Nat)
    (hc : c ≠ 0) (q : Int) :
    sqrt f mode (.finite true c q) = invalidResult := by
  simp [sqrt, hc]

/-- The returned square root has at most half a decimal grid unit of real error. -/
theorem sqrt_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : 0 ≤ a)
    (hfinite : (sqrt f mode x).status.overflow = false) :
    ∃ value : ℚ, (sqrt f mode x).value.toRat? = some value ∧
      |(value : ℝ) - Real.sqrt (a : ℝ)| ≤ (10 : ℝ) ^ sqrtQuantum f a / 2 := by
  cases x <;> simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx
  subst a
  rename_i s c q
  by_cases hc : c = 0
  · subst c
    refine ⟨0, ?_, ?_⟩
    · simp [sqrt_zero, Datum.toRat?_eq]
    · simp only [Nat.cast_zero, mul_zero, zero_mul, Rat.cast_zero, Real.sqrt_zero,
        sub_zero, abs_zero]
      exact div_nonneg (zpow_pos (by norm_num) _).le (by norm_num)
  · have hs : s = false := by
      cases s
      · rfl
      · have hp : (0 : ℚ) < (c : ℚ) * (10 : ℚ) ^ q :=
          mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hc) (zpow_pos (by norm_num) q)
        simp only [↓reduceIte, neg_one_mul] at ha
        nlinarith
    subst s
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at ha ⊢
    simp only [sqrt, if_neg hc, Bool.false_eq_true, ↓reduceIte] at hfinite ⊢
    exact sqrtMagnitude_error_le_half f mode hm ha _ hfinite

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
