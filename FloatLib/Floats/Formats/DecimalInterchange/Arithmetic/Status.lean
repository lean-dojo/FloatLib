/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Zero

/-!
# Numerical inexactness and signed-zero arithmetic

Here the inexact flag gets its numerical meaning. For finite operands and a finite result, it is
raised if and only if the returned value differs from the exact rational expression, and that
includes a result that overflows to the greatest finite datum. A finite quotient rules out a zero
divisor by itself. Zero results take the operation's sign rule and its preferred quantum, clamped
to the destination range. Landing a zero in a different cohort doesn't raise inexact.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- Adding two finite datums raises inexact if and only if a finite result differs from the exact
sum. -/
theorem add_inexact_iff (f : Format) (mode : RoundingMode)
    (x y : Datum) (a b value : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hv : (add f mode x y).value.toRat? = some value) :
    (add f mode x y).status.inexact = true ↔ value ≠ a + b := by
  cases x <;> cases y <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx hy
  subst a
  subst b
  exact project_inexact_iff f mode _ value _ _ hv

/-- Subtracting two finite datums raises inexact if and only if a finite result differs from the
exact difference. -/
theorem sub_inexact_iff (f : Format) (mode : RoundingMode)
    (x y : Datum) (a b value : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hv : (sub f mode x y).value.toRat? = some value) :
    (sub f mode x y).status.inexact = true ↔ value ≠ a - b := by
  cases x <;> cases y <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx hy
  subst a
  subst b
  rename_i sx cx qx sy cy qy
  have hn : Datum.finiteValue (!sy) cy qy = -Datum.finiteValue sy cy qy := by
    cases sy <;> simp [Datum.finiteValue]
  simp only [sub, Datum.negate, add, hn, ← sub_eq_add_neg] at hv ⊢
  exact project_inexact_iff f mode _ value _ _ hv

/-- Multiplying two finite datums raises inexact if and only if a finite result differs from the
exact product. -/
theorem mul_inexact_iff (f : Format) (mode : RoundingMode)
    (x y : Datum) (a b value : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hv : (mul f mode x y).value.toRat? = some value) :
    (mul f mode x y).status.inexact = true ↔ value ≠ a * b := by
  cases x <;> cases y <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx hy
  subst a
  subst b
  exact project_inexact_iff f mode _ value _ _ hv

/-- Dividing two finite datums raises inexact if and only if a finite result differs from the exact
quotient. A zero divisor gives a NaN or an infinity, so a finite result has a nonzero divisor. -/
theorem div_inexact_iff (f : Format) (mode : RoundingMode)
    (x y : Datum) (a b value : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hv : (div f mode x y).value.toRat? = some value) :
    (div f mode x y).status.inexact = true ↔ value ≠ a / b := by
  cases x <;> cases y <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx hy
  subst a
  subst b
  rename_i sx cx qx sy cy qy
  by_cases hc : cy = 0
  · by_cases hcx : cx = 0 <;>
      simp [div, hc, hcx, invalidResult, Datum.toRat?_eq] at hv
  simp only [div, hc, ↓reduceIte] at hv ⊢
  exact project_inexact_iff f mode _ value _ _ hv

/-- A fused multiply-add of three finite datums raises inexact if and only if a finite result
differs from the exact value of `a * b + c`. -/
theorem fma_inexact_iff (f : Format) (mode : RoundingMode)
    (x y z : Datum) (a b c value : ℚ)
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hz : z.toRat? = some c)
    (hv : (fma f mode x y z).value.toRat? = some value) :
    (fma f mode x y z).status.inexact = true ↔ value ≠ a * b + c := by
  cases x <;> cases y <;> cases z <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx hy hz
  subst a
  subst b
  subst c
  exact project_inexact_iff f mode _ value _ _ hv

/-- Adding zeros of equal sign keeps that sign, and opposite signs follow the cancellation rule. -/
theorem add_zeros (f : Format) (mode : RoundingMode) (sx sy : Bool) (qx qy : Int) :
    add f mode (.finite sx 0 qx) (.finite sy 0 qy) =
      { value := .finite (zeroSumSign mode sx sy) 0
          (max f.minQuantum (min (min qx qy) f.maxQuantum)) } := by
  simp [add, Datum.finiteValue, project_zero]

/-- A zero product uses the XOR sign and clamps the sum of operand quanta to the format range. -/
theorem mul_zero_left (f : Format) (mode : RoundingMode)
    (sx sy : Bool) (c : Nat) (qx qy : Int) :
    mul f mode (.finite sx 0 qx) (.finite sy c qy) =
      { value := .finite (sx ^^ sy) 0
          (max f.minQuantum (min (qx + qy) f.maxQuantum)) } := by
  simp [mul, Datum.finiteValue, project_zero]

/-- A zero divided by a nonzero finite datum is an exact zero with the XOR sign and no flags. Its
quantum is the difference of the operand quanta, clamped to the format range. -/
theorem div_zero_numerator (f : Format) (mode : RoundingMode)
    (sx sy : Bool) (c : Nat) (hc : c ≠ 0) (qx qy : Int) :
    div f mode (.finite sx 0 qx) (.finite sy c qy) =
      { value := .finite (sx ^^ sy) 0
          (max f.minQuantum (min (qx - qy) f.maxQuantum)) } := by
  simp [div, hc, Datum.finiteValue, project_zero]

/-- Divide-by-zero is raised for a finite nonzero numerator, with the quotient's XOR sign. -/
theorem div_zero_denominator (f : Format) (mode : RoundingMode)
    (sx sy : Bool) (c : Nat) (hc : c ≠ 0) (qx qy : Int) :
    div f mode (.finite sx c qx) (.finite sy 0 qy) =
      { value := .infinity (sx ^^ sy), status := { divideByZero := true } } := by
  simp [div, hc]

/-- Infinity divided by zero does not raise divide-by-zero: the numerator is not finite. -/
theorem div_infinity_zero (f : Format) (mode : RoundingMode)
    (sx sy : Bool) (q : Int) :
    div f mode (.infinity sx) (.finite sy 0 q) =
      { value := .infinity (sx ^^ sy) } := rfl

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
