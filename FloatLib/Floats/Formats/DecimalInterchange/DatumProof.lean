/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Datum
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Tactic.Ring

/-!
# Cohort identities, including signed zero and decimal rescaling

These are the small cohort identities. Moving a trailing zero of the coefficient into the quantum
exponent keeps a datum in its cohort, which is why `10 × 10^-1` and `1 × 10^0` share a cohort.
Zero's cohort depends on its sign and not on its quantum. Each infinity is alone in its cohort, and
NaNs belong to no cohort at all. The last two theorems say that a literal has the rational value of
the same literal in `ℚ`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Datum

/-- Moving a trailing decimal zero into the quantum exponent preserves the cohort.
Whether each datum is representable at a particular width is another matter. -/
theorem sameCohort_shift (s : Bool) (c : Nat) (q : Int) :
    SameCohort (.finite s (10 * c) q) (.finite s c (q + 1)) := by
  refine ⟨rfl, ?_⟩
  rw [zpow_add_one₀ (by decide : (10 : ℚ) ≠ 0)]
  push_cast
  ring

/-- Zero's quantum exponent does not change its cohort, but its sign does. -/
theorem sameCohort_zero_iff (s t : Bool) (q r : Int) :
    SameCohort (.finite s 0 q) (.finite t 0 r) ↔ s = t := by
  simp [SameCohort]

/-- `+0` and `-0` lie in different cohorts, whatever their quanta. -/
theorem not_sameCohort_opposite_zeros (q r : Int) :
    ¬SameCohort (.finite false 0 q) (.finite true 0 r) := by
  simp [sameCohort_zero_iff]

/-- Equal finite cohorts have equal exact rational values. The converse also needs
the sign of zero, which the rational value alone cannot retain. -/
theorem toRat?_eq_of_sameCohort {s t : Bool} {c d : Nat} {q r : Int}
    (h : SameCohort (.finite s c q) (.finite t d r)) :
    toRat? (.finite s c q) = toRat? (.finite t d r) := by
  obtain ⟨rfl, h⟩ := h
  simp only [toRat?_eq, mul_assoc, h]

/-- Each infinity has exactly one datum in its cohort. -/
theorem sameCohort_infinity_iff (s : Bool) (d : Datum) :
    SameCohort (.infinity s) d ↔ d = .infinity s := by
  cases d <;> simp [SameCohort, eq_comm]

/-- Cohorts contain floating-point numbers, which exclude NaNs (IEEE 754-2019 §2.1). -/
theorem not_sameCohort_nan (s signaling : Bool) (p : Nat) (d : Datum) :
    ¬SameCohort (.nan s signaling p) d := by
  cases d <;> simp [SameCohort]

/-- A natural literal has the value of that natural number. -/
theorem toRat?_ofNat (n : Nat) : (OfNat.ofNat n : Datum).toRat? = some (n : ℚ) := by
  change (Datum.finite false n 0).toRat? = _
  simp [toRat?_eq]

/-- A decimal literal has the rational value of the same literal written in `ℚ`. -/
theorem toRat?_ofScientific (mantissa : Nat) (exponentSign : Bool) (decimalExponent : Nat) :
    (OfScientific.ofScientific mantissa exponentSign decimalExponent : Datum).toRat? =
      some (OfScientific.ofScientific mantissa exponentSign decimalExponent : ℚ) := by
  change (Datum.finite false mantissa _).toRat? = _
  rw [Rat.ofScientific_def']
  simp [toRat?_eq]

end FloatLib.Floats.Formats.DecimalInterchange.Datum
