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

Moving a trailing decimal zero into the quantum exponent preserves the cohort. Zero's cohort
depends on its sign but not its quantum; infinities have singleton cohorts, and NaNs belong to
no cohort.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Datum

/-- Moving a trailing decimal zero into the quantum exponent preserves the cohort.
Representability at a particular width is a separate condition on each datum. -/
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

end FloatLib.Floats.Formats.DecimalInterchange.Datum
