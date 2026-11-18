/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Format

/-!
# N1169's implementation-defined adjacent rounding

N1169, ISO/IEC TR 18037:2006(E), §4.1.3 and C 6.3.1.3a permit either adjacent
representable value. `Rounding` records that freedom independently of the format.
Floor, ceiling and nearest-even are concrete members. `NearestRounding` additionally
specifies the nearest-grid requirement of C 7.18a.6.3 (`roundfx`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.3: an executable choice of either neighboring integer. -/
structure Rounding where
  /-- Integer chosen on the coefficient grid. -/
  run : ℚ → Int
  /-- The choice is adjacent, including exact preservation of integral inputs. -/
  adjacent (x : ℚ) : run x = x.floor ∨ run x = x.ceil

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.3: nearest rounding, with arbitrary
    choices at midpoints. -/
structure NearestRounding extends Rounding where
  /-- No other integer is closer to the input. -/
  nearest (x : ℚ) (k : Int) : |(run x : ℚ) - x| ≤ |(k : ℚ) - x|

/-- Downward rounding is a permitted adjacent choice in WG14 N1169 (2006 TR 18037 draft), §4.1.3. -/
def Rounding.floor : Rounding :=
  ⟨Rat.floor, fun _ ↦ Or.inl rfl⟩

/-- Upward rounding is a permitted adjacent choice in WG14 N1169 (2006 TR 18037 draft), §4.1.3. -/
def Rounding.ceil : Rounding :=
  ⟨Rat.ceil, fun _ ↦ Or.inr rfl⟩

/-- Nearest-even reuses the common exact rational quotient algorithm. -/
def NearestRounding.even : NearestRounding where
  run := roundRatEven
  adjacent x := by
    rw [roundRatEven_eq_floor_ceil]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · split
        · exact Or.inr rfl
        · split
          · exact Or.inl rfl
          · exact Or.inr rfl
  nearest := roundRatEven_nearest

/-- Every permitted adjacent choice fixes integers. -/
@[simp] theorem Rounding.run_intCast (rounding : Rounding) (k : Int) :
    rounding.run (k : ℚ) = k := by
  rcases rounding.adjacent (k : ℚ) with h | h <;>
    simpa only [Rat.floor_intCast, Rat.ceil_intCast] using h

/-- An integral lower bound also bounds either adjacent rounding choice. -/
theorem Rounding.int_le_run (rounding : Rounding) {x : ℚ} {k : Int}
    (h : (k : ℚ) ≤ x) : k ≤ rounding.run x := by
  rcases rounding.adjacent x with he | he
  · rw [he]
    exact Rat.le_floor_iff.mpr h
  · rw [he]
    exact_mod_cast h.trans Rat.le_ceil

/-- An integral upper bound also bounds either adjacent rounding choice. -/
theorem Rounding.run_le_int (rounding : Rounding) {x : ℚ} {k : Int}
    (h : x ≤ (k : ℚ)) : rounding.run x ≤ k := by
  rcases rounding.adjacent x with he | he
  · rw [he]
    exact_mod_cast (Rat.floor_le x).trans h
  · rw [he]
    exact Rat.ceil_le_iff.mpr h

/-- Adjacent rounding cannot escape an interval with integral endpoints. -/
theorem Rounding.in_range (rounding : Rounding) (range : IntegerRange) {x : ℚ}
    (h : (range.lower : ℚ) ≤ x ∧ x ≤ (range.upper : ℚ)) :
    range.Contains (rounding.run x) :=
  ⟨rounding.int_le_run h.1, rounding.run_le_int h.2⟩

/-- Every nearest choice, including arbitrary midpoint choices, has at most half-unit error. -/
theorem NearestRounding.error_le_half (rounding : NearestRounding) (x : ℚ) :
    |(rounding.run x : ℚ) - x| ≤ 1 / 2 :=
  (rounding.nearest x (roundRatEven x)).trans (roundRatEven_error_le_half x)

end FloatLib.Floats.Formats.FixedPoint.Embedded
