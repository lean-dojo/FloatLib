/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Exact

/-!
# Signed zero and its preferred quantum

Every zero projects exactly with the supplied sign and the preferred exponent
clamped to the representable exponent interval. No exception is raised, even
when clamping changes its representation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Stripping trailing zeros from a zero coefficient consumes all of the fuel. -/
theorem stripTrailing_zero (fuel : Nat) : stripTrailing fuel 0 = (0, fuel) := by
  cases fuel <;> simp [stripTrailing]

/-- An exact zero retains its sign and chooses the closest representable preferred exponent. -/
theorem projectMagnitude_zero (f : Format) (mode : RoundingMode) (s : Bool)
    (preferred : Int) :
    projectMagnitude f mode s 0 preferred =
      { value := .finite s 0 (max f.minQuantum (min preferred f.maxQuantum)) } := by
  simp [projectMagnitude, preferredCohort, stripTrailing_zero]
  omega

/-- An exact zero projects to a zero with the requested sign and no flags, at the preferred quantum
clamped to the format's quantum range. -/
theorem project_zero (f : Format) (mode : RoundingMode) (s : Bool) (preferred : Int) :
    project f mode 0 preferred s =
      { value := .finite s 0 (max f.minQuantum (min preferred f.maxQuantum)) } := by
  simpa [project] using projectMagnitude_zero f mode s preferred

end FloatLib.Floats.Formats.DecimalInterchange
