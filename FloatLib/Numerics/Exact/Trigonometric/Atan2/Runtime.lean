/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
-- architecture: allow-proof-imports
Adaptive argument comparison uses an erased proof that rational enclosures eventually separate.
-/

module

public import FloatLib.Numerics.Exact.Trigonometric.Atan2.Enclosure.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Pi.Runtime

/-!
# Exact comparisons for two-coordinate arctangent

The input order is `(x, y)`, giving the principal argument of `x + i*y` in `(-π, π]`.
Ordinary comparisons share reduced arctangent and π enclosures across rounding boundaries.
Comparisons in units of π use the exact rational quadrant shift and the pi-scaled arctangent
comparator, including its rational special values.

Both comparators use zero as the value at the origin, matching Mathlib's totalized argument.
Posit wrappers must reject `(0, 0)` before rounding, as required by the Posit Standard.

## Reference

* Posit Standard (2022), §5.5 and footnote 11, https://posithub.org/docs/posit_standard-2.pdf
-/

@[expose] public section

namespace FloatLib.Numerics.TrigonometricComparison

/--
Prepare comparisons of `arg (x + i*y)` with rational boundaries.
The first `levels` enclosure depths are cached; refinement beyond that prefix remains unbounded.
-/
def prepareAtan2 (x y : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  if hzero : 0 ≤ x ∧ y = 0 then .direct (fun boundary => cmp 0 boundary)
  else
    let intervals := Enclosure.Comparison.cacheIntervals
      (fun n => atan2Interval x y (2 ^ n)) levels
    .enclosed intervals (fun boundary => by
      simpa only [intervals, Enclosure.Comparison.cacheIntervals_apply] using
        exists_atan2_separating x y boundary hzero)

/-- Compare the principal argument of `x + i*y` with a rational radian boundary. -/
def compareAtan2 (x y boundary : ℚ) : Ordering :=
  (prepareAtan2 x y 0).compare boundary

/--
Prepare comparisons of `arg (x + i*y) / π`, using an exact rational quadrant shift.
No rounded approximation to π and no intermediate rounding enters the comparison.
-/
def prepareAtan2Pi (x y : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  let reduced := atan2Reduction x y
  let arctangent := prepareArctanPi reduced.1 levels
  let shift := reduced.2 / 4
  .direct (fun boundary => arctangent.compare (boundary - shift))

/-- Compare the principal argument of `x + i*y`, divided by π, with a rational boundary. -/
def compareAtan2Pi (x y boundary : ℚ) : Ordering :=
  (prepareAtan2Pi x y 0).compare boundary

end FloatLib.Numerics.TrigonometricComparison
