/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Termination
public import FloatLib.Numerics.Enclosure.Comparison.Cache

/-!
# Exact comparisons with natural logarithms and exponentials

The runtime compares rational enclosures, doubling the Taylor degree until the ordering is
known. The imported termination proof is erased during compilation.

`compareExp` uses `exp x < y ↔ x < log y` for positive `y`. This avoids materializing an
enormous exponential when the destination will saturate. `prepareExp` instead caches direct
exponential enclosures for arguments in `[-8, 8]`, and uses the logarithmic comparison outside
that interval.
-/

@[expose] public section

namespace FloatLib.Numerics.ElementaryComparison

/-- Compare the natural logarithm of a positive rational with a rational boundary. -/
def compareLog (argument boundary : ℚ) (hpositive : 0 < argument) : Ordering :=
  if hone : argument = 1 then cmp 0 boundary
  else Enclosure.Comparison.compare
    (fun n => Enclosure.log argument (2 ^ n)) boundary
    (Enclosure.exists_log_separating argument boundary hpositive hone)

/-- Compare a rational-input exponential with any rational boundary. -/
def compareExp (argument boundary : ℚ) : Ordering :=
  if hpositive : 0 < boundary then
    (compareLog boundary argument hpositive).swap
  else .gt

/--
Prepare a logarithm comparator that shares its first `levels` enclosures across boundaries.
Cached levels are reused across boundary queries; levels beyond this prefix are computed on demand.
-/
def prepareLog (argument : ℚ) (levels : Nat) (hpositive : 0 < argument) :
    Enclosure.Comparison.Prepared :=
  if hone : argument = 1 then .direct (fun boundary => cmp 0 boundary)
  else
    let intervals := Enclosure.Comparison.cacheIntervals
      (fun n => Enclosure.log argument (2 ^ n)) levels
    .enclosed intervals (fun boundary => by
      simpa only [intervals, Enclosure.Comparison.cacheIntervals_apply] using
        Enclosure.exists_log_separating argument boundary hpositive hone)

/--
Prepare an exponential comparator, sharing enclosures for arguments in `[-8, 8]`.

Repeated squaring can create large rational intermediates even when the final comparison is
easy. Outside this moderate interval the logarithm-of-boundary comparison avoids that growth.
The threshold selects an algorithm; it does not restrict the function's domain or accuracy.
-/
def prepareExp (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  if hzero : argument = 0 then .direct (fun boundary => cmp 1 boundary)
  else if |argument| ≤ 8 then
    let intervals := Enclosure.Comparison.cacheIntervals
      (fun n => Enclosure.exp argument (2 ^ n)) levels
    .enclosed intervals (fun boundary => by
      simpa only [intervals, Enclosure.Comparison.cacheIntervals_apply] using
        Enclosure.exists_exp_separating argument boundary hzero)
  else .direct (compareExp argument)

end FloatLib.Numerics.ElementaryComparison
