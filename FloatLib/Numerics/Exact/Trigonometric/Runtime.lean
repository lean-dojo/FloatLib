/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

-- architecture: allow-proof-imports
-- Adaptive comparisons carry erased proofs that refinement eventually separates the boundary.
module

public import FloatLib.Numerics.Enclosure.Trigonometric.Termination
public import FloatLib.Numerics.Enclosure.Comparison.Cache

/-!
# Total comparisons for ordinary trigonometric functions

These operations compare an exact trigonometric value with a rational boundary. Adaptive
rational enclosures determine the ordering; irrationality proves that the search terminates
outside the explicitly handled rational values at zero. Prepared comparators share a finite
prefix of enclosures across boundary queries, with unrestricted refinement beyond that prefix.

Tangent compares `sin x - b * cos x` with zero and uses the sign of cosine. Inverse sine and
cosine compare through their monotone principal branches, after exact comparisons with π
locate the boundary. Their real-domain contract is `-1 ≤ argument ≤ 1`.

These are ordinary radian functions. No rational-angle equality decision for π-scaled
functions is inferred from these searches.
-/

@[expose] public section

namespace FloatLib.Numerics.TrigonometricComparison

/-- Prepare a total sine comparator, sharing reduced enclosures across rational boundaries. -/
def prepareSin (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  if hzero : argument = 0 then .direct (fun boundary => cmp 0 boundary)
  else
    let intervals := Enclosure.Comparison.cacheIntervals
      (fun n => Enclosure.sinReduced argument (2 ^ n)) levels
    .enclosed intervals (fun boundary => by
      simpa only [intervals, Enclosure.Comparison.cacheIntervals_apply] using
        Enclosure.exists_sin_separating argument boundary hzero)

/-- Prepare a total cosine comparator, including the exact value `cos 0 = 1`. -/
def prepareCos (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  if hzero : argument = 0 then .direct (fun boundary => cmp 1 boundary)
  else
    let intervals := Enclosure.Comparison.cacheIntervals
      (fun n => Enclosure.cosReduced argument (2 ^ n)) levels
    .enclosed intervals (fun boundary => by
      simpa only [intervals, Enclosure.Comparison.cacheIntervals_apply] using
        Enclosure.exists_cos_separating argument boundary hzero)

/-- Prepare a total arctangent comparator, with exact equality at zero. -/
def prepareArctan (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  if hzero : argument = 0 then .direct (fun boundary => cmp 0 boundary)
  else
    let intervals := Enclosure.Comparison.cacheIntervals
      (fun n => Enclosure.atan argument (2 ^ n)) levels
    .enclosed intervals (fun boundary => by
      simpa only [intervals, Enclosure.Comparison.cacheIntervals_apply] using
        Enclosure.exists_atan_separating argument boundary hzero)

/-- Compare the sine of any rational argument with any rational boundary. -/
def compareSin (argument boundary : ℚ) : Ordering :=
  (prepareSin argument 0).compare boundary

/-- Compare the cosine of any rational argument with any rational boundary. -/
def compareCos (argument boundary : ℚ) : Ordering :=
  (prepareCos argument 0).compare boundary

/-- Compare the arctangent of any rational argument with any rational boundary. -/
def compareArctan (argument boundary : ℚ) : Ordering :=
  (prepareArctan argument 0).compare boundary

/--
Prepare tangent comparisons without interval division.

Rational arguments are never tangent poles. The cosine sign and the cached sine/cosine
enclosures are shared across queries, while each boundary determines a different residual.
-/
def prepareTan (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  if hzero : argument = 0 then .direct (fun boundary => cmp 0 boundary)
  else
    let sines := Enclosure.Comparison.cacheIntervals
      (fun n => Enclosure.sinReduced argument (2 ^ n)) levels
    let cosines := Enclosure.Comparison.cacheIntervals
      (fun n => Enclosure.cosReduced argument (2 ^ n)) levels
    let cosineSign := Enclosure.Comparison.compare cosines.get 0 (by
      simpa only [cosines, Enclosure.Comparison.cacheIntervals_apply] using
        Enclosure.exists_cos_separating argument 0 hzero)
    .direct (fun boundary =>
      let residual := Enclosure.Comparison.compare
        (fun n => (sines.get n).sub ((cosines.get n).scale boundary)) 0 (by
          simpa only [sines, cosines, Enclosure.Comparison.cacheIntervals_apply,
            Enclosure.sinSubCos] using
              Enclosure.exists_sinSubCos_separating argument boundary hzero)
      if cosineSign = .gt then residual else residual.swap)

/-- Compare the tangent of any rational argument with any rational boundary. -/
def compareTan (argument boundary : ℚ) : Ordering :=
  (prepareTan argument 0).compare boundary

/--
Prepare inverse sine comparisons on `[-1, 1]`, sharing the π/4 enclosures.

Boundaries outside the principal branch are decided first. Inside it, sine is strictly
increasing, so the inverse comparison reduces to a direct sine comparison with reversed order.
-/
def prepareArcsin (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  let quarter := prepareArctan 1 levels
  .direct (fun boundary =>
    if quarter.compare (boundary / 2) = .lt then .lt
    else if quarter.compare (-boundary / 2) = .lt then .gt
    else (compareSin boundary argument).swap)

/-- Compare inverse sine on its real domain with any rational boundary. -/
def compareArcsin (argument boundary : ℚ) : Ordering :=
  (prepareArcsin argument 0).compare boundary

/--
Prepare inverse cosine comparisons on `[-1, 1]`, sharing the π/4 enclosures.

The principal branch is `[0, π]`, where cosine is strictly decreasing.
-/
def prepareArccos (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  let quarter := prepareArctan 1 levels
  .direct (fun boundary =>
    if boundary < 0 then .gt
    else if quarter.compare (boundary / 4) = .lt then .lt
    else compareCos boundary argument)

/-- Compare inverse cosine on its real domain with any rational boundary. -/
def compareArccos (argument boundary : ℚ) : Ordering :=
  (prepareArccos argument 0).compare boundary

end FloatLib.Numerics.TrigonometricComparison
