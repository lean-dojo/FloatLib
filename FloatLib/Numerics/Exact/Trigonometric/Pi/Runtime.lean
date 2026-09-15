/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
-- architecture: allow-proof-imports
Adaptive comparisons carry erased proofs that interval refinement terminates.
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.Pi.Termination
public import FloatLib.Numerics.Exact.Trigonometric.PiValues.Inverse
public import FloatLib.Numerics.Enclosure.Comparison.Cache

/-!
# Exact comparisons for pi-scaled trigonometric functions

Exact rational-angle classifiers decide every rational special value before refinement.
Sine and cosine first remove full turns exactly, so their classifiers and interval generators
receive bounded angles even when the input has a very large integer part.
All other direct values are irrational, and converging rational intervals separate every
rational boundary. The inverse operations compare through their monotone principal branches;
the branch endpoints are rational in units of pi, so no inverse enclosure is necessary.

The numerical tangent helper agrees with Mathlib's totalized tangent, which is zero at a pole.
A format operation must reject half-integer tangent arguments before using this helper when
its contract requires an invalid result there. Inverse sine/cosine contracts require `[-1, 1]`.
-/

@[expose] public section

namespace FloatLib.Numerics.TrigonometricComparison

/-- Prepare exact pi-scaled sine comparisons, with complete rational special-value handling. -/
def prepareSinPi (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  let reduced := Enclosure.piReduced argument
  match hvalue : sinPiExact reduced with
  | some value => .direct (fun boundary => cmp value boundary)
  | none =>
    let intervals := Enclosure.Comparison.cacheIntervals
      (fun n => Enclosure.sinPi reduced (2 ^ n)) levels
    .enclosed intervals (fun boundary => by
      simpa only [intervals, Enclosure.Comparison.cacheIntervals_apply] using
        Enclosure.exists_sinPi_separating reduced boundary hvalue)

/-- Prepare exact pi-scaled cosine comparisons, including thirds and half-integer angles. -/
def prepareCosPi (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  let reduced := Enclosure.piReduced argument
  match hvalue : cosPiExact reduced with
  | some value => .direct (fun boundary => cmp value boundary)
  | none =>
    let intervals := Enclosure.Comparison.cacheIntervals
      (fun n => Enclosure.cosPi reduced (2 ^ n)) levels
    .enclosed intervals (fun boundary => by
      simpa only [intervals, Enclosure.Comparison.cacheIntervals_apply] using
        Enclosure.exists_cosPi_separating reduced boundary hvalue)

/-- Compare `sin (argument * π)` with a rational boundary. -/
def compareSinPi (argument boundary : ℚ) : Ordering :=
  (prepareSinPi argument 0).compare boundary

/-- Compare `cos (argument * π)` with a rational boundary. -/
def compareCosPi (argument boundary : ℚ) : Ordering :=
  (prepareCosPi argument 0).compare boundary

/--
Prepare pi-scaled tangent comparisons using the cosine sign and a linear residual.

The half-integer branch returns the ordering of zero, matching the totalized real tangent.
Format wrappers with an invalid-result policy at poles must perform the same exact pole test.
-/
def prepareTanPi (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  if hpole : Int.fract argument = 1 / 2 then .direct (fun boundary => cmp 0 boundary)
  else match hvalue : tanPiExact argument with
  | some value => .direct (fun boundary => cmp value boundary)
  | none =>
    let cosineSign := (prepareCosPi argument levels).compare 0
    let sines := Enclosure.Comparison.cacheIntervals
      (fun n => Enclosure.sinPi argument (2 ^ n)) levels
    let cosines := Enclosure.Comparison.cacheIntervals
      (fun n => Enclosure.cosPi argument (2 ^ n)) levels
    .direct (fun boundary =>
      let residual := Enclosure.Comparison.compare
        (fun n => (sines.get n).sub ((cosines.get n).scale boundary)) 0 (by
          simpa only [sines, cosines, Enclosure.Comparison.cacheIntervals_apply,
            Enclosure.sinPiSubCos] using
              Enclosure.exists_sinPiSubCos_separating argument boundary hpole hvalue)
      if cosineSign = .gt then residual else residual.swap)

/-- Compare the totalized real tangent at `argument * π` with a rational boundary. -/
def compareTanPi (argument boundary : ℚ) : Ordering :=
  (prepareTanPi argument 0).compare boundary

/-- Prepare inverse sine divided by pi, using rational branch bounds and direct sine comparisons. -/
def prepareArcsinPi (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  match arcsinPiExact argument with
  | some value => .direct (fun boundary => cmp value boundary)
  | none => .direct (fun boundary =>
      if boundary < -1 / 2 then .gt
      else if 1 / 2 < boundary then .lt
      else ((prepareSinPi boundary levels).compare argument).swap)

/-- Compare `arcsin argument / π` on its real domain with a rational boundary. -/
def compareArcsinPi (argument boundary : ℚ) : Ordering :=
  (prepareArcsinPi argument 0).compare boundary

/-- Prepare inverse cosine divided by pi, comparing cosine on its decreasing `[0, π]` branch. -/
def prepareArccosPi (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  match arccosPiExact argument with
  | some value => .direct (fun boundary => cmp value boundary)
  | none => .direct (fun boundary =>
      if boundary < 0 then .gt
      else if 1 < boundary then .lt
      else (prepareCosPi boundary levels).compare argument)

/-- Compare `arccos argument / π` on its real domain with a rational boundary. -/
def compareArccosPi (argument boundary : ℚ) : Ordering :=
  (prepareArccosPi argument 0).compare boundary

/-- Prepare inverse tangent divided by pi, whose branch is the open interval `(-1/2, 1/2)`. -/
def prepareArctanPi (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  match arctanPiExact argument with
  | some value => .direct (fun boundary => cmp value boundary)
  | none => .direct (fun boundary =>
      if boundary ≤ -1 / 2 then .gt
      else if 1 / 2 ≤ boundary then .lt
      else ((prepareTanPi boundary levels).compare argument).swap)

/-- Compare `arctan argument / π` with any rational boundary. -/
def compareArctanPi (argument boundary : ℚ) : Ordering :=
  (prepareArctanPi argument 0).compare boundary

end FloatLib.Numerics.TrigonometricComparison
