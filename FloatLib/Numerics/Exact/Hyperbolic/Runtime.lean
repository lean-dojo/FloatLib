/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
-- architecture: allow-proof-imports
Adaptive comparisons require erased proofs that some rational enclosure separates the boundary.
-/

module

public import FloatLib.Numerics.Exact.Elementary.Runtime
public import FloatLib.Numerics.Enclosure.Hyperbolic.Proof

/-!
# Exact comparisons for hyperbolic functions

Inverse hyperbolic tangent reduces to a logarithm of an exact rational ratio. Hyperbolic
tangent uses the same comparison in reverse. Neither operation constructs an exponential
at the input, so large rational arguments do not produce exponentially large integers.

Hyperbolic sine and cosine first compare the exponential with a rational bound using a
logarithm. Only unresolved cases construct exponential enclosures; in those cases the
exponential lies in a rational interval of width one around twice the comparison boundary.
-/

@[expose] public section

namespace FloatLib.Numerics.HyperbolicComparison

/-- Compare `artanh argument` with a rational boundary on its open real domain. -/
def compareArtanh (argument boundary : ℚ) (hlower : -1 < argument) (hupper : argument < 1) :
    Ordering :=
  ElementaryComparison.compareLog ((1 + argument) / (1 - argument)) (2 * boundary)
    (div_pos (by linarith) (by linarith))

/-- Compare hyperbolic tangent with a rational boundary, using its inverse on `(-1, 1)`. -/
def compareTanh (argument boundary : ℚ) : Ordering :=
  if hlower : -1 < boundary then
    if hupper : boundary < 1 then
      (compareArtanh boundary argument hlower hupper).swap
    else .lt
  else .gt

/--
Compare positive-argument hyperbolic sine using the bounds `0 < exp (-x) < 1`.
Only `2 * boundary < exp x < 2 * boundary + 1` requires exponential enclosures.
-/
def compareSinhPositive (argument boundary : ℚ) (hpositive : 0 < argument) : Ordering :=
  if boundary ≤ 0 then .gt
  else if ElementaryComparison.compareExp argument (2 * boundary + 1) = .lt then
    if ElementaryComparison.compareExp argument (2 * boundary) = .gt then
      Enclosure.Comparison.compare (fun n => Enclosure.sinh argument (2 ^ n)) boundary
        (Enclosure.exists_sinh_separating argument boundary (ne_of_gt hpositive))
    else .lt
  else .gt

/-- Exact hyperbolic sine comparison, using odd symmetry for negative inputs. -/
def compareSinh (argument boundary : ℚ) : Ordering :=
  if hpositive : 0 < argument then compareSinhPositive argument boundary hpositive
  else if hnegative : argument < 0 then
    (compareSinhPositive (-argument) (-boundary) (neg_pos.mpr hnegative)).swap
  else cmp 0 boundary

/--
Compare positive-argument hyperbolic cosine using the bounds `0 < exp (-x) < 1`.
Only `2 * boundary - 1 < exp x < 2 * boundary` requires exponential enclosures.
-/
def compareCoshPositive (argument boundary : ℚ) (hpositive : 0 < argument) : Ordering :=
  if boundary ≤ 1 then .gt
  else if ElementaryComparison.compareExp argument (2 * boundary) = .lt then
    if ElementaryComparison.compareExp argument (2 * boundary - 1) = .gt then
      Enclosure.Comparison.compare (fun n => Enclosure.cosh argument (2 ^ n)) boundary
        (Enclosure.exists_cosh_separating argument boundary (ne_of_gt hpositive))
    else .lt
  else .gt

/-- Exact hyperbolic cosine comparison, using even symmetry and handling zero exactly. -/
def compareCosh (argument boundary : ℚ) : Ordering :=
  if hzero : argument = 0 then cmp 1 boundary
  else compareCoshPositive |argument| boundary (abs_pos.mpr hzero)

/-- Compare inverse hyperbolic sine by the globally increasing hyperbolic sine. -/
def compareArsinh (argument boundary : ℚ) : Ordering :=
  (compareSinh boundary argument).swap

/-- Compare inverse hyperbolic cosine on its nonnegative branch; callers require `argument ≥ 1`. -/
def compareArcosh (argument boundary : ℚ) : Ordering :=
  if boundary < 0 then .gt else (compareCosh boundary argument).swap

/--
Prepare inverse hyperbolic sine at a positive argument.

The two logarithmic bounds depend only on the argument. Their enclosure caches are allocated
before the boundary closure, so rounding queries share the first `levels` Taylor enclosures.
-/
def prepareArsinhPositive (argument : ℚ) (levels : Nat) (hpositive : 0 < argument) :
    Enclosure.Comparison.Prepared :=
  let upper := ElementaryComparison.prepareLog (2 * argument + 1) levels (by linarith)
  let lower := ElementaryComparison.prepareLog (2 * argument) levels (by linarith)
  .direct (fun boundary =>
    if hboundary : 0 < boundary then
      (if (upper.compare boundary).swap = .lt then
        if (lower.compare boundary).swap = .gt then
          Enclosure.Comparison.compare (fun n => Enclosure.sinh boundary (2 ^ n)) argument
            (Enclosure.exists_sinh_separating boundary argument (ne_of_gt hboundary))
        else .lt
      else .gt).swap
    else compareArsinh argument boundary)

/-- Prepare inverse hyperbolic sine, sharing logarithmic bounds and using odd symmetry. -/
def prepareArsinh (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  if hpositive : 0 < argument then prepareArsinhPositive argument levels hpositive
  else if hnegative : argument < 0 then
    let positive := prepareArsinhPositive (-argument) levels (neg_pos.mpr hnegative)
    .direct (fun boundary => (positive.compare (-boundary)).swap)
  else .direct (fun boundary => cmp 0 boundary)

/--
Prepare inverse hyperbolic cosine with shared logarithms of `2 * argument` and
`2 * argument - 1`. The real-domain contract remains `argument ≥ 1`.
-/
def prepareArcosh (argument : ℚ) (levels : Nat) : Enclosure.Comparison.Prepared :=
  if hargument : 1 < argument then
    let upper := ElementaryComparison.prepareLog (2 * argument) levels (by linarith)
    let lower := ElementaryComparison.prepareLog (2 * argument - 1) levels (by linarith)
    .direct (fun boundary =>
      if hboundary : 0 < boundary then
        (if (upper.compare boundary).swap = .lt then
          if (lower.compare boundary).swap = .gt then
            Enclosure.Comparison.compare (fun n => Enclosure.cosh boundary (2 ^ n)) argument
              (Enclosure.exists_cosh_separating boundary argument (ne_of_gt hboundary))
          else .lt
        else .gt).swap
      else compareArcosh argument boundary)
  else .direct (compareArcosh argument)

/-- Prepare inverse hyperbolic tangent, sharing the logarithm of its exact rational ratio. -/
def prepareArtanh (argument : ℚ) (levels : Nat)
    (hlower : -1 < argument) (hupper : argument < 1) : Enclosure.Comparison.Prepared :=
  let logarithm := ElementaryComparison.prepareLog ((1 + argument) / (1 - argument)) levels
    (div_pos (by linarith) (by linarith))
  .direct (fun boundary => logarithm.compare (2 * boundary))

end FloatLib.Numerics.HyperbolicComparison
