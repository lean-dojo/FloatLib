/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Comparison.Runtime
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime

/-!
# Exactly rounded integer roots of posits

For positive degree, raising a nonnegative candidate to that degree preserves order. Exact
rational powers therefore decide which side of every posit rounding boundary contains the root,
even when the root is irrational. The shared comparator rounder supplies the bisection, saturation,
and appended-bit tie rule. Negative degrees invert the exact radicand before the search.

## Reference

* [Posit Standard (2022), §§4.1, 5.1 and 5.8](https://posithub.org/docs/posit_standard-2.pdf)
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

namespace RootRounding

/--
Compare a nonnegative root with a rational candidate using exact integer powers.

For positive degree and nonnegative radicand, this is real comparison with the root. Negative
candidates lie below it. At zero, compare the radicand with zero directly, preserving zero and
nonpositive-input handling even outside the positive-degree contract.
-/
@[inline] def compareRoot (radicand : Rat) (degree : Nat) (candidate : Rat) : Ordering :=
  if candidate < 0 then .gt
  else if candidate = 0 then cmp radicand 0
  else cmp radicand (candidate ^ degree)

/-- Model-valued exact root rounding, with positive degree as its semantic domain. -/
@[inline] def round (format : Format) (radicand : Rat) (degree : Nat) : Model format :=
  ComparisonRounding.round format (compareRoot radicand degree)

end RootRounding

/--
Integer root, rounded once, choosing the nonnegative root for even degrees and the signed real
root for odd degrees. NaR inputs, degree zero, negative inputs with even degree, and zero inputs
with negative degree produce NaR.
-/
@[inline] def rootN {format : Format} (value : Model format) (degree : Int) : Model format :=
  match value.toRat? with
  | none => nar format
  | some q =>
    if degree = 0 then nar format
    else if q = 0 ∧ degree < 0 then nar format
    else if q < 0 ∧ degree % 2 = 0 then nar format
    else
      let radicand := if degree < 0 then |q|⁻¹ else |q|
      let root := RootRounding.round format radicand degree.natAbs
      if q < 0 then neg root else root

end FloatLib.Floats.Formats.Posit.Model
