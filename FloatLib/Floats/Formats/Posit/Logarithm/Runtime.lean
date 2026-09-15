/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Comparison.Runtime
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime
public import FloatLib.Numerics.Exact.RationalPower.Enclosure.Runtime

/-!
# Exactly rounded base-two and base-ten posit logarithms

For a base greater than one, comparing `log_base x` with a rational boundary `q` is equivalent
to comparing `x` with `base ^ q`. The rational-power comparator decides this exactly, using
proved logarithm bounds first and exact algebraic comparison when necessary.

The `Plus1` functions form `1 + x` exactly before any rounding. In particular a small posit
argument is not lost by first adding it to a posit representation of one.

Reference: Posit Standard (2022), §§4.1, 4.2, 5.1 and 5.5,
<https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

namespace Logarithm

/-- Compare the logarithm of a positive argument with a rational rounding candidate. -/
def compareTarget (base argument candidate : Rat) (degree : Nat) : Ordering :=
  (FloatLib.Numerics.RationalPower.compareWithEnclosure base candidate argument degree).swap

/--
Round a rational-argument logarithm once; nonpositive arguments produce NaR.

The mathematical domain requires `base > 1`. The preliminary series degree follows the target
width; correctness does not depend on this choice because an inconclusive bound uses exact
algebraic comparison. Such fallback cases may require large intermediate integers.
-/
def roundRat (format : Format) (base argument : Rat) : Model format :=
  if argument ≤ 0 then nar format
  else ComparisonRounding.roundSigned format
    (fun candidate => compareTarget base argument candidate (format.bits + 8))

/-- Apply a logarithm after adding an exact rational offset to the decoded argument. -/
def apply {format : Format} (base offset : Rat) (value : Model format) : Model format :=
  match value.toRat? with
  | none => nar format
  | some q => roundRat format base (q + offset)

end Logarithm

/-- Base-two logarithm, rounded once; NaR and nonpositive inputs produce NaR. -/
def log2 {format : Format} (value : Model format) : Model format :=
  Logarithm.apply 2 0 value

/-- Base-two logarithm of exact `1 + x`; NaR and inputs at or below `-1` produce NaR. -/
def log2Plus1 {format : Format} (value : Model format) : Model format :=
  Logarithm.apply 2 1 value

/-- Base-ten logarithm, rounded once; NaR and nonpositive inputs produce NaR. -/
def log10 {format : Format} (value : Model format) : Model format :=
  Logarithm.apply 10 0 value

/-- Base-ten logarithm of exact `1 + x`; NaR and inputs at or below `-1` produce NaR. -/
def log10Plus1 {format : Format} (value : Model format) : Model format :=
  Logarithm.apply 10 1 value

end FloatLib.Floats.Formats.Posit.Model
