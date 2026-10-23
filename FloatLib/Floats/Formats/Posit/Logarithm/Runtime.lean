/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Comparison.Runtime
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime
public import FloatLib.Numerics.Exact.RationalPower.Runtime

/-!
# Exactly rounded base-two and base-ten posit logarithms

For a base greater than one, comparing `log_base x` with a rational boundary `q` is equivalent
to comparing `x` with `base ^ q`. The rational-power comparator decides this exactly: it settles
equality, as in `log2 8 = 3`, by exact roots and capped exponentiation, and separates every other
boundary with proved logarithm bounds.

The `Plus1` functions form `1 + x` exactly before any rounding, so a small posit argument is
not lost by first adding it to a posit one.

Reference: Posit Standard (2022), §§4.1, 4.2, 5.1 and 5.5,
<https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

namespace Logarithm

/-- Compare the logarithm of a positive argument with a rational rounding candidate. -/
def compareTarget (base argument candidate : Rat) : Ordering :=
  (FloatLib.Numerics.RationalPower.compare base candidate argument).swap

/--
Round a rational-argument logarithm once. Nonpositive arguments produce NaR.

The mathematical domain requires `base > 1`. Each boundary comparison is the exact rational-power
comparison of the argument with `base ^ candidate`.
-/
def roundRat (format : Format) (base argument : Rat) : Model format :=
  if argument ≤ 0 then nar format
  else ComparisonRounding.roundSigned format (compareTarget base argument)

/-- Apply a logarithm after adding an exact rational offset to the decoded argument. -/
def apply {format : Format} (base offset : Rat) (value : Model format) : Model format :=
  match value.toRat? with
  | none => nar format
  | some q => roundRat format base (q + offset)

end Logarithm

/-- Base-two logarithm, rounded once. NaR and nonpositive inputs produce NaR. -/
def log2 {format : Format} (value : Model format) : Model format :=
  Logarithm.apply 2 0 value

/-- Base-two logarithm of exact `1 + x`. NaR and inputs at or below `-1` produce NaR. -/
def log2Plus1 {format : Format} (value : Model format) : Model format :=
  Logarithm.apply 2 1 value

/-- Base-ten logarithm, rounded once. NaR and nonpositive inputs produce NaR. -/
def log10 {format : Format} (value : Model format) : Model format :=
  Logarithm.apply 10 0 value

/-- Base-ten logarithm of exact `1 + x`. NaR and inputs at or below `-1` produce NaR. -/
def log10Plus1 {format : Format} (value : Model format) : Model format :=
  Logarithm.apply 10 1 value

end FloatLib.Floats.Formats.Posit.Model
