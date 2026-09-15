/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory
public import FloatLib.Floats.Formats.Flocq.Calculation.Bracket
public import FloatLib.Floats.Formats.Flocq.Calculation.Arithmetic
public import FloatLib.Floats.Formats.Flocq.Calculation.Operations
public import FloatLib.Floats.Formats.Flocq.Calculation.Round
public import FloatLib.Floats.Formats.Flocq.GenericFormat

/-!
# Flocq-style numerical format family

Flocq-style formats combine a rounded-real theorem library, representation-level calculations,
and a semantic embedding into FloatLib's representation-independent format and quantization
interfaces.

## References

* S. Boldo and G. Melquiond, “Flocq: A Unified Library for Proving Floating-Point
  Algorithms in Coq,” ARITH 2011, DOI 10.1109/ARITH.2011.40.
* Flocq project documentation and source,
  <https://flocq.gitlabpages.inria.fr/flocq/>.

## Calculation

This layer turns the generic Flocq-style format theory into calculations. It provides exact
mantissa/exponent operations, brackets values at a chosen exponent, and applies
directed or nearest rounding.

The calculation modules build on `Theory`, relating mantissa/exponent calculations to the abstract
format and rounding laws.
-/

@[expose] public section
