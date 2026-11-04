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

Flocq, the Coq library of Boldo and Melquiond, describes a format by the set of reals it can
represent, through an exponent function, with no bit layout involved. This family brings that
approach to FloatLib in three parts: a theorem library about rounded reals, calculations on
mantissa and exponent representations, and an embedding into FloatLib's representation-independent
format and quantization interfaces.

## References

* S. Boldo and G. Melquiond, “Flocq: A Unified Library for Proving Floating-Point
  Algorithms in Coq,” ARITH 2011, DOI 10.1109/ARITH.2011.40.
* Flocq project documentation and source,
  <https://flocq.gitlabpages.inria.fr/flocq/>.

## Calculation

The calculation layer turns the generic format theory into something you can compute with. It has
exact mantissa and exponent operations, it brackets a value at a chosen exponent, and it applies
directed or nearest rounding. Each calculation is related back to the abstract format and rounding
laws of `Theory`, which these modules build on.
-/

@[expose] public section
