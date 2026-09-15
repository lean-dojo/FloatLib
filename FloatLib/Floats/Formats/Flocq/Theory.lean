/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Neighbors
public import FloatLib.Floats.Formats.Flocq.Theory.Analysis.StandardUlp
public import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Sterbenz
public import FloatLib.Floats.Formats.Flocq.Theory.Analysis.SterbenzFLT
public import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Ulp
public import FloatLib.Floats.Formats.Flocq.Theory.Arithmetic
public import FloatLib.Floats.Formats.Flocq.Theory.Automation
public import FloatLib.Floats.Formats.Flocq.Theory.Core
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Addition
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Bounds
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Directed
public import FloatLib.Floats.Formats.Flocq.Theory.Error.DivisionSqrt
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Exactness
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Multiplication
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Relative
public import FloatLib.Floats.Formats.Flocq.Theory.Format.Digits
public import FloatLib.Floats.Formats.Flocq.Theory.Format.Formats
public import FloatLib.Floats.Formats.Flocq.Theory.Format.Generic
public import FloatLib.Floats.Formats.Flocq.Theory.Format.Magnitude
public import FloatLib.Floats.Formats.Flocq.Theory.Format.Theorems
public import FloatLib.Floats.Formats.Flocq.Theory.NumericalSystem
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Away
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Core
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Double
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Generic
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Nearest
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Odd
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Order
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Predicates
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Properties
public import FloatLib.Floats.Formats.Flocq.Theory.Scalar.NF
public import FloatLib.Floats.Formats.Flocq.Theory.Scalar.Representable
public import FloatLib.Floats.Formats.Flocq.Theory.Special.FTZ

/-!
# Flocq-style rounded-real theory

This umbrella exports the radix-parametric format and rounding theory, exact mantissa/exponent
negation and multiplication, and the rounded scalar `NF`. The theory is independent of concrete
IEEE bit encodings. Its main definitions are `FloatRep`, `genericFormat`, `round`, `ulp`, and
`bpow`.

Import a child module for a smaller dependency set; import this module for the full theory.

## Analysis

The `Analysis` modules provide ULP functions, adjacent representable values, and Sterbenz
exact-subtraction results. The
representability of the rounded-addition error, which is the specification of the TwoSum and
FastTwoSum error-free transformations, is proved in `Theory.Error.Addition`; the operation-level
exactness of those algorithms is not formalized.

## Error

The `Error` modules collect the generic error results used by format-specific
`BinaryInterchange.Model.roundAt` theorems, runtime-refinement proofs, verifier margins, and
numerical analyses.

## Format

The `Format` modules develop magnitude, exponent selection, and representability, following
Flocq's generic-format organization. A client that only needs a format predicate can import its
defining module without the rounding and error theory.

## Rounding

The `Rounding` modules contain rounding functions and their semantic laws: directed modes, nearest
choices, order properties, round-to-odd, round-away, and double rounding. A format supplies the
representable grid and a rounding policy selects a point on that grid.

## Scalar

`NF` is the scalar-facing interface to generic rounding. This folder keeps the carrier and its
representability invariant together. The raw carrier may contain any real value; statements that
require membership in the declared grid use `NF.IsRepresentable` explicitly.

## References

- S. Boldo and G. Melquiond, "Flocq: A Unified Library for Proving Floating-Point Algorithms in
  Coq," *IEEE ARITH*, 2011, doi:10.1109/ARITH.2011.40.
- IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE 754-2019, Sections 4 and 7.
- P. H. Sterbenz, *Floating-Point Computation*, Prentice-Hall, 1974.
- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, second edition, SIAM, 2002.
- D. Goldberg, "What Every Computer Scientist Should Know About Floating-Point Arithmetic,"
  *ACM Computing Surveys* 23(1), 1991, doi:10.1145/103162.103163.
-/

@[expose] public section
