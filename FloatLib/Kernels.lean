/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord
public import FloatLib.Kernels.LimbArray.Shift.Proof

/-!
# Verified execution kernels

Every execution backend ends up doing the same integer work: shifting a significand with
nearest-even rounding, dividing two of them, taking a square root, adding with a carry across limbs.
The kernels are those shared algorithms. They cover nearest-even shifts and quotients, two- and
four-limb addition and multiplication, restoring division and square root, and the comparison and
normalisation helpers built on them. Runtime modules implement them over `UInt64`, `UInt128`, and
`UInt256`, and each proof module relates the result to a natural-number or exact-value
specification. `LimbArray` is the runtime-sized counterpart, with in-place addition, subtraction,
schoolbook multiplication, shifts, and nearest-even rounding over arrays of 32-bit limbs, each
specified by its effect on the array's value.

A kernel knows nothing about a particular format. Its caller handles format-specific decoding,
rounding policies, exceptional values, and packing, and
`FloatLib/Floats/ExecFloat/Backends/README.md` catalogues the backends that do this and the formats
each one serves. Import this collection when you implement a backend, or `FloatLib` for the
application API.

Importing this module changes how the compiler treats some standard-library functions. The
`@[csimp]` theorems in `FixedWord.Core.Proof.Rounding` and `FixedWord.IntegerSquareRoot.Proof` route
compiled `Numerics.roundShiftRightEven`, `Numerics.roundQuotientEven`, and `Nat.sqrt` through
native-word dispatchers:

- shifting and square root use the native kernels for values below `2^64`,
- quotient rounding needs a numerator below `2^63` and a nonzero denominator below `2^64`.

`IntegerSquareRoot.natSqrt_eq_sqrtNat` in particular affects every compiled `Nat.sqrt` in downstream
code. Each substitution is justified by a proved equation. Outside the word range, quotient rounding
uses the logical definition, shifting keeps a guard bit and tests the discarded bits only when it
has to, and square root checks an increasing-precision Newton candidate before falling back to
`Nat.sqrt.iter`.
-/

@[expose] public section
