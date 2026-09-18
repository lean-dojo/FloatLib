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

Kernels are the integer and fixed-word algorithms shared by every execution backend: nearest-even
shifts and quotients, two- and four-limb addition and multiplication, restoring division and
square root, and the comparison and normalisation helpers built on them. Runtime modules contain
the implementations over `UInt64`, `UInt128`, and `UInt256`; their proof modules relate each
result to a natural-number or exact-value specification. `LimbArray` adds the runtime-sized
counterpart: in-place addition, subtraction, schoolbook multiplication, shifts, and nearest-even
rounding over arrays of 32-bit limbs, each specified by its effect on the array's value.

Kernels know nothing about a particular format. Callers handle format-specific decoding, rounding
policies, exceptional values, and packing. The backends that do so, and the formats each one
serves, are catalogued in `FloatLib/Floats/ExecFloat/Backends/README.md`. Import this collection
when implementing a backend, or `FloatLib` for the application API.

Importing this module changes how the compiler treats some standard-library functions. The
`@[csimp]` theorems in `FixedWord.Core.Proof.Rounding` and `FixedWord.IntegerSquareRoot.Proof`
route compiled `Numerics.roundShiftRightEven`, `Numerics.roundQuotientEven`, and `Nat.sqrt`
through native-word dispatchers. Shifting and square root use the native kernels for values
below `2^64`; quotient rounding requires a numerator below `2^63` and a nonzero denominator
below `2^64`. In particular, `IntegerSquareRoot.natSqrt_eq_sqrtNat` affects every compiled
`Nat.sqrt` in downstream code. Each substitution is justified by a proved equation, and the
arbitrary-precision branch of each replacement is the unchanged logical definition.
-/

@[expose] public section
