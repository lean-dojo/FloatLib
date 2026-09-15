/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Core.Runtime
public import Mathlib.Data.Rat.Cast.Order

/-!
# Finite binary32 runtime coordinates

Finite binary32 fields are converted into the mantissa-and-scale coordinates shared by native
arithmetic kernels. For every nonzero finite value, the coordinates denote its magnitude
`mantissa * 2^(scale - 149)`, with exponent subtraction in `Int`. Bounds and decoder agreement
live in `Finite.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/-- Decode a finite binary32 significand into one native word. -/
@[inline] def finiteMantissa (exponent fraction : UInt32) : UInt64 :=
  if exponent == 0 then
    fraction.toUInt64
  else
    fraction.toUInt64 ||| 0x800000

/--
Encode the finite exponent as a nonnegative scale, giving magnitude
`mantissa * 2^(scale - 149)` with exponent subtraction in `Int`.

The binary32 entry point only widens its native field; the scale rule itself is shared with every
word kernel.
-/
@[always_inline, inline] def finiteScale (exponent : UInt32) : UInt64 :=
  FloatLib.Numerics.FixedWord.finiteScale exponent.toUInt64

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
