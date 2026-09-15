/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Runtime

/-!
# Guard-and-sticky rounding for exact dyadic targets

Some packed arithmetic kernels construct an exact `Dyadic` result because their aligned sum may
require arbitrary precision. This bridge uses the fixed-carrier kernel when the significand fits
in one word and the shared arbitrary-width direct packer otherwise.

The capacity check is on the result, not the source format. Consequently the same kernel remains
correct for every posit format through 64 bits. Both branches implement the same field-oriented
guard-and-sticky semantics.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordRounding.GuardSticky.DyadicTarget

open FloatLib.Numerics

/--
Round an exact dyadic using a machine-word significand when it fits.

The dependent branch proof erases after compilation. On the accepted path, `UInt64.ofNat` is
exact. The wider path applies the same direct packer to the original arbitrary-width fields.
-/
@[inline] def roundCodeNat
    (format : Format) (heligible : NativeWord.Eligible format)
    (target : FloatLib.Numerics.Dyadic) : Nat :=
  if _hfit : target.significand < 2 ^ 64 then
    GuardSticky.roundCodeNat format heligible target.negative
      (UInt64.ofNat target.significand) target.exponent
  else
    DirectDyadicPacking.roundCode format target

end FloatLib.Floats.Formats.Posit.Model.NativeWordRounding.GuardSticky.DyadicTarget
