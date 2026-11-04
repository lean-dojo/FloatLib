/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Fields.Runtime

/-!
# Native-word posit decoding

Posit words stored in a `UInt64` are decoded here. `decodeFinite` takes a word known to be finite
and nonzero, and the total decoder `toDyadic?` takes any word, giving `none` for NaR and the
canonical exact-dyadic zero for zero. Their storage and range refinements, along with those of the
candidate decoder, are in
`FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Decode.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWord

/-- Decode a known nonzero finite native posit word. -/
@[inline] def decodeFinite (format : Format) (code : UInt64) :
    FloatLib.Numerics.Dyadic :=
  let negative := decide (format.signMaskNat ≤ code.toNat)
  let magnitude := UInt64.ofNat (magnitudeNat format code)
  { nonnegativeDyadicAt format magnitude with negative }

/--
Total direct decoder for one stored native posit word.

NaR is returned as `none`, zero uses the canonical exact-dyadic zero, and every other word takes
the direct finite decoder.
-/
@[noinline] def toDyadic? (format : Format) (code : UInt64) :
    Option FloatLib.Numerics.Dyadic :=
  if code.toNat == format.signMaskNat then
    none
  else if code == 0 then
    some FloatLib.Numerics.Dyadic.zero
  else
    some (decodeFinite format code)

end FloatLib.Floats.Formats.Posit.Model.NativeWord
