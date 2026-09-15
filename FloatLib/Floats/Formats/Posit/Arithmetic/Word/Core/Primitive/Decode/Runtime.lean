/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Fields.Runtime

/-!
# Native-word posit decoding

Candidate, finite, and total decoders read posit encodings stored in `UInt64`. Their storage and
range refinements live in
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
