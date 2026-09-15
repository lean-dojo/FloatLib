/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Candidate.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Spec.Fields
public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Runtime

/-!
# Executable direct exact-dyadic posit packing

Direct posit packing rounds the normalized exact-dyadic bit stream in one pass:

* the exact binary scale determines the standard two-bit-exponent regime;
* the regime, exponent, and normalized fraction are emitted most-significant bit first;
* one shared guard-and-sticky kernel performs nearest-even rounding at every width.

Direct packing avoids the reference rounder's search. Its equality to the exact model is proved
in `Direct.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DirectDyadicPacking

open FloatLib.Numerics

/--
Round a positive exact dyadic directly from its normalized bit stream.

Interior values use one general guard/sticky kernel for every width. Regimes that consume the
entire payload map directly to `maxPos` or `minPos`.
-/
@[inline] def roundPositiveCode
    (format : Format) (target : FloatLib.Numerics.Dyadic) : Nat :=
  if target.significand == 0 || target.negative then
    0
  else
    let leading := leadingBit target.significand
    let minScale := -(4 * Int.ofNat (format.payloadBits - 1))
    if Dyadic.isLessPowerOfTwoAtLeading
        target.significand target.exponent leading minScale then
      1
    else
      let scale := target.exponent + Int.ofNat leading
      let regime := scale.ediv 4
      let exponentField := (scale.emod 4).toNat
      if 0 ≤ regime then
        let run := regime.toNat + 1
        if format.payloadBits ≤ run then
          format.signMaskNat - 1
        else
          GuardStickyRounding.roundInteriorCodeFromFields format regime exponentField
            target.significand leading (run + 1)
      else
        let run := (-regime).toNat
        -- Unreachable: a negative regime long enough to fill the payload puts the value below
        -- `minPositive`, which the `isLessPowerOfTwoAtLeading` test above already sent to code 1.
        -- The branch is kept so the match on the run length is total without a proof argument.
        if format.payloadBits ≤ run then
          1
        else
          GuardStickyRounding.roundInteriorCodeFromFields format regime exponentField
            target.significand leading (run + 1)

/-- Pack a positive exact dyadic with the direct guard-and-sticky constructor. -/
@[inline] def roundPositive
    (format : Format) (target : FloatLib.Numerics.Dyadic) : Model format :=
  Model.ofNatBits (roundPositiveCode format target)

/--
Return the complete signed Posit encoding of an exact dyadic.

The positive magnitude is packed by the shared arbitrary-width guard/sticky kernel. Sign
restoration is the standard whole-word two's complement, with exact zero kept unique.
-/
@[noinline] def roundCode
    (format : Format) (value : FloatLib.Numerics.Dyadic) : Nat :=
  if value.significand == 0 then
    0
  else
    let magnitude := DyadicRounding.magnitude value
    let positiveCode := roundPositiveCode format magnitude
    DyadicRounding.restoreSignCode format value.negative positiveCode

/--
Round any exact dyadic through the direct positive packer and whole-word sign restoration.

Exact zero remains the unique unsigned zero. A negative nonzero result uses the Posit Standard
(2022)'s whole-word two's-complement symmetry.
-/
@[noinline] def round
    (format : Format) (value : FloatLib.Numerics.Dyadic) : Model format :=
  if value.significand == 0 then
    Model.zero format
  else
    let magnitude := DyadicRounding.magnitude value
    if value.negative then
      Model.neg (roundPositive format magnitude)
    else
      roundPositive format magnitude

end FloatLib.Floats.Formats.Posit.Model.DirectDyadicPacking
