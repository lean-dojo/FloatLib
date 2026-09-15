/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import all Init.Data.Fin.Log2
import all Init.Data.UInt.Log2
public import FloatLib.Floats.Formats.Posit.Descriptor
public import FloatLib.Numerics.Exact.Dyadic.Basic

/-!
# Executable direct posit candidate generation

Direct candidate generation constructs a proposed lower posit code from a normalized exact
dyadic. It contains only executable field extraction and packing. The accompanying proof module
records the field and range properties reused by the direct guard-and-sticky rounder.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DirectDyadicPacking

open FloatLib.Numerics

/--
Return the index of the leading one bit, or zero for a zero significand, using the native word
primitive whenever the significand fits in `UInt64`.

Wider significands use exact `Nat.log2`, so the operation remains total at every format width.
-/
@[inline] def leadingBit (value : Nat) : Nat :=
  if h : value < UInt64.size then
    (UInt64.ofNatLT value h).log2.toNat
  else
    value.log2

/--
Take the first `count` normalized fraction bits after the leading one.

`leading` is `Nat.log2 significand`. When more bits are requested than the integer significand
stores, the exact dyadic expansion is padded with zeros rather than converted through `Rat`.
-/
@[inline] def fractionPrefix
    (significand leading count : Nat) : Nat :=
  let fraction := significand - (1 <<< leading)
  if count ≤ leading then
    fraction >>> (leading - count)
  else
    fraction <<< (count - leading)

/--
Take the first `count` bits of the standard exponent/fraction tail.

The Posit Standard (2022) fixes the maximum exponent field at two bits. Tapering removes its low
bits first, so a short tail keeps the most-significant exponent bits. Any remaining positions are
filled by the normalized dyadic fraction.
-/
@[inline] def tailPrefix
    (exponentField significand leading count : Nat) : Nat :=
  if count ≤ 2 then
    exponentField >>> (2 - count)
  else
    (exponentField <<< (count - 2)) +
      fractionPrefix significand leading (count - 2)

/--
Pack already normalized regime, exponent, and significand fields into the unsigned lower code.

Separating normalization from layout gives native-word and fixed-limb backends one common packing
boundary. The function saturates above maxPos and truncates below minPos.
-/
@[inline] def lowerCandidateFromFields
    (format : Format) (regime : Int)
    (exponentField significand leading : Nat) : Nat :=
  let payload := format.payloadBits
  if 0 ≤ regime then
    let run := regime.toNat + 1
    if payload ≤ run then
      format.signMaskNat - 1
    else
      let trailing := payload - run - 1
      (((1 <<< run) - 1) <<< (payload - run)) +
        tailPrefix exponentField significand leading trailing
  else
    let run := (-regime).toNat
    if payload ≤ run then
      0
    else
      let trailing := payload - run - 1
      (1 <<< trailing) +
        tailPrefix exponentField significand leading trailing

/--
Construct the unsigned lower posit candidate directly from a positive exact dyadic.

The function is total. Zero and negative carriers return zero; magnitudes above maxPos produce
the all-ones positive payload; magnitudes below minPos produce zero. The public rounder handles
the standard's nonzero-underflow-to-minPos rule before consulting this candidate.
-/
@[inline] def lowerCandidate (format : Format) (target : FloatLib.Numerics.Dyadic) : Nat :=
  if target.significand == 0 || target.negative then
    0
  else
    let leading := leadingBit target.significand
    let scale := target.exponent + Int.ofNat leading
    let regime := scale.ediv 4
    let exponentField := (scale.emod 4).toNat
    lowerCandidateFromFields format regime exponentField
      target.significand leading

end FloatLib.Floats.Formats.Posit.Model.DirectDyadicPacking
