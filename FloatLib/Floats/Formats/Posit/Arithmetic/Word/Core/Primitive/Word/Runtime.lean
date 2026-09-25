/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Model.Fields
public import FloatLib.Kernels.FixedWord.Core.Runtime

/-!
# Native-word posit primitives

Posit kernels use these primitives when a complete candidate encoding fits in one `UInt64`.
Widths stay explicit because identical stored bits have different regime and fraction boundaries
at different total widths.

The operations here avoid `BitVec` construction and arbitrary-precision arithmetic on packed hot
paths. Proofs relating them to the exact-width posit model live in
`FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Word.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWord

open FloatLib.Numerics

/-- Capacity contract for complete posit execution in one native word. -/
def Eligible (format : Format) : Prop :=
  format.bits ≤ 64

instance (format : Format) : Decidable (Eligible format) := by
  unfold Eligible
  infer_instance

/--
Capacity contract for decoding a nonnegative candidate code in one native word.

The candidate omits the descriptor's sign bit, leaving all 64 stored bits available for its
nonnegative magnitude. The descriptor may therefore be one bit wider than a complete signed
encoding stored in the same carrier.
-/
def CandidateEligible (format : Format) : Prop :=
  format.bits ≤ 65

instance (format : Format) : Decidable (CandidateEligible format) := by
  unfold CandidateEligible
  infer_instance

/-- Positive-code endpoint represented directly in the native storage word. -/
@[inline] def signMaskWord (format : Format) : UInt64 :=
  (1 : UInt64) <<< UInt64.ofNat format.signIndex

/--
Exact-width modulus represented modulo the native machine word.

For widths below 64 this is `2 ^ format.bits`; for Posit64 it is zero, matching
`UInt64.ofNat (2 ^ 64)`.
-/
@[inline] def modulusWord (format : Format) : UInt64 :=
  signMaskWord format + signMaskWord format

/-- Restore a posit sign without leaving the native-word carrier. -/
@[inline] def restoreSignWord
    (format : Format) (negative : Bool) (positiveCode : UInt64) : UInt64 :=
  if negative then
    if positiveCode == 0 then
      0
    else
      modulusWord format - positiveCode
  else
    positiveCode

/--
Read one bit from a native word using least-significant-bit numbering.

The explicit range check is required because `UInt64` shifts reduce their count modulo 64,
whereas a bit read beyond the stored word must be `false`.
-/
@[inline] def bitAt (value : UInt64) (index : Nat) : Bool :=
  if index < 64 then
    (((value >>> UInt64.ofNat index) &&& 1) == 1)
  else
    false

/-- Low-bit mask in one native word, including the complete 64-bit mask. -/
@[inline] def lowMask (width : Nat) : UInt64 :=
  if width < 64 then
    ((1 : UInt64) <<< UInt64.ofNat width) - 1
  else
    0xffffffffffffffff

/-- Retain exactly the low `width` bits of a native word. -/
@[inline] def lowBits (value : UInt64) (width : Nat) : UInt64 :=
  value &&& lowMask width

/-- Count leading zeroes in the low `width` bits of a machine word. -/
@[inline] def countLeadingZeros (value : UInt64) (width : Nat) : Nat :=
  let truncated := lowBits value width
  if truncated == 0 then
    width
  else
    width - ((FixedWord.log2Word truncated).toNat + 1)

/--
Count a leading run in the low `width` bits of a native word.

The branch beyond 64 bits keeps this helper total for callers outside the native backend.
-/
@[inline] def countLeadingRun (value : UInt64) (width : Nat) (bit : Bool) : Nat :=
  if width ≤ 64 then
    countLeadingZeros (if bit then ~~~value else value) width
  else
    Model.countLeadingRun value.toNat width bit

/-- Shift right by a natural amount, returning zero at and beyond the word width. -/
@[inline] def shiftRight (value : UInt64) (shift : Nat) : UInt64 :=
  if shift < 64 then
    value >>> UInt64.ofNat shift
  else
    0

end FloatLib.Floats.Formats.Posit.Model.NativeWord
