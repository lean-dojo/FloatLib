/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.DType.Semantics
public meta import FloatLib.Floats.Formats.BinaryInterchange.Configured

/-!
# The recommended operations of IEEE 754-2019 clause 9 on binary formats

Special cases of the operations of IEEE 754-2019 §9.4 to §9.7 on binary16, as ISO/IEC 9899:2024
(C23, N3220) F.10.9.4, F.10.9.5 and F.10.13, ISO/IEC TS 18661-4 (N1797) F.10.10a and Riedy and
Demmel (ARITH 2018) state them. `cases` holds every case once. It is checked twice: by compiled
evaluation when this module is elaborated, and a selection of the cases by Lean's kernel on the
definitions as written (`decide +kernel`).

The second half applies the theorems of the operations to binary32 and binary64, which shows
that their premises on the format hold for the interchange formats.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.Recommended

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

/-- The binary16 value with the encoding `bits`. -/
def b16 (bits : Nat) : Binary16 := ExecFloat.Binary.ofNatBits bits

/-- Head, tail and flags of an augmented result as encodings. -/
def augmented (outcome : AugmentedOutcome Binary16) : Nat × Nat × FloatLib.Numerics.IEEEStatus :=
  (outcome.head.toNatBits, outcome.tail.toNatBits, outcome.status)

/-- Product, scale factor and flags of a scaled product as encodings. -/
def scaled (outcome : ScaledProduct Binary16) : Nat × Int × FloatLib.Numerics.IEEEStatus :=
  (outcome.product.toNatBits, outcome.scaleFactor, outcome.status)

/-- Product, scale factor and flags of a scaled product that may reject its operands. -/
def scaled? (outcome : Except FloatLib.Numerics.ReductionError (ScaledProduct Binary16)) :
    Option (Nat × Int × FloatLib.Numerics.IEEEStatus) :=
  match outcome with
  | .ok value => some (scaled value)
  | .error _ => none

/--
The special cases: a name and whether the case holds. The encodings are binary16: `0x3C00` is
one, `0xC000` minus two, `0x7C00` infinity, `0x7E00` a quiet NaN, `0x7D00` a signaling NaN,
`0x3C01` the successor of one and `0x1000` is `2 ^ -11`, half a unit in the last place of one.
-/
def cases : List (String × Bool) :=
  [ ("minimumMagnitude 1 -2",
      (ExecFloat.Binary.minimumMagnitude (b16 0x3C00) (b16 0xC000)).toNatBits == 0x3C00),
    ("maximumMagnitude 1 -2",
      (ExecFloat.Binary.maximumMagnitude (b16 0x3C00) (b16 0xC000)).toNatBits == 0xC000),
    ("minimumMagnitude -1 1 is minimum",
      (ExecFloat.Binary.minimumMagnitude (b16 0xBC00) (b16 0x3C00)).toNatBits == 0xBC00),
    ("maximumMagnitude -1 1 is maximum",
      (ExecFloat.Binary.maximumMagnitude (b16 0xBC00) (b16 0x3C00)).toNatBits == 0x3C00),
    ("minimumMagnitude +0 -0",
      (ExecFloat.Binary.minimumMagnitude (b16 0x0000) (b16 0x8000)).toNatBits == 0x8000),
    ("maximumMagnitude -0 +0",
      (ExecFloat.Binary.maximumMagnitude (b16 0x8000) (b16 0x0000)).toNatBits == 0x0000),
    ("minimumMagnitude NaN 1 is the NaN",
      (ExecFloat.Binary.minimumMagnitude (b16 0x7E00) (b16 0x3C00)).toNatBits == 0x7E00),
    ("minimumMagnitudeNumber NaN 1 is the number",
      (ExecFloat.Binary.minimumMagnitudeNumber (b16 0x7E00) (b16 0x3C00)).toNatBits == 0x3C00),
    ("maximumMagnitudeNumber 1 sNaN is the number",
      (ExecFloat.Binary.maximumMagnitudeNumber (b16 0x3C00) (b16 0x7D00)).toNatBits == 0x3C00),
    ("maximumMagnitudeNumber 1 sNaN raises invalid",
      (ExecFloat.Binary.maximumMagnitudeNumber (b16 0x3C00) (b16 0x7D00)
        (status := true)).status == { invalid := true }),
    ("maximumMagnitude -inf 1",
      (ExecFloat.Binary.maximumMagnitude (b16 0xFC00) (b16 0x3C00)).toNatBits == 0xFC00),
    ("getPayload of a quiet NaN with payload 5",
      (ExecFloat.Binary.getPayload (b16 0x7E05)).toNatBits == 0x4500),
    ("getPayload of a signaling NaN with payload 256",
      (ExecFloat.Binary.getPayload (b16 0x7D00)).toNatBits == 0x5C00),
    ("getPayload of a number is -1",
      (ExecFloat.Binary.getPayload (b16 0x3C00)).toNatBits == 0xBC00),
    ("setPayload 5",
      (ExecFloat.Binary.setPayload (b16 0x4500)).toNatBits == 0x7E05),
    ("setPayload 0.5 is +0",
      (ExecFloat.Binary.setPayload (b16 0x3800)).toNatBits == 0x0000),
    ("setPayload -1 is +0",
      (ExecFloat.Binary.setPayload (b16 0xBC00)).toNatBits == 0x0000),
    ("setPayloadSignaling 5",
      (ExecFloat.Binary.setPayloadSignaling (b16 0x4500)).toNatBits == 0x7C05),
    ("setPayloadSignaling 0 is +0",
      (ExecFloat.Binary.setPayloadSignaling (b16 0x0000)).toNatBits == 0x0000),
    ("augmentedAddition keeps a tie toward zero",
      augmented (ExecFloat.Binary.augmentedAddition (b16 0x3C01) (b16 0x1000)) ==
        (0x3C01, 0x1000, {})),
    ("addition rounds the same tie to even",
      ((b16 0x3C01) + (b16 0x1000)).toNatBits == 0x3C02),
    ("augmentedMultiplication delivers the error",
      augmented (ExecFloat.Binary.augmentedMultiplication (b16 0x3C01) (b16 0x3C01)) ==
        (0x3C02, 0x0010, {})),
    ("augmentedAddition overflows to equal infinities",
      augmented (ExecFloat.Binary.augmentedAddition (b16 0x7BFF) (b16 0x7BFF)) ==
        (0x7C00, 0x7C00, { overflow := true, inexact := true })),
    ("augmentedAddition -0 -0",
      augmented (ExecFloat.Binary.augmentedAddition (b16 0x8000) (b16 0x8000)) ==
        (0x8000, 0x8000, {})),
    ("augmentedAddition 1 -1",
      augmented (ExecFloat.Binary.augmentedAddition (b16 0x3C00) (b16 0xBC00)) ==
        (0x0000, 0x0000, {})),
    ("augmentedSubtraction 1 1",
      augmented (ExecFloat.Binary.augmentedSubtraction (b16 0x3C00) (b16 0x3C00)) ==
        (0x0000, 0x0000, {})),
    ("augmentedAddition inf -inf is invalid",
      (ExecFloat.Binary.augmentedAddition (b16 0x7C00) (b16 0xFC00)).status ==
        { invalid := true }),
    ("augmentedAddition inf -inf is a NaN",
      ExecFloat.Binary.isNaN (ExecFloat.Binary.augmentedAddition (b16 0x7C00) (b16 0xFC00)).head),
    ("sumAbs 1 -2 0.5",
      (ExecFloat.Binary.sumAbs #[b16 0x3C00, b16 0xC000, b16 0x3800]).toNatBits == 0x4300),
    ("sumAbs -inf NaN is +inf",
      (ExecFloat.Binary.sumAbs #[b16 0xFC00, b16 0x7E00]).toNatBits == 0x7C00),
    ("sumAbs of a signaling NaN raises invalid",
      (ExecFloat.Binary.sumAbs #[b16 0x7D00] (status := true)).status == { invalid := true }),
    ("sumSquare 3 4",
      (ExecFloat.Binary.sumSquare #[b16 0x4200, b16 0x4400]).toNatBits == 0x4E40),
    ("sumSquare of nothing is +0",
      (ExecFloat.Binary.sumSquare (#[] : Array Binary16)).toNatBits == 0x0000),
    ("scaledProd 3 5 is 1.875 * 2^3",
      scaled (ExecFloat.Binary.scaledProd #[b16 0x4200, b16 0x4500]) == (0x3F80, 3, {})),
    ("scaledProd of nothing is 1",
      scaled (ExecFloat.Binary.scaledProd (#[] : Array Binary16)) == (0x3C00, 0, {})),
    ("scaledProd 0 inf is invalid",
      (ExecFloat.Binary.scaledProd #[b16 0x0000, b16 0x7C00]).status == { invalid := true }),
    ("scaledProdSum (1+3)(2+4) is 1.5 * 2^4",
      scaled? (ExecFloat.Binary.scaledProdSum #[b16 0x3C00, b16 0x4000]
        #[b16 0x4200, b16 0x4400]) == some (0x3E00, 4, {})),
    ("scaledProdDiff (5-1)(7-2) is 1.25 * 2^4",
      scaled? (ExecFloat.Binary.scaledProdDiff #[b16 0x4500, b16 0x4700]
        #[b16 0x3C00, b16 0x4000]) == some (0x3D00, 4, {})),
    ("scaledProdSum rejects unequal lengths",
      scaled? (ExecFloat.Binary.scaledProdSum #[b16 0x3C00] (#[] : Array Binary16)) == none) ]

/-- The names of the cases that fail. -/
def failing : List String :=
  cases.filterMap fun (name, holds) => if holds then none else some name

#eval show IO Unit from do
  unless failing.isEmpty do
    throw (IO.userError s!"clause 9 special cases that fail: {failing}")

/-! ## The same definitions in Lean's kernel -/

example : (ExecFloat.Binary.minimumMagnitude (b16 0xBC00) (b16 0x3C00)).toNatBits = 0xBC00 := by
  decide +kernel

example : (ExecFloat.Binary.maximumMagnitudeNumber (b16 0x3C00) (b16 0x7D00)
    (status := true)).status = { invalid := true } := by
  decide +kernel

example : (ExecFloat.Binary.setPayloadSignaling (b16 0x4500)).toNatBits = 0x7C05 := by
  decide +kernel

example : augmented (ExecFloat.Binary.augmentedAddition (b16 0x3C01) (b16 0x1000)) =
    (0x3C01, 0x1000, {}) := by
  decide +kernel

example : augmented (ExecFloat.Binary.augmentedMultiplication (b16 0x3C01) (b16 0x3C01)) =
    (0x3C02, 0x0010, {}) := by
  decide +kernel

example : (ExecFloat.Binary.sumSquare #[b16 0x4200, b16 0x4400]).toNatBits = 0x4E40 := by
  decide +kernel

example : scaled (ExecFloat.Binary.scaledProd #[b16 0x4200, b16 0x4500]) = (0x3F80, 3, {}) := by
  decide +kernel

/-! ## The theorems on binary32 and binary64 -/

section Contracts

open Model
open FloatLib.Floats.Formats.Flocq (genericRepresentable_zero)
open FloatLib.Numerics.Representations (FixedInt)

/-- binary64 meets the two format premises of the theorems below. -/
example : FloatFormat.binary64.isIEEE = true ∧
    (FloatFormat.binary64.fracWidth : Int) ≤ FloatFormat.binary64.maxNormalExponent := by
  decide

/--
The error-free transformation of §9.5 on `1 + 2 ^ -52` and `2 ^ -53` in binary64: the finite
head, which the kernel computes, discharges the premise of `toReal_augmentedAddition_add`.
-/
example :
    toReal (augmentedAddition (ofNatBits 0x3FF0000000000001 : Model FloatFormat.binary64)
        (ofNatBits 0x3CA0000000000000)).head +
      toReal (augmentedAddition (ofNatBits 0x3FF0000000000001 : Model FloatFormat.binary64)
        (ofNatBits 0x3CA0000000000000)).tail =
      toReal (ofNatBits 0x3FF0000000000001 : Model FloatFormat.binary64) +
        toReal (ofNatBits 0x3CA0000000000000 : Model FloatFormat.binary64) :=
  (toReal_augmentedAddition_add rfl _ _ (by decide +kernel)).1

variable (x y : Model FloatFormat.binary64)

example (hfinite : isFinite (augmentedAddition x y).head = true) :
    toReal (augmentedAddition x y).head =
      roundTiesTowardZeroAt FloatFormat.binary64 (toReal x + toReal y) :=
  toReal_augmentedAddition_head rfl x y hfinite

example (hx : isFinite x = true) (hy : isFinite y = true)
    (hinfinite : isFinite (augmentedAddition x y).head = false) :
    (augmentedAddition x y).tail = (augmentedAddition x y).head :=
  (augmentedAddition_of_isFinite_head_eq_false rfl x y hx hy hinfinite).1

example (hfinite : isFinite (augmentedSubtraction x y).head = true) :
    toReal (augmentedSubtraction x y).head + toReal (augmentedSubtraction x y).tail =
      toReal x - toReal y :=
  toReal_augmentedSubtraction_sub rfl x y hfinite

example (hfinite : isFinite (augmentedMultiplication x y).head = true) :
    toReal (augmentedMultiplication x y).head =
      roundTiesTowardZeroAt FloatFormat.binary64 (toReal x * toReal y) :=
  toReal_augmentedMultiplication_head rfl x y hfinite

example (hhead : isFinite (augmentedMultiplication x y).head = true)
    (htail : isFinite (augmentedMultiplication x y).tail = true) :
    toReal (augmentedMultiplication x y).tail =
      roundTiesTowardZeroAt FloatFormat.binary64
        (toReal x * toReal y - toReal (augmentedMultiplication x y).head) :=
  toReal_augmentedMultiplication_tail rfl x y hhead htail

example (hhead : isFinite (augmentedMultiplication x y).head = true)
    (htail : isFinite (augmentedMultiplication x y).tail = true) :
    (augmentedMultiplication x y).status.inexact = true ↔
      toReal (augmentedMultiplication x y).head + toReal (augmentedMultiplication x y).tail ≠
        toReal x * toReal y :=
  (augmentedMultiplication_inexact_iff rfl x y hhead htail).1

example (hx : isFinite x = true) (hy : isFinite y = true)
    (hinfinite : isFinite (augmentedMultiplication x y).head = false) :
    (augmentedMultiplication x y).tail = (augmentedMultiplication x y).head :=
  (augmentedMultiplication_of_isFinite_head_eq_false rfl x y hx hy hinfinite).1

example (h : isNaN x = true ∨ isNaN y = true) : minimumMagnitude x y = minimum x y :=
  magnitudeExtremum_of_isNaN false _ h

example : (maximumMagnitudeNumber x y (status := true)).status =
    { invalid := isSignaling x || isSignaling y } :=
  magnitudeExtremum_status true _ x y

example (hx : isFinite x = true) (hy : isFinite y = true) :
    |toReal (minimumMagnitude x y)| = min |toReal x| |toReal y| :=
  abs_toReal_minimumMagnitude x y rfl hx hy

example (hx : isFinite x = true) (hy : isFinite y = true) :
    |toReal (maximumMagnitude x y)| = max |toReal x| |toReal y| :=
  abs_toReal_maximumMagnitude x y rfl hx hy

example (hx : isFinite x = true) (hy : isFinite y = true) :
    |toReal (minimumMagnitudeNumber x y)| = min |toReal x| |toReal y| :=
  abs_toReal_minimumMagnitudeNumber x y rfl hx hy

example (hx : isFinite x = true) (hy : isFinite y = true) :
    |toReal (maximumMagnitudeNumber x y)| = max |toReal x| |toReal y| :=
  abs_toReal_maximumMagnitudeNumber x y rfl hx hy

example : signBit (setPayload x) = false :=
  signBit_setPayload rfl x

example (h : admissiblePayload? x = none) : setPayloadSignaling x = posZero _ :=
  setPayloadSignaling_of_admissiblePayload?_eq_none h

example {n : Nat} (h : admissiblePayload? x = some n) (hpos : n ≠ 0) :
    isSignaling (setPayloadSignaling x) = true ∧ getPayload (setPayloadSignaling x) = x :=
  ⟨isSignaling_setPayloadSignaling rfl h hpos, getPayload_setPayloadSignaling rfl h hpos⟩

example (hnan : isNaN x = true) : toReal (getPayload x) = nanPayload x :=
  toReal_getPayload rfl (by decide) hnan

example : roundTiesTowardZeroAt FloatFormat.binary64 0 = 0 :=
  roundTiesTowardZeroAt_of_genericFormat _ genericRepresentable_zero

example (negative : Bool) (exponent : Int) :
    roundDyadicTiesTowardZero FloatFormat.binary64 ⟨negative, 0, exponent⟩ =
      zero FloatFormat.binary64 negative :=
  roundDyadicTiesTowardZero_zero _ negative exponent

variable (values : Array (Model FloatFormat.binary32))

example {infinity : Model FloatFormat.binary32}
    (h : Reduction.Internal.decidingInfinity? values = some infinity) :
    sumAbs FloatFormat.binary64 values .nearest (status := true) =
      cast FloatFormat.binary32 FloatFormat.binary64 (abs infinity) .nearest (status := true) :=
  Reduction.sumAbs_status_of_decidingInfinity? _ values .nearest h

example {infinity : Model FloatFormat.binary32}
    (h : Reduction.Internal.decidingInfinity? values = some infinity) :
    sumSquare FloatFormat.binary64 values .nearest (status := true) =
      cast FloatFormat.binary32 FloatFormat.binary64 (abs infinity) .nearest (status := true) :=
  Reduction.sumSquare_status_of_decidingInfinity? _ values .nearest h

/-- The premise `isIEEE` of the reduction theorems holds for a binary64 destination. -/
example := Reduction.toReal_sumAbs FloatFormat.binary64 values rfl
example (exact : ℚ) := Reduction.toReal_sumSquare FloatFormat.binary64 values exact rfl
example := Reduction.toReal_scaledProd_product FloatFormat.binary64 values rfl
example := Reduction.mixedError_scaledProd FloatFormat.binary64 values rfl
example (subtract : Bool) (outcome : ScaledProduct (Model FloatFormat.binary64)) :=
  Reduction.toReal_scaledProdOfSums_product FloatFormat.binary64 values values subtract outcome rfl

example {mode : IEEERoundingMode} {result : FixedInt 32}
    {status : FloatLib.Floats.ExecFloat.ConversionStatus}
    (h : ExecDType.convertToIntegerExact (width := 32) x mode = .success result status) :
    ExecDType.convertToInteger (width := 32) x mode =
      .success result { status with inexact := false } :=
  ExecDType.convertToInteger_of_convertToIntegerExact_eq_success h

example {mode : IEEERoundingMode} {reason : FloatLib.Floats.ExecFloat.ConversionFailure}
    (h : ExecDType.convertToIntegerExact (width := 32) x mode = .failure reason) :
    ExecDType.convertToInteger (width := 32) x mode = .failure reason :=
  ExecDType.convertToInteger_of_convertToIntegerExact_eq_failure h

end Contracts

end FloatLibTests.Conformance.BinaryInterchange.Recommended
