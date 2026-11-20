/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Recommended.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Text.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.DType.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Schedule.KernelPath

/-!
# Kernel rules for the remaining operations of IEEE 754-2019 on binary values

`float_decide` checks statements about `nextUp`, `nextDown`, `copy`, `remainder`, `setPayload`
and `setPayloadSignaling` on encodings, through the rules of `Configured.Recommended.KernelPath`,
about the five formatOf operations between formats, the three augmented operations and the
reductions `sum`, `dot`, `sumAbs`, `sumSquare`, `scaledProd`, `scaledProdSum` and
`scaledProdDiff`, about the reductions that round at each addition (`sumInOrder`, `sumAlong`
and their siblings of `Reduction.Schedule.KernelPath`), and about `convertFromInt`,
`convertToInteger…` and `convertToIntegerExact…` of the descriptor model through the rules of
`DType.KernelPath`, about `pown`, `rootn`, `rSqrt` and `hypot`, and about the conversions to and
from character sequences (`format` and `parse`, in decimal and in hexadecimal) through the rules of
`Configured.Text.KernelPath`. The cases are the special values of
IEEE 754-2019 §5.3.1, §5.4.1, §6.2 and §9.7: the two zeros, the least subnormals, the largest
finite values, the infinities, quiet and signaling NaNs, the operands that name a payload or
none, and integers at the ends of the range of their width, in binary16, binary32, binary64,
binary128 and a format with its own field widths, and every pair of encodings of a five-bit
format. Each proof depends on the three standard axioms only.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.KernelCoverage

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath
open FloatLib.Numerics.Representations

/-- The IEEE layout with two exponent bits and two fraction bits: 32 encodings. -/
abbrev Binary5 := ExecFloat.Binary (exponentBits := 2) (fractionBits := 2)

/-! ## The rewrite reaches the operations -/

set_option backward.isDefEq.respectTransparency false in
example (x : Binary32) : ExecFloat.Binary.nextUp x = Value.nextUp x ∧
    ExecFloat.Binary.nextDown x = Value.nextDown x ∧ ExecFloat.Binary.copy x = x := by
  simp only [kernel_optimize, and_self]

set_option backward.isDefEq.respectTransparency false in
example (x : Binary64) : ExecFloat.Binary.setPayload x = Value.setPayload x ∧
    ExecFloat.Binary.setPayloadSignaling x = Value.setPayloadSignaling x := by
  simp only [kernel_optimize, and_self]

/-- The encoding of a neighbor is the flat operation on the encoding. -/
example (x : Binary128) :
    toNat (ExecFloat.Binary.nextUp x) = toNat (Value.nextUp x) := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [kernel_optimize]

/-! ## `nextUp` and `nextDown` (§5.3.1) -/

/--
`nextUp` at the zeros, the least subnormals, one, the largest finite value, the infinities and
NaNs: both zeros give the least positive subnormal, `-∞` the most negative finite value, and a
signaling NaN is quieted.
-/
theorem binary32_nextUp :
    toNat (ExecFloat.Binary.nextUp (ofNat 0 : Binary32)) = 1 ∧
      toNat (ExecFloat.Binary.nextUp (ofNat 0x80000000 : Binary32)) = 1 ∧
      toNat (ExecFloat.Binary.nextUp (ofNat 0x80000001 : Binary32)) = 0x80000000 ∧
      toNat (ExecFloat.Binary.nextUp (1 : Binary32)) = 0x3f800001 ∧
      toNat (ExecFloat.Binary.nextUp (-1 : Binary32)) = 0xbf7fffff ∧
      toNat (ExecFloat.Binary.nextUp (ofNat 0x007fffff : Binary32)) = 0x00800000 ∧
      toNat (ExecFloat.Binary.nextUp (ofNat 0x7f7fffff : Binary32)) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.nextUp (ofNat 0x7f800000 : Binary32)) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.nextUp (ofNat 0xff800000 : Binary32)) = 0xff7fffff ∧
      toNat (ExecFloat.Binary.nextUp (ofNat 0x7fa00001 : Binary32)) = 0x7fe00001 ∧
      toNat (ExecFloat.Binary.nextUp (ofNat 0xffc00002 : Binary32)) = 0xffc00002 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary32_nextUp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary32_nextUp

/-- `nextDown` at the same values: both zeros give the negative subnormal of least magnitude. -/
theorem binary32_nextDown :
    toNat (ExecFloat.Binary.nextDown (ofNat 0 : Binary32)) = 0x80000001 ∧
      toNat (ExecFloat.Binary.nextDown (ofNat 0x80000000 : Binary32)) = 0x80000001 ∧
      toNat (ExecFloat.Binary.nextDown (ofNat 1 : Binary32)) = 0 ∧
      toNat (ExecFloat.Binary.nextDown (1 : Binary32)) = 0x3f7fffff ∧
      toNat (ExecFloat.Binary.nextDown (-1 : Binary32)) = 0xbf800001 ∧
      toNat (ExecFloat.Binary.nextDown (ofNat 0x00800000 : Binary32)) = 0x007fffff ∧
      toNat (ExecFloat.Binary.nextDown (ofNat 0xff7fffff : Binary32)) = 0xff800000 ∧
      toNat (ExecFloat.Binary.nextDown (ofNat 0xff800000 : Binary32)) = 0xff800000 ∧
      toNat (ExecFloat.Binary.nextDown (ofNat 0x7f800000 : Binary32)) = 0x7f7fffff ∧
      toNat (ExecFloat.Binary.nextDown (ofNat 0x7fa00001 : Binary32)) = 0x7fe00001 ∧
      toNat (ExecFloat.Binary.nextDown (ofNat 0xffc00002 : Binary32)) = 0xffc00002 := by
  float_decide

/-- With `status := true` a signaling NaN raises `invalid`, and no other operand does. -/
theorem binary32_neighbor_status :
    (ExecFloat.Binary.nextUp (ofNat 0x7fa00000 : Binary32) (status := true)).status.invalid =
        true ∧
      toNat (ExecFloat.Binary.nextUp (ofNat 0x7fa00000 : Binary32) (status := true)).value =
        0x7fe00000 ∧
      (ExecFloat.Binary.nextUp (ofNat 0x7fc00000 : Binary32) (status := true)).status.invalid =
        false ∧
      (ExecFloat.Binary.nextDown (ofNat 0xffa00000 : Binary32) (status := true)).status.invalid =
        true ∧
      (ExecFloat.Binary.nextDown (1 : Binary32) (status := true)).status.invalid = false ∧
      (ExecFloat.Binary.nextDown (1 : Binary32) (status := true)).ternary = .eq := by
  float_decide

/-- The same steps in binary16, binary64, binary128 and a format of 71 bits. -/
theorem neighbors_by_format :
    toNat (ExecFloat.Binary.nextUp (1 : Binary16)) = 0x3c01 ∧
      toNat (ExecFloat.Binary.nextDown (1 : Binary64)) = 0x3fefffffffffffff ∧
      toNat (ExecFloat.Binary.nextUp (ofNat 0 : Binary128)) = 1 ∧
      ExecFloat.Binary.nextDown (ExecFloat.Binary.nextUp
        (3 : ExecFloat.Binary (exponentBits := 11) (fractionBits := 59))) = 3 ∧
      ExecFloat.Binary.copy (2.5 : Binary64) = 2.5 := by
  float_decide

/--
On the 1,024 pairs of encodings without a NaN: no value of the format lies strictly between a
value and its `nextUp`, nor between its `nextDown` and the value, and `nextUp` is above the
value unless the value is `+∞`.
-/
theorem binary5_neighbors : ∀ a b : Fin 32,
    (ExecFloat.Binary.isNaN (ofNat a : Binary5) || ExecFloat.Binary.isNaN (ofNat b : Binary5)) =
        true ∨
      ((ExecFloat.Binary.compareQuietLess (ofNat a : Binary5) (ofNat b)).value &&
          (ExecFloat.Binary.compareQuietLess (ofNat b : Binary5)
            (ExecFloat.Binary.nextUp (ofNat a))).value) = false ∧
        ((ExecFloat.Binary.compareQuietLess (ExecFloat.Binary.nextDown (ofNat a : Binary5))
            (ofNat b)).value &&
          (ExecFloat.Binary.compareQuietLess (ofNat b : Binary5) (ofNat a)).value) = false ∧
        (toNat (ofNat a : Binary5) = 12 ∨
          (ExecFloat.Binary.compareQuietLess (ofNat a : Binary5)
            (ExecFloat.Binary.nextUp (ofNat a))).value = true) := by
  float_decide

/-! ## `remainder` (§5.3.1) -/

/--
The quotient is rounded to the nearest integer, ties to even: `5 rem 3` is `-1`, `7 rem 2` is
`-1` and `5 rem 2` is `1`. A zero remainder has the sign of the dividend, a finite dividend
with an infinite divisor is returned, and an infinite dividend and a zero divisor are invalid.
The remainder of `1e30` by `3`, 70 binary places apart, is exact.
-/
theorem binary32_remainder :
    ExecFloat.Binary.remainder (5 : Binary32) 3 = -1 ∧
      ExecFloat.Binary.remainder (7 : Binary32) 2 = -1 ∧
      ExecFloat.Binary.remainder (5 : Binary32) 2 = 1 ∧
      ExecFloat.Binary.remainder (-5 : Binary32) 3 = 1 ∧
      toNat (ExecFloat.Binary.remainder (6 : Binary32) 3) = 0 ∧
      toNat (ExecFloat.Binary.remainder (-6 : Binary32) 3) = 0x80000000 ∧
      toNat (ExecFloat.Binary.remainder (1e30 : Binary32) 3) = 0 ∧
      toNat (ExecFloat.Binary.remainder (0.1 : Binary32) 0.03) = 0x3c23d70e ∧
      ExecFloat.Binary.remainder (2.5 : Binary32) (ofNat 0x7f800000) = 2.5 ∧
      ExecFloat.Binary.isNaN (ExecFloat.Binary.remainder (ofNat 0x7f800000 : Binary32) 1) =
        true ∧
      ExecFloat.Binary.isNaN (ExecFloat.Binary.remainder (1 : Binary32) (ofNat 0)) = true ∧
      ExecFloat.Binary.remainder (5 : Binary64) 3 = -1 ∧
      ExecFloat.Binary.remainder (5.5 : Binary16) 2 = -0.5 ∧
      ExecFloat.Binary.remainder (10 : Binary128) 4 = 2 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary32_remainder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary32_remainder

/--
On the 1,024 pairs of encodings of the five-bit format with a finite dividend and a finite
nonzero divisor: twice the magnitude of the remainder does not exceed the magnitude of the
divisor.
-/
theorem binary5_remainder : ∀ a b : Fin 32,
    (ExecFloat.Binary.isFinite (ofNat a : Binary5) && ExecFloat.Binary.isFinite (ofNat b : Binary5)
        && !ExecFloat.Binary.isZero (ofNat b : Binary5)) = false ∨
      (ExecFloat.Binary.compareQuietLessEqual
        (ExecFloat.Binary.scale
          (ExecFloat.Binary.abs (ExecFloat.Binary.remainder (ofNat a : Binary5) (ofNat b))) 1)
        (ExecFloat.Binary.abs (ofNat b : Binary5))).value = true := by
  float_decide

/--
With `status := true` the value is the remainder, and `invalid` is raised by a zero divisor, an
infinite dividend and a signaling NaN, and not by an infinite divisor nor by a quiet NaN.
-/
theorem binary32_remainder_status :
    (ExecFloat.Binary.remainder (5 : Binary32) 3 (status := true)).status.invalid = false ∧
      toNat (ExecFloat.Binary.remainder (5 : Binary32) 3 (status := true)).value =
        0xbf800000 ∧
      (ExecFloat.Binary.remainder (5 : Binary32) 3 (status := true)).ternary = .eq ∧
      (ExecFloat.Binary.remainder (5 : Binary32) (ofNat 0) (status := true)).status.invalid =
        true ∧
      (ExecFloat.Binary.remainder (ofNat 0x7f800000 : Binary32) 3
        (status := true)).status.invalid = true ∧
      (ExecFloat.Binary.remainder (5 : Binary32) (ofNat 0x7f800000)
        (status := true)).status.invalid = false ∧
      (ExecFloat.Binary.remainder (ofNat 0x7fa00000 : Binary32) 3
        (status := true)).status.invalid = true ∧
      (ExecFloat.Binary.remainder (5 : Binary32) (ofNat 0x7fa00000)
        (status := true)).status.invalid = true ∧
      (ExecFloat.Binary.remainder (ofNat 0x7fc00000 : Binary32) (ofNat 0)
        (status := true)).status.invalid = false := by
  float_decide

/--
On the 1,024 pairs of encodings of the five-bit format: the value with status is the value
without, and `invalid` is raised exactly by a signaling NaN, or without a NaN by an infinite
dividend or a zero divisor.
-/
theorem binary5_remainder_status : ∀ a b : Fin 32,
    (ExecFloat.Binary.remainder (ofNat a : Binary5) (ofNat b) (status := true)).value =
        ExecFloat.Binary.remainder (ofNat a : Binary5) (ofNat b) ∧
      (ExecFloat.Binary.remainder (ofNat a : Binary5) (ofNat b) (status := true)).status.invalid =
        (ExecFloat.Binary.isSignaling (ofNat a : Binary5) ||
          ExecFloat.Binary.isSignaling (ofNat b : Binary5) ||
          (!ExecFloat.Binary.isNaN (ofNat a : Binary5) &&
            !ExecFloat.Binary.isNaN (ofNat b : Binary5) &&
            (ExecFloat.Binary.isInfinite (ofNat a : Binary5) ||
              ExecFloat.Binary.isZero (ofNat b : Binary5)))) := by
  float_decide

/-! ## `setPayload` and `setPayloadSignaling` (§9.7) -/

/--
`setPayload` gives the quiet NaN with the payload of a nonnegative integral operand below the
bound `2 ^ 22`, and `+0` for `-0`, a negative integer, a fraction, an integer at the bound, an
infinity and a NaN.
-/
theorem binary32_setPayload :
    toNat (ExecFloat.Binary.setPayload (5 : Binary32)) = 0x7fc00005 ∧
      toNat (ExecFloat.Binary.setPayload (ofNat 0 : Binary32)) = 0x7fc00000 ∧
      toNat (ExecFloat.Binary.setPayload (4194303 : Binary32)) = 0x7fffffff ∧
      toNat (ExecFloat.Binary.setPayload (4194304 : Binary32)) = 0 ∧
      toNat (ExecFloat.Binary.setPayload (ofNat 0x80000000 : Binary32)) = 0 ∧
      toNat (ExecFloat.Binary.setPayload (-1 : Binary32)) = 0 ∧
      toNat (ExecFloat.Binary.setPayload (1.5 : Binary32)) = 0 ∧
      toNat (ExecFloat.Binary.setPayload (ofNat 0x7f800000 : Binary32)) = 0 ∧
      toNat (ExecFloat.Binary.setPayload (ofNat 0x7fc00001 : Binary32)) = 0 ∧
      toNat (ExecFloat.Binary.setPayload (ofNat 0x7f7fffff : Binary32)) = 0 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary32_setPayload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary32_setPayload

/--
`setPayloadSignaling` gives the signaling NaN with a nonzero payload, and `+0` for the payload
zero, whose word would be an infinity.
-/
theorem binary32_setPayloadSignaling :
    toNat (ExecFloat.Binary.setPayloadSignaling (5 : Binary32)) = 0x7f800005 ∧
      toNat (ExecFloat.Binary.setPayloadSignaling (ofNat 0 : Binary32)) = 0 ∧
      toNat (ExecFloat.Binary.setPayloadSignaling (4194303 : Binary32)) = 0x7fbfffff ∧
      toNat (ExecFloat.Binary.setPayloadSignaling (4194304 : Binary32)) = 0 ∧
      toNat (ExecFloat.Binary.setPayloadSignaling (-3 : Binary32)) = 0 ∧
      toNat (ExecFloat.Binary.setPayloadSignaling (0.5 : Binary32)) = 0 ∧
      ExecFloat.Binary.isSignaling (ExecFloat.Binary.setPayloadSignaling (7 : Binary32)) =
        true := by
  float_decide

/-- The payload set is the payload read, in binary16, binary64, binary128 and 71 bits. -/
theorem payload_by_format :
    ExecFloat.Binary.getPayload (ExecFloat.Binary.setPayload (291 : Binary64)) = 291 ∧
      ExecFloat.Binary.getPayload (ExecFloat.Binary.setPayloadSignaling (291 : Binary64)) =
        291 ∧
      toNat (ExecFloat.Binary.setPayload (3 : Binary16)) = 0x7e03 ∧
      ExecFloat.Binary.getPayload (ExecFloat.Binary.setPayload (1000000 : Binary128)) =
        1000000 ∧
      ExecFloat.Binary.getPayload (ExecFloat.Binary.setPayload
        (12 : ExecFloat.Binary (exponentBits := 11) (fractionBits := 59))) = 12 := by
  float_decide

/--
On every encoding of the five-bit format, whose payload bound is two: `setPayload` is a NaN
exactly for `+0` and `1`, with the payload it was given, and `setPayloadSignaling` is a NaN
exactly for `1`.
-/
theorem binary5_setPayload : ∀ a b : Fin 32,
    ExecFloat.Binary.isNaN (ExecFloat.Binary.setPayload (ofNat a : Binary5)) =
        (Nat.beq a 0 || Nat.beq a 4) ∧
      (ExecFloat.Binary.isNaN (ExecFloat.Binary.setPayload (ofNat a : Binary5)) = false ∨
        toNat (ExecFloat.Binary.getPayload (ExecFloat.Binary.setPayload (ofNat a : Binary5))) =
          a) ∧
      ExecFloat.Binary.isSignaling (ExecFloat.Binary.setPayloadSignaling (ofNat b : Binary5)) =
        Nat.beq b 4 := by
  float_decide

/-! ## Conversions between a format and an integer format (§5.4.1) -/

/--
`convertToIntegerExact…` rounds in its direction and raises `inexact` for a fraction; a value
beyond the 64-bit range, an infinity and a NaN fail with their reason.
-/
theorem binary64_convertToIntegerExact :
    ExecDType.convertToIntegerExactTiesToEven (ExecFloat.Binary.toModel (2.5 : Binary64)) =
        .success (FixedInt.ofInt (width := 64) 2) { inexact := true } ∧
      ExecDType.convertToIntegerExactTiesToAway (ExecFloat.Binary.toModel (2.5 : Binary64)) =
        .success (FixedInt.ofInt (width := 64) 3) { inexact := true } ∧
      ExecDType.convertToIntegerExactTowardZero (ExecFloat.Binary.toModel (-2.5 : Binary64)) =
        .success (FixedInt.ofInt (width := 64) (-2)) { inexact := true } ∧
      ExecDType.convertToIntegerExactTowardPositive
          (ExecFloat.Binary.toModel (2.25 : Binary64)) =
        .success (FixedInt.ofInt (width := 64) 3) { inexact := true } ∧
      ExecDType.convertToIntegerExactTowardNegative
          (ExecFloat.Binary.toModel (-2.25 : Binary64)) =
        .success (FixedInt.ofInt (width := 64) (-3)) { inexact := true } ∧
      ExecDType.convertToIntegerExactTiesToEven (ExecFloat.Binary.toModel (-7 : Binary64)) =
        .success (FixedInt.ofInt (width := 64) (-7)) {} ∧
      ExecDType.convertToIntegerExactTiesToEven (width := 64)
          (ExecFloat.Binary.toModel (1e30 : Binary64)) = .failure .outOfRange ∧
      ExecDType.convertToIntegerExactTiesToEven (width := 64)
          (ExecFloat.Binary.toModel (ofNat 0xfff0000000000000 : Binary64)) =
        .failure (.infinity .source true) := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary64_convertToIntegerExact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary64_convertToIntegerExact

/--
The ends of the range of eight signed bits: `127.5` toward zero and `-128` fit, `128` and
`-128.5` toward negative infinity do not, and `convertToInteger…` keeps `inexact` clear.
-/
theorem binary32_convertToInteger_range :
    ExecDType.convertToIntegerExactTowardZero (ExecFloat.Binary.toModel (127.5 : Binary32)) =
        .success (FixedInt.ofInt (width := 8) 127) { inexact := true } ∧
      ExecDType.convertToIntegerExactTiesToEven (ExecFloat.Binary.toModel (-128 : Binary32)) =
        .success (FixedInt.ofInt (width := 8) (-128)) {} ∧
      ExecDType.convertToIntegerExactTiesToEven (width := 8)
          (ExecFloat.Binary.toModel (128 : Binary32)) = .failure .outOfRange ∧
      ExecDType.convertToIntegerExactTowardNegative (width := 8)
          (ExecFloat.Binary.toModel (-128.5 : Binary32)) = .failure .outOfRange ∧
      ExecDType.convertToIntegerTowardZero (ExecFloat.Binary.toModel (127.5 : Binary32)) =
        .success (FixedInt.ofInt (width := 8) 127) {} ∧
      ExecDType.convertToIntegerTiesToEven (width := 8)
          (ExecFloat.Binary.toModel (ofNat 0x7f800000 : Binary32)) =
        .failure (.infinity .source false) := by
  float_decide

/--
`convertFromInt` rounds an integer once: `2 ^ 24 + 1` is a tie in binary32 and goes to the even
neighbor, upward to the next value, and a 64-bit integer is exact in binary128.
-/
theorem convertFromInt_by_format :
    (ExecFloat.Binary.ofModel (ExecDType.convertFromInt _ (FixedInt.ofInt (width := 64) 16777217)) :
        Binary32) = 16777216 ∧
      (ExecFloat.Binary.ofModel
        (ExecDType.convertFromInt _ (FixedInt.ofInt (width := 64) 16777217) .up) : Binary32) =
        16777218 ∧
      (ExecFloat.Binary.ofModel (ExecDType.convertFromInt _ (FixedInt.ofInt (width := 64) (-5))) :
        Binary16) = -5 ∧
      (ExecFloat.Binary.ofModel (ExecDType.convertFromInt _ (FixedInt.ofInt (width := 8) 200)) :
        Binary64) = -56 ∧
      toNat (ExecFloat.Binary.ofModel
        (ExecDType.convertFromInt _ (FixedInt.ofInt (width := 64) 0)) : Binary128) = 0 ∧
      (ExecFloat.Binary.ofModel
        (ExecDType.convertFromInt _ (FixedInt.ofInt (width := 64) 9007199254740993)) :
        Binary128) = 9007199254740993 := by
  float_decide

/--
On every encoding of the five-bit format: the integer that the checked conversion delivers
toward zero, read back by `convertFromInt`, is the operand rounded to an integral value.
-/
theorem binary5_integer_roundtrip : ∀ a b : Fin 32,
    (ExecFloat.Binary.isFinite (ofNat a : Binary5) = false ∨
        ExecFloat.Binary.isZero (ofNat a : Binary5) = true ∨
        (match ExecDType.convertToIntegerExactTowardZero (width := 8)
            (ExecFloat.Binary.toModel (ofNat a : Binary5)) with
          | .success value _ =>
              toNat (ExecFloat.Binary.ofModel (ExecDType.convertFromInt _ value) : Binary5) ==
                toNat (ExecFloat.Binary.roundToIntegralTowardZero (ofNat a : Binary5)) ||
              ExecFloat.Binary.isZero (ExecFloat.Binary.roundToIntegralTowardZero
                (ofNat a : Binary5))
          | .failure _ => false) = true) ∧
      (ExecFloat.Binary.isFinite (ofNat b : Binary5) = true ∨
        (match ExecDType.convertToIntegerExactTiesToEven (width := 8)
            (ExecFloat.Binary.toModel (ofNat b : Binary5)) with
          | .success _ _ => false
          | .failure _ => true) = true) := by
  float_decide

/-! ## The formatOf operations (§5.4.1) -/

/-- The value of a formatOf sum stored in binary32 is the kernel operation on the encodings. -/
example (x y : Binary64) :
    toNat (ExecFloat.Binary.ofModel (Model.formatOfAddition _ (ExecFloat.Binary.toModel x)
      (ExecFloat.Binary.toModel y)).value : Binary32) =
      KernelPath.formatOfAddition FloatFormat.binary64 FloatFormat.binary64 FloatFormat.binary32
        .nearest (toNat x) (toNat y) := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [kernel_optimize]
  rfl

/--
One rounding of the exact result: `1 + 2 ^ (-24)` plus `2 ^ (-60)` in binary64 lies above the
midpoint of two binary32 values and rounds up, where the binary64 sum cast to binary32 is the
tie and rounds to even. A difference of equal values is `+0`, and `-0` toward negative
infinity.
-/
theorem binary64_formatOf_sum :
    toNat (ExecFloat.Binary.ofModel (Model.formatOfAddition _
      (ExecFloat.Binary.toModel (ofNat 0x3ff0000010000000 : Binary64))
      (ExecFloat.Binary.toModel (ofNat 0x3c30000000000000 : Binary64))).value : Binary32) =
        0x3f800001 ∧
      toNat (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel
        ((ofNat 0x3ff0000010000000 : Binary64) + ofNat 0x3c30000000000000)) .nearest) :
        Binary32) = 0x3f800000 ∧
      toNat (ExecFloat.Binary.ofModel (Model.formatOfSubtraction _
        (ExecFloat.Binary.toModel (1.5 : Binary64))
        (ExecFloat.Binary.toModel (1.5 : Binary64))).value : Binary32) = 0 ∧
      toNat (ExecFloat.Binary.ofModel (Model.formatOfSubtraction _
        (ExecFloat.Binary.toModel (1.5 : Binary64))
        (ExecFloat.Binary.toModel (1.5 : Binary64)) .down).value : Binary32) = 0x80000000 ∧
      (ExecFloat.Binary.ofModel (Model.formatOfSubtraction _
        (ExecFloat.Binary.toModel (5 : Binary16))
        (ExecFloat.Binary.toModel (1.5 : Binary128))).value : Binary32) = 3.5 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary64_formatOf_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary64_formatOf_sum

/--
Products, quotients and fused multiply-adds between formats: a product of two binary32 values
is exact in binary64, one third of binary64 operands is rounded once into binary32 in each
direction, a division by zero gives an infinity and zero by zero a NaN.
-/
theorem formatOf_products :
    (ExecFloat.Binary.ofModel (Model.formatOfMultiplication _
      (ExecFloat.Binary.toModel (16777217 : Binary64))
      (ExecFloat.Binary.toModel (16777217 : Binary64))).value : Binary128) =
        281474976710656 + 33554432 + 1 ∧
      toNat (ExecFloat.Binary.ofModel (Model.formatOfDivision _
        (ExecFloat.Binary.toModel (1 : Binary64))
        (ExecFloat.Binary.toModel (3 : Binary64))).value : Binary32) = 0x3eaaaaab ∧
      toNat (ExecFloat.Binary.ofModel (Model.formatOfDivision _
        (ExecFloat.Binary.toModel (1 : Binary64))
        (ExecFloat.Binary.toModel (3 : Binary64)) .towardZero).value : Binary32) =
        0x3eaaaaaa ∧
      toNat (ExecFloat.Binary.ofModel (Model.formatOfDivision _
        (ExecFloat.Binary.toModel (-1 : Binary16))
        (ExecFloat.Binary.toModel (ofNat 0 : Binary64))).value : Binary32) = 0xff800000 ∧
      ExecFloat.Binary.isNaN (ExecFloat.Binary.ofModel (Model.formatOfDivision _
        (ExecFloat.Binary.toModel (ofNat 0 : Binary64))
        (ExecFloat.Binary.toModel (ofNat 0 : Binary64))).value : Binary32) = true ∧
      (ExecFloat.Binary.ofModel (Model.formatOfFusedMultiplyAdd _
        (ExecFloat.Binary.toModel (3 : Binary32)) (ExecFloat.Binary.toModel (0.5 : Binary32))
        (ExecFloat.Binary.toModel (0.25 : Binary64))).value : Binary16) = 1.75 ∧
      ExecFloat.Binary.isNaN (ExecFloat.Binary.ofModel (Model.formatOfMultiplication _
        (ExecFloat.Binary.toModel (ofNat 0x7ff0000000000001 : Binary64))
        (ExecFloat.Binary.toModel (2 : Binary32))).value : Binary16) = true := by
  float_decide

/--
On the 1,024 pairs of encodings of the five-bit format, the formatOf operations within the
format are its own arithmetic: two kernel forms of each operation agree.
-/
theorem binary5_formatOf : ∀ a b : Fin 32,
    toNat (ExecFloat.Binary.ofModel (Model.formatOfAddition _
        (ExecFloat.Binary.toModel (ofNat a : Binary5))
        (ExecFloat.Binary.toModel (ofNat b : Binary5))).value : Binary5) =
        toNat ((ofNat a : Binary5) + ofNat b) ∧
      toNat (ExecFloat.Binary.ofModel (Model.formatOfSubtraction _
        (ExecFloat.Binary.toModel (ofNat a : Binary5))
        (ExecFloat.Binary.toModel (ofNat b : Binary5))).value : Binary5) =
        toNat ((ofNat a : Binary5) - ofNat b) ∧
      toNat (ExecFloat.Binary.ofModel (Model.formatOfMultiplication _
        (ExecFloat.Binary.toModel (ofNat a : Binary5))
        (ExecFloat.Binary.toModel (ofNat b : Binary5))).value : Binary5) =
        toNat ((ofNat a : Binary5) * ofNat b) ∧
      toNat (ExecFloat.Binary.ofModel (Model.formatOfDivision _
        (ExecFloat.Binary.toModel (ofNat a : Binary5))
        (ExecFloat.Binary.toModel (ofNat b : Binary5))).value : Binary5) =
        toNat ((ofNat a : Binary5) / ofNat b) := by
  float_decide

/-! ## Augmented arithmetic (§9.5) -/

/--
A tie goes toward zero: `1 + 2 ^ (-23) + 2 ^ (-24)` has the head `1 + 2 ^ (-23)`, which
nearest-even rounds to `1 + 2 ^ (-22)`, and the tail `2 ^ (-24)`, for both signs. An exact sum
has a zero tail with the sign of the head, and an exact cancellation gives `+0` twice.
-/
theorem binary32_augmentedAddition :
    toNat (ExecFloat.Binary.augmentedAddition (ofNat 0x3f800001 : Binary32)
      (ofNat 0x33800000)).head = 0x3f800001 ∧
      toNat (ExecFloat.Binary.augmentedAddition (ofNat 0x3f800001 : Binary32)
        (ofNat 0x33800000)).tail = 0x33800000 ∧
      toNat ((ofNat 0x3f800001 : Binary32) + ofNat 0x33800000) = 0x3f800002 ∧
      toNat (ExecFloat.Binary.augmentedAddition (ofNat 0xbf800001 : Binary32)
        (ofNat 0xb3800000)).head = 0xbf800001 ∧
      toNat (ExecFloat.Binary.augmentedAddition (ofNat 0xbf800001 : Binary32)
        (ofNat 0xb3800000)).tail = 0xb3800000 ∧
      (ExecFloat.Binary.augmentedAddition (ofNat 0x3f800001 : Binary32)
        (ofNat 0x33800000)).status.inexact = false ∧
      toNat (ExecFloat.Binary.augmentedAddition (-1.5 : Binary32) (-2.5)).head = 0xc0800000 ∧
      toNat (ExecFloat.Binary.augmentedAddition (-1.5 : Binary32) (-2.5)).tail = 0x80000000 ∧
      toNat (ExecFloat.Binary.augmentedAddition (1.5 : Binary32) (-1.5)).head = 0 ∧
      toNat (ExecFloat.Binary.augmentedAddition (1.5 : Binary32) (-1.5)).tail = 0 ∧
      toNat (ExecFloat.Binary.augmentedSubtraction (ofNat 0x3f800001 : Binary32)
        (ofNat 0xb3800000)).tail = 0x33800000 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary32_augmentedAddition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary32_augmentedAddition

/--
The product `(1 + 2 ^ (-23)) ^ 2` has the head `1 + 2 ^ (-22)` and the tail `2 ^ (-46)`. An
overflowing head comes with an equal tail and the flags `overflow` and `inexact`, and a NaN
operand gives a NaN twice.
-/
theorem binary32_augmented_special :
    toNat (ExecFloat.Binary.augmentedMultiplication (ofNat 0x3f800001 : Binary32)
      (ofNat 0x3f800001)).head = 0x3f800002 ∧
      toNat (ExecFloat.Binary.augmentedMultiplication (ofNat 0x3f800001 : Binary32)
        (ofNat 0x3f800001)).tail = 0x28800000 ∧
      toNat (ExecFloat.Binary.augmentedAddition (ofNat 0x7f7fffff : Binary32)
        (ofNat 0x7f7fffff)).head = 0x7f800000 ∧
      toNat (ExecFloat.Binary.augmentedAddition (ofNat 0x7f7fffff : Binary32)
        (ofNat 0x7f7fffff)).tail = 0x7f800000 ∧
      (ExecFloat.Binary.augmentedAddition (ofNat 0x7f7fffff : Binary32)
        (ofNat 0x7f7fffff)).status.overflow = true ∧
      (ExecFloat.Binary.augmentedAddition (ofNat 0x7f7fffff : Binary32)
        (ofNat 0x7f7fffff)).status.inexact = true ∧
      ExecFloat.Binary.isNaN (ExecFloat.Binary.augmentedMultiplication
        (ofNat 0x7fc00000 : Binary32) 1).head = true ∧
      ExecFloat.Binary.isNaN (ExecFloat.Binary.augmentedMultiplication
        (ofNat 0x7fc00000 : Binary32) 1).tail = true ∧
      toNat (ExecFloat.Binary.augmentedMultiplication (3 : Binary64) (-0.5)).head =
        0xbff8000000000000 ∧
      toNat (ExecFloat.Binary.augmentedMultiplication (3 : Binary16) (0.5)).tail = 0 := by
  float_decide

set_option maxRecDepth 100000 in
/--
On the 1,024 pairs of encodings of the five-bit format: `augmentedSubtraction` is
`augmentedAddition` of the negated operand, and a sum that every rounding direction delivers
alike is the head, with a zero tail.
-/
theorem binary5_augmented : ∀ a b : Fin 32,
    (toNat (ExecFloat.Binary.augmentedSubtraction (ofNat a : Binary5) (ofNat b)).head =
        toNat (ExecFloat.Binary.augmentedAddition (ofNat a : Binary5) (-(ofNat b))).head ∧
      toNat (ExecFloat.Binary.augmentedSubtraction (ofNat a : Binary5) (ofNat b)).tail =
        toNat (ExecFloat.Binary.augmentedAddition (ofNat a : Binary5) (-(ofNat b))).tail) ∧
    (ExecFloat.Binary.isFinite ((ofNat a : Binary5) + ofNat b) = false ∨
      toNat (ExecFloat.Binary.add (ofNat a : Binary5) (ofNat b) (mode := .up)) ≠
        toNat (ExecFloat.Binary.add (ofNat a : Binary5) (ofNat b) (mode := .down)) ∨
      toNat (ExecFloat.Binary.augmentedAddition (ofNat a : Binary5) (ofNat b)).head =
          toNat ((ofNat a : Binary5) + ofNat b) ∧
        ExecFloat.Binary.isZero (ExecFloat.Binary.augmentedAddition (ofNat a : Binary5)
          (ofNat b)).tail = true) := by
  float_decide

/-- A format with 35 exponent bits and three fraction bits: the exponent range of 4,096 bits. -/
abbrev WideExponent := ExecFloat.Binary (exponentBits := 35) (fractionBits := 3)

/--
The augmented operations in a format with 35 exponent bits, where the exponents of the format
are numbers of ten digits: an exact sum, a tie toward zero, an exact product with its tail,
overflow from the largest finite value and from a product of two large powers of two, and
products below the least subnormal value and inside the subnormal range. No step of the kernel
forms shifts by an exponent of the format. The expected words are those of the compiled
reference operations.
-/
theorem wideExponent_augmented :
    toNat (ExecFloat.Binary.augmentedAddition (ofNat 0x1ffffffff8 : WideExponent)
      (ofNat 0x1ffffffff8)).head = 0x2000000000 ∧
      toNat (ExecFloat.Binary.augmentedAddition (ofNat 0x1ffffffff8 : WideExponent)
        (ofNat 0x1ffffffff8)).tail = 0x0 ∧
      toNat (ExecFloat.Binary.augmentedAddition (ofNat 0x1ffffffff9 : WideExponent)
        (ofNat 0x1fffffffd8)).head = 0x1ffffffff9 ∧
      toNat (ExecFloat.Binary.augmentedAddition (ofNat 0x1ffffffff9 : WideExponent)
        (ofNat 0x1fffffffd8)).tail = 0x1fffffffd8 ∧
      toNat (ExecFloat.Binary.augmentedSubtraction (ofNat 0x1ffffffff9 : WideExponent)
        (ofNat 0x5fffffffd8)).head = 0x1ffffffff9 ∧
      toNat (ExecFloat.Binary.augmentedSubtraction (ofNat 0x1ffffffff9 : WideExponent)
        (ofNat 0x5fffffffd8)).tail = 0x1fffffffd8 ∧
      toNat (ExecFloat.Binary.augmentedAddition (ofNat 0x3ffffffff7 : WideExponent)
        (ofNat 0x3ffffffff7)).head = 0x3ffffffff8 ∧
      toNat (ExecFloat.Binary.augmentedAddition (ofNat 0x3ffffffff7 : WideExponent)
        (ofNat 0x3ffffffff7)).tail = 0x3ffffffff8 ∧
      (ExecFloat.Binary.augmentedAddition (ofNat 0x3ffffffff7 : WideExponent)
        (ofNat 0x3ffffffff7)).status.overflow = true ∧
      toNat (ExecFloat.Binary.augmentedMultiplication (ofNat 0x1ffffffff9 : WideExponent)
        (ofNat 0x1ffffffff9)).head = 0x1ffffffffa ∧
      toNat (ExecFloat.Binary.augmentedMultiplication (ofNat 0x1ffffffff9 : WideExponent)
        (ofNat 0x1ffffffff9)).tail = 0x1fffffffc8 ∧
      toNat (ExecFloat.Binary.augmentedMultiplication (ofNat 0x2ffffffffb : WideExponent)
        (ofNat 0x0ffffffffd)).head = 0x2000000001 ∧
      toNat (ExecFloat.Binary.augmentedMultiplication (ofNat 0x2ffffffffb : WideExponent)
        (ofNat 0x0ffffffffd)).tail = 0x5fffffffc8 ∧
      toNat (ExecFloat.Binary.augmentedMultiplication (ofNat 0x2ffffffff8 : WideExponent)
        (ofNat 0x2ffffffff8)).head = 0x3ffffffff8 ∧
      (ExecFloat.Binary.augmentedMultiplication (ofNat 0x2ffffffff8 : WideExponent)
        (ofNat 0x2ffffffff8)).status.overflow = true ∧
      toNat (ExecFloat.Binary.augmentedMultiplication (ofNat 1 : WideExponent)
        (ofNat 1)).head = 0x0 ∧
      toNat (ExecFloat.Binary.augmentedMultiplication (ofNat 1 : WideExponent)
        (ofNat 1)).tail = 0x0 ∧
      (ExecFloat.Binary.augmentedMultiplication (ofNat 1 : WideExponent)
        (ofNat 1)).status.underflow = true ∧
      toNat (ExecFloat.Binary.augmentedMultiplication (ofNat 9 : WideExponent)
        (ofNat 0x1ffffffff0)).head = 0x4 ∧
      toNat (ExecFloat.Binary.augmentedMultiplication (ofNat 9 : WideExponent)
        (ofNat 0x1ffffffff0)).tail = 0x0 ∧
      (ExecFloat.Binary.augmentedMultiplication (ofNat 9 : WideExponent)
        (ofNat 0x1ffffffff0)).status.inexact = true := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.wideExponent_augmented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wideExponent_augmented

/-! ## Reductions (§9.4) -/

set_option maxRecDepth 100000 in
/--
One rounding of the exact result: `1e16 + 1 - 1e16` is one, where the two additions in order
lose the one. The empty sum is `+0`, a sum of negative zeros is `-0`, and the direction of the
one rounding is the caller's.
-/
theorem binary64_sum :
    ExecFloat.Binary.sum #[(1e16 : Binary64), 1, -1e16] = 1 ∧
      ((1e16 : Binary64) + 1) + -1e16 = 0 ∧
      toNat (ExecFloat.Binary.sum (#[] : Array Binary64)) = 0 ∧
      toNat (ExecFloat.Binary.sum #[(ofNat 0x8000000000000000 : Binary64),
        ofNat 0x8000000000000000]) = 0x8000000000000000 ∧
      toNat (ExecFloat.Binary.sum #[(1.5 : Binary64), -1.5]) = 0 ∧
      toNat (ExecFloat.Binary.sum #[(1.5 : Binary64), -1.5] (mode := .down)) =
        0x8000000000000000 ∧
      toNat (ExecFloat.Binary.sum #[(1 : Binary64), ofNat 0x3c30000000000000]
        (mode := .up)) = 0x3ff0000000000001 ∧
      toNat (ExecFloat.Binary.sum #[(ofNat 0x7ff0000000000000 : Binary64), 1]) =
        0x7ff0000000000000 ∧
      ExecFloat.Binary.isNaN (ExecFloat.Binary.sum #[(ofNat 0x7ff0000000000000 : Binary64),
        ofNat 0xfff0000000000000]) = true := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary64_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary64_sum

/--
`sumAbs` and `sumSquare` add magnitudes and squares without error, and an infinite operand
decides, also beside a quiet NaN. `dot` multiplies and adds without error and rejects arrays
of unequal lengths.
-/
theorem binary32_reductions :
    ExecFloat.Binary.sumAbs #[(-1.5 : Binary32), 2.5, -4] = 8 ∧
      ExecFloat.Binary.sumSquare #[(3 : Binary32), -4] = 25 ∧
      toNat (ExecFloat.Binary.sumAbs #[(ofNat 0xff800000 : Binary32), ofNat 0x7fc00000]) =
        0x7f800000 ∧
      toNat (ExecFloat.Binary.sumSquare #[(ofNat 0xff800000 : Binary32), 2]) = 0x7f800000 ∧
      ExecFloat.Binary.isNaN (ExecFloat.Binary.sumSquare #[(ofNat 0x7fc00000 : Binary32), 2]) =
        true ∧
      (match ExecFloat.Binary.dot #[(1 : Binary32), 2, 3] #[4, 5, 6] with
        | .ok value => toNat value
        | .error _ => 0) = 0x42000000 ∧
      (match ExecFloat.Binary.dot #[(16777217 : Binary64)] #[(16777217 : Binary64)] with
        | .ok value => toNat value
        | .error _ => 0) = 0x42f0000020000010 ∧
      (match ExecFloat.Binary.dot #[(1 : Binary32)] #[2, 3] with
        | .ok _ => 0
        | .error (.lengthMismatch left right) => 10 * left + right) = 12 ∧
      ExecFloat.Binary.sumSquare #[(1.5 : Binary16), 2] = 6.25 ∧
      ExecFloat.Binary.sum #[(0.5 : Binary128), 0.25, 0.125] = 0.875 := by
  float_decide

set_option maxRecDepth 100000 in
/--
On the 1,024 pairs of encodings of the five-bit format: the sum of two operands is their
addition and the dot product of one pair is their product, NaNs, infinities and signed zeros
included.
-/
theorem binary5_reductions : ∀ a b : Fin 32,
    toNat (ExecFloat.Binary.sum #[(ofNat a : Binary5), ofNat b]) =
        toNat ((ofNat a : Binary5) + ofNat b) ∧
      (match ExecFloat.Binary.dot #[(ofNat a : Binary5)] #[(ofNat b : Binary5)] with
        | .ok value => toNat value
        | .error _ => 32) = toNat ((ofNat a : Binary5) * ofNat b) := by
  float_decide

/--
`scaledProd` delivers a product of magnitude in `[1, 2]` with the exponent as the scale
factor: `3 × 5 × 7` is `1.640625 × 2 ^ 6`, the square of the largest finite value does not
overflow, the empty product is one, a zero factor gives a zero with the product of the signs,
and zero times infinity is invalid.
-/
theorem binary32_scaledProd :
    (ExecFloat.Binary.scaledProd #[(3 : Binary32), 5, 7]).product = 1.640625 ∧
      (ExecFloat.Binary.scaledProd #[(3 : Binary32), 5, 7]).scaleFactor = 6 ∧
      toNat (ExecFloat.Binary.scaledProd #[(ofNat 0x7f7fffff : Binary32),
        ofNat 0x7f7fffff]).product = 0x3ffffffe ∧
      (ExecFloat.Binary.scaledProd #[(ofNat 0x7f7fffff : Binary32),
        ofNat 0x7f7fffff]).scaleFactor = 255 ∧
      (ExecFloat.Binary.scaledProd #[(ofNat 0x7f7fffff : Binary32),
        ofNat 0x7f7fffff]).status.inexact = true ∧
      (ExecFloat.Binary.scaledProd (#[] : Array Binary32)).product = 1 ∧
      toNat (ExecFloat.Binary.scaledProd #[(ofNat 0 : Binary32), -3]).product = 0x80000000 ∧
      toNat (ExecFloat.Binary.scaledProd #[(2 : Binary32), ofNat 0xff800000]).product =
        0xff800000 ∧
      (ExecFloat.Binary.scaledProd #[(ofNat 0 : Binary32), ofNat 0x7f800000]).status.invalid =
        true ∧
      ExecFloat.Binary.isNaN (ExecFloat.Binary.scaledProd #[(ofNat 0 : Binary32),
        ofNat 0x7f800000]).product = true := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary32_scaledProd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary32_scaledProd

/--
`scaledProdSum` and `scaledProdDiff` multiply exact sums and differences: `(1 + 3) (2 + 4)` is
`1.5 × 2 ^ 4` and `(5 - 3) (7 - 4)` is `1.5 × 2 ^ 2`. Arrays of unequal lengths are rejected.
-/
theorem binary64_scaledProdOfSums :
    (match ExecFloat.Binary.scaledProdSum #[(1 : Binary64), 2] #[3, 4] with
      | .ok outcome => toNat outcome.product + outcome.scaleFactor.natAbs
      | .error _ => 0) = 0x3ff8000000000000 + 4 ∧
      (match ExecFloat.Binary.scaledProdDiff #[(5 : Binary64), 7] #[3, 4] with
        | .ok outcome => toNat outcome.product + outcome.scaleFactor.natAbs
        | .error _ => 0) = 0x3ff8000000000000 + 2 ∧
      (match ExecFloat.Binary.scaledProdSum #[(1 : Binary64)] #[3, 4] with
        | .ok _ => 0
        | .error (.lengthMismatch left right) => 10 * left + right) = 12 ∧
      (match ExecFloat.Binary.scaledProdDiff #[(1.5 : Binary16)] #[(1.5 : Binary16)] with
        | .ok outcome => toNat outcome.product
        | .error _ => 1) = 0 := by
  float_decide

/--
On the 1,024 pairs of encodings of the five-bit format: the scaled product of one difference
is the scaled product of the sum with the negated operand.
-/
theorem binary5_scaledProd : ∀ a b : Fin 32,
    (match ExecFloat.Binary.scaledProdDiff #[(ofNat a : Binary5)] #[(ofNat b : Binary5)] with
      | .ok outcome => toNat outcome.product + 32 * outcome.scaleFactor.natAbs
      | .error _ => 0) =
      (match ExecFloat.Binary.scaledProdSum #[(ofNat a : Binary5)] #[-(ofNat b : Binary5)] with
        | .ok outcome => toNat outcome.product + 32 * outcome.scaleFactor.natAbs
        | .error _ => 0) := by
  float_decide

/-! ## Reductions with one rounding at each addition (§9.4) -/

/-- A reduction accumulated in the format of the operand `anchor`, as an encoding. -/
def inFormat {fmt : FloatFormat} (_anchor : Model fmt)
    (reduce : (acc out : FloatFormat) → Model out) : Nat :=
  (reduce fmt fmt).toNatBits

/--
The order and the accumulator decide the result: from left to right in binary32,
`1e8 + 1 - 1e8` is zero; along the tree that cancels first, and with a binary64 accumulator, it
is one. `sumAbsInOrder`, `sumSquareInOrder` and `dotInOrder` add their terms the same way.
-/
theorem binary32_inOrder :
    (Model.sumInOrder FloatFormat.binary32 FloatFormat.binary32
      [ExecFloat.Binary.toModel (1e8 : Binary32), ExecFloat.Binary.toModel (1 : Binary32),
        ExecFloat.Binary.toModel (-1e8 : Binary32)]).toNatBits = 0 ∧
      (Model.sumAlong FloatFormat.binary32 FloatFormat.binary32
        (.node (.node (.leaf (ExecFloat.Binary.toModel (1e8 : Binary32)))
          (.leaf (ExecFloat.Binary.toModel (-1e8 : Binary32))))
          (.leaf (ExecFloat.Binary.toModel (1 : Binary32))))).toNatBits = 0x3f800000 ∧
      (Model.sumInOrder FloatFormat.binary64 FloatFormat.binary32
        [ExecFloat.Binary.toModel (1e8 : Binary32), ExecFloat.Binary.toModel (1 : Binary32),
          ExecFloat.Binary.toModel (-1e8 : Binary32)]).toNatBits = 0x3f800000 ∧
      (Model.sumAbsInOrder FloatFormat.binary32 FloatFormat.binary32
        [ExecFloat.Binary.toModel (-1.5 : Binary32),
          ExecFloat.Binary.toModel (2.5 : Binary32)]).toNatBits = 0x40800000 ∧
      (Model.sumSquareInOrder FloatFormat.binary64 FloatFormat.binary64
        [ExecFloat.Binary.toModel (3 : Binary16),
          ExecFloat.Binary.toModel (-4 : Binary16)]).toNatBits = 0x4039000000000000 ∧
      (Model.dotInOrder FloatFormat.binary32 FloatFormat.binary32
        ([ExecFloat.Binary.toModel (1 : Binary32), ExecFloat.Binary.toModel (2 : Binary32),
          ExecFloat.Binary.toModel (3 : Binary32)].zip
          [ExecFloat.Binary.toModel (4 : Binary32), ExecFloat.Binary.toModel (5 : Binary32),
            ExecFloat.Binary.toModel (6 : Binary32)])).toNatBits = 0x42000000 ∧
      (Model.sumInOrder FloatFormat.binary32 FloatFormat.binary32
        ([] : List (Model FloatFormat.binary32))).toNatBits = 0 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary32_inOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary32_inOrder

/--
On the 1,024 pairs of encodings of the five-bit format without a NaN: the sum of two operands
along the tree of one addition is their addition, and the sum of their squares along that tree
is the sum of the two products. (A NaN operand is quieted by the conversion to the accumulator
before the addition chooses between two NaNs.)
-/
theorem binary5_along : ∀ a b : Fin 32,
    (ExecFloat.Binary.isNaN (ofNat a : Binary5) || ExecFloat.Binary.isNaN (ofNat b : Binary5)) =
        true ∨
      inFormat (ExecFloat.Binary.toModel (ofNat a : Binary5)) (fun acc out =>
          Model.sumAlong acc out (.node (.leaf (ExecFloat.Binary.toModel (ofNat a : Binary5)))
            (.leaf (ExecFloat.Binary.toModel (ofNat b : Binary5))))) =
          toNat ((ofNat a : Binary5) + ofNat b) ∧
        inFormat (ExecFloat.Binary.toModel (ofNat a : Binary5)) (fun acc out =>
          Model.sumSquareAlong acc out
            (.node (.leaf (ExecFloat.Binary.toModel (ofNat a : Binary5)))
              (.leaf (ExecFloat.Binary.toModel (ofNat b : Binary5))))) =
          toNat ((ofNat a : Binary5) * ofNat a + (ofNat b : Binary5) * ofNat b) := by
  float_decide [inFormat]

/-! ## `pown` (§9.2) -/

/--
`pown` through its kernel form: exact powers, powers rounded once with positive and negative
exponents, the exponent zero at a number and at NaNs, the zeros and the infinities with the
sign of an odd power, overflow, underflow, subnormal results and the least subnormal squared.
-/
theorem binary32_pown :
    toNat (ExecFloat.Binary.pown (2 : Binary32) 10) = 0x44800000 ∧
      toNat (ExecFloat.Binary.pown (3 : Binary32) 5) = 0x43730000 ∧
      toNat (ExecFloat.Binary.pown (1.5 : Binary32) (-2)) = 0x3ee38e39 ∧
      toNat (ExecFloat.Binary.pown (-2 : Binary32) 3) = 0xc1000000 ∧
      toNat (ExecFloat.Binary.pown (-2 : Binary32) (-3)) = 0xbe000000 ∧
      toNat (ExecFloat.Binary.pown (10 : Binary32) (-1)) = 0x3dcccccd ∧
      toNat (ExecFloat.Binary.pown (10 : Binary32) (-2)) = 0x3c23d70a ∧
      toNat (ExecFloat.Binary.pown (3 : Binary32) (-5)) = 0x3b86d905 ∧
      toNat (ExecFloat.Binary.pown (1.0000001 : Binary32) 1000000) = 0x3f90349d ∧
      toNat (ExecFloat.Binary.pown (7 : Binary32) 0) = 0x3f800000 ∧
      toNat (ExecFloat.Binary.pown (ofNat 0x7fc00001 : Binary32) 0) = 0x3f800000 ∧
      toNat (ExecFloat.Binary.pown (ofNat 0x7fa00001 : Binary32) 0) = 0x7fe00001 ∧
      toNat (ExecFloat.Binary.pown (ofNat 0 : Binary32) (-1)) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.pown (ofNat 0x80000000 : Binary32) (-3)) = 0xff800000 ∧
      toNat (ExecFloat.Binary.pown (ofNat 0x80000000 : Binary32) 3) = 0x80000000 ∧
      toNat (ExecFloat.Binary.pown (ofNat 0x80000000 : Binary32) 2) = 0x0 ∧
      toNat (ExecFloat.Binary.pown (ofNat 0x7f800000 : Binary32) (-2)) = 0x0 ∧
      toNat (ExecFloat.Binary.pown (ofNat 0xff800000 : Binary32) 3) = 0xff800000 ∧
      toNat (ExecFloat.Binary.pown (2 : Binary32) 200) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.pown (2 : Binary32) (-200)) = 0x0 ∧
      toNat (ExecFloat.Binary.pown (2 : Binary32) (-140)) = 0x200 ∧
      toNat (ExecFloat.Binary.pown (-2 : Binary32) (-149)) = 0x80000001 ∧
      toNat (ExecFloat.Binary.pown (ofNat 1 : Binary32) 2) = 0x0 ∧
      toNat (ExecFloat.Binary.pown (ofNat 0x7f7fffff : Binary32) (-1)) = 0x200000 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary32_pown' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary32_pown

/--
On the 32 encodings of the five-bit format: the power zero of a value that is not a signaling
NaN is one, and for a value that is not a NaN the first power is the value, the square is the
product with itself and the power minus one is the quotient of one by the value, zeros and
infinities included.
-/
theorem binary5_pown : ∀ a : Fin 32,
    (ExecFloat.Binary.isSignaling (ofNat a : Binary5) = true ∨
        ExecFloat.Binary.pown (ofNat a : Binary5) 0 = 1) ∧
      (ExecFloat.Binary.isNaN (ofNat a : Binary5) = true ∨
        ExecFloat.Binary.pown (ofNat a : Binary5) 1 = ofNat a ∧
        ExecFloat.Binary.pown (ofNat a : Binary5) 2 = (ofNat a : Binary5) * ofNat a ∧
        ExecFloat.Binary.pown (ofNat a : Binary5) (-1) = 1 / (ofNat a : Binary5)) := by
  float_decide

/-! ## `rootn`, `rSqrt` and `hypot` (§9.2) -/

set_option backward.isDefEq.respectTransparency false in
example (x y : Binary64) (n : Int) : ExecFloat.Binary.rootn x n = Value.rootn n x ∧
    ExecFloat.Binary.rSqrt x = Value.rSqrt x ∧
    ExecFloat.Binary.hypot x y = Value.hypot x y := by
  simp only [kernel_optimize, and_self]

/--
`rootn` through its kernel form: exact roots, roots rounded once with positive and negative
degrees, the odd roots of negative values, the degrees one and minus one, the least subnormal,
the largest subnormal, the least normal and the largest finite value, the zeros and the
infinities with the sign of an odd root, the degree zero, an even root of a negative value and
a signaling NaN.
-/
theorem binary32_rootn :
    toNat (ExecFloat.Binary.rootn (8 : Binary32) 3) = 0x40000000 ∧
      toNat (ExecFloat.Binary.rootn (2 : Binary32) 2) = 0x3fb504f3 ∧
      toNat (ExecFloat.Binary.rootn (10 : Binary32) 3) = 0x4009e242 ∧
      toNat (ExecFloat.Binary.rootn (-27 : Binary32) 3) = 0xc0400000 ∧
      toNat (ExecFloat.Binary.rootn (-8 : Binary32) (-3)) = 0xbf000000 ∧
      toNat (ExecFloat.Binary.rootn (2 : Binary32) (-2)) = 0x3f3504f3 ∧
      toNat (ExecFloat.Binary.rootn (10 : Binary32) (-3)) = 0x3eeda63c ∧
      toNat (ExecFloat.Binary.rootn (3 : Binary32) 5) = 0x3f9f741d ∧
      toNat (ExecFloat.Binary.rootn (2 : Binary32) 100) = 0x3f80e3eb ∧
      toNat (ExecFloat.Binary.rootn (2 : Binary32) (-100)) = 0x3f7e3b4f ∧
      toNat (ExecFloat.Binary.rootn (1.5 : Binary32) 7) = 0x3f87a216 ∧
      toNat (ExecFloat.Binary.rootn (0.1 : Binary32) 3) = 0x3eeda63c ∧
      toNat (ExecFloat.Binary.rootn (1000000 : Binary32) 6) = 0x41200000 ∧
      toNat (ExecFloat.Binary.rootn (7 : Binary32) 1) = 0x40e00000 ∧
      toNat (ExecFloat.Binary.rootn (7 : Binary32) (-1)) = 0x3e124925 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 1 : Binary32) 2) = 0x1a3504f3 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 1 : Binary32) 3) = 0x26a14518 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 1 : Binary32) 7) = 0x34d2017f ∧
      toNat (ExecFloat.Binary.rootn (ofNat 1 : Binary32) (-2)) = 0x64b504f3 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 1 : Binary32) 1) = 0x1 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 1 : Binary32) (-1)) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x00400000 : Binary32) (-1)) = 0x7f000000 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x007fffff : Binary32) 2) = 0x1fffffff ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x00800000 : Binary32) 2) = 0x20000000 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x7f7fffff : Binary32) 2) = 0x5f7fffff ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x7f7fffff : Binary32) 3) = 0x54cb2ff5 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x7f7fffff : Binary32) (-2)) = 0x1f800000 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x7f7fffff : Binary32) (-1)) = 0x200000 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x80000001 : Binary32) 3) = 0xa6a14518 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x80000001 : Binary32) (-3)) = 0xd84b2ff5 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0 : Binary32) 3) = 0x0 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x80000000 : Binary32) 3) = 0x80000000 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x80000000 : Binary32) 2) = 0x0 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0 : Binary32) (-3)) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x80000000 : Binary32) (-3)) = 0xff800000 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x80000000 : Binary32) (-2)) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x7f800000 : Binary32) 2) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0xff800000 : Binary32) 3) = 0xff800000 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x7f800000 : Binary32) (-2)) = 0x0 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0xff800000 : Binary32) (-3)) = 0x80000000 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0xff800000 : Binary32) 2) = 0x7fc00000 ∧
      toNat (ExecFloat.Binary.rootn (-4 : Binary32) 2) = 0x7fc00000 ∧
      toNat (ExecFloat.Binary.rootn (4 : Binary32) 0) = 0x7fc00000 ∧
      toNat (ExecFloat.Binary.rootn (ofNat 0x7fa00001 : Binary32) 3) = 0x7fe00001 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary32_rootn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary32_rootn

/--
`rSqrt` through its kernel form: exact results, results rounded once, the neighbors of one, the
least subnormal, the largest subnormal, the least normal and the largest finite value, the
zeros, a negative value, the infinities and a signaling NaN.
-/
theorem binary32_rSqrt :
    toNat (ExecFloat.Binary.rSqrt (4 : Binary32)) = 0x3f000000 ∧
      toNat (ExecFloat.Binary.rSqrt (2 : Binary32)) = 0x3f3504f3 ∧
      toNat (ExecFloat.Binary.rSqrt (0.25 : Binary32)) = 0x40000000 ∧
      toNat (ExecFloat.Binary.rSqrt (3 : Binary32)) = 0x3f13cd3a ∧
      toNat (ExecFloat.Binary.rSqrt (10 : Binary32)) = 0x3ea1e89b ∧
      toNat (ExecFloat.Binary.rSqrt (1 : Binary32)) = 0x3f800000 ∧
      toNat (ExecFloat.Binary.rSqrt (ofNat 0x3eaaaaab : Binary32)) = 0x3fddb3d7 ∧
      toNat (ExecFloat.Binary.rSqrt (ofNat 0x3f800001 : Binary32)) = 0x3f7fffff ∧
      toNat (ExecFloat.Binary.rSqrt (ofNat 0x3f7fffff : Binary32)) = 0x3f800000 ∧
      toNat (ExecFloat.Binary.rSqrt (ofNat 1 : Binary32)) = 0x64b504f3 ∧
      toNat (ExecFloat.Binary.rSqrt (ofNat 0x007fffff : Binary32)) = 0x5f000001 ∧
      toNat (ExecFloat.Binary.rSqrt (ofNat 0x00800000 : Binary32)) = 0x5f000000 ∧
      toNat (ExecFloat.Binary.rSqrt (ofNat 0x7f7fffff : Binary32)) = 0x1f800000 ∧
      toNat (ExecFloat.Binary.rSqrt (ofNat 0 : Binary32)) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.rSqrt (ofNat 0x80000000 : Binary32)) = 0xff800000 ∧
      toNat (ExecFloat.Binary.rSqrt (-1 : Binary32)) = 0x7fc00000 ∧
      toNat (ExecFloat.Binary.rSqrt (ofNat 0x7f800000 : Binary32)) = 0x0 ∧
      toNat (ExecFloat.Binary.rSqrt (ofNat 0xff800000 : Binary32)) = 0x7fc00000 ∧
      toNat (ExecFloat.Binary.rSqrt (ofNat 0x7fa00001 : Binary32)) = 0x7fe00001 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary32_rSqrt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary32_rSqrt

/--
`hypot` through its kernel form: exact norms, norms rounded once, an operand far below the
other, subnormal operands and results, the least normal and the largest finite values with a
norm that overflows and one that does not, the zeros, the infinities beside a number and beside
a quiet NaN, and quiet and signaling NaNs.
-/
theorem binary32_hypot :
    toNat (ExecFloat.Binary.hypot (3 : Binary32) 4) = 0x40a00000 ∧
      toNat (ExecFloat.Binary.hypot (1 : Binary32) 1) = 0x3fb504f3 ∧
      toNat (ExecFloat.Binary.hypot (-5 : Binary32) 12) = 0x41500000 ∧
      toNat (ExecFloat.Binary.hypot (-7 : Binary32) (-24)) = 0x41c80000 ∧
      toNat (ExecFloat.Binary.hypot (1.5 : Binary32) 2) = 0x40200000 ∧
      toNat (ExecFloat.Binary.hypot (0.1 : Binary32) 0.2) = 0x3e64f92e ∧
      toNat (ExecFloat.Binary.hypot (1 : Binary32) 3) = 0x404a62c2 ∧
      toNat (ExecFloat.Binary.hypot (1 : Binary32) (ofNat 0x35800000)) = 0x3f800000 ∧
      toNat (ExecFloat.Binary.hypot (16777216 : Binary32) 1) = 0x4b800000 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 1 : Binary32) (ofNat 1)) = 0x1 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 1 : Binary32) (ofNat 0)) = 0x1 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 0x80000001 : Binary32) (ofNat 3)) = 0x3 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 2 : Binary32) (ofNat 0x80000002)) = 0x3 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 3 : Binary32) (ofNat 4)) = 0x5 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 0x007fffff : Binary32) (ofNat 0x80000000)) =
        0x007fffff ∧
      toNat (ExecFloat.Binary.hypot (ofNat 0x00800000 : Binary32) (ofNat 0x00800000)) =
        0x00b504f3 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 0x7f000000 : Binary32) (ofNat 0x7f000000)) =
        0x7f3504f3 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 0x7f3504f3 : Binary32) (ofNat 0x7f3504f3)) =
        0x7f800000 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 0x7f7fffff : Binary32) (ofNat 0x7f7fffff)) =
        0x7f800000 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 0x7f7fffff : Binary32) (ofNat 1)) = 0x7f7fffff ∧
      toNat (ExecFloat.Binary.hypot (ofNat 0 : Binary32) (ofNat 0x80000000)) = 0x0 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 0x80000000 : Binary32) (ofNat 0x80000000)) = 0x0 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 0xff800000 : Binary32) 1) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 0x7f800000 : Binary32) (ofNat 0x7fc00001)) =
        0x7f800000 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 0x7fc00001 : Binary32) (ofNat 0xff800000)) =
        0x7f800000 ∧
      toNat (ExecFloat.Binary.hypot (1 : Binary32) (ofNat 0x7fc00001)) = 0x7fc00001 ∧
      toNat (ExecFloat.Binary.hypot (ofNat 0x7fa00001 : Binary32) (ofNat 0x7f800000)) =
        0x7fe00001 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary32_hypot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary32_hypot

/-- The same norms in binary16, binary64 and binary128. -/
theorem hypot_by_format :
    toNat (ExecFloat.Binary.hypot (3 : Binary16) 4) = 0x4500 ∧
      toNat (ExecFloat.Binary.hypot (1 : Binary16) 1) = 0x3da8 ∧
      toNat (ExecFloat.Binary.hypot (0.1 : Binary16) 0.2) = 0x3327 ∧
      toNat (ExecFloat.Binary.hypot (1 : Binary16) 3) = 0x4253 ∧
      toNat (ExecFloat.Binary.hypot (3 : Binary64) 4) = 0x4014000000000000 ∧
      toNat (ExecFloat.Binary.hypot (1 : Binary64) 1) = 0x3ff6a09e667f3bcd ∧
      toNat (ExecFloat.Binary.hypot (0.1 : Binary64) 0.2) = 0x3fcc9f25c5bfedda ∧
      toNat (ExecFloat.Binary.hypot (1 : Binary64) 3) = 0x40094c583ada5b53 ∧
      toNat (ExecFloat.Binary.hypot (3 : Binary128) 4) = 0x40014000000000000000000000000000 ∧
      toNat (ExecFloat.Binary.hypot (1 : Binary128) 1) = 0x3fff6a09e667f3bcc908b2fb1366ea95 ∧
      toNat (ExecFloat.Binary.hypot (0.1 : Binary128) 0.2) =
        0x3ffcc9f25c5bfedd93565294670094b0 ∧
      toNat (ExecFloat.Binary.hypot (1 : Binary128) 3) = 0x400094c583ada5b529204a2bc830cd9c := by
  float_decide

/--
On every pair of the 32 encodings of the five-bit format without a NaN: the norm does not
depend on the order of its operands, and the norm with a zero is the magnitude of the other
operand, infinities included.
-/
theorem binary5_hypot : ∀ a b : Fin 32,
    (ExecFloat.Binary.isNaN (ofNat a : Binary5) || ExecFloat.Binary.isNaN (ofNat b : Binary5)) =
        true ∨
      ExecFloat.Binary.hypot (ofNat a : Binary5) (ofNat b) =
          ExecFloat.Binary.hypot (ofNat b : Binary5) (ofNat a) ∧
        (ExecFloat.Binary.isZero (ofNat b : Binary5) = false ∨
          ExecFloat.Binary.hypot (ofNat a : Binary5) (ofNat b) =
            ExecFloat.Binary.abs (ofNat a : Binary5)) := by
  float_decide

/-- The same roots in binary16, binary64 and binary128. -/
theorem roots_by_format :
    toNat (ExecFloat.Binary.rootn (2 : Binary16) 2) = 0x3da8 ∧
      toNat (ExecFloat.Binary.rootn (10 : Binary16) 3) = 0x404f ∧
      toNat (ExecFloat.Binary.rootn (-27 : Binary16) 3) = 0xc200 ∧
      toNat (ExecFloat.Binary.rootn (2 : Binary16) (-2)) = 0x39a8 ∧
      toNat (ExecFloat.Binary.rootn (0.1 : Binary16) 5) = 0x390c ∧
      toNat (ExecFloat.Binary.rSqrt (2 : Binary16)) = 0x39a8 ∧
      toNat (ExecFloat.Binary.rSqrt (3 : Binary16)) = 0x389e ∧
      toNat (ExecFloat.Binary.rSqrt (0.1 : Binary16)) = 0x4253 ∧
      toNat (ExecFloat.Binary.rootn (2 : Binary64) 2) = 0x3ff6a09e667f3bcd ∧
      toNat (ExecFloat.Binary.rootn (10 : Binary64) 3) = 0x40013c484138704f ∧
      toNat (ExecFloat.Binary.rootn (-27 : Binary64) 3) = 0xc008000000000000 ∧
      toNat (ExecFloat.Binary.rootn (2 : Binary64) (-2)) = 0x3fe6a09e667f3bcd ∧
      toNat (ExecFloat.Binary.rootn (0.1 : Binary64) 5) = 0x3fe430cd74f6d478 ∧
      toNat (ExecFloat.Binary.rSqrt (2 : Binary64)) = 0x3fe6a09e667f3bcd ∧
      toNat (ExecFloat.Binary.rSqrt (3 : Binary64)) = 0x3fe279a74590331c ∧
      toNat (ExecFloat.Binary.rSqrt (0.1 : Binary64)) = 0x40094c583ada5b52 ∧
      toNat (ExecFloat.Binary.rootn (2 : Binary128) 2) = 0x3fff6a09e667f3bcc908b2fb1366ea95 ∧
      toNat (ExecFloat.Binary.rootn (10 : Binary128) 3) = 0x400013c484138704eca8a22d724dea09 ∧
      toNat (ExecFloat.Binary.rootn (-27 : Binary128) 3) = 0xc0008000000000000000000000000000 ∧
      toNat (ExecFloat.Binary.rootn (2 : Binary128) (-2)) = 0x3ffe6a09e667f3bcc908b2fb1366ea95 ∧
      toNat (ExecFloat.Binary.rootn (0.1 : Binary128) 5) = 0x3ffe430cd74f6d477ffa9a0d5ea65c50 ∧
      toNat (ExecFloat.Binary.rSqrt (2 : Binary128)) = 0x3ffe6a09e667f3bcc908b2fb1366ea95 ∧
      toNat (ExecFloat.Binary.rSqrt (3 : Binary128)) = 0x3ffe279a74590331c4d218f81e4afb25 ∧
      toNat (ExecFloat.Binary.rSqrt (0.1 : Binary128)) = 0x400094c583ada5b529204a2bc830cd9c := by
  float_decide

/--
On the 32 encodings of the five-bit format, for a value that is not a NaN: the first root is
the value, the root of degree minus one is the quotient of one by the value, and for a value
without the sign bit the square root is the root of degree two and the reciprocal square root
is the root of degree minus two, zeros and infinities included.
-/
theorem binary5_roots : ∀ a : Fin 32,
    ExecFloat.Binary.isNaN (ofNat a : Binary5) = true ∨
      ExecFloat.Binary.rootn (ofNat a : Binary5) 1 = ofNat a ∧
      ExecFloat.Binary.rootn (ofNat a : Binary5) (-1) = 1 / (ofNat a : Binary5) ∧
      (ExecFloat.Binary.signBit (ofNat a : Binary5) = true ∨
        ExecFloat.Binary.rootn (ofNat a : Binary5) 2 = ExecFloat.Binary.sqrt (ofNat a : Binary5) ∧
        ExecFloat.Binary.rSqrt (ofNat a : Binary5) =
          ExecFloat.Binary.rootn (ofNat a : Binary5) (-2)) := by
  float_decide

/-! ## Conversions to and from character sequences (§5.12) -/

/-- A format of 1,024 bits: 27 exponent bits and 996 fraction bits. -/
abbrev Binary1024 := ExecFloat.Binary (exponentBits := 27) (fractionBits := 996)

/-- The encoding of a parsed value, and zero for an error. -/
def parsedWord {F : Type} [FloatLib.Numerics.EncodedFormat F] {format : FloatFormat}
    [NatView F format] (outcome : Except Model.ParseError (ExecFloat F)) : Nat :=
  match outcome with
  | .ok value => toNat value
  | .error _ => 0

/-- The rewrite turns a formatted value that is read back into operations on its encoding. -/
example (x : Binary64) (mode : Model.IEEERoundingMode) :
    (ExecFloat.Binary.format x (mode := mode)).length =
        (formatCharacters FloatFormat.binary64 .shortest mode (toNat x)).length ∧
      (ExecFloat.Binary.parse (ExecFloat.Binary.format x .hex) mode :
          Except Model.ParseError Binary64) =
        (parseCharacters FloatFormat.binary64 mode
          (formatCharacters FloatFormat.binary64 .hex .nearest (toNat x))).map ofNat := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [kernel_optimize]
  exact ⟨rfl, rfl⟩

/--
The display of binary64 values: short exact values, the shortest decimal that reads back, the
least subnormal and the largest finite value, the negative zero, the infinities and a NaN.
-/
theorem binary64_format :
    ExecFloat.Binary.format (1.5 : Binary64) = "1.5" ∧
      ExecFloat.Binary.format (0.1 : Binary64) = "0.1" ∧
      ExecFloat.Binary.format (1e23 : Binary64) = "1e23" ∧
      ExecFloat.Binary.format (-2.5e-7 : Binary64) = "-2.5e-7" ∧
      ExecFloat.Binary.format (ofNat 1 : Binary64) = "5e-324" ∧
      ExecFloat.Binary.format (ofNat 0x7fefffffffffffff : Binary64) = "1.7976931348623157e308" ∧
      ExecFloat.Binary.format (ofNat 0x8000000000000000 : Binary64) = "-0" ∧
      ExecFloat.Binary.format (ofNat 0x7ff0000000000000 : Binary64) = "inf" ∧
      ExecFloat.Binary.format (ofNat 0xfff0000000000000 : Binary64) = "-inf" ∧
      ExecFloat.Binary.format (ofNat 0x7ff8000000000001 : Binary64) = "nan" := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary64_format' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary64_format

/--
Every style of `format` on the binary32 value nearest `0.1`, with the rounding directions that
change its digits, and the exact spellings of a NaN with its payload and of an infinity.
-/
theorem binary32_styles :
    ExecFloat.Binary.format (0.1 : Binary32) = "0.1" ∧
      ExecFloat.Binary.format (0.1 : Binary32) (mode := .down) = "0.100000002" ∧
      ExecFloat.Binary.format (0.1 : Binary32) .exact = "100000001490116119384765625e-27" ∧
      ExecFloat.Binary.format (0.1 : Binary32) (.significant 4) = "1000e-4" ∧
      ExecFloat.Binary.format (0.1 : Binary32) (.significant 4) .up = "1001e-4" ∧
      ExecFloat.Binary.format (0.1 : Binary32) (.fixed 3) = "0.100" ∧
      ExecFloat.Binary.format (0.1 : Binary32) (.fixed 3) .up = "0.101" ∧
      ExecFloat.Binary.format (0.1 : Binary32) (.scientific 3) = "1.000e-1" ∧
      ExecFloat.Binary.format (0.1 : Binary32) .hex = "0xcccccdp-27" ∧
      ExecFloat.Binary.format (0.1 : Binary32) (.hex (.significant 3)) = "0x19ap-12" ∧
      ExecFloat.Binary.format (0.1 : Binary32) (.hex (.significant 3)) .down = "0x199p-12" ∧
      ExecFloat.Binary.format (65504 : Binary16) = "65504" ∧
      ExecFloat.Binary.format (ofNat 0x7ff8000000000001 : Binary64) .exact = "NaN2251799813685249" ∧
      ExecFloat.Binary.format (ofNat 0xfff4000000000001 : Binary64) .hex = "-sNaN1125899906842625" ∧
      ExecFloat.Binary.format (ofNat 0xfff0000000000000 : Binary64) .exact = "-Infinity" := by
  float_decide

/--
`parse` on decimal and hexadecimal text in several rounding directions: a value below the least
subnormal, an exponent far beyond the range, both sides of half the least subnormal of
binary64, an infinity, and NaNs with and without a payload.
-/
theorem binary32_parse :
    parsedWord (ExecFloat.Binary.parse "0.1" :
        Except Model.ParseError Binary32) = 0x3dcccccd ∧
      parsedWord (ExecFloat.Binary.parse "-1e-50" .down :
        Except Model.ParseError Binary32) = 0x80000001 ∧
      parsedWord (ExecFloat.Binary.parse "-1e-50" .up :
        Except Model.ParseError Binary32) = 0x80000000 ∧
      parsedWord (ExecFloat.Binary.parse "1e99999999999" :
        Except Model.ParseError Binary32) = 0x7f800000 ∧
      parsedWord (ExecFloat.Binary.parse "1e99999999999" .towardZero :
        Except Model.ParseError Binary32) = 0x7f7fffff ∧
      parsedWord (ExecFloat.Binary.parse "0x1.8p1" :
        Except Model.ParseError Binary32) = 0x40400000 ∧
      parsedWord (ExecFloat.Binary.parse "-Infinity" :
        Except Model.ParseError Binary32) = 0xff800000 ∧
      parsedWord (ExecFloat.Binary.parse "sNaN5" :
        Except Model.ParseError Binary32) = 0x7f800005 ∧
      parsedWord (ExecFloat.Binary.parse "nan" :
        Except Model.ParseError Binary32) = 0x7fc00000 ∧
      parsedWord (ExecFloat.Binary.parse "2.4703282292062328e-324" :
        Except Model.ParseError Binary64) = 1 ∧
      parsedWord (ExecFloat.Binary.parse "2.4703282292062327e-324" :
        Except Model.ParseError Binary64) = 0 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelCoverage.binary32_parse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary32_parse

/--
At 1,024 bits: the shortest decimal of the value nearest `0.1` has three characters, a third
has 303 characters in decimal and 257 in hexadecimal, and each of them reads back as the value
it was written for.
-/
theorem binary1024_text :
    ExecFloat.Binary.format (0.1 : Binary1024) = "0.1" ∧
      (ExecFloat.Binary.format ((1 : Binary1024) / 3)).length = 303 ∧
      (ExecFloat.Binary.format ((1 : Binary1024) / 3) .hex).length = 257 ∧
      parsedWord (ExecFloat.Binary.parse (ExecFloat.Binary.format ((1 : Binary1024) / 3)) :
        Except Model.ParseError Binary1024) = toNat ((1 : Binary1024) / 3) ∧
      parsedWord (ExecFloat.Binary.parse (ExecFloat.Binary.format ((1 : Binary1024) / 3) .hex) :
        Except Model.ParseError Binary1024) = toNat ((1 : Binary1024) / 3) := by
  float_decide

/--
On the 32 encodings of the five-bit format: the hexadecimal and the exact decimal text read
back as the encoding, NaNs with their payloads included, and the display of a value that is not
a NaN reads back as the value in each of the six rounding directions.
-/
theorem binary5_text : ∀ a : Fin 32,
    parsedWord (ExecFloat.Binary.parse (ExecFloat.Binary.format (ofNat a : Binary5) .hex) :
        Except Model.ParseError Binary5) = a ∧
      parsedWord (ExecFloat.Binary.parse (ExecFloat.Binary.format (ofNat a : Binary5) .exact) :
        Except Model.ParseError Binary5) = a ∧
      (ExecFloat.Binary.isNaN (ofNat a : Binary5) = true ∨
        parsedWord (ExecFloat.Binary.parse (ExecFloat.Binary.format (ofNat a : Binary5)) :
          Except Model.ParseError Binary5) = a ∧
        parsedWord (ExecFloat.Binary.parse
          (ExecFloat.Binary.format (ofNat a : Binary5) (mode := .up)) .up :
          Except Model.ParseError Binary5) = a ∧
        parsedWord (ExecFloat.Binary.parse
          (ExecFloat.Binary.format (ofNat a : Binary5) (mode := .down)) .down :
          Except Model.ParseError Binary5) = a ∧
        parsedWord (ExecFloat.Binary.parse
          (ExecFloat.Binary.format (ofNat a : Binary5) (mode := .towardZero)) .towardZero :
          Except Model.ParseError Binary5) = a ∧
        parsedWord (ExecFloat.Binary.parse
          (ExecFloat.Binary.format (ofNat a : Binary5) (mode := .nearestAway)) .nearestAway :
          Except Model.ParseError Binary5) = a ∧
        parsedWord (ExecFloat.Binary.parse
          (ExecFloat.Binary.format (ofNat a : Binary5) (mode := .away)) .away :
          Except Model.ParseError Binary5) = a) := by
  float_decide

/-- The descriptor of the four-bit format with two exponent bits and one fraction bit. -/
abbrev binary4 : FloatFormat := FloatFormat.ieee 2 1 (by decide) (by decide)

/--
On the 256 pairs of encodings of the four-bit format, the status number of an operation at the
word of its flat value is the flat status number, which computes that value itself: the six
operations to nearest, the sum toward zero and the quotient upward.
-/
theorem binary4_status_with : ∀ a b : Fin 16,
    Flat.addStatusWith binary4 .nearest a.val b.val (Flat.add binary4 .nearest a.val b.val) =
        Flat.addStatus binary4 .nearest a.val b.val ∧
      Flat.subStatusWith binary4 .nearest a.val b.val (Flat.sub binary4 .nearest a.val b.val) =
        Flat.subStatus binary4 .nearest a.val b.val ∧
      Flat.mulStatusWith binary4 .nearest a.val b.val (Flat.mul binary4 .nearest a.val b.val) =
        Flat.mulStatus binary4 .nearest a.val b.val ∧
      Flat.fmaStatusWith binary4 .nearest a.val b.val a.val
          (Flat.fma binary4 .nearest a.val b.val a.val) =
        Flat.fmaStatus binary4 .nearest a.val b.val a.val ∧
      Flat.divStatusWith binary4 .nearest a.val b.val (Flat.div binary4 .nearest a.val b.val) =
        Flat.divStatus binary4 .nearest a.val b.val ∧
      Flat.roundToIntegralStatusWith binary4 .nearest a.val
          (Flat.roundToIntegral binary4 .nearest a.val) =
        Flat.roundToIntegralStatus binary4 .nearest a.val ∧
      Flat.addStatusWith binary4 .towardZero a.val b.val
          (Flat.add binary4 .towardZero a.val b.val) =
        Flat.addStatus binary4 .towardZero a.val b.val ∧
      Flat.divStatusWith binary4 .up a.val b.val (Flat.div binary4 .up a.val b.val) =
        Flat.divStatus binary4 .up a.val b.val := by
  float_decide

end FloatLibTests.Conformance.BinaryInterchange.KernelCoverage
