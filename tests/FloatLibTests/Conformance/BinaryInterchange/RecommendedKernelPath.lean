/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Recommended.KernelPath

/-!
# Kernel rules for the named operations of IEEE 754-2019

`float_decide` checks statements about the 22 comparisons, the integral roundings and integer
conversions under their names, `class`, `isNormal`, `isSubnormal`, `isSignaling`,
`totalOrderMag`, `scale`, `logB`, `getPayload`, `abs`, `copySign` and the eight minimum and
maximum operations on encodings, through the rules of `Configured.Recommended.KernelPath`. The
cases are the special values of IEEE 754-2019 §5.3.3, §5.6.1, §5.11, §6.2, §9.6 and §9.7: the
two zeros, infinities, quiet and signaling NaNs with payloads, overflow and underflow of
`scaleB`, in binary16, binary32, binary64, binary128 and a format with its own field widths,
and every pair of encodings of a five-bit format. Each proof depends on the three standard
axioms only.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RecommendedKernelPath

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath

/-! ## The rewrite reaches the operations -/

set_option backward.isDefEq.respectTransparency false in
example (x y : Binary32) : ExecFloat.Binary.minimum x y = Value.minimum x y ∧
    ExecFloat.Binary.maximumNumber x y = Value.maximumNumber x y ∧
    ExecFloat.Binary.minimumMagnitude x y = Value.minimumMagnitude x y ∧
    ExecFloat.Binary.maximumMagnitudeNumber x y = Value.maximumMagnitudeNumber x y ∧
    ExecFloat.Binary.abs x = Value.abs x ∧ ExecFloat.Binary.copySign x y = Value.copySign x y := by
  simp only [kernel_optimize, and_self]

/-- A named member is its family at one direction, which has a kernel operation. -/
example (x : Binary64) :
    ExecFloat.Binary.roundToIntegralTowardPositive x = Value.roundToIntegral .up x := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [kernel_optimize]

/--
A comparison under its name is the predicate at the comparison code of the encodings, the code
that `ExecFloat.compareLessEqual` tests.
-/
example (x y : Binary16) : (ExecFloat.Binary.compareQuietLessEqual x y).value =
    ExecFloat.compareLessEqual x y := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [kernel_optimize]
  rfl

/-- The encoding of a minimum is the flat selection between the two encodings. -/
example (x y : Binary128) :
    toNat (ExecFloat.Binary.minimum x y) = toNat (Value.minimum x y) := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [kernel_optimize]

/-! ## Comparisons (§5.6.1 and §5.11) -/

/-- The zeros are equal, and a quiet NaN is unordered without a flag. -/
theorem binary32_quiet :
    (ExecFloat.Binary.compareQuietLess (1 : Binary32) 2).value = true ∧
      (ExecFloat.Binary.compareQuietEqual (ofNat 0 : Binary32) (ofNat 0x80000000)).value = true ∧
      (ExecFloat.Binary.compareQuietGreaterEqual (ofNat 0x7f800000 : Binary32) 3).value = true ∧
      (ExecFloat.Binary.compareQuietUnordered (ofNat 0x7fc00000 : Binary32) 1).value = true ∧
      (ExecFloat.Binary.compareQuietUnordered (ofNat 0x7fc00000 : Binary32) 1).status.invalid =
        false ∧
      (ExecFloat.Binary.compareQuietNotEqual (ofNat 0x7fc00000 : Binary32)
        (ofNat 0x7fc00000)).value = true ∧
      (ExecFloat.Binary.compareQuietLessUnordered (1 : Binary32) (ofNat 0x7fc00001)).value =
        true ∧
      (ExecFloat.Binary.compareQuietOrdered (1 : Binary32) (ofNat 0xff800000)).value = true := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.RecommendedKernelPath.binary32_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary32_quiet

/-- A signaling NaN raises `invalid` in a quiet comparison, and any NaN in a signaling one. -/
theorem binary32_invalid :
    (ExecFloat.Binary.compareQuietLess (ofNat 0x7fa00000 : Binary32) 1).status.invalid = true ∧
      (ExecFloat.Binary.compareQuietLess (ofNat 0x7fa00000 : Binary32) 1).value = false ∧
      (ExecFloat.Binary.compareSignalingLess (ofNat 0x7fc00000 : Binary32) 1).status.invalid =
        true ∧
      (ExecFloat.Binary.compareSignalingNotGreater (ofNat 0x7fc00000 : Binary32) 1).value =
        true ∧
      (ExecFloat.Binary.compareSignalingGreaterUnordered (2 : Binary32) 1).value = true ∧
      (ExecFloat.Binary.compareSignalingGreaterUnordered (2 : Binary32) 1).status.invalid =
        false := by
  float_decide

/-- The same rules in binary16, binary64, binary128 and a format of 71 bits. -/
theorem comparisons_by_format :
    (ExecFloat.Binary.compareQuietLess (1.5 : Binary16) 2.25).value = true ∧
      (ExecFloat.Binary.compareSignalingLessEqual (2.25 : Binary64) 2.25).value = true ∧
      (ExecFloat.Binary.compareQuietNotLess (0.1 : Binary128) 0.2).value = false ∧
      (ExecFloat.Binary.compareQuietGreater
        (3 : ExecFloat.Binary (exponentBits := 11) (fractionBits := 59)) 2.5).value = true := by
  float_decide

/-! ## Integral rounding and conversion to an integer (§5.3.1 and §5.4.1) -/

theorem binary32_roundToIntegral :
    ExecFloat.Binary.roundToIntegralTiesToEven (2.5 : Binary32) = 2 ∧
      ExecFloat.Binary.roundToIntegralTiesToAway (2.5 : Binary32) = 3 ∧
      ExecFloat.Binary.roundToIntegralTowardZero (-2.5 : Binary32) = -2 ∧
      ExecFloat.Binary.roundToIntegralTowardPositive (2.25 : Binary32) = 3 ∧
      ExecFloat.Binary.roundToIntegralTowardNegative (2.75 : Binary32) = 2 ∧
      (ExecFloat.Binary.roundToIntegralExact (2.5 : Binary32)).status.inexact = true ∧
      (ExecFloat.Binary.roundToIntegralExact (4 : Binary32)).status.inexact = false := by
  float_decide

theorem binary64_convertToInteger :
    ExecFloat.Binary.convertToIntegerTiesToEven (2.5 : Binary64) = some 2 ∧
      ExecFloat.Binary.convertToIntegerTiesToAway (2.5 : Binary64) = some 3 ∧
      ExecFloat.Binary.convertToIntegerTowardZero (-2.5 : Binary64) = some (-2) ∧
      ExecFloat.Binary.convertToIntegerTowardPositive (2.25 : Binary64) = some 3 ∧
      ExecFloat.Binary.convertToIntegerTowardNegative (-2.25 : Binary64) = some (-3) ∧
      ExecFloat.Binary.convertToIntegerTowardZero (ofNat 0x7ff0000000000000 : Binary64) =
        none := by
  float_decide

/-! ## Classification (§5.7.2) -/

/-- The ten classes, read off the encoding. -/
theorem binary32_class :
    ExecFloat.Binary.classify (ofNat 0x7fa00000 : Binary32) = .signalingNaN ∧
      ExecFloat.Binary.classify (ofNat 0xffc00000 : Binary32) = .quietNaN ∧
      ExecFloat.Binary.classify (ofNat 0xff800000 : Binary32) = .negativeInfinity ∧
      ExecFloat.Binary.classify (-1.5 : Binary32) = .negativeNormal ∧
      ExecFloat.Binary.classify (ofNat 0x80000001 : Binary32) = .negativeSubnormal ∧
      ExecFloat.Binary.classify (ofNat 0x80000000 : Binary32) = .negativeZero ∧
      ExecFloat.Binary.classify (0 : Binary32) = .positiveZero ∧
      ExecFloat.Binary.classify (ofNat 0x007fffff : Binary32) = .positiveSubnormal ∧
      ExecFloat.Binary.classify (ofNat 0x00800000 : Binary32) = .positiveNormal ∧
      ExecFloat.Binary.classify (ofNat 0x7f800000 : Binary32) = .positiveInfinity := by
  float_decide

/-- `isNormal`, `isSubnormal` and `isSignaling` at the boundaries of their classes. -/
theorem binary64_predicates :
    ExecFloat.Binary.isNormal (ofNat 0x0010000000000000 : Binary64) = true ∧
      ExecFloat.Binary.isNormal (ofNat 0x000fffffffffffff : Binary64) = false ∧
      ExecFloat.Binary.isNormal (ofNat 0x7ff0000000000000 : Binary64) = false ∧
      ExecFloat.Binary.isSubnormal (ofNat 0x000fffffffffffff : Binary64) = true ∧
      ExecFloat.Binary.isSubnormal (0 : Binary64) = false ∧
      ExecFloat.Binary.isSubnormal (ofNat 0x7ff8000000000001 : Binary64) = false ∧
      ExecFloat.Binary.isSignaling (ofNat 0x7ff0000000000001 : Binary64) = true ∧
      ExecFloat.Binary.isSignaling (ofNat 0x7ff8000000000001 : Binary64) = false ∧
      ExecFloat.Binary.isSignaling (1 : Binary64) = false := by
  float_decide

/-! ## Sign operations (§5.5.1) -/

/-- `abs` clears the sign of a number and of a NaN, and `copySign` copies it onto a NaN too. -/
theorem binary32_sign :
    toNat (ExecFloat.Binary.abs (ofNat 0xbf800000 : Binary32)) = 0x3f800000 ∧
      toNat (ExecFloat.Binary.abs (ofNat 0xffc00001 : Binary32)) = 0x7fc00001 ∧
      toNat (ExecFloat.Binary.abs (ofNat 0x80000000 : Binary32)) = 0 ∧
      toNat (ExecFloat.Binary.copySign (1 : Binary32) (ofNat 0x80000000)) = 0xbf800000 ∧
      toNat (ExecFloat.Binary.copySign (ofNat 0x7fa00000 : Binary32) (-1)) = 0xffa00000 ∧
      toNat (ExecFloat.Binary.copySign (ofNat 0xff800000 : Binary32) 2) = 0x7f800000 := by
  float_decide

/-! ## `scaleB` (§5.3.3) -/

/--
`scaleB` moves the exponent and rounds once: exact results, an overflow in two rounding
directions, the least subnormal, a tie and a result below half the least subnormal, a zero and
an infinity returned as they are, and a signaling NaN quieted.
-/
theorem binary32_scaleB :
    ExecFloat.Binary.scale (1.5 : Binary32) 3 = 12 ∧
      ExecFloat.Binary.scale (12 : Binary32) (-3) = 1.5 ∧
      toNat (ExecFloat.Binary.scale (1 : Binary32) 128) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.scale (1 : Binary32) 128 (mode := .towardZero)) = 0x7f7fffff ∧
      toNat (ExecFloat.Binary.scale (1 : Binary32) (-149)) = 1 ∧
      toNat (ExecFloat.Binary.scale (1 : Binary32) (-150)) = 0 ∧
      toNat (ExecFloat.Binary.scale (1.5 : Binary32) (-150)) = 1 ∧
      toNat (ExecFloat.Binary.scale (1 : Binary32) (-150) (mode := .up)) = 1 ∧
      toNat (ExecFloat.Binary.scale (ofNat 0x80000000 : Binary32) 5) = 0x80000000 ∧
      toNat (ExecFloat.Binary.scale (ofNat 0xff800000 : Binary32) (-7)) = 0xff800000 ∧
      toNat (ExecFloat.Binary.scale (ofNat 0x7fa00001 : Binary32) 2) = 0x7fe00001 ∧
      ExecFloat.Binary.scale (3 : Binary64) 10 = 3072 ∧
      ExecFloat.Binary.scale (-0.75 : Binary16) 2 = -3 ∧
      ExecFloat.Binary.scale (1 : Binary128) (-1) = 0.5 := by
  float_decide

/--
`logB` is the exponent of the leading bit: of normal and subnormal numbers of both signs, of a
zero (`-∞`), of an infinity (`+∞`) and of a NaN (quieted).
-/
theorem binary32_logB :
    ExecFloat.Binary.logB (1 : Binary32) = 0 ∧
      ExecFloat.Binary.logB (1.5 : Binary32) = 0 ∧
      ExecFloat.Binary.logB (-8 : Binary32) = 3 ∧
      ExecFloat.Binary.logB (0.375 : Binary32) = -2 ∧
      ExecFloat.Binary.logB (ofNat 0x7f7fffff : Binary32) = 127 ∧
      ExecFloat.Binary.logB (ofNat 0x00800000 : Binary32) = -126 ∧
      ExecFloat.Binary.logB (ofNat 0x00000001 : Binary32) = -149 ∧
      ExecFloat.Binary.logB (ofNat 0x80400000 : Binary32) = -127 ∧
      toNat (ExecFloat.Binary.logB (ofNat 0x80000000 : Binary32)) = 0xff800000 ∧
      toNat (ExecFloat.Binary.logB (ofNat 0xff800000 : Binary32)) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.logB (ofNat 0x7fa00001 : Binary32)) = 0x7fe00001 ∧
      ExecFloat.Binary.logB (1024 : Binary64) = 10 ∧
      ExecFloat.Binary.logB (0.1 : Binary16) = -4 ∧
      ExecFloat.Binary.logB (3 : Binary128) = 1 := by
  float_decide

/-! ## `getPayload` (§9.7) -/

/--
`getPayload` is the payload of a quiet or signaling NaN of either sign as a number of the
format, and `-1` for a number, a zero and an infinity.
-/
theorem binary32_getPayload :
    ExecFloat.Binary.getPayload (ofNat 0x7fc00005 : Binary32) = 5 ∧
      ExecFloat.Binary.getPayload (ofNat 0x7fa00001 : Binary32) = 2097153 ∧
      ExecFloat.Binary.getPayload (ofNat 0x7fffffff : Binary32) = 4194303 ∧
      toNat (ExecFloat.Binary.getPayload (ofNat 0xffc00000 : Binary32)) = 0 ∧
      ExecFloat.Binary.getPayload (1.5 : Binary32) = -1 ∧
      ExecFloat.Binary.getPayload (ofNat 0x7f800000 : Binary32) = -1 ∧
      ExecFloat.Binary.getPayload (ofNat 0x80000000 : Binary32) = -1 ∧
      ExecFloat.Binary.getPayload (ofNat 0x7e01 : Binary16) = 1 ∧
      ExecFloat.Binary.getPayload (ofNat 0x7ff8000000000123 : Binary64) = 291 := by
  float_decide

/-! ## The total order of magnitudes (§5.10) -/

/--
`totalOrderMag` orders absolute values: the two zeros tie, a NaN of either sign is above the
infinities, and a signaling NaN is below a quiet one.
-/
theorem binary32_totalOrderMag :
    ExecFloat.Binary.totalOrderMag (-2 : Binary32) 1 = false ∧
      ExecFloat.Binary.totalOrderMag (1 : Binary32) (-2) = true ∧
      ExecFloat.Binary.totalOrderMag (ofNat 0x80000000 : Binary32) (ofNat 0) = true ∧
      ExecFloat.Binary.totalOrderMag (ofNat 0 : Binary32) (ofNat 0x80000000) = true ∧
      ExecFloat.Binary.totalOrderMag (ofNat 0xffc00000 : Binary32) (ofNat 0x7f800000) = false ∧
      ExecFloat.Binary.totalOrderMag (ofNat 0x7f800000 : Binary32) (ofNat 0xffc00000) = true ∧
      ExecFloat.Binary.totalOrderMag (ofNat 0xffa00000 : Binary32) (ofNat 0x7fc00000) = true ∧
      ExecFloat.Binary.totalOrderMag (ofNat 0x7fc00000 : Binary32) (ofNat 0xffa00000) = false ∧
      ExecFloat.Binary.totalOrderMag (-1.5 : Binary128) 1.5 = true ∧
      ExecFloat.Binary.totalOrderMag (2.5 : Binary16) (-2.25) = false := by
  float_decide

/-! ## Minimum and maximum (§9.6) -/

/-- `-0` is below `+0`, and a NaN operand of `minimum` and `maximum` is returned quieted. -/
theorem binary32_extrema :
    toNat (ExecFloat.Binary.minimum (ofNat 0 : Binary32) (ofNat 0x80000000)) = 0x80000000 ∧
      toNat (ExecFloat.Binary.maximum (ofNat 0x80000000 : Binary32) (ofNat 0)) = 0 ∧
      ExecFloat.Binary.minimum (1.5 : Binary32) 2.25 = 1.5 ∧
      ExecFloat.Binary.maximum (1.5 : Binary32) 2.25 = 2.25 ∧
      toNat (ExecFloat.Binary.maximum (ofNat 0x7f800000 : Binary32) 1) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.minimum (ofNat 0x7fa00000 : Binary32) 1) = 0x7fe00000 ∧
      toNat (ExecFloat.Binary.maximum (1 : Binary32) (ofNat 0xffc00003)) = 0xffc00003 ∧
      toNat (ExecFloat.Binary.minimum (ofNat 0x7fc00001 : Binary32) (ofNat 0x7fa00002)) =
        0x7fe00002 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.RecommendedKernelPath.binary32_extrema' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary32_extrema

/-- `minimumNumber` and `maximumNumber` prefer a number to a NaN, also to a signaling one. -/
theorem binary32_extremaNumber :
    toNat (ExecFloat.Binary.minimumNumber (ofNat 0x7fa00000 : Binary32) 1) = 0x3f800000 ∧
      toNat (ExecFloat.Binary.maximumNumber (1 : Binary32) (ofNat 0x7fc00000)) = 0x3f800000 ∧
      toNat (ExecFloat.Binary.maximumNumber (ofNat 0x7fc00001 : Binary32) (ofNat 0x7fa00002)) =
        0x7fe00002 ∧
      toNat (ExecFloat.Binary.minimumNumber (ofNat 0x7fc00001 : Binary32) (ofNat 0x7fc00002)) =
        0x7fc00001 ∧
      toNat (ExecFloat.Binary.minimumNumber (ofNat 0x80000000 : Binary32) (ofNat 0)) =
        0x80000000 := by
  float_decide

/-- The magnitude selections compare absolute values and fall back on equal magnitudes. -/
theorem binary32_magnitude :
    toNat (ExecFloat.Binary.minimumMagnitude (ofNat 0xbf800000 : Binary32) 2) = 0xbf800000 ∧
      toNat (ExecFloat.Binary.maximumMagnitude (ofNat 0xc0000000 : Binary32) 1) = 0xc0000000 ∧
      toNat (ExecFloat.Binary.minimumMagnitude (ofNat 0xbf800000 : Binary32) 1) = 0xbf800000 ∧
      toNat (ExecFloat.Binary.maximumMagnitude (ofNat 0xbf800000 : Binary32) 1) = 0x3f800000 ∧
      toNat (ExecFloat.Binary.maximumMagnitude (ofNat 0x7fa00000 : Binary32) 1) = 0x7fe00000 ∧
      toNat (ExecFloat.Binary.maximumMagnitudeNumber (ofNat 0x7fc00000 : Binary32)
        (ofNat 0xff800000)) = 0xff800000 ∧
      toNat (ExecFloat.Binary.minimumMagnitudeNumber (ofNat 0x7fa00000 : Binary32) (-3)) =
        0xc0400000 := by
  float_decide

/-- With `status := true` a signaling NaN raises `invalid`, also when a number is returned. -/
theorem binary32_extrema_status :
    (ExecFloat.Binary.minimum (ofNat 0x7fa00000 : Binary32) 1 (status := true)).status.invalid =
        true ∧
      (ExecFloat.Binary.minimum (ofNat 0x7fc00000 : Binary32) 1 (status := true)).status.invalid =
        false ∧
      (ExecFloat.Binary.minimumNumber (ofNat 0x7fa00000 : Binary32) 1
        (status := true)).status.invalid = true ∧
      toNat (ExecFloat.Binary.minimumNumber (ofNat 0x7fa00000 : Binary32) 1
        (status := true)).value = 0x3f800000 ∧
      (ExecFloat.Binary.maximumMagnitude (1 : Binary32) (ofNat 0xffa00000)
        (status := true)).status.invalid = true ∧
      (ExecFloat.Binary.maximumMagnitudeNumber (1 : Binary32) 2 (status := true)).ternary =
        .eq := by
  float_decide

/-- The same selections in binary16, binary64, binary128 and a format of 71 bits. -/
theorem extrema_by_format :
    ExecFloat.Binary.minimum (1.5 : Binary16) 2.25 = 1.5 ∧
      ExecFloat.Binary.maximumNumber (1.5 : Binary64) 2.25 = 2.25 ∧
      ExecFloat.Binary.minimumMagnitude (-1.5 : Binary128) 2.25 = -1.5 ∧
      ExecFloat.Binary.maximumMagnitudeNumber
        (-3 : ExecFloat.Binary (exponentBits := 11) (fractionBits := 59)) 2.5 = -3 := by
  float_decide

/-! ## Every pair of encodings of a five-bit format -/

/-- The IEEE layout with two exponent bits and two fraction bits: 32 encodings. -/
abbrev Binary5 := ExecFloat.Binary (exponentBits := 2) (fractionBits := 2)

/--
On the 1,024 pairs of encodings: `minimum` and `maximum` do not depend on the order of their
operands unless both are NaNs, and `minimumNumber` is a NaN only for two NaNs.
-/
theorem binary5_extrema : ∀ a b : Fin 32,
    (toNat (ExecFloat.Binary.minimum (ofNat a : Binary5) (ofNat b)) =
        toNat (ExecFloat.Binary.minimum (ofNat b : Binary5) (ofNat a)) ∧
      toNat (ExecFloat.Binary.maximum (ofNat a : Binary5) (ofNat b)) =
        toNat (ExecFloat.Binary.maximum (ofNat b : Binary5) (ofNat a)) ∨
      (ExecFloat.Binary.isNaN (ofNat a : Binary5) && ExecFloat.Binary.isNaN (ofNat b : Binary5)) =
        true) ∧
    ExecFloat.Binary.isNaN (ExecFloat.Binary.minimumNumber (ofNat a : Binary5) (ofNat b)) =
      (ExecFloat.Binary.isNaN (ofNat a : Binary5) &&
        ExecFloat.Binary.isNaN (ofNat b : Binary5)) := by
  float_decide

/--
On every encoding that is not a NaN: `scaleB` by one is the product with two, and `scaleB` by
minus one the product with one half, a subnormal number of the format.
-/
theorem binary5_scaleB : ∀ a b : Fin 32,
    ExecFloat.Binary.isNaN (ofNat a : Binary5) = true ∨
      toNat (ExecFloat.Binary.scale (ofNat a : Binary5) 1) = toNat ((ofNat a : Binary5) * 2) ∧
        toNat (ExecFloat.Binary.scale (ofNat a : Binary5) (-1)) =
          toNat ((ofNat a : Binary5) * 0.5) ∧
        toNat (ExecFloat.Binary.scale (ofNat a : Binary5) ((b : Int) - 16)) =
          toNat (ExecFloat.Binary.scale
            (ExecFloat.Binary.scale (ofNat a : Binary5) ((b : Int) - 16)) 0) := by
  float_decide

/--
On every encoding: `getPayload` is `-1` exactly when the encoding is not a NaN, and the payload
of a NaN is not negative.
-/
theorem binary5_getPayload : ∀ a b : Fin 32,
    (ExecFloat.Binary.isNaN (ofNat a : Binary5) = true ∨
        ExecFloat.Binary.getPayload (ofNat a : Binary5) = -1) ∧
      (ExecFloat.Binary.isNaN (ofNat b : Binary5) = false ∨
        (ExecFloat.Binary.compareQuietLessEqual (0 : Binary5)
          (ExecFloat.Binary.getPayload (ofNat b : Binary5))).value = true) := by
  float_decide

/--
On the 1,024 pairs of positive finite encodings ordered by value, `logB` is monotone: the
exponent of the leading bit of the smaller value is not above that of the larger.
-/
theorem binary5_logB : ∀ a b : Fin 32,
    (ExecFloat.Binary.isFinite (ofNat a : Binary5) &&
        ExecFloat.Binary.isFinite (ofNat b : Binary5) &&
        !ExecFloat.Binary.isZero (ofNat a : Binary5) &&
        (ExecFloat.Binary.compareQuietLessEqual (ofNat 0 : Binary5) (ofNat a)).value &&
        (ExecFloat.Binary.compareQuietLessEqual (ofNat a : Binary5) (ofNat b)).value) = false ∨
      (ExecFloat.Binary.compareQuietLessEqual (ExecFloat.Binary.logB (ofNat a : Binary5))
        (ExecFloat.Binary.logB (ofNat b : Binary5))).value = true := by
  float_decide

/--
On the 1,024 pairs of encodings: `totalOrderMag` is the total order of the absolute values.
-/
theorem binary5_totalOrderMag : ∀ a b : Fin 32,
    ExecFloat.Binary.totalOrderMag (ofNat a : Binary5) (ofNat b) =
      ExecFloat.Binary.totalOrder (ExecFloat.Binary.abs (ofNat a : Binary5))
        (ExecFloat.Binary.abs (ofNat b : Binary5)) := by
  float_decide

/--
On the 1,024 pairs of encodings without a NaN: the minimum is not above the maximum, and the
minimum by magnitude is not above the maximum by magnitude in absolute value.
-/
theorem binary5_order : ∀ a b : Fin 32,
    (ExecFloat.Binary.isNaN (ofNat a : Binary5) || ExecFloat.Binary.isNaN (ofNat b : Binary5)) =
        true ∨
      (ExecFloat.Binary.compareQuietLessEqual
          (ExecFloat.Binary.minimum (ofNat a : Binary5) (ofNat b))
          (ExecFloat.Binary.maximum (ofNat a : Binary5) (ofNat b))).value = true ∧
        (ExecFloat.Binary.compareQuietLessEqual
          (ExecFloat.Binary.abs (ExecFloat.Binary.minimumMagnitude (ofNat a : Binary5) (ofNat b)))
          (ExecFloat.Binary.abs
            (ExecFloat.Binary.maximumMagnitude (ofNat a : Binary5) (ofNat b)))).value = true := by
  float_decide

end FloatLibTests.Conformance.BinaryInterchange.RecommendedKernelPath
