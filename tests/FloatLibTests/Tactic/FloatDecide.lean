/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Backends
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.KernelPath
public import FloatLib.Floats.Formats.OCP.FP8.E4M3
public import FloatLib.Floats.Formats.OCP.FP8.E5M2

/-!
# Kernel decision tests

True statements about concrete computations close in every binary family: configured types with
word, wide and custom storage, the one-byte OCP formats, and plain descriptors. The statements
cover the arithmetic operations in all six rounding directions, the IEEE status flags and the
ternary value of the six arithmetic operations, of integral rounding, of rational literals and
of casts, decimal and rational literals, comparisons, the total order and classification,
casts between descriptors, conversions to integers and to exact rational values,
loops over `List.range` and `List.range'`, and a statement about all pairs of encodings of a
one-byte format. Each proof depends on the three standard axioms only. A false statement, an
open statement and a statement without a `Decidable` instance fail with a message that says
which.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.KernelPath

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath

/-! ## The rewrite reaches every family and operation -/

example (x y : Binary32) : x + y = Value.add .nearest x y := Value.add_notation_eq x y

set_option backward.isDefEq.respectTransparency false in
example (x y z : Binary16) : ExecFloat.fma x y z - x * y / z =
    Value.sub .nearest (Value.fma .nearest x y z)
      (Value.div .nearest (Value.mul .nearest x y) z) := by
  simp only [kernel_optimize]

set_option backward.isDefEq.respectTransparency false in
example (x y : E4M3) : ExecFloat.sqrt (x + y) = Value.sqrt .nearest (Value.add .nearest x y) := by
  simp only [kernel_optimize]

set_option backward.isDefEq.respectTransparency false in
example (format : FloatFormat) (x y : ExecFloat (Descriptor format)) :
    ExecFloat.mul x y = Value.mul .nearest x y := by
  simp only [kernel_optimize]

/-- An operation with a rounding direction becomes the kernel operation in that direction. -/
example (x y : Binary64) :
    ExecFloat.Binary.div x y (mode := .up) = Value.div .up x y ∧
      ExecFloat.Binary.sqrt x (mode := .down) = Value.sqrt .down x := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [kernel_optimize, and_self]

/-- A fold over a range becomes a recursion on its length, and its additions kernel additions. -/
example (x : Binary32) (n : Nat) : (List.range n).foldl (fun s _ => s + x) 0 =
    Nat.rec (motive := fun _ => Binary32) 0 (fun _ s => Value.add .nearest s x) n := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [kernel_optimize]

/-! ## The rewrite rules by name

Each example states what one rule gives at binary32 (and binary64 for the casts): the kernel
operation or the operation on encodings that the public operation becomes.
-/

example (x y : Binary32) : x - y = Value.sub .nearest x y := Value.sub_notation_eq x y

example (x y : Binary32) : x * y = Value.mul .nearest x y := Value.mul_notation_eq x y

example (x y : Binary32) : x / y = Value.div .nearest x y := Value.div_notation_eq x y

example (x y : Binary32) : x = y ↔ toNat x = toNat y := eq_iff_toNat_eq x y

/-- The encoding of the value with a given encoding is that number below `2 ^ 32`. -/
example (n : Nat) :
    toNat (ofNat n : Binary32) = Nat.mod n (Nat.pow 2 FloatFormat.binary32.bitWidth) :=
  toNat_ofNat_kernel n

/-- The encoding of the result of a loop is the same loop over encodings. -/
example (x : Binary32) (step : Nat → Binary32 → Binary32) (n : Nat) :
    toNat (Nat.rec (motive := fun _ => Binary32) x step n) =
      Nat.rec (motive := fun _ => Nat) (toNat x)
        (fun index state => toNat (step index (ofNat state))) n :=
  toNat_natRec x step n

/-- The comparisons are tests on the comparison code of the two encodings. -/
example (x y : Binary32) : ExecFloat.compareGreater x y =
    Nat.beq (Flat.compare FloatFormat.binary32 (toNat x) (toNat y)) 2 :=
  Value.compareGreater_eq x y

example (x y : Binary32) : ExecFloat.compareGreaterEqual x y =
    (Nat.ble 1 (Flat.compare FloatFormat.binary32 (toNat x) (toNat y)) &&
      Nat.ble (Flat.compare FloatFormat.binary32 (toNat x) (toNat y)) 2) :=
  Value.compareGreaterEqual_eq x y

example (x y : Binary32) :
    (x < y) = (Nat.beq (Flat.compare FloatFormat.binary32 (toNat x) (toNat y)) 0 = true) :=
  Configured.lt_eq x y

example (x y : Binary32) :
    (x ≤ y) = (Nat.ble (Flat.compare FloatFormat.binary32 (toNat x) (toNat y)) 1 = true) :=
  Configured.le_eq x y

example (x y : Binary32) : ExecFloat.Binary.totalOrder x y =
    Nat.beq (Flat.totalOrder FloatFormat.binary32 (toNat x) (toNat y)) 1 :=
  Configured.totalOrder_eq x y

/-- The encodings of literals and of integral rounding are the flat operations. -/
example : toNat (Value.ofNatural 3 : Binary32) = Flat.ofNatural FloatFormat.binary32 3 :=
  Value.toNat_ofNatural 3

example : toNat (Value.ofScientific 15 true 1 : Binary32) =
    Flat.ofScientific FloatFormat.binary32 15 true 1 :=
  Value.toNat_ofScientific 15 true 1

example : toNat (Value.ofRatio .up false 1 3 : Binary32) =
    Flat.ofRatio FloatFormat.binary32 .up (signNat false) 1 3 :=
  Value.toNat_ofRatio .up false 1 3

example (x : Binary32) : toNat (Value.roundToIntegral .up x) =
    Flat.roundToIntegral FloatFormat.binary32 .up (toNat x) :=
  Value.toNat_roundToIntegral .up x

/-- Integral rounding is the reference rounding carried through the family's conversions. -/
example (x : Binary32) : Value.roundToIntegral .up x =
    NatView.liftUnary (fun x => Model.roundToIntegral x .up) x :=
  Value.roundToIntegral_eq_lift .up x

/-- The encoding of a cast is the flat cast of the encoding of the operand. -/
example (x : Binary32) : toNat (Value.cast .up x : Binary64) =
    Flat.cast FloatFormat.binary32 FloatFormat.binary64 .up (toNat x) :=
  Value.toNat_cast .up x

/-- The reference cast of a configured value is the kernel cast, with its flags. -/
example (x : Binary64) :
    (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x) .up) : Binary32) =
      Value.cast .up x :=
  Configured.cast_eq .up x

example (x : Binary64) :
    (Model.cast _ FloatFormat.binary32 (ExecFloat.Binary.toModel x) .up (status := true)).status =
      decodeStatus (Flat.castStatus FloatFormat.binary64 FloatFormat.binary32 .up (toNat x)) :=
  (Configured.cast_status_eq (mode := .up) x).1

/-- Classification, the exact value and the interchange word are read from the encoding. -/
example (x : Binary32) : ExecFloat.Binary.toRat? x =
    someWhen (finiteCode FloatFormat.binary32 (toNat x))
        (ratValue FloatFormat.binary32 (toNat x)) :=
  Configured.toRat?_eq x

example (x : Binary32) :
    ExecFloat.Binary.isNaN x = Nat.beq (nanCode FloatFormat.binary32 (toNat x)) 1 :=
  Configured.isNaN_eq x

example (x : Binary32) :
    ExecFloat.Binary.isInfinite x = Nat.beq (infCode FloatFormat.binary32 (toNat x)) 1 :=
  Configured.isInfinite_eq x

example (x : Binary32) :
    ExecFloat.Binary.isFinite x = Nat.beq (finiteCode FloatFormat.binary32 (toNat x)) 1 :=
  Configured.isFinite_eq x

example (x : Binary32) : ExecFloat.Binary.toNatBits x = toNat x := Configured.toNatBits_eq x

example (bits : Nat) : (ExecFloat.Binary.ofNatBits bits : Binary32) = ofNat bits :=
  Configured.ofNatBits_eq bits

/-- A rational literal in a rounding direction is the kernel's rounded ratio. -/
example (q : ℚ) : (ExecFloat.Binary.ofModel (Model.ofRat _ q (mode := .up)) : Binary32) =
    Value.ofRatio .up (decide (q.num < 0)) q.num.natAbs q.den :=
  Configured.ofRat_eq q .up

example (q : ℚ) : (ExecFloat.Binary.IEEEOutcome.ofModel
      (Model.ofRat _ q (mode := .up) (status := true))).value =
    (Value.ofRatio .up (decide (q.num < 0)) q.num.natAbs q.den : Binary32) := by
  rw [Configured.ofRat_outcome_eq]

/-- A statement about the flags of an outcome becomes one comparison of natural numbers. -/
example (code : Nat) (status : FloatLib.Numerics.IEEEStatus) :
    decodeStatus code = status ↔ Nat.land code 31 = statusCode status .lt :=
  decodeStatus_eq_iff code status

/-- The loop rewrites by name. -/
example (f : Nat → Nat → Nat) (n : Nat) :
    (List.range n).foldl f 0 = Nat.rec (motive := fun _ => Nat) 0 (fun i s => f s i) n :=
  FloatLib.Floats.ExecFloat.KernelPath.foldl_range f 0 n

example (f : Nat → Nat → Nat) (lo n step : Nat) :
    (List.range' lo n step).foldl f 0 =
      Nat.rec (motive := fun _ => Nat) 0 (fun i s => f s (Nat.add lo (Nat.mul step i))) n :=
  FloatLib.Floats.ExecFloat.KernelPath.foldl_range' f 0 lo n step

/-! ## The words of the special results and the copies of the stages

`zeroWord`, `overflowWord`, `roundOverflowWord` and `invalidWord` are written on the two widths
of a format and are the encodings of the zero, of the overflow results and of the invalid result
of the model. The copies in kernel shape of the stages for operands that are not finite are the
stages. -/

/-- The words of the zeros of binary32, of E4M3 with its signed zero, and of an encoding with
one zero. -/
example :
    zeroWord FloatFormat.binary32 false = 0 ∧ zeroWord FloatFormat.binary32 true = 2 ^ 31 ∧
      zeroWord FloatFormat.e4m3 true = 128 ∧
      zeroWord FloatFormat.e4m3fnuz true = 0 := by
  decide +kernel

example (fmt : FloatFormat) (negative : Bool) :
    zeroWord fmt negative = (Model.zero fmt negative).toNatBits :=
  zeroWord_eq fmt negative

/-- The words of the overflow and invalid results of binary32: the infinities, the largest
finite value in the truncating direction, and the quiet NaN. -/
example :
    overflowWord FloatFormat.binary32 false = 0x7F800000 ∧
      overflowWord FloatFormat.binary32 true = 0xFF800000 ∧
      roundOverflowWord FloatFormat.binary32 .towardZero false = 0x7F7FFFFF ∧
      roundOverflowWord FloatFormat.binary32 .nearest true = 0xFF800000 ∧
      roundOverflowWord FloatFormat.binary32 .up true = 0xFF7FFFFF ∧
      invalidWord FloatFormat.binary32 = 0x7FC00000 := by
  decide +kernel

/-- The same words of E4M3, whose largest pattern is its NaN, and of the encoding with one
zero, whose NaN is the word of the sign bit. -/
example :
    overflowWord FloatFormat.e4m3 false = 0x7F ∧ overflowWord FloatFormat.e4m3 true = 0xFF ∧
      roundOverflowWord FloatFormat.e4m3 .towardZero true = 0xFE ∧
      invalidWord FloatFormat.e4m3 = 0x7F ∧
      overflowWord FloatFormat.e4m3fnuz false = 0x80 ∧
      invalidWord FloatFormat.e4m3fnuz = 0x80 := by
  decide +kernel

example (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (negative : Bool) :
    overflowWord fmt negative = (Model.nativeOverflow fmt negative).toNatBits ∧
      roundOverflowWord fmt mode negative =
        (Model.directedOverflow fmt negative
          (mode.overflowRoundsMagnitudeUp negative)).toNatBits ∧
      invalidWord fmt = (Model.invalidResult fmt).toNatBits :=
  ⟨overflowWord_eq fmt negative, roundOverflowWord_eq fmt mode negative, invalidWord_eq fmt⟩

example : @zeroWord = @zeroWord.kernel ∧ @packRare = @packRare.kernel ∧
    @addSpecial = @addSpecial.kernel ∧ @nanFlag = @nanFlag.kernel ∧
    @overflowWord = @overflowWord.kernel ∧ @invalidWord = @invalidWord.kernel :=
  ⟨zeroWord.kernel_eq, packRare.kernel_eq, addSpecial.kernel_eq, nanFlag.kernel_eq,
    overflowWord.kernel_eq, invalidWord.kernel_eq⟩

/-! ## True statements: arithmetic -/

/-- One thousand binary32 additions of `0.1`, with the exact value of the result. -/
def tenth : Binary32 := 0.1

/-- `0.1` added to zero `n` times in binary32. -/
def sumTenth (n : Nat) : Binary32 := (List.range n).foldl (fun s _ => s + tenth) 0

set_option maxRecDepth 100000 in
theorem sumTenth_thousand :
    ExecFloat.Binary.toRat? (sumTenth 1000) = some (13107075 / 131072) := by
  float_decide [sumTenth]

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.sumTenth_thousand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sumTenth_thousand

/-- A fold over an offset range, as `List.range' lo n` builds it. -/
def sumFrom (lo n : Nat) : Binary32 := (List.range' lo n).foldl (fun s _ => s + tenth) 0

set_option maxRecDepth 100000 in
theorem sumFrom_thousand : toNat (sumFrom 5 1000) = 1120403331 := by float_decide [sumFrom]

/-- The index of a stepped range is used by the loop body. -/
theorem range'_index : (List.range' 3 4 2).foldl (fun s i => s + i) 0 = 24 := by float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.sumFrom_thousand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sumFrom_thousand

theorem binary64_expression : (1.5 : Binary64) * 2.25 - 1 / 3 = 3.0416666666666665 := by
  float_decide

theorem binary16_fma : ExecFloat.fma (1.5 : Binary16) 2.25 0.125 = 3.5 := by float_decide

theorem bfloat16_div : (1 : BFloat16) / 3 = 0.33398438 := by float_decide

theorem binary32_sqrt : ExecFloat.Binary.sqrt (2.25 : Binary32) = 1.5 := by float_decide

theorem binary128_add : ExecFloat.Binary.add (1.5 : Binary128) 2.25 = 3.75 := by float_decide

/-- Sums of one sign with and without a carry, and differences with and without cancellation. -/
theorem binary32_sum_paths :
    toNat ((1 : Binary32) + 1.125) = 0x40080000 ∧ toNat ((1 : Binary32) + 0.001) = 0x3f8020c5 ∧
      toNat ((4 : Binary32) - 1.125) = 0x40380000 ∧ toNat ((1 : Binary32) - 0.5) = 0x3f000000 ∧
      toNat ((1 : Binary32) - 1.125) = 0xbe000000 ∧ toNat ((1 : Binary32) - 1) = 0 ∧
      toNat ((1 : Binary32) - 0.1) = 0x3f666666 ∧
      toNat ((ofNat 0x00800000 : Binary32) - ofNat 0x00000001) = 0x007fffff := by
  float_decide

/-- Signed zeros, an infinity and a NaN go through the same path. -/
theorem binary32_special :
    (0 : Binary32) * -1 = -0 ∧ ExecFloat.Binary.isInfinite ((1 : Binary32) / 0) = true ∧
      ExecFloat.Binary.isNaN ((0 : Binary32) / 0) = true := by
  float_decide

/-- NaN payloads, the quiet bit and the invalid operations are computed on the encoding. -/
theorem binary32_nan_and_infinity :
    toNat ((ofNat 0x7f812345 : Binary32) + ofNat 0x3f800000) = 0x7fc12345 ∧
      toNat ((ofNat 0x7f800000 : Binary32) - ofNat 0x7f800000) = 0x7fc00000 ∧
      toNat ((ofNat 0x7f800000 : Binary32) * ofNat 0x80000000) = 0x7fc00000 ∧
      toNat ((ofNat 0x3f800000 : Binary32) / ofNat 0x80000000) = 0xff800000 ∧
      toNat (ExecFloat.sqrt (ofNat 0xbf800000 : Binary32)) = 0x7fc00000 ∧
      toNat (ExecFloat.fma (ofNat 0x7f800000 : Binary32) (ofNat 0x40000000)
        (ofNat 0xff800000)) = 0x7fc00000 := by
  float_decide

/-- The NaN of E4M3 is propagated with its sign, and its overflow is the NaN. -/
theorem e4m3fn_nan : toNat ((ofNat 0xff : E4M3) + ofNat 0x38) = 0xff ∧
    toNat ((ofNat 0x7e : E4M3) * ofNat 0x7e) = 0x7f := by
  float_decide

/-- A format with its own field widths: 11 exponent and 59 fraction bits. -/
abbrev Binary71 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 59)

theorem custom_width : (1.5 : Binary71) + 2.25 = 3.75 := by float_decide

/-- The 4,096-bit interchange format: 35 exponent and 4,060 fraction bits. -/
abbrev Binary4096 := ExecFloat.Binary (exponentBits := 35) (fractionBits := 4060)

/--
A wide format takes the paths that do not grow with the width: a bit length by binary search in
the general rounding (a difference that cancels, a fused multiply-add, a subnormal quotient) and
the second attempt of the square root. A sum with a zero or with the least subnormal number has
an exponent gap of more than `2 ^ 34`, and a product of two zeros or of two least subnormal
numbers lies that far below the subnormal range: no path turns such a distance into a power of
two.
-/
theorem wide_format :
    (1.5 : Binary4096) + 2.25 = 3.75 ∧ (1.5 : Binary4096) - 1.25 = 0.25 ∧
      (0 : Binary4096) + 1.5 = 1.5 ∧ (1.5 : Binary4096) - 0 = 1.5 ∧
      toNat ((ofNat 1 : Binary4096) + 1.5) = toNat (1.5 : Binary4096) ∧
      toNat (ExecFloat.Binary.add (ofNat 1 : Binary4096) 1.5 (mode := .up)) =
        toNat (1.5 : Binary4096) + 1 ∧
      ExecFloat.Binary.isNaN ((0 : Binary4096) / 0 + 0) = true ∧
      (0 : Binary4096) * 0 = 0 ∧ toNat ((ofNat 1 : Binary4096) * ofNat 1) = 0 ∧
      toNat (ExecFloat.Binary.mul (ofNat 1 : Binary4096) (ofNat 1) (mode := .up)) = 1 ∧
      toNat ((ofNat 1 : Binary4096) / 1e3000) = 0 ∧
      (1.5 : Binary4096) * 2.5 = 3.75 ∧ (3 : Binary4096) / 2 = 1.5 ∧
      toNat ((ofNat 6 : Binary4096) / 2) = 3 ∧
      ExecFloat.fma (1.5 : Binary4096) 2 1 = 4 ∧
      ExecFloat.sqrt (4 : Binary4096) = 2 ∧ ExecFloat.sqrt (2.25 : Binary4096) = 1.5 ∧
      ExecFloat.sqrt (2 : Binary4096) < 1.5 := by
  float_decide

/--
Division in the wide format when the exponents of the operands are as far apart as they can be:
a zero dividend, the least subnormal number over the largest finite number (a quotient more than
`2 ^ 35` binades under the subnormal range, which rounds to zero and, upward, to the least
subnormal number), and the largest finite number over the least subnormal one (an overflow). The
denominator is shifted by two places at most, so these cost what any other quotient costs.
-/
theorem wide_division :
    (0 : Binary4096) / 1.5 = 0 ∧
      toNat ((ofNat 1 : Binary4096) / ofNat (2 ^ 4095 - 2 ^ 4060 - 1)) = 0 ∧
      toNat (ExecFloat.Binary.div (ofNat 1 : Binary4096) (ofNat (2 ^ 4095 - 2 ^ 4060 - 1))
        (mode := .up)) = 1 ∧
      ExecFloat.Binary.isInfinite
        ((ofNat (2 ^ 4095 - 2 ^ 4060 - 1) : Binary4096) / ofNat 1) = true ∧
      toNat (ExecFloat.Binary.div (ofNat 1 : Binary4096) 1e3000 (mode := .up)) = 1 := by
  float_decide

theorem e4m3fn_add : E4M3.ofNatBits 0x38 + E4M3.ofNatBits 0x38 = E4M3.ofNatBits 0x40 := by
  float_decide

theorem e5m2_mul : E5M2.ofNatBits 0x3c * E5M2.ofNatBits 0x40 = E5M2.ofNatBits 0x40 := by
  float_decide

/-- The encoding of a result, read as a natural number. -/
theorem e4m3fn_encoding : toNat ((ofNat 0x38 : E4M3) + ofNat 0x38) = 0x40 := by float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.e4m3fn_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms e4m3fn_add

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.binary64_expression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary64_expression

/-! ## True statements: the six rounding directions -/

/-- A sum, a difference and a product in each direction. -/
theorem directed_sum_and_product :
    toNat (ExecFloat.Binary.add (0.1 : Binary32) 0.2 (mode := .down)) = 0x3e999999 ∧
      toNat (ExecFloat.Binary.add (0.1 : Binary32) 0.2 (mode := .up)) = 0x3e99999a ∧
      toNat (ExecFloat.Binary.add (-0.1 : Binary32) (-0.2) (mode := .towardZero)) = 0xbe999999 ∧
      toNat (ExecFloat.Binary.add (-0.1 : Binary32) (-0.2) (mode := .away)) = 0xbe99999a ∧
      toNat (ExecFloat.Binary.sub (1 : Binary32) 1 (mode := .down)) = 0x80000000 ∧
      toNat (ExecFloat.Binary.mul (0.1 : Binary64) 0.1 (mode := .down)) = 0x3f847ae147ae147b ∧
      toNat (ExecFloat.Binary.mul (0.1 : Binary64) 0.1 (mode := .up)) = 0x3f847ae147ae147c ∧
      toNat (ExecFloat.Binary.fma (0.1 : Binary64) 0.1 1 (mode := .towardZero)) =
        0x3ff028f5c28f5c28 := by
  float_decide

/-- A quotient in each direction, with a tie, an overflow and an underflow. -/
theorem directed_div :
    toNat (ExecFloat.Binary.div (1 : Binary32) 3 (mode := .down)) = 0x3eaaaaaa ∧
      toNat (ExecFloat.Binary.div (1 : Binary32) 3 (mode := .up)) = 0x3eaaaaab ∧
      toNat (ExecFloat.Binary.div (-1 : Binary32) 3 (mode := .towardZero)) = 0xbeaaaaaa ∧
      toNat (ExecFloat.Binary.div (-1 : Binary32) 3 (mode := .down)) = 0xbeaaaaab ∧
      toNat (ExecFloat.Binary.div (1 : Binary32) 3 (mode := .away)) = 0x3eaaaaab ∧
      toNat (ExecFloat.Binary.div (ofNat 0x00800001 : Binary32) 2 (mode := .nearest)) =
        0x00400000 ∧
      toNat (ExecFloat.Binary.div (ofNat 0x00800001 : Binary32) 2 (mode := .nearestAway)) =
        0x00400001 ∧
      toNat (ExecFloat.Binary.div (1e30 : Binary32) 1e-30 (mode := .towardZero)) = 0x7f7fffff ∧
      toNat (ExecFloat.Binary.div (1e30 : Binary32) 1e-30 (mode := .up)) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.div (1e-30 : Binary32) 1e30 (mode := .up)) = 1 ∧
      toNat (ExecFloat.Binary.div (1e-30 : Binary32) 1e30 (mode := .down)) = 0 := by
  float_decide

/-- A square root in each direction, exact roots, a subnormal operand and the special values. -/
theorem directed_sqrt :
    toNat (ExecFloat.sqrt (2 : Binary32)) = 0x3fb504f3 ∧
      toNat (ExecFloat.Binary.sqrt (2 : Binary32) (mode := .down)) = 0x3fb504f3 ∧
      toNat (ExecFloat.Binary.sqrt (2 : Binary32) (mode := .towardZero)) = 0x3fb504f3 ∧
      toNat (ExecFloat.Binary.sqrt (2 : Binary32) (mode := .up)) = 0x3fb504f4 ∧
      toNat (ExecFloat.Binary.sqrt (2 : Binary32) (mode := .away)) = 0x3fb504f4 ∧
      toNat (ExecFloat.Binary.sqrt (2 : Binary32) (mode := .nearestAway)) = 0x3fb504f3 ∧
      toNat (ExecFloat.Binary.sqrt (4 : Binary32) (mode := .up)) = 0x40000000 ∧
      toNat (ExecFloat.Binary.sqrt (4 : Binary32) (mode := .down)) = 0x40000000 ∧
      toNat (ExecFloat.Binary.sqrt (ofNat 1 : Binary32) (mode := .down)) = 0x1a3504f3 ∧
      toNat (ExecFloat.Binary.sqrt (ofNat 1 : Binary32) (mode := .up)) = 0x1a3504f4 ∧
      toNat (ExecFloat.Binary.sqrt (2 : Binary64) (mode := .down)) = 0x3ff6a09e667f3bcc ∧
      toNat (ExecFloat.Binary.sqrt (2 : Binary64) (mode := .up)) = 0x3ff6a09e667f3bcd ∧
      toNat (ExecFloat.Binary.sqrt (-1 : Binary32) (mode := .up)) = 0x7fc00000 ∧
      toNat (ExecFloat.Binary.sqrt (ofNat 0x80000000 : Binary32) (mode := .up)) = 0x80000000 ∧
      toNat (ExecFloat.Binary.sqrt (ofNat 0x7f800000 : Binary32) (mode := .down)) =
        0x7f800000 := by
  float_decide

/-- A direction on a one-byte format, through the kernel operations on stored values. -/
theorem e4m3fn_directed :
    toNat (Value.add .up (ofNat 0x38 : E4M3) (ofNat 0x01)) = 0x39 ∧
      toNat (Value.add .down (ofNat 0x38 : E4M3) (ofNat 0x01)) = 0x38 ∧
      toNat (Value.sqrt .up (ofNat 0x40 : E4M3)) = 0x3c ∧
      toNat (Value.sqrt .down (ofNat 0x40 : E4M3)) = 0x3b := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.directed_sqrt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms directed_sqrt

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.directed_div' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms directed_div

/-! ## True statements: status flags and the ternary value -/

/-- An inexact sum, an exact sum, an overflow, an underflow and an invalid operation. -/
theorem status_flags :
    (ExecFloat.Binary.add (0.1 : Binary32) 0.2 (status := true)).status = { inexact := true } ∧
      (ExecFloat.Binary.add (1 : Binary32) 2 (status := true)).status = {} ∧
      (ExecFloat.Binary.add (1 : Binary32) 2 (status := true)).ternary = .eq ∧
      (ExecFloat.Binary.add (1 : Binary32) 2 (status := true)).value = 3 ∧
      (ExecFloat.Binary.mul (1e30 : Binary32) 1e30 (status := true)).status =
        { overflow := true, inexact := true } ∧
      (ExecFloat.Binary.mul (1e30 : Binary32) 1e30 (status := true)).ternary = .gt ∧
      (ExecFloat.Binary.mul (1e-30 : Binary32) 1e-30 (status := true)).status =
        { underflow := true, inexact := true } ∧
      (ExecFloat.Binary.sub ((1 : Binary64) / 0) ((1 : Binary64) / 0) (status := true)).status =
        { invalid := true } ∧
      (ExecFloat.Binary.fma (0.5 : Binary64) 4 (-2) (status := true)).status = {} := by
  float_decide

/--
The flags of an outcome are read off the status number at the word of the kernel value: the
rewrite leaves the value of the sum once, as an argument of the status number.
-/
example (x y : Binary32) :
    (ExecFloat.Binary.add x y (status := true)).status =
      decodeStatus
        (Flat.addStatusWith (ExecFloat.Binary.descriptor (exponentBits := 8) (fractionBits := 23))
          .nearest (KernelPath.toNat x) (KernelPath.toNat y)
          (KernelPath.toNat (KernelPath.Value.add .nearest x y))) := by
  simp only [kernel_optimize]

/-- The ternary value follows the rounding direction. -/
theorem ternary_by_direction :
    (ExecFloat.Binary.add (0.1 : Binary32) 0.2 (mode := .down) (status := true)).ternary = .lt ∧
      (ExecFloat.Binary.add (0.1 : Binary32) 0.2 (mode := .up) (status := true)).ternary = .gt ∧
      (ExecFloat.Binary.mul (1e-30 : Binary32) 1e-30 (status := true)).ternary = .lt ∧
      (ExecFloat.Binary.mul (1e-30 : Binary32) 1e-30 (mode := .up) (status := true)).ternary =
        .gt := by
  float_decide

/--
The status of a quotient: inexact unless the quotient is a value of the format, divide by zero
for a nonzero value over zero, invalid for zero over zero, an infinity over an infinity and a
signaling NaN, overflow and underflow at the ends of the range, and a ternary value that follows
the rounding direction.
-/
theorem div_status :
    (ExecFloat.Binary.div (1 : Binary32) 3 (status := true)).status = { inexact := true } ∧
      (ExecFloat.Binary.div (1 : Binary32) 3 (status := true)).ternary = .gt ∧
      (ExecFloat.Binary.div (1 : Binary32) 3 (mode := .down) (status := true)).ternary = .lt ∧
      (ExecFloat.Binary.div (1 : Binary32) 3 (status := true)).value = 0.33333334 ∧
      (ExecFloat.Binary.div (1 : Binary32) 4 (status := true)).status = {} ∧
      (ExecFloat.Binary.div (1 : Binary32) 4 (status := true)).ternary = .eq ∧
      (ExecFloat.Binary.div (1 : Binary64) 10 (status := true)).ternary = .gt ∧
      (ExecFloat.Binary.div (1 : Binary32) 0 (status := true)).status =
        { divideByZero := true } ∧
      (ExecFloat.Binary.div (1 : Binary32) 0 (status := true)).ternary = .eq ∧
      (ExecFloat.Binary.div (0 : Binary32) 0 (status := true)).status = { invalid := true } ∧
      (ExecFloat.Binary.div ((1 : Binary32) / 0) ((1 : Binary32) / 0) (status := true)).status =
        { invalid := true } ∧
      (ExecFloat.Binary.div (ofNat 0x7fa00000 : Binary32) 1 (status := true)).status =
        { invalid := true } ∧
      (ExecFloat.Binary.div (ofNat 0x7fc00000 : Binary32) 1 (status := true)).status = {} := by
  float_decide

/-- Overflow and underflow of a quotient, with the ternary value in two directions. -/
theorem div_status_range :
    (ExecFloat.Binary.div (1e30 : Binary32) 1e-30 (status := true)).status =
        { overflow := true, inexact := true } ∧
      (ExecFloat.Binary.div (1e30 : Binary32) 1e-30 (status := true)).ternary = .gt ∧
      (ExecFloat.Binary.div (1e30 : Binary32) 1e-30 (mode := .towardZero)
        (status := true)).status = { overflow := true, inexact := true } ∧
      (ExecFloat.Binary.div (1e30 : Binary32) 1e-30 (mode := .towardZero)
        (status := true)).ternary = .lt ∧
      (ExecFloat.Binary.div (1e-30 : Binary32) 1e30 (status := true)).status =
        { underflow := true, inexact := true } ∧
      (ExecFloat.Binary.div (1e-30 : Binary32) 1e30 (status := true)).ternary = .lt ∧
      (ExecFloat.Binary.div (1e-30 : Binary32) 1e30 (mode := .up) (status := true)).ternary =
        .gt ∧
      (ExecFloat.Binary.div (ofNat 0x00800000 : Binary32) 2 (status := true)).status = {} := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.div_status' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms div_status

/--
The status of a square root: inexact unless the operand is a square, invalid for a negative
operand and for a signaling NaN, and a ternary value that follows the rounding direction.
-/
theorem sqrt_status :
    (ExecFloat.Binary.sqrt (2 : Binary32) (status := true)).status = { inexact := true } ∧
      (ExecFloat.Binary.sqrt (2 : Binary32) (status := true)).ternary = .lt ∧
      (ExecFloat.Binary.sqrt (2 : Binary32) (mode := .up) (status := true)).ternary = .gt ∧
      (ExecFloat.Binary.sqrt (2 : Binary64) (status := true)).ternary = .gt ∧
      (ExecFloat.Binary.sqrt (4 : Binary32) (status := true)).status = {} ∧
      (ExecFloat.Binary.sqrt (4 : Binary32) (mode := .up) (status := true)).ternary = .eq ∧
      (ExecFloat.Binary.sqrt (4 : Binary32) (status := true)).value = 2 ∧
      (ExecFloat.Binary.sqrt (-1 : Binary32) (status := true)).status = { invalid := true } ∧
      (ExecFloat.Binary.sqrt (ofNat 0x7fa00000 : Binary32) (status := true)).status =
        { invalid := true } ∧
      (ExecFloat.Binary.sqrt (ofNat 0x7fc00000 : Binary32) (status := true)).status = {} ∧
      (ExecFloat.Binary.sqrt (ofNat 0x80000000 : Binary32) (status := true)).status = {} ∧
      (ExecFloat.Binary.sqrt (ofNat 1 : Binary32) (status := true)).ternary = .lt := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.sqrt_status' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sqrt_status

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.status_flags' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms status_flags

/-! ## True statements: literals -/

/-- Decimal literals round to nearest, and a literal behind a definition is computed too. -/
theorem decimal_literals :
    toNat (0.1 : Binary32) = 0x3dcccccd ∧ toNat (0.1 : Binary64) = 0x3fb999999999999a ∧
      toNat (1e-45 : Binary32) = 1 ∧ toNat (3.5e38 : Binary32) = 0x7f800000 ∧
      toNat (0.3 : Binary16) = 0x34cd ∧ toNat tenth = 0x3dcccccd := by
  float_decide

/-- Rational literals in a rounding direction. -/
theorem rational_literals :
    toNat (ExecFloat.Binary.ofRat (1 / 3) : Binary32) = 0x3eaaaaab ∧
      toNat (ExecFloat.Binary.ofRat (1 / 3) (mode := .down) : Binary32) = 0x3eaaaaaa ∧
      toNat (ExecFloat.Binary.ofRat (-1 / 3) (mode := .down) : Binary32) = 0xbeaaaaab ∧
      toNat (ExecFloat.Binary.ofRat (1 / 10) (mode := .up) : Binary64) = 0x3fb999999999999a := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.rational_literals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rational_literals

/--
The status of a rounded rational number: inexact unless the number is a value of the format,
overflow beyond the finite range, and underflow for an inexact result that is still tiny after
rounding.
-/
theorem rational_literal_status :
    (let third := ExecFloat.Binary.ofRat (1 / 3) (status := true);
      (third.value : Binary32) = 0.33333334 ∧ third.status = { inexact := true } ∧
        third.ternary = .gt) ∧
    (let third := ExecFloat.Binary.ofRat (-1 / 3) (mode := .down) (status := true);
      toNat (third.value : Binary32) = 0xbeaaaaab ∧ third.ternary = .lt) ∧
    (let half := ExecFloat.Binary.ofRat (1 / 2) (status := true);
      (half.value : Binary16) = 0.5 ∧ half.status = {} ∧ half.ternary = .eq) ∧
    (let big := ExecFloat.Binary.ofRat (10 ^ 39) (mode := .towardZero) (status := true);
      toNat (big.value : Binary32) = 0x7f7fffff ∧
        big.status = { overflow := true, inexact := true } ∧ big.ternary = .lt) ∧
    (let tiny := ExecFloat.Binary.ofRat (1 / 10 ^ 46) (mode := .up) (status := true);
      toNat (tiny.value : Binary32) = 1 ∧
        tiny.status = { underflow := true, inexact := true } ∧ tiny.ternary = .gt) ∧
    (let least := ExecFloat.Binary.ofRat (1 / 2 ^ 149) (status := true);
      toNat (least.value : Binary32) = 1 ∧ least.status = {} ∧ least.ternary = .eq) ∧
    (let edge := ExecFloat.Binary.ofRat ((2 ^ 26 - 1) / 2 ^ 152) (status := true);
      toNat (edge.value : Binary32) = 0x00800000 ∧ edge.status = { inexact := true }) ∧
    (let edge := ExecFloat.Binary.ofRat ((2 ^ 26 - 5) / 2 ^ 152) (status := true);
      toNat (edge.value : Binary32) = 0x007fffff ∧
        edge.status = { underflow := true, inexact := true } ∧ edge.ternary = .lt) ∧
    (let tie := ExecFloat.Binary.ofRat ((2 ^ 11 + 1) / 2 ^ 11) (mode := .nearestAway)
        (status := true);
      toNat (tie.value : Binary16) = 0x3c01 ∧ tie.ternary = .gt) ∧
    (let tiny := ExecFloat.Binary.ofRat (-1 / 10 ^ 400) (mode := .down) (status := true);
      toNat (tiny.value : Binary64) = 0x8000000000000001 ∧
        tiny.status = { underflow := true, inexact := true } ∧ tiny.ternary = .lt) := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.rational_literal_status' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rational_literal_status

/-! ## True statements: comparisons and classification -/

theorem comparisons :
    (0.1 : Binary32) < 0.2 ∧ (0.1 : Binary64) + 0.2 ≤ 0.30000000000000004 ∧
      (0.1 : Binary64) + 0.2 > 0.3 ∧ ¬ ((0.3 : Binary64) < 0.1 + 0.2 - 0.1) ∧
      ((0 : Binary32) == -0) = true ∧ ((1 : Binary32) != 2) = true ∧
      ExecFloat.compare (1.5 : Binary16) 2.5 = some .lt ∧
      ExecFloat.compare ((0 : Binary32) / 0) 1 = none ∧
      ExecFloat.compareGreaterEqual (2 : Binary32) 1 = true ∧
      ExecFloat.compareLessEqual (2 : Binary32) 1 = false ∧
      ExecFloat.compareLess (0.5 : E4M3) 0.75 = true ∧
      ((0.5 : E4M3) + 0.25 == 0.75) = true := by
  float_decide

theorem classification :
    ExecFloat.Binary.isNaN ((0 : Binary32) / 0) = true ∧
      ExecFloat.Binary.isInfinite ((1 : Binary32) / 0) = true ∧
      ExecFloat.Binary.isFinite (1 : Binary32) = true ∧
      ExecFloat.Binary.isZero (-0 : Binary32) = true ∧
      ExecFloat.Binary.signBit (-0 : Binary32) = true ∧
      ExecFloat.Binary.toNatBits ((1 : Binary32) + 1) = 0x40000000 ∧
      (ExecFloat.Binary.ofNatBits 0x3f800000 : Binary32) = 1 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.comparisons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms comparisons

/--
The IEEE total order: the negative zero before the positive zero, values by their order,
infinities at the ends of the numbers, and NaNs outside them by sign, signaling class and
fraction.
-/
theorem total_order :
    ExecFloat.Binary.totalOrder (-0 : Binary32) 0 = true ∧
      ExecFloat.Binary.totalOrder (0 : Binary32) (-0) = false ∧
      ExecFloat.Binary.totalOrder (1 : Binary32) 2 = true ∧
      ExecFloat.Binary.totalOrder (2 : Binary32) 1 = false ∧
      ExecFloat.Binary.totalOrder (1.5 : Binary64) 1.5 = true ∧
      ExecFloat.Binary.totalOrder (-1 : Binary64) (-2) = false ∧
      ExecFloat.Binary.totalOrder (ofNat 0xff800000 : Binary32) (-3.4e38) = true ∧
      ExecFloat.Binary.totalOrder (3.4e38 : Binary32) (ofNat 0x7f800000) = true ∧
      ExecFloat.Binary.totalOrder (ofNat 0x7f800000 : Binary32) (ofNat 0x7fa00000) = true ∧
      ExecFloat.Binary.totalOrder (ofNat 0x7fa00000 : Binary32) (ofNat 0x7fc00000) = true ∧
      ExecFloat.Binary.totalOrder (ofNat 0x7fc00000 : Binary32) (ofNat 0x7fa00000) = false ∧
      ExecFloat.Binary.totalOrder (ofNat 0x7fc00001 : Binary32) (ofNat 0x7fc00002) = true ∧
      ExecFloat.Binary.totalOrder (ofNat 0xffc00001 : Binary32) (ofNat 0xffc00002) = false ∧
      ExecFloat.Binary.totalOrder (ofNat 0xffc00000 : Binary32) (ofNat 0xffa00000) = true ∧
      ExecFloat.Binary.totalOrder (ofNat 0xffa00000 : Binary32) (ofNat 0xff800000) = true ∧
      ExecFloat.Binary.totalOrder (ofNat 0xffc00000 : Binary32) (ofNat 0x7fc00000) = true ∧
      ExecFloat.Binary.totalOrder (ofNat 0x7fc00000 : Binary32) 1 = false ∧
      ExecFloat.Binary.totalOrder (ofNat 0xffc00000 : Binary32) 1 = true ∧
      ExecFloat.Binary.totalOrder (1 : Binary32) (ofNat 0x7fc00000) = true ∧
      ExecFloat.Binary.totalOrder (1 : Binary32) (ofNat 0xffc00000) = false := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.total_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms total_order

/-! ## True statements: casts between descriptors -/

/-- Narrowing with rounding in a direction, widening, and a cast to the same format. -/
theorem cast_rounding :
    (Value.cast .nearest (0.1 : Binary64) : Binary32) = 0.1 ∧
      (Value.cast .nearest (0.1 : Binary32) : Binary64) = 0.10000000149011612 ∧
      (Value.cast .nearest (1.5 : Binary32) : Binary32) = 1.5 ∧
      toNat (Value.cast .up (0.1 : Binary64) : Binary32) = 0x3dcccccd ∧
      toNat (Value.cast .down (0.1 : Binary64) : Binary32) = 0x3dcccccc ∧
      toNat (Value.cast .towardZero (-0.1 : Binary64) : Binary32) = 0xbdcccccc := by
  float_decide

/-- Overflow, saturation of a format without infinities, NaN payloads, subnormals and zeros. -/
theorem cast_special :
    ExecFloat.Binary.isInfinite (Value.cast .nearest (1e300 : Binary64) : Binary32) = true ∧
      toNat (Value.cast .nearest (1e10 : Binary64) : E4M3) = 0x7f ∧
      toNat (Value.cast .towardZero (1e10 : Binary64) : E4M3) = 0x7e ∧
      toNat (Value.cast .nearest (ofNat 0x7fc12345 : Binary32) : Binary64) =
        0x7ff8000000012345 ∧
      toNat (Value.cast .nearest (ofNat 0x7ff8000000012345 : Binary64) : Binary16) = 0x7e00 ∧
      toNat (Value.cast .nearest (ofNat 0x7f800000 : Binary32) : E4M3) = 0x7f ∧
      toNat (Value.cast .nearest (ofNat 0xff : E4M3) : Binary32) = 0xffc00000 ∧
      toNat (Value.cast .nearest (1e-320 : Binary64) : Binary32) = 0 ∧
      toNat (Value.cast .nearest (-0 : Binary64) : Binary16) = 0x8000 ∧
      toNat (Value.cast .nearest (1e-40 : Binary64) : Binary32) = 71362 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.cast_special' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms cast_special

/--
The status of a cast, stated on the reference cast of a decoded value: inexact when the value is
rounded, overflow and underflow of the destination, nothing for a widening or an exact
subnormal, invalid for a signaling NaN and for a NaN cast into a format without NaNs, and
overflow for an infinity cast into a format without infinities.
-/
theorem cast_status :
    (let o := Model.cast _ FloatFormat.binary32 (ExecFloat.Binary.toModel (0.1 : Binary64))
        .nearest (status := true);
      o.status = { inexact := true } ∧ o.ternary = .gt ∧
        (ExecFloat.Binary.ofModel o.value : Binary32) = 0.1) ∧
    (let o := Model.cast _ FloatFormat.binary64 (ExecFloat.Binary.toModel (0.1 : Binary32)) .up
        (status := true);
      o.status = {} ∧ o.ternary = .eq) ∧
    (let o := Model.cast _ FloatFormat.binary32 (ExecFloat.Binary.toModel (1e300 : Binary64))
        .nearest (status := true);
      o.status = { overflow := true, inexact := true } ∧ o.ternary = .gt) ∧
    (let o := Model.cast _ FloatFormat.binary32 (ExecFloat.Binary.toModel (1e300 : Binary64))
        .towardZero (status := true);
      o.status = { overflow := true, inexact := true } ∧ o.ternary = .lt) ∧
    (let o := Model.cast _ FloatFormat.binary32 (ExecFloat.Binary.toModel (1e-320 : Binary64))
        .nearest (status := true);
      o.status = { underflow := true, inexact := true } ∧ o.ternary = .lt) ∧
    (let o := Model.cast _ FloatFormat.binary32
        (ExecFloat.Binary.toModel (ofNat 0x36a0000000000000 : Binary64)) .nearest
        (status := true);
      o.status = {} ∧ o.ternary = .eq ∧
        toNat (ExecFloat.Binary.ofModel o.value : Binary32) = 1) ∧
    (let o := Model.cast _ FloatFormat.binary16
        (ExecFloat.Binary.toModel (ofNat 0x33000001 : Binary32)) .nearest (status := true);
      o.status = { underflow := true, inexact := true } ∧ o.ternary = .gt) := by
  float_decide

/-- The status of a cast of a NaN or an infinity, into formats with and without them. -/
theorem cast_status_special :
    (let o := Model.cast _ FloatFormat.binary32
        (ExecFloat.Binary.toModel (ofNat 0x7ff0000000000001 : Binary64)) .nearest
        (status := true);
      o.status = { invalid := true } ∧ o.ternary = .eq) ∧
    (let o := Model.cast _ FloatFormat.binary32
        (ExecFloat.Binary.toModel (ofNat 0x7ff8000000000001 : Binary64)) .nearest
        (status := true);
      o.status = {} ∧ o.ternary = .eq) ∧
    (let o := Model.cast _ FloatFormat.e4m3fnuz
        (ExecFloat.Binary.toModel (ofNat 0x7fc00000 : Binary32)) .nearest (status := true);
      o.status = {} ∧ o.ternary = .eq) ∧
    (let o := Model.cast _ (FloatFormat.finite 4 3)
        (ExecFloat.Binary.toModel (ofNat 0x7fc00000 : Binary32)) .nearest (status := true);
      o.status = { invalid := true } ∧ o.ternary = .eq) ∧
    (let o := Model.cast _ FloatFormat.binary16
        (ExecFloat.Binary.toModel (ofNat 0x7f800000 : Binary32)) .nearest (status := true);
      o.status = {} ∧ o.ternary = .eq) ∧
    (let o := Model.cast _ FloatFormat.e4m3
        (ExecFloat.Binary.toModel (ofNat 0x7f800000 : Binary32)) .nearest (status := true);
      o.status = { overflow := true, inexact := true } ∧ o.ternary = .lt) ∧
    (let o := Model.cast _ FloatFormat.e4m3
        (ExecFloat.Binary.toModel (ofNat 0xff800000 : Binary32)) .nearest (status := true);
      o.status = { overflow := true, inexact := true } ∧ o.ternary = .gt) ∧
    (let o := Model.cast _ (FloatFormat.finite 4 3)
        (ExecFloat.Binary.toModel (ofNat 0x7f800000 : Binary32)) .nearest (status := true);
      o.status = { overflow := true, inexact := true } ∧ o.ternary = .lt) := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.cast_status' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms cast_status

/-! ## True statements: integers -/

/-- Conversion to an integer in each direction, with the values that have no integer. -/
theorem to_integer :
    ExecFloat.Binary.toInt? (2.75 : Binary32) = some 2 ∧
      ExecFloat.Binary.toInt? (-2.75 : Binary32) = some (-2) ∧
      ExecFloat.Binary.toInt? (2.5 : Binary64) .nearest = some 2 ∧
      ExecFloat.Binary.toInt? (3.5 : Binary64) .nearest = some 4 ∧
      ExecFloat.Binary.toInt? (2.5 : Binary64) .nearestAway = some 3 ∧
      ExecFloat.Binary.toInt? (-2.5 : Binary64) .down = some (-3) ∧
      ExecFloat.Binary.toInt? (-2.5 : Binary64) .up = some (-2) ∧
      ExecFloat.Binary.toInt? (2.25 : Binary64) .away = some 3 ∧
      ExecFloat.Binary.toInt? ((1 : Binary32) / 0) = none ∧
      ExecFloat.Binary.toInt? ((0 : Binary32) / 0) = none ∧
      ExecFloat.Binary.toInt? (1e20 : Binary64) = some 100000000000000000000 := by
  float_decide

/-- Rounding to an integer in the format, with a negative zero, an infinity and a NaN. -/
theorem round_to_integral :
    ExecFloat.Binary.roundToIntegral (2.5 : Binary32) = 2 ∧
      ExecFloat.Binary.roundToIntegral (2.5 : Binary32) .up = 3 ∧
      ExecFloat.Binary.roundToIntegral (-2.5 : Binary32) .up = -2 ∧
      ExecFloat.Binary.roundToIntegral (1e30 : Binary32) = 1e30 ∧
      toNat (ExecFloat.Binary.roundToIntegral (-0.3 : Binary32)) = 0x80000000 ∧
      toNat (ExecFloat.Binary.roundToIntegral (ofNat 0x7f800000 : Binary32)) = 0x7f800000 ∧
      toNat (ExecFloat.Binary.roundToIntegral (ofNat 0x7f812345 : Binary32)) = 0x7fc12345 := by
  float_decide

/--
The status of a rounding to an integral value: inexact for a fractional operand, invalid for a
signaling NaN, and a ternary value that compares the delivered integer with the operand.
-/
theorem round_to_integral_status :
    (ExecFloat.Binary.roundToIntegral (2.5 : Binary32) (status := true)).status =
        { inexact := true } ∧
      (ExecFloat.Binary.roundToIntegral (2.5 : Binary32) (status := true)).ternary = .lt ∧
      (ExecFloat.Binary.roundToIntegral (2.5 : Binary32) (status := true)).value = 2 ∧
      (ExecFloat.Binary.roundToIntegral (2.5 : Binary32) .up (status := true)).ternary = .gt ∧
      (ExecFloat.Binary.roundToIntegral (-2.5 : Binary64) .down (status := true)).ternary =
        .lt ∧
      (ExecFloat.Binary.roundToIntegral (3 : Binary32) (status := true)).status = {} ∧
      (ExecFloat.Binary.roundToIntegral (3 : Binary32) (status := true)).ternary = .eq ∧
      (ExecFloat.Binary.roundToIntegral (ofNat 0x7fa00000 : Binary32) (status := true)).status =
        { invalid := true } ∧
      (ExecFloat.Binary.roundToIntegral (ofNat 0x7f800000 : Binary32) (status := true)).status =
        {} := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.round_to_integral_status' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms round_to_integral_status

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.to_integer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms to_integer

/-- The exact rational value of a finite value, and none for an infinity or a NaN. -/
theorem to_rational :
    ExecFloat.Binary.toRat? (0.1 : Binary32) = some (13421773 / 134217728) ∧
      ExecFloat.Binary.toRat? (-0.5 : Binary64) = some (-1 / 2) ∧
      ExecFloat.Binary.toRat? (0 : Binary32) = some 0 ∧
      ExecFloat.Binary.toRat? (-0 : Binary32) = some 0 ∧
      ExecFloat.Binary.toRat? (ofNat 1 : Binary32) = some (1 / 2 ^ 149) ∧
      ExecFloat.Binary.toRat? (3 : Binary16) = some 3 ∧
      ExecFloat.Binary.toRat? (1e30 : Binary32) = some 1000000015047466219876688855040 ∧
      ExecFloat.Binary.toRat? (ofNat 0x7f800000 : Binary32) = none ∧
      ExecFloat.Binary.toRat? (ofNat 0x7fc00000 : Binary32) = none := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.to_rational' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms to_rational

/--
An integer, a classification, comparisons and an outcome with its flags and ternary value, all
of the result of a loop: the rewrite is proved for every length of the loop, with the optional
results behind `someWhen`.
-/
theorem sumTenth_observed :
    ExecFloat.Binary.toInt? (sumTenth 1000) = some 99 ∧
      ExecFloat.Binary.toInt? (sumTenth 1000) (mode := .nearest) = some 100 ∧
      ExecFloat.Binary.isFinite (sumTenth 1000) = true ∧ sumTenth 1000 < 101 ∧
      ExecFloat.Binary.totalOrder (sumTenth 1000) 101 = true ∧
      (ExecFloat.Binary.add (sumTenth 1000) 1 (status := true)).status = {} ∧
      (ExecFloat.Binary.add (sumTenth 1000) 1 (status := true)).ternary = .eq := by
  float_decide [sumTenth]

/-! ## True statements: all pairs of a small index type -/

/--
Addition of E4M3 commutes on the 1,024 pairs of the encodings below 32. `float_decide` checks
a goal of this shape with one loop over the pairs.
-/
theorem e4m3fn_add_comm_small : ∀ a b : Fin 32,
    toNat ((ofNat a : E4M3) + ofNat b) = toNat ((ofNat b : E4M3) + ofNat a) := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelPath.e4m3fn_add_comm_small' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms e4m3fn_add_comm_small

/-! ## Failures say why -/

/--
error: float_decide: the statement is false:
  1.5 + 2.25 = 3.5
-/
#guard_msgs in
example : (1.5 : Binary64) + 2.25 = 3.5 := by float_decide

/--
error: float_decide: the statement is false:
  E4M3.ofNatBits 56 + E4M3.ofNatBits 56 = E4M3.ofNatBits 65
-/
#guard_msgs in
example : E4M3.ofNatBits 0x38 + E4M3.ofNatBits 0x38 = E4M3.ofNatBits 0x41 := by
  float_decide

/--
error: float_decide: the statement is false:
  toNat (ExecFloat.Binary.sqrt 2 Model.IEEERoundingMode.down) = 1068827892
-/
#guard_msgs in
example : toNat (ExecFloat.Binary.sqrt (2 : Binary32) (mode := .down)) = 0x3fb504f4 := by
  float_decide

/--
error: float_decide: the statement is false:
  (ExecFloat.Binary.add 0.1 0.2 Model.IEEERoundingMode.nearest true).status = { }
-/
#guard_msgs in
example : (ExecFloat.Binary.add (0.1 : Binary32) 0.2 (status := true)).status = {} := by
  float_decide

/--
error: float_decide: the statement is false:
  (ExecFloat.Binary.div 1 3 Model.IEEERoundingMode.nearest true).status = { }
-/
#guard_msgs in
example : (ExecFloat.Binary.div (1 : Binary32) 3 (status := true)).status = {} := by
  float_decide

/--
error: float_decide: the statement is false:
  (ExecFloat.Binary.sqrt 2 Model.IEEERoundingMode.nearest true).status = { }
-/
#guard_msgs in
example : (ExecFloat.Binary.sqrt (2 : Binary32) (status := true)).status = {} := by
  float_decide

/--
error: float_decide: the statement is false:
  let third := ExecFloat.Binary.ofRat (1 / 3) Model.IEEERoundingMode.nearest true;
  third.value = 0.33333334 ∧ third.status = { }
-/
#guard_msgs in
example :
    let third := ExecFloat.Binary.ofRat (1 / 3) (status := true)
    (third.value : Binary32) = 0.33333334 ∧ third.status = {} := by
  float_decide

/--
error: float_decide: the statement is false:
  (Model.cast FloatFormat.binary64 FloatFormat.binary32 (ExecFloat.Binary.toModel 0.1) Model.IEEERoundingMode.nearest
        true).status =
    { }
-/
#guard_msgs in
example :
    (Model.cast FloatFormat.binary64 FloatFormat.binary32
      (ExecFloat.Binary.toModel (0.1 : Binary64)) .nearest (status := true)).status = {} := by
  float_decide

/--
error: float_decide: the statement is false:
  ExecFloat.Binary.totalOrder 0 (-0) = true
-/
#guard_msgs in
example : ExecFloat.Binary.totalOrder (0 : Binary32) (-0) = true := by float_decide

/--
error: float_decide: the statement is false:
  ExecFloat.Binary.toRat? 0.1 = some (1 / 10)
-/
#guard_msgs in
example : ExecFloat.Binary.toRat? (0.1 : Binary32) = some (1 / 10) := by float_decide

/--
error: float_decide: the statement is false:
  0.2 < 0.1
-/
#guard_msgs in
example : (0.2 : Binary32) < 0.1 := by float_decide

/--
error: float_decide: the statement is false:
  ∀ (a b : Fin 32), toNat (ofNat ↑a + ofNat ↑b) = toNat (ofNat ↑a)
-/
#guard_msgs in
example : ∀ a b : Fin 32, toNat ((ofNat a : E4M3) + ofNat b) = toNat (ofNat a : E4M3) := by
  float_decide

/--
error: float_decide: the statement mentions local variables or hypotheses, so it is not closed:
  x + 0 = x
-/
#guard_msgs in
example (x : Binary32) : x + 0 = x := by float_decide

end FloatLibTests.Conformance.BinaryInterchange.KernelPath
