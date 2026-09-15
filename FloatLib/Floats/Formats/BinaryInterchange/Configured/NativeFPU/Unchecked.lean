/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import Init.Data.Float.Float32
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Runtime

/-!
# Explicit unchecked host-FPU operations

This opt-in module exposes guarded binary32 and binary64 operations backed by Lean's `Float32`
and `Float` runtime primitives. They are useful for differential testing and performance
experiments, but they do not carry FloatLib refinement certificates and are never selected by
the proof-carrying configured planner.

Compiled calls require round-to-nearest, ties-to-even and gradual underflow. Changing the process
rounding mode, enabling flush-to-zero, or enabling denormals-are-zero can make a call disagree
with the proved software operation.

NaNs, zero divisors, and negative square-root inputs retain the software path. This preserves
FloatLib's payload and invalid-result policies at those boundaries, but it is not a proof that
the remaining host operations agree bit-for-bit with the software specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked

open FloatLib.Floats

/-! ## Implementation guards -/

/-- Whether a binary32 interchange word is finite. -/
@[inline] def binary32Finite (bits : UInt32) : Bool :=
  ((bits >>> 23) &&& 0xff) != 0xff

/-- Whether a binary32 interchange word is either signed zero. -/
@[inline] def binary32Zero (bits : UInt32) : Bool :=
  (bits &&& 0x7fffffff) == 0

/-- Whether a binary32 interchange word has a nonnegative sign. -/
@[inline] def binary32Nonnegative (bits : UInt32) : Bool :=
  (bits &&& 0x80000000) == 0

/-- Whether a binary64 interchange word is finite. -/
@[inline] def binary64Finite (bits : UInt64) : Bool :=
  ((bits >>> 52) &&& 0x7ff) != 0x7ff

/-- Whether a binary64 interchange word is either signed zero. -/
@[inline] def binary64Zero (bits : UInt64) : Bool :=
  (bits &&& 0x7fffffffffffffff) == 0

/-- Whether a binary64 interchange word has a nonnegative sign. -/
@[inline] def binary64Nonnegative (bits : UInt64) : Bool :=
  (bits &&& 0x8000000000000000) == 0

/-! ## Binary32 -/

/-- Opt in to guarded host binary32 addition. This function has no refinement certificate. -/
@[always_inline, inline] def add32
    {width_le : FloatFormat.binary32.bitWidth ≤ 32}
    (left right : NativeFPU.Binary32Value width_le) : NativeFPU.Binary32Value width_le :=
  let leftBits := left.raw.1
  let rightBits := right.raw.1
  if binary32Finite leftBits && binary32Finite rightBits then
    NativeFPU.ofBinary32Bits <|
      (Float32.ofBits leftBits + Float32.ofBits rightBits).toBits
  else
    Backend.wordAdd left right

/-- Opt in to guarded host binary32 subtraction. This function has no refinement certificate. -/
@[always_inline, inline] def sub32
    {width_le : FloatFormat.binary32.bitWidth ≤ 32}
    (left right : NativeFPU.Binary32Value width_le) : NativeFPU.Binary32Value width_le :=
  let leftBits := left.raw.1
  let rightBits := right.raw.1
  if binary32Finite leftBits && binary32Finite rightBits then
    NativeFPU.ofBinary32Bits <|
      (Float32.ofBits leftBits - Float32.ofBits rightBits).toBits
  else
    Backend.wordSub left right

/-- Opt in to guarded host binary32 multiplication. This function has no refinement certificate. -/
@[always_inline, inline] def mul32
    {width_le : FloatFormat.binary32.bitWidth ≤ 32}
    (left right : NativeFPU.Binary32Value width_le) : NativeFPU.Binary32Value width_le :=
  let leftBits := left.raw.1
  let rightBits := right.raw.1
  if binary32Finite leftBits && binary32Finite rightBits then
    NativeFPU.ofBinary32Bits <|
      (Float32.ofBits leftBits * Float32.ofBits rightBits).toBits
  else
    Backend.wordMul left right

/--
Opt in to guarded host binary32 division. This function has no refinement certificate.

A zero denominator retains the software path so `0 / 0`, division by signed zero, and the
library's exact invalid-result policy are not delegated to host NaN selection.
-/
@[always_inline, inline] def div32
    {width_le : FloatFormat.binary32.bitWidth ≤ 32}
    (left right : NativeFPU.Binary32Value width_le) : NativeFPU.Binary32Value width_le :=
  let leftBits := left.raw.1
  let rightBits := right.raw.1
  if binary32Finite leftBits && binary32Finite rightBits && !binary32Zero rightBits then
    NativeFPU.ofBinary32Bits <|
      (Float32.ofBits leftBits / Float32.ofBits rightBits).toBits
  else
    Backend.wordDiv left right

/--
Out-of-line software square root used when the host path declines.

The word dispatcher inlines the complete binary32 kernel; keeping this fallback as a call leaves
the unchecked entry point small.
-/
@[noinline] def softwareSqrt32 {width_le : FloatFormat.binary32.bitWidth ≤ 32}
    (value : NativeFPU.Binary32Value width_le) : NativeFPU.Binary32Value width_le :=
  Backend.wordSqrt value

/-- Out-of-line software square root for the binary64 host path; see `softwareSqrt32`. -/
@[noinline] def softwareSqrt64 {width_le : FloatFormat.binary64.bitWidth ≤ 64}
    (value : NativeFPU.Binary64Value width_le) : NativeFPU.Binary64Value width_le :=
  Backend.wordSqrt value

/--
Opt in to guarded host binary32 square root for nonnegative finite inputs and signed zero.
This function has no refinement certificate.

The explicit zero disjunct admits negative zero, whose sign must be preserved by IEEE square root,
without admitting any negative nonzero input.
-/
@[always_inline, inline] def sqrt32
    {width_le : FloatFormat.binary32.bitWidth ≤ 32}
    (value : NativeFPU.Binary32Value width_le) : NativeFPU.Binary32Value width_le :=
  let bits := value.raw.1
  if binary32Finite bits && (binary32Nonnegative bits || binary32Zero bits) then
    NativeFPU.ofBinary32Bits <| (Float32.ofBits bits).sqrt.toBits
  else
    softwareSqrt32 value

/-! ## Binary64 -/

/-- Opt in to guarded host binary64 addition. This function has no refinement certificate. -/
@[always_inline, inline] def add64
    {width_le : FloatFormat.binary64.bitWidth ≤ 64}
    (left right : NativeFPU.Binary64Value width_le) : NativeFPU.Binary64Value width_le :=
  let leftBits := left.raw.1
  let rightBits := right.raw.1
  if binary64Finite leftBits && binary64Finite rightBits then
    NativeFPU.ofBinary64Bits <|
      (Float.ofBits leftBits + Float.ofBits rightBits).toBits
  else
    Backend.wordAdd left right

/-- Opt in to guarded host binary64 subtraction. This function has no refinement certificate. -/
@[always_inline, inline] def sub64
    {width_le : FloatFormat.binary64.bitWidth ≤ 64}
    (left right : NativeFPU.Binary64Value width_le) : NativeFPU.Binary64Value width_le :=
  let leftBits := left.raw.1
  let rightBits := right.raw.1
  if binary64Finite leftBits && binary64Finite rightBits then
    NativeFPU.ofBinary64Bits <|
      (Float.ofBits leftBits - Float.ofBits rightBits).toBits
  else
    Backend.wordSub left right

/-- Opt in to guarded host binary64 multiplication. This function has no refinement certificate. -/
@[always_inline, inline] def mul64
    {width_le : FloatFormat.binary64.bitWidth ≤ 64}
    (left right : NativeFPU.Binary64Value width_le) : NativeFPU.Binary64Value width_le :=
  let leftBits := left.raw.1
  let rightBits := right.raw.1
  if binary64Finite leftBits && binary64Finite rightBits then
    NativeFPU.ofBinary64Bits <|
      (Float.ofBits leftBits * Float.ofBits rightBits).toBits
  else
    Backend.wordMul left right

/--
Opt in to guarded host binary64 division, with policy-sensitive zero denominators kept in
software. This function has no refinement certificate.
-/
@[always_inline, inline] def div64
    {width_le : FloatFormat.binary64.bitWidth ≤ 64}
    (left right : NativeFPU.Binary64Value width_le) : NativeFPU.Binary64Value width_le :=
  let leftBits := left.raw.1
  let rightBits := right.raw.1
  if binary64Finite leftBits && binary64Finite rightBits && !binary64Zero rightBits then
    NativeFPU.ofBinary64Bits <|
      (Float.ofBits leftBits / Float.ofBits rightBits).toBits
  else
    Backend.wordDiv left right

/--
Opt in to guarded host binary64 square root for nonnegative finite inputs and signed zero.
This function has no refinement certificate.

The explicit zero disjunct admits negative zero, whose sign must be preserved by IEEE square root,
without admitting any negative nonzero input.
-/
@[always_inline, inline] def sqrt64
    {width_le : FloatFormat.binary64.bitWidth ≤ 64}
    (value : NativeFPU.Binary64Value width_le) : NativeFPU.Binary64Value width_le :=
  let bits := value.raw.1
  if binary64Finite bits && (binary64Nonnegative bits || binary64Zero bits) then
    NativeFPU.ofBinary64Bits <| (Float.ofBits bits).sqrt.toBits
  else
    softwareSqrt64 value

end FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked
