/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Runtime
public import Init.Data.Float.Model.Unpacked.Round

/-!
# Integer square roots at the rounding scale

Discarding twice as many radicand bits as root bits preserves the truncated root. One retained
root bit and an exact square comparison recover the round and sticky bits without constructing
the full root or shifting it one bit at a time.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.ScaledSqrt

open Float.Model.UnpackedFloat

/-- Accuracy of an integer square root, from its exact nonnegative remainder. -/
@[inline] def accuracy (radicand root : Nat) : Accuracy :=
  let remainder := radicand - root * root
  if remainder = 0 then .exact
  else .inexact (if remainder ≤ root then .lt else .gt)

/-- The integer square root after a right shift, retaining exact round and sticky bits. -/
@[inline] def shifted (radicand shift : Nat) : ExtendedMantissa :=
  match shift with
  | 0 =>
      let root := Numerics.FixedWord.IntegerSquareRoot.sqrtNat radicand
      ExtendedMantissa.ofMantissaAndAccuracy root (accuracy radicand root)
  | dropped + 1 =>
      let radicandShift := 2 * dropped
      let root :=
        Numerics.FixedWord.IntegerSquareRoot.sqrtNat (radicand >>> radicandShift)
      ⟨root >>> 1, root % 2 != 0, radicand != ((root * root) <<< radicandShift)⟩

/-- Round a scaled integer square root through the unpacked model's normalization rules. -/
@[inline] def round (spec : Float.Model.Format) (sign : Sign)
    (radicand : Nat) (exponent : Int) : Float.Model.UnpackedFloat :=
  let totalExponent := Int.ofNat (radicand.log2 / 2) + 1 + exponent
  let shift := (spec.targetExponent totalExponent - exponent).toNat
  let extended := shifted radicand shift
  let rounded := extended.roundedMantissa
  let (finalExtended, finalExponent) :=
    shiftToTargetExponent spec rounded (exponent + shift) .exact
  if hzero : finalExtended.mantissa = 0 then
    .zero sign
  else
    .finite sign finalExtended.mantissa finalExponent (Nat.pos_of_ne_zero hzero)

end FloatLib.Floats.Formats.BinaryInterchange.Model.ScaledSqrt
