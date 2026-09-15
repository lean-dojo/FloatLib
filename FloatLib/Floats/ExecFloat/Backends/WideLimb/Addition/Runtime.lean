/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Round.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.Dyadic

/-!
# Wide-limb addition and subtraction runtime

`alignAndRound?` combines two signed magnitudes given at unsigned scales, the shared core of
addition, subtraction, and fused multiply-add. After ordering the operands by scale it takes one
of two routes.

* When the scale difference `d` is at least three and the higher-scale operand dominates, the
  lower operand is shifted right by `d - 3` bits and the higher operand is shifted left by three.
  The discarded tail supplies a sticky bit after addition, or a borrow and sticky bit after
  subtraction. The dominance bound leaves enough bits above the jammed position for
  `roundShiftRightEven_shiftRightJam` to preserve the final nearest-even result.
* Otherwise the exact sum or difference is formed in limbs; cancellation is exact.

Both routes end in `roundNormal?`. `addNormal?` decodes two normal stored values into this core;
`add` and `sub` use `Model.Spec.add` and `Model.Spec.sub`, respectively, for declined cases.
`Addition.Proof` proves that they equal `Model.Spec.add` and `Model.Spec.sub`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

open FloatLib.Numerics

/--
Combine two nonzero signed magnitudes whose scales satisfy `sb ≤ sa`.

The value computed is `(aSign, a * 2^sa) + (bSign, b * 2^sb)` at unsigned scale `sb`, rounded by
`roundNormal?` with the given rounding offset. Both magnitudes are expected to be at least
`2^fracWidth`; `Addition.Proof.alignOrdered?_refines` states the contract.
-/
def alignOrdered? (fmt : FloatFormat) (roundOffset : Nat) (aSign : Bool) (a : LimbArray) (sa : Nat)
    (bSign : Bool) (b : LimbArray) (sb : Nat) : Option (Value fmt) :=
  let distance := sa - sb
  let aLeading := a.log2
  let bLeading := b.log2
  if 3 ≤ distance ∧ bLeading + 2 ≤ aLeading + distance then
    let jam := distance - 3
    let shifted := b.shiftRight jam
    let sticky := b.anyBelow jam
    let scaled := a.shiftLeft 3
    if aSign == bSign then
      roundNormal? fmt aSign ((scaled.add shifted).orLowBit sticky) jam (sb + roundOffset)
    else
      roundNormal? fmt aSign
        ((scaled.sub shifted (if sticky then 1 else 0)).orLowBit sticky) jam (sb + roundOffset)
  else
    let scaled := a.shiftLeft distance
    if aSign == bSign then
      roundNormal? fmt aSign (scaled.add b) 0 (sb + roundOffset)
    else
      match scaled.compare b with
      | .eq => some (pack fmt false 0 (LimbArray.zero 0))
      | .gt => roundNormal? fmt aSign (scaled.sub b) 0 (sb + roundOffset)
      | .lt => roundNormal? fmt bSign (b.sub scaled) 0 (sb + roundOffset)

/-- Combine two nonzero signed magnitudes at arbitrary unsigned scales. -/
def alignAndRound? (fmt : FloatFormat) (roundOffset : Nat) (aSign : Bool) (a : LimbArray) (sa : Nat)
    (bSign : Bool) (b : LimbArray) (sb : Nat) : Option (Value fmt) :=
  if sa < sb then
    alignOrdered? fmt roundOffset bSign b sb aSign a sa
  else
    alignOrdered? fmt roundOffset aSign a sa bSign b sb

/--
Add two normal stored values, negating the second when `negateY` holds; other cases are declined.
-/
def addNormal? (fmt : FloatFormat) (negateY : Bool) (x y : Value fmt) : Option (Value fmt) :=
  let xExponent := expWord x
  let yExponent := expWord y
  if xExponent == 0 || xExponent == expAllOnes fmt ||
      yExponent == 0 || yExponent == expAllOnes fmt then
    none
  else
    alignAndRound? fmt (FiniteKernel.finiteScaleOffset fmt)
      (signBit x) (normalMantissa x) (xExponent.toNat - 1)
      (Bool.xor (signBit y) negateY) (normalMantissa y) (yExponent.toNat - 1)

/-- Wide-limb addition with the reference operation for declined cases. -/
def add (fmt : FloatFormat) (x y : Value fmt) : Value fmt :=
  match addNormal? fmt false x y with
  | some sum => sum
  | none => ofModel (Spec.add (toModel x) (toModel y))

/-- Wide-limb subtraction with the reference operation for declined cases. -/
def sub (fmt : FloatFormat) (x y : Value fmt) : Value fmt :=
  match addNormal? fmt true x y with
  | some difference => difference
  | none => ofModel (Spec.sub (toModel x) (toModel y))

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
