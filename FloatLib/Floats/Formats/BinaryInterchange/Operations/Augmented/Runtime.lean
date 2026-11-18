/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.TiesTowardZero
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime

/-!
# Augmented arithmetic operations

IEEE 754-2019 §9.5 recommends, for binary formats, three operations that deliver two results: a
rounded result, the head, and the error of that rounding, the tail. They standardize the
transformations known as twoSum and twoProduct, with a rounding direction of their own, to
nearest with ties toward zero, which makes the results independent of the order in which a
reduction is evaluated.

The standard's text is not public. The clause number is the one in the 754 working group's list
of changes from 754-2008 (<https://grouper.ieee.org/groups/msc/ANSI_IEEE-Std-754-2019/background/>).
The definitions below follow Riedy and Demmel, "Augmented Arithmetic Operations Proposed for
IEEE-754 2018" (ARITH 2018, Section III and Tables II and III), and the statement of the
published operations in Boldo, Lauter and Muller, "Emulating Round-to-Nearest Ties-to-Zero
'Augmented' Floating-Point Operations Using Round-to-Nearest Ties-to-Even Arithmetic" (IEEE
Transactions on Computers 70(7), 2021, Section I), where `RN₀` is `roundTiesTowardZeroAt`:

* `augmentedAddition x y` has head `RN₀(x + y)` and, when the head is finite, tail
  `x + y - head`, which is a value of the format. A zero tail has the sign of the head.
* `augmentedSubtraction x y` is `augmentedAddition x (-y)`.
* `augmentedMultiplication x y` has head `RN₀(x * y)` and, when the head is finite, tail
  `RN₀(x * y - head)`, which differs from `x * y - head` only when that error has bits below the
  least subnormal. A zero tail of an exact error has the sign of the head.
* When the head overflows, head and tail are the same infinity, and `overflow` and `inexact` are
  raised. Overflow is decided on the head rounded with an unbounded exponent range, so the
  midpoint between the largest finite value and the next grid value does not overflow.
* A zero head comes with an equal zero tail: the sum of two zeros is `-0` only when both are,
  an exact cancellation is `+0`, and a zero product has the product of the signs.
* Operands that are not both finite give the special value of ordinary addition or
  multiplication as head and as tail, with its `invalid` flag: a quiet NaN for a NaN operand, for
  infinities of opposite signs and for zero times infinity, and the infinity otherwise.
* `inexact` is raised exactly when head and tail do not add up to the exact result, and then
  `underflow` is raised too unless the head overflowed: an error of a product has at most as many
  significant bits as the format, so it is rounded only below the least subnormal.

All three run one kernel, `Internal.Status.augmented`, on the exact dyadic sum or product. The
definitions cover every `FloatFormat`; a descriptor without infinities delivers its own overflow
value as head and tail.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange

/--
The two results of an augmented operation and the exceptions it raised. The carrier `α` is
`Model fmt` for the descriptor model and a configured type for stored values.
-/
structure AugmentedOutcome (α : Type) where
  /-- The exact result rounded to nearest with ties toward zero. -/
  head : α
  /-- The error of the head: the exact result minus the head, rounded the same way. -/
  tail : α
  /-- Exceptions raised by the operation. -/
  status : Numerics.IEEEStatus := {}
  deriving DecidableEq

/-- Carry head and tail through a conversion of the carrier. The flags are kept. -/
def AugmentedOutcome.map {α β : Type} (convert : α → β) (outcome : AugmentedOutcome α) :
    AugmentedOutcome β :=
  { head := convert outcome.head, tail := convert outcome.tail, status := outcome.status }

namespace Model

namespace Internal.Status

/--
Head, tail and flags of an exact dyadic result. `zeroNegative` is the sign of a zero result, which
the exact value does not determine.

The head is `roundDyadicTiesTowardZero fmt exact`. Its grid value is subtracted from the exact
result without error, and the difference is rounded the same way to give the tail.
-/
def augmented (fmt : FloatFormat) (exact : Numerics.Dyadic) (zeroNegative : Bool) :
    AugmentedOutcome (Model fmt) :=
  if exact.significand == 0 then
    { head := zero fmt zeroNegative, tail := zero fmt zeroNegative }
  else
    let grid := tiesTowardZeroGrid fmt exact
    let head := Model.roundDyadic fmt grid
    if dyadicMagnitudeOverflows fmt grid then
      { head, tail := head, status := { overflow := true, inexact := true } }
    else
      let error := Numerics.Dyadic.sub exact grid
      if error.significand == 0 then
        { head, tail := zero fmt exact.negative }
      else
        let tailGrid := tiesTowardZeroGrid fmt error
        let inexact := (Numerics.Dyadic.sub error tailGrid).significand != 0
        { head, tail := Model.roundDyadic fmt tailGrid,
          status := { underflow := inexact, inexact } }

/-- Head and tail are both the special value of an ordinary operation, with its flags. -/
@[inline] def augmentedSpecial {fmt : FloatFormat} (special : IEEEOutcome fmt) :
    AugmentedOutcome (Model fmt) :=
  { head := special.value, tail := special.value, status := special.status }

end Internal.Status

/--
IEEE 754-2019 §9.5 `augmentedAddition`: the head `RN₀(x + y)`, rounded to nearest with ties
toward zero, and the tail `x + y - head`. For finite operands of a conventional IEEE descriptor
with a finite head, `toReal_augmentedAddition_head` and `toReal_augmentedAddition_add` prove that
the head is that rounding and that head and tail add up to `x + y` exactly. See the module
documentation for zeros, overflow, infinities and NaNs.
-/
def augmentedAddition {fmt : FloatFormat} (x y : Model fmt) : AugmentedOutcome (Model fmt) :=
  match toDyadic? x, toDyadic? y with
  | some dx, some dy =>
      Internal.Status.augmented fmt (addDyadic dx dy) (dx.negative && dy.negative)
  | _, _ => Internal.Status.augmentedSpecial (add x y (status := true))

/--
IEEE 754-2019 §9.5 `augmentedSubtraction`: `augmentedAddition x (-y)`, as the standard defines
it.
-/
def augmentedSubtraction {fmt : FloatFormat} (x y : Model fmt) : AugmentedOutcome (Model fmt) :=
  augmentedAddition x (neg y)

/--
IEEE 754-2019 §9.5 `augmentedMultiplication`: the head `RN₀(x * y)`, rounded to nearest with
ties toward zero, and the tail `RN₀(x * y - head)`. For finite operands of a conventional IEEE
descriptor with finite results, `toReal_augmentedMultiplication_head` and
`toReal_augmentedMultiplication_tail` prove these two roundings, and
`augmentedMultiplication_inexact_iff` that `inexact` is raised exactly when head and tail do not
add up to `x * y`. See the module documentation for zeros, overflow, infinities and NaNs.
-/
def augmentedMultiplication {fmt : FloatFormat} (x y : Model fmt) : AugmentedOutcome (Model fmt) :=
  match toDyadic? x, toDyadic? y with
  | some dx, some dy =>
      Internal.Status.augmented fmt
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
        (Bool.xor dx.negative dy.negative)
  | _, _ => Internal.Status.augmentedSpecial (mul x y (status := true))

end Model
end FloatLib.Floats.Formats.BinaryInterchange
