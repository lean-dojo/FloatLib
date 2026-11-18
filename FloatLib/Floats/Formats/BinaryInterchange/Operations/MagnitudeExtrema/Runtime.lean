/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# Minimum and maximum by magnitude

IEEE 754-2019 §9.6 recommends eight minimum and maximum operations. Four of them compare the
operands themselves (`minimum`, `maximum`, `minimumNumber`, `maximumNumber`, in
`Operations.Compare.Runtime` and `Operations.Runtime`). This module adds the four that compare
magnitudes first: `minimumMagnitude`, `maximumMagnitude`, `minimumMagnitudeNumber` and
`maximumMagnitudeNumber`.

The clause number is taken from the 754 working group's list of changes from 754-2008
(<https://grouper.ieee.org/groups/msc/ANSI_IEEE-Std-754-2019/background/>), and the semantics
from the C23 binding of these operations (ISO/IEC 9899:2024 working draft N3220, Table F.2,
7.12.12.6, 7.12.12.7, 7.12.12.10, 7.12.12.11 and F.10.9.4, F.10.9.5): `minimumMagnitude x y` is
`x` if `|x| < |y|`, `y` if `|y| < |x|`, and `minimum x y` otherwise, and the `Number` forms differ
only in their treatment of NaN operands.

All four are one selection, `Internal.Value.magnitudeExtremum larger base`: compare `abs x` with
`abs y` numerically, deliver the operand of smaller (or larger) magnitude, and fall back on `base`
when the magnitudes are equal or an operand is a NaN. `base` is the operation of the same name
without `Magnitude`, so NaN selection, the signed-zero rule and the invalid signal are inherited.
The operations are exact, so they take only `status`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

namespace Internal.Value

/--
Selection by magnitude: the operand whose absolute value is numerically smaller (`larger :=
false`) or larger (`larger := true`), and `base x y` when the magnitudes compare equal or an
operand is a NaN.
-/
@[inline] def magnitudeExtremum {fmt : FloatFormat} (larger : Bool)
    (base : Model fmt → Model fmt → Model fmt) (x y : Model fmt) : Model fmt :=
  match compare (abs x) (abs y) with
  | some .lt => if larger then y else x
  | some .gt => if larger then x else y
  | some .eq | none => base x y

end Internal.Value

/--
A selection by magnitude with the invalid signal of IEEE 754-2019 §6.2 and §9.6: with
`status := true` the result is the `IEEEOutcome` whose `invalid` flag is set exactly when an
operand is a signaling NaN. The four operations below are its instances.
-/
@[macro_inline] def magnitudeExtremum {fmt : FloatFormat} (larger : Bool)
    (base : Model fmt → Model fmt → Model fmt) (x y : Model fmt) (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true =>
      outcomeWithInvalid (Internal.Value.magnitudeExtremum larger base x y)
        (isSignaling x || isSignaling y)
  | false => Internal.Value.magnitudeExtremum larger base x y

/--
IEEE 754-2019 §9.6 `minimumMagnitude` (C23 `fminimum_mag`, N3220 7.12.12.7): `x` if `|x| < |y|`,
`y` if `|y| < |x|`, and `minimum x y` otherwise, which propagates a NaN operand as a quiet NaN.
With `status := true` the result is the `IEEEOutcome`, with `invalid` set exactly when an operand
is a signaling NaN.
-/
@[macro_inline] def minimumMagnitude {fmt : FloatFormat} (x y : Model fmt)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  magnitudeExtremum false (fun x y => minimum x y) x y status

/--
IEEE 754-2019 §9.6 `maximumMagnitude` (C23 `fmaximum_mag`, N3220 7.12.12.6): `x` if `|x| > |y|`,
`y` if `|y| > |x|`, and `maximum x y` otherwise, which propagates a NaN operand as a quiet NaN.
With `status := true` the result is the `IEEEOutcome`, with `invalid` set exactly when an operand
is a signaling NaN.
-/
@[macro_inline] def maximumMagnitude {fmt : FloatFormat} (x y : Model fmt)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  magnitudeExtremum true (fun x y => maximum x y) x y status

/--
IEEE 754-2019 §9.6 `minimumMagnitudeNumber` (C23 `fminimum_mag_num`, N3220 7.12.12.11 and
F.10.9.5): `x` if `|x| < |y|`, `y` if `|y| < |x|`, and `minimumNumber x y` otherwise, which
returns the number when exactly one operand is a NaN. With `status := true` the result is the
`IEEEOutcome`, with `invalid` set exactly when an operand is a signaling NaN, also when the
other operand supplies the result.
-/
@[macro_inline] def minimumMagnitudeNumber {fmt : FloatFormat} (x y : Model fmt)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  magnitudeExtremum false (fun x y => minimumNumber x y) x y status

/--
IEEE 754-2019 §9.6 `maximumMagnitudeNumber` (C23 `fmaximum_mag_num`, N3220 7.12.12.10 and
F.10.9.5): `x` if `|x| > |y|`, `y` if `|y| > |x|`, and `maximumNumber x y` otherwise, which
returns the number when exactly one operand is a NaN. With `status := true` the result is the
`IEEEOutcome`, with `invalid` set exactly when an operand is a signaling NaN, also when the
other operand supplies the result.
-/
@[macro_inline] def maximumMagnitudeNumber {fmt : FloatFormat} (x y : Model fmt)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  magnitudeExtremum true (fun x y => maximumNumber x y) x y status

end Model
end FloatLib.Floats.Formats.BinaryInterchange
