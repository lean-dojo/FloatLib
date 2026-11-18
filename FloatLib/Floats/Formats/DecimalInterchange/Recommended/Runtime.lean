/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Comparison.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.TotalOrder.Runtime
public meta import FloatLib.Tactic.IEEENames

/-!
# Quantum, minimum and maximum, and NaN payloads of decimal data

Three groups of operations of IEEE 754-2019 on decimal data, for every `Format`. The text of the
standard is not public. Names and clause numbers are those of the operation table of
ISO/IEC 9899:2024 (C23, working draft N3220) Annex F, Table F.2, and of the 754 working group's
list of changes from 754-2008
(<https://grouper.ieee.org/groups/msc/ANSI_IEEE-Std-754-2019/background/>).

`quantum` (§5.3.2, new in 2019; C23 `quantumdN`, N3220 7.12.15.3) is the quantum of a finite
datum, `1 × 10 ^ q` for the quantum exponent `q`. An infinity gives `+∞`, and a NaN is
propagated as a quiet NaN.

The eight minimum and maximum operations of §9.6 (C23 `fminimum` to `fmaximum_mag_num`, N3220
7.12.12.4 to 7.12.12.11 and F.10.9.4, F.10.9.5) are the instances of `extremum`, which has three
Boolean parameters: whether the larger operand is selected, whether the operands are compared
by magnitude, and whether a number is preferred to a NaN.

* Two operands that are not NaNs are compared by value, and the smaller or the larger one is
  delivered as it is, with its quantum. Operands of equal value are ordered by `totalOrder`:
  `-0` is below `+0`, and of two members of one cohort the positive one with the smaller
  exponent is the smaller. The standard leaves the choice between equal operands of one sign
  free. This is the choice of Cowlishaw's General Decimal Arithmetic Specification 1.70 (`max`
  and `min`, pages 31 and 32), which makes the operations commutative.
* By magnitude, the operand of smaller or larger absolute value is selected, and operands of
  equal magnitude fall back to the comparison by value.
* A NaN operand gives a quiet NaN, the first one of two. When a number is preferred, one NaN
  operand gives the other operand, and two NaN operands give a quiet NaN.
* `invalid` is raised exactly when an operand is a signaling NaN, also when the other operand
  supplies the result. No other flag is raised.

`getPayload`, `setPayload` and `setPayloadSignaling` (§9.7; C23 `getpayloaddN`, `setpayloaddN`,
`setpayloadsigdN`, N3220 F.10.13.2 to F.10.13.4) read the payload of a NaN as a nonnegative
integral datum with quantum exponent zero, and build the quiet or the signaling NaN with a
clear sign and a given payload. An operand of `getPayload` that is not a NaN gives `-1`. An
operand of the two setters that is not a nonnegative integer below `payloadBound` of the format
gives `+0`. These three raise no flag.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/--
IEEE 754-2019 §5.3.2 `quantum` (C23 `quantumdN`, N3220 7.12.15.3): `1 × 10 ^ q` for a finite
datum of quantum exponent `q`, `+∞` for an infinity, and a quiet NaN for a NaN, with `invalid`
for a signaling one.
-/
def quantum (f : Format) : Datum → Outcome
  | .nan s t p => nanResult f s p t
  | .infinity _ => { value := .infinity false }
  | .finite _ _ q => { value := .finite false 1 q }

/--
The smaller (`larger := false`) or larger (`larger := true`) of two data that are not NaNs, by
value, and by `totalOrder` when the values are equal.
-/
def selectExtremum (larger : Bool) (x y : Datum) : Datum :=
  match x.compare y with
  | some .lt => if larger then y else x
  | some .gt => if larger then x else y
  | _ => if x.totalOrder y = larger then y else x

/--
The datum of smaller (`larger := false`) or larger (`larger := true`) magnitude of two data
that are not NaNs, and `selectExtremum larger x y` when the magnitudes are equal.
-/
def selectByMagnitude (larger : Bool) (x y : Datum) : Datum :=
  match x.abs.compare y.abs with
  | some .lt => if larger then y else x
  | some .gt => if larger then x else y
  | _ => selectExtremum larger x y

/--
The minimum and maximum operations of IEEE 754-2019 §9.6 as one selection. `larger` selects the
larger operand, `magnitude` compares by absolute value, and `number` prefers a number to a NaN.
See the module documentation for equal operands, NaNs and the `invalid` flag.
-/
def extremum (f : Format) (larger magnitude number : Bool) : Datum → Datum → Outcome
  | .nan s t p, .nan _ u _ => nanResult f s p (t || u)
  | .nan s t p, y => if number then { value := y, status := { invalid := t } }
      else nanResult f s p t
  | x, .nan s t p => if number then { value := x, status := { invalid := t } }
      else nanResult f s p t
  | x, y => { value := if magnitude then selectByMagnitude larger x y
      else selectExtremum larger x y }

ieee_extrema extremum (f : Format) (x y : Datum) : Outcome :=
  fun larger magnitude number => extremum f larger magnitude number x y

end Arithmetic

namespace Datum

/--
The payload that a datum names: its value when it is a nonnegative integer below
`f.payloadBound` with a clear sign, in any member of its cohort.
-/
def admissiblePayload? (f : Format) : Datum → Option Nat
  | .finite false c (.ofNat k) =>
      if c * 10 ^ k < f.payloadBound then some (c * 10 ^ k) else none
  | .finite false c (.negSucc k) =>
      if c % 10 ^ (k + 1) = 0 ∧ c / 10 ^ (k + 1) < f.payloadBound then
        some (c / 10 ^ (k + 1))
      else none
  | _ => none

/--
IEEE 754-2019 §9.7 `getPayload` (C23 `getpayloaddN`, N3220 F.10.13.2): the payload of a quiet or
signaling NaN as a nonnegative integer with quantum exponent zero, and `-1` for a datum that is
not a NaN. No flag is raised.
-/
def getPayload : Datum → Datum
  | .nan _ _ p => .finite false p 0
  | _ => .finite true 1 0

/--
IEEE 754-2019 §9.7 `setPayload` (C23 `setpayloaddN`, N3220 F.10.13.3): the quiet NaN with a
clear sign and the payload that the operand names, and `+0` when it names none
(`admissiblePayload?`). No flag is raised.
-/
def setPayload (f : Format) (x : Datum) : Datum :=
  match x.admissiblePayload? f with
  | some n => .nan false false n
  | none => .finite false 0 0

/--
IEEE 754-2019 §9.7 `setPayloadSignaling` (C23 `setpayloadsigdN`, N3220 F.10.13.4): the
signaling NaN with a clear sign and the payload that the operand names, and `+0` when it names
none (`admissiblePayload?`). No flag is raised.
-/
def setPayloadSignaling (f : Format) (x : Datum) : Datum :=
  match x.admissiblePayload? f with
  | some n => .nan false true n
  | none => .finite false 0 0

end Datum
end FloatLib.Floats.Formats.DecimalInterchange
