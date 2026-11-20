/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Comparison.Runtime
public import FloatLib.Numerics.Enclosure.Rational.Runtime
public import FloatLib.Numerics.Order.Bisection.Runtime

/-!
# Rounding a real number that exact comparisons locate, into a decimal format

An exact comparator `compare` locates a real number `r`: `compare c` is the ordering of `r` and
the rational `c`. `ComparisonRounding.round` rounds `r` into a decimal format from such a
comparator alone, in each of the five rounding directions of IEEE 754-2019 §4.3, and delivers
the value with its exception flags. The comparators are those of `Numerics.Exact`, which do not
depend on the radix, so this is the decimal counterpart of the binary
`Model.ComparisonRounding`.

The rounding has four steps. A comparison with the first power of ten beyond the finite range
settles overflow. A bisection over the quantum exponents finds the decade of the magnitude, and
with it the quantum exponent of the grid there, which is the least quantum exponent for a
magnitude below the least normal one. A bisection over the coefficients finds the integer part
of the magnitude in units of that quantum. Two more comparisons say whether the magnitude is
that grid point, and otherwise on which side of the midpoint of its cell it lies: these are the
guard and sticky bits, from which `MagnitudeRounding.increment` rounds in the direction. The
result is delivered with the least possible quantum exponent, so a coefficient has all the
digits of the precision unless the result is subnormal.

`inexact` is raised when the magnitude is not a grid point, `underflow` for an inexact result
whose exact magnitude is below the least normal one (tininess is detected before rounding, as
for the other decimal operations), and a rounded magnitude beyond the largest finite one gives
the overflow result of the direction with `overflow` and `inexact`.

`within` makes a comparator cheaper without changing its answers: it decides a comparison from
a rational enclosure of the located number wherever the enclosure decides it. `Rule.deliver`,
`unary` and `binary` apply the rule tables of `Model.ComparisonRounding` (`Rule`, `Operand`) to
decimal data, with the NaN rule of decimal arithmetic: the first NaN operand, quieted, with
`invalid` for a signaling NaN.

`Rounding.Comparison.Proof` proves that the result is the correctly rounded value in every
direction.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

open FloatLib.Numerics
open BinaryInterchange.Model (IEEERoundingMode)

/-- The member of the binary type of rounding directions with the same direction. -/
def RoundingMode.toIEEE : RoundingMode → IEEERoundingMode
  | .nearest => .nearest
  | .nearestAway => .nearestAway
  | .towardZero => .towardZero
  | .up => .up
  | .down => .down

namespace ComparisonRounding

open BinaryInterchange.Model.ComparisonRounding (Rule Operand)
open KernelPath (overflow)

/-- The first power of ten beyond every finite magnitude: `10 ^ (maxQuantum + precision)`. -/
def overflowBound (f : Format) : ℚ :=
  f.minNormal * (10 : ℚ) ^ ((f.maxQuantum - f.minQuantum).toNat + 1)

/--
The quantum exponent of the grid at a magnitude from the least normal magnitude up to
`overflowBound`, found by bisection: the least quantum exponent plus the number of decades
between the least normal magnitude and the located one.
-/
def quantum (f : Format) (compare : ℚ → Ordering) : Int :=
  let span := (f.maxQuantum - f.minQuantum).toNat
  f.minQuantum + bisect
    (fun index => decide (compare (f.minNormal * (10 : ℚ) ^ index) ≠ .lt))
    (span.log2 + 1) 0 (span + 1)

/--
The integer part of the located magnitude in units of `10 ^ quantum`, found by bisection over
the coefficients below `10 ^ precision`.
-/
def coefficient (f : Format) (compare : ℚ → Ordering) (quantum : Int) : Nat :=
  bisect (fun candidate => decide (compare ((candidate : ℚ) * (10 : ℚ) ^ quantum) ≠ .lt))
    (f.coefficientBound.log2 + 1) 0 f.coefficientBound

/-- A positive magnitude below `overflowBound`, located on the grid of a decimal format. -/
structure Located where
  /-- The quantum exponent of the grid at the magnitude. -/
  quantum : Int
  /-- The integer part of the magnitude in units of `10 ^ quantum`. -/
  coefficient : Nat
  /-- Whether the rest is at least half a unit. -/
  guard : Bool
  /-- Whether the rest is neither zero nor exactly half a unit. -/
  sticky : Bool
  /-- Whether the magnitude is below the least normal magnitude. -/
  tiny : Bool

/--
Locate a positive magnitude below `overflowBound` on the grid of the format: its quantum
exponent, the integer part of its coefficient, and the place of the rest in the cell.
-/
def locate (f : Format) (compare : ℚ → Ordering) : Located :=
  let tiny := compare f.minNormal == .lt
  let quantum := if tiny then f.minQuantum else quantum f compare
  let coefficient := coefficient f compare quantum
  let unit : ℚ := (10 : ℚ) ^ quantum
  if compare ((coefficient : ℚ) * unit) == .eq then ⟨quantum, coefficient, false, false, tiny⟩
  else
    let half := compare (((coefficient : ℚ) + 1 / 2) * unit)
    ⟨quantum, coefficient, half != .lt, half != .eq, tiny⟩

/--
The outcome of rounding a located magnitude with the sign `negative` in the direction `mode`:
the coefficient or the next one, as the direction decides from the guard and sticky bits, a
carry into the next decade when the coefficient reaches the coefficient bound, and the
overflow result when the quantum exponent then exceeds the largest one.
-/
def Located.round (f : Format) (mode : RoundingMode) (negative : Bool) (located : Located) :
    Outcome :=
  let rounded :=
    if (mode.toIEEE.magnitudeRounding negative).increment (located.coefficient % 2 == 1)
        located.guard located.sticky then located.coefficient + 1
    else located.coefficient
  let carried : Nat × Int :=
    if rounded = f.coefficientBound then (f.payloadBound, located.quantum + 1)
    else (rounded, located.quantum)
  if f.maxQuantum < carried.2 then overflow f mode negative
  else
    let inexact := located.guard || located.sticky
    { value := .finite negative carried.1 carried.2
      status := { inexact := inexact, underflow := located.tiny && inexact } }

/--
Rounding of a positive magnitude that `compare` locates, with the sign `negative`, in the
direction `mode`: the value with its flags.
-/
def roundMagnitude (f : Format) (mode : RoundingMode) (negative : Bool)
    (compare : ℚ → Ordering) : Outcome :=
  if compare (overflowBound f) ≠ .lt then overflow f mode negative
  else (locate f compare).round f mode negative

/--
Rounding of the real number `r` that `compare` locates (`compare c` is the ordering of `r` and
`c`), in the direction `mode`: the value with its flags. A zero is delivered as `+0` with the
least quantum exponent, and a negative `r` is rounded by its magnitude.
-/
def round (f : Format) (mode : RoundingMode) (compare : ℚ → Ordering) : Outcome :=
  match compare 0 with
  | .eq => { value := .finite false 0 f.minQuantum }
  | .gt => roundMagnitude f mode false compare
  | .lt => roundMagnitude f mode true fun candidate => (compare (-candidate)).swap

/--
A comparator that answers from a rational enclosure of the located number where the enclosure
decides: a candidate below the enclosure is below the number, one above it is above, and the
comparator is asked only about a candidate inside.
-/
def within (interval : RationalInterval) (compare : ℚ → Ordering) (candidate : ℚ) : Ordering :=
  if candidate < interval.lo then .gt
  else if interval.hi < candidate then .lt
  else compare candidate

/--
The outcome of a rule in a decimal format and a rounding direction. An exact zero has the
least quantum exponent. A rule that rounds a real number asks its comparator through the
enclosure when `enclosure` has one.
-/
def deliver (f : Format) (mode : RoundingMode)
    (enclosure : Unit → Option RationalInterval := fun _ => none) : Rule → Outcome
  | .zero negative => { value := .finite negative 0 f.minQuantum }
  | .infinity negative => { value := .infinity negative }
  | .pole negative => { value := .infinity negative, status := { divideByZero := true } }
  | .invalid => Arithmetic.invalidResult
  | .real compare =>
      round f mode <|
        match enclosure () with
        | some interval => within interval compare
        | none => compare

/-- The operand that a datum is, or `none` for a NaN: a finite datum with its sign and its
exact value, or an infinity. -/
def operand? : Datum → Option Operand
  | .finite negative coefficient quantum =>
      some (.finite negative (Datum.finiteValue negative coefficient quantum))
  | .infinity negative => some (.infinite negative)
  | .nan .. => none

/--
A function of one decimal operand given by its table of rules: a NaN gives that NaN quieted,
with `invalid` when it was signaling, and every other operand the outcome of its rule, with
the enclosure of that operand.
-/
def unary (f : Format) (rule : Operand → Rule) (mode : RoundingMode) (x : Datum)
    (enclosure : Operand → Unit → Option RationalInterval := fun _ _ => none) : Outcome :=
  match x with
  | .nan negative signaling payload => Arithmetic.nanResult f negative payload signaling
  | x =>
      match operand? x with
      | some operand => deliver f mode (enclosure operand) (rule operand)
      | none => Arithmetic.invalidResult

/--
A function of two decimal operands given by its table of rules: the first NaN operand quieted,
with `invalid` when an operand is a signaling NaN, and every other pair the outcome of its
rule, with the enclosure of that pair.
-/
def binary (f : Format) (rule : Operand → Operand → Rule) (mode : RoundingMode) (x y : Datum)
    (enclosure : Operand → Operand → Unit → Option RationalInterval := fun _ _ _ => none) :
    Outcome :=
  match x, y with
  | .nan negative signaling payload, y =>
      Arithmetic.nanResult f negative payload (signaling || y.isSignaling)
  | _, .nan negative signaling payload => Arithmetic.nanResult f negative payload signaling
  | x, y =>
      match operand? x, operand? y with
      | some left, some right => deliver f mode (enclosure left right) (rule left right)
      | _, _ => Arithmetic.invalidResult

end ComparisonRounding

end FloatLib.Floats.Formats.DecimalInterchange
