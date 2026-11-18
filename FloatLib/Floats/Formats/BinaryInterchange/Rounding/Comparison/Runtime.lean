/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.DirectedRuntime
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime

/-!
# Rounding a real number that exact comparisons locate

An exact comparator `compare` locates a real number `r`: `compare c` is the ordering of `r` and
the rational `c`. `ComparisonRounding.round` rounds `r` into a binary format from such a
comparator alone, in any rounding direction: to nearest-even with `AlgebraicRounding.round` on
its magnitude, and in the other directions with the shared guard-and-sticky calculation of
`AlgebraicRounding.roundMagnitude`.
`ComparisonRounding.deliver` adds the exception flags and the ternary value of that one
rounding, which the comparator also decides: `inexact` when `r` is not the delivered value,
`overflow` when the rounding overflows, and `underflow` when an inexact result is tiny after
rounding.

The search costs one comparison for each bit of the significand. A caller that can round `r` to
nearest-even faster, from an enclosure for instance, passes that result to `deliver` as a
`Hint`, and `deliver` then uses the comparator only for what the hint leaves open. The theorems
ask that the hint is the correctly rounded value (`Hint.Sound`).

`Rule` is what an operation delivers at one operand: an exact zero or infinity, a pole (an
infinity with `divideByZero`), the invalid operation, or one rounding of a located real number.
`Unary` and `Binary` apply a table of rules to one or two operands after the NaN rule of
IEEE 754: a NaN operand gives that NaN quieted, a signaling one before a quiet one and the left
before the right, with `invalid` for a signaling NaN.

`Transcendentals.Recommended` builds the recommended functions of IEEE 754-2019 §9.2 from these.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.ComparisonRounding

/--
A dyadic number that stands for the nonnegative real number `r` that `compare` locates when `r`
is rounded. With `away := none` it lies in the same place between the values of the format as
`r`, for the two directions to nearest: the truncated significand of
`AlgebraicRounding.certificate` with two more bits that say whether the discarded part is zero,
below, at or above a half. With `away := some false` it is at most `r` and rounds toward zero as
`r` does (`representative_toward_le`), and with `away := some true` it is at least `r` and rounds
away from zero as `r` does (`le_representative_away`), unless `r` is `2 ^ (emax + 1)` or more.
For an `r` at most half the least subnormal or at least `2 ^ (emax + 1)` it is zero or a power
of two below, at or beyond the range of the format.
-/
def representative (fmt : FloatFormat) (sign : Bool) (compare : ℚ → Ordering)
    (away : Option Bool) : Numerics.Dyadic :=
  let bounds := AlgebraicRounding.powerBounds fmt compare
  match bounds.compare compare (AlgebraicRounding.lowerExponent fmt) with
  | .lt =>
      match away with
      | none => ⟨sign, 1, AlgebraicRounding.lowerExponent fmt - 1⟩
      | some false => ⟨sign, 0, 0⟩
      | some true => ⟨sign, 1, AlgebraicRounding.lowerExponent fmt⟩
  | .eq => ⟨sign, 1, AlgebraicRounding.lowerExponent fmt⟩
  | .gt =>
      if bounds.compare compare (AlgebraicRounding.upperExponent fmt) ≠ .lt then
        ⟨sign, 1, AlgebraicRounding.upperExponent fmt⟩
      else
        let certificate := AlgebraicRounding.certificate fmt compare
        match away with
        | none =>
            ⟨sign, 4 * certificate.mantissa +
              AlgebraicRounding.accuracyQuarter certificate.accuracy, certificate.exponent - 2⟩
        | some false => ⟨sign, certificate.mantissa, certificate.exponent⟩
        | some true =>
            ⟨sign,
              match certificate.accuracy with
              | .exact => certificate.mantissa
              | .inexact _ => certificate.mantissa + 1,
              certificate.exponent⟩

/--
Rounding of a signed magnitude that `compare` locates, in `mode`: to nearest-even by
`AlgebraicRounding.round`, and in every other direction by the shared
`AlgebraicRounding.roundMagnitude`.
-/
def roundMagnitude (fmt : FloatFormat) (sign : Bool) (compare : ℚ → Ordering)
    (mode : IEEERoundingMode) : Model fmt :=
  match mode with
  | .nearest => AlgebraicRounding.round fmt sign compare
  | mode => AlgebraicRounding.roundMagnitude fmt mode sign compare

/--
Rounding of the real number `r` that `compare` locates (`compare c` is the ordering of `r` and
`c`), in `mode` (nearest-even by default). A zero is delivered as `+0`, and a negative `r` is
rounded by its magnitude.
-/
def round (fmt : FloatFormat) (compare : ℚ → Ordering) (mode : IEEERoundingMode := .nearest) :
    Model fmt :=
  match compare 0 with
  | .eq => zero fmt false
  | .gt => roundMagnitude fmt false compare mode
  | .lt => roundMagnitude fmt true (fun candidate => (compare (-candidate)).swap) mode

/--
A nearest-even rounding of the located number that was found without the comparator: the value,
and the ordering of that value and the number (`.lt` for a value below it) when it is known.
-/
structure Hint (fmt : FloatFormat) where
  /-- The rounded value. -/
  value : Model fmt
  /-- The ordering of the value and the located number, if it is known. -/
  ternary : Option Ordering

/--
The outcome of delivering `value` in `mode` for the real number `r` that `compare` locates. A
finite delivery is compared with `r` once, unless `known` already is the ordering of the
delivery and `r`: the reversed comparison is the ternary value, and
`inexact` is its difference from `.eq`. `underflow` is raised for an inexact result that is tiny
after rounding: a zero or subnormal delivery, or the least normal magnitude delivered for an `r`
below the boundary of the direction (`underflowMidpoint` to nearest, `underflowPredecessor`
when the direction rounds the magnitude up). A rounding beyond the finite range raises
`overflow`, including when the format or rounding direction delivers the largest finite value.
The rounding direction determines where overflow begins on the grid of the destination.
-/
def outcome (fmt : FloatFormat) (compare : ℚ → Ordering) (value : Model fmt)
    (mode : IEEERoundingMode := .nearest) (known : Option Ordering := none) : IEEEOutcome fmt :=
  match toRat? value with
  | some delivered =>
      let ternary :=
        match known with
        | some ordering => ordering
        | none => (compare delivered).swap
      let inexact := ternary != .eq
      let negative := signBit value
      -- The ordering of the magnitude of `r` and a positive boundary.
      let magnitude (boundary : ℚ) : Ordering :=
        if negative then (compare (-boundary)).swap else compare boundary
      -- The least normal and the largest finite magnitude, read off the fields of the encoding,
      -- so that the boundaries of the exponent range are built only for a delivery next to them.
      let leastNormal := expField value == 1 && fracField value == 0
      let largestFinite :=
        expField value == fmt.maxFiniteExpField && fracField value == fmt.maxFiniteFracField
      let tiny := isTinyAfterRounding value ||
        (leastNormal &&
          match mode with
          | .nearest | .nearestAway => magnitude (underflowMidpoint fmt).toRat == .lt
          | .towardZero => false
          | .up | .down | .away =>
              mode.roundsAwayFromZero negative &&
                magnitude (underflowPredecessor fmt).toRat != .gt)
      let overflow := inexact && largestFinite &&
        match mode with
        | .nearest =>
            match magnitude (overflowMidpoint fmt).toRat with
            | .gt => true
            | .eq => maxFiniteMantissaOdd fmt
            | .lt => false
        | .nearestAway => magnitude (overflowMidpoint fmt).toRat != .lt
        | .towardZero | .up | .down | .away =>
            if mode.roundsAwayFromZero negative then magnitude (maxFiniteDyadic fmt).toRat == .gt
            else magnitude (overflowLimit fmt).toRat != .lt
      { value
        status := { overflow := overflow, underflow := tiny && inexact, inexact := inexact }
        ternary }
  | none =>
      { value
        status := { overflow := true, inexact := true }
        -- An overflow NaN can have a fixed encoding for both signs.
        ternary := compare 0 }

/--
The value that `deliver` delivers, with what is known of its ordering: to nearest-even the
result of `hint` when it has one, and the rounding by comparisons otherwise. The other
directions do not read the hint.
-/
def resolve (fmt : FloatFormat) (compare : ℚ → Ordering) (mode : IEEERoundingMode)
    (hint : Unit → Option (Hint fmt)) : Hint fmt :=
  match mode with
  | .nearest =>
      match hint () with
      | some found => found
      | none => ⟨round fmt compare .nearest, none⟩
  | mode => ⟨round fmt compare mode, none⟩

/--
One rounding in `mode` of the real number that `compare` locates, with its flags: the outcome
of the value that `resolve` selects.
-/
def deliver (fmt : FloatFormat) (compare : ℚ → Ordering) (mode : IEEERoundingMode := .nearest)
    (hint : Unit → Option (Hint fmt) := fun _ => none) : IEEEOutcome fmt :=
  let resolved := resolve fmt compare mode hint
  outcome fmt compare resolved.value mode resolved.ternary

/-- What an operation delivers at one operand or pair of operands. -/
inductive Rule where
  /-- An exact zero of the given sign, without a flag. -/
  | zero (negative : Bool)
  /-- An exact infinity of the given sign, without a flag. -/
  | infinity (negative : Bool)
  /-- A pole: the infinity of the given sign with `divideByZero`. -/
  | pole (negative : Bool)
  /-- The invalid operation: the default NaN with `invalid`. -/
  | invalid
  /-- One rounding of the real number that the comparator locates. -/
  | real (compare : ℚ → Ordering)

namespace Rule

/-- The rule of an exact rational value: one rounding of it, exact when it is representable. -/
def rational (value : ℚ) : Rule :=
  .real fun candidate => cmp value candidate

/-- The rule of a function with `f (±0) = ±0`: the zero of the operand's sign at zero, and the
located real number elsewhere. -/
def oddAt (negative : Bool) (argument : ℚ) (compare : ℚ → Ordering) : Rule :=
  if argument = 0 then .zero negative else .real compare

/-- The outcome of a rule in a format and a rounding direction. A rule that rounds a real number
passes `hint` on to `ComparisonRounding.deliver`. -/
def deliver (fmt : FloatFormat) (mode : IEEERoundingMode := .nearest)
    (hint : Unit → Option (Hint fmt) := fun _ => none) : Rule → IEEEOutcome fmt
  | .zero negative => { value := Model.zero fmt negative, status := .clear, ternary := .eq }
  | .infinity negative =>
      { value := nativeOverflow fmt negative, status := .clear
        ternary := exactInfinityTernary negative (nativeOverflow fmt negative) }
  | .pole negative =>
      { value := nativeOverflow fmt negative, status := { divideByZero := true }
        ternary := exactInfinityTernary negative (nativeOverflow fmt negative) }
  | .invalid => outcomeWithInvalid (invalidResult fmt) true
  | .real compare => ComparisonRounding.deliver fmt compare mode hint

end Rule

/-- An operand that is not a NaN: a finite value with its sign bit, or an infinity. -/
inductive Operand where
  /-- A finite operand: its sign bit, which a zero has too, and its exact value. -/
  | finite (negative : Bool) (value : ℚ)
  /-- An infinite operand with its sign. -/
  | infinite (negative : Bool)

/-- The sign of an operand: the sign bit of a finite one, zeros included. -/
def Operand.negative : Operand → Bool
  | .finite negative _ => negative
  | .infinite negative => negative

/-- The operand that a value is, or `none` for a NaN. -/
def Operand.of? {fmt : FloatFormat} (x : Model fmt) : Option Operand :=
  if isNaN x then none
  else if isInfinite x then some (.infinite (signBit x))
  else (toRat? x).map (.finite (signBit x))

/--
A function of one operand given by its table of rules: a NaN gives that NaN quieted, with
`invalid` when it was signaling, and every other operand the outcome of its rule, with the hint
of that operand.
-/
def unary {fmt : FloatFormat} (rule : Operand → Rule) (x : Model fmt)
    (mode : IEEERoundingMode := .nearest)
    (hint : Operand → Unit → Option (Hint fmt) := fun _ _ => none) : IEEEOutcome fmt :=
  match Operand.of? x with
  | some operand => (rule operand).deliver fmt mode (hint operand)
  | none => outcomeWithInvalid (quietNaN x) (isSignaling x)

/--
A function of two operands given by its table of rules: a NaN operand gives that NaN quieted, a
signaling one before a quiet one and the left before the right, with `invalid` when one was
signaling, and every other pair the outcome of its rule, with the hint of that pair.
-/
def binary {fmt : FloatFormat} (rule : Operand → Operand → Rule) (x y : Model fmt)
    (mode : IEEERoundingMode := .nearest)
    (hint : Operand → Operand → Unit → Option (Hint fmt) := fun _ _ _ => none) : IEEEOutcome fmt :=
  match Operand.of? x, Operand.of? y with
  | some left, some right => (rule left right).deliver fmt mode (hint left right)
  | _, _ =>
      outcomeWithInvalid ((chooseNaN2 x y).getD (invalidResult fmt))
        (isSignaling x || isSignaling y)

end FloatLib.Floats.Formats.BinaryInterchange.Model.ComparisonRounding
