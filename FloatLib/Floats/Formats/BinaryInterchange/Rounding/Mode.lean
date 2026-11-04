/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Operation.Context
public import FloatLib.Numerics.Quantization.Deterministic.MagnitudeRounding

/-!
# IEEE rounding modes for `Model`

`IEEERoundingMode` is the rounding direction that executable rounding and its proofs share. It has
the five rounding-direction attributes of IEEE 754-2019, which are the two nearest modes (they
differ only at an exact tie) and the three directed ones, plus rounding away from zero. IEEE 754
doesn't define that last one, but GNU MPFR does, as `MPFR_RNDA`. Stochastic rounding lives in the
broader quantization-policy vocabulary `Numerics.RoundingMode`, which has these directions too.

Next to the type sit helpers that say how each direction treats the magnitude of a result,
overflow, negation and a sum that cancels to an exact zero. For instance,
`IEEERoundingMode.magnitudeRounding` names the `Numerics.MagnitudeRounding` rule that a direction
applies to the magnitude of a result whose sign is known.

You write the constructors `nearest` (ties to even), `nearestAway`, `towardZero`, `up`, `down` and
`away` with a leading dot, as in `(mode := .up)`, and `open FloatLib.Rounding` names the type
`IEEERoundingMode` without its namespace.

## References

- IEEE Std 754-2019, "IEEE Standard for Floating-Point Arithmetic", Sections 4.3 and 6.3.
- The GNU MPFR Library manual, Section 4.4, "Rounding":
  <https://www.mpfr.org/mpfr-current/mpfr.html#Rounding>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Deterministic rounding direction: the five IEEE 754-2019 rounding-direction attributes and
rounding away from zero.

Operations take a direction as the option `(mode := .up)`, nearest-even by default. The leading
dot finds the constructor in the mode type the call expects, so the same spelling names the
direction of a P3109 or decimal operation, or of a conversion into a binary format.
-/
inductive IEEERoundingMode where
  /--
  Round to the nearest representable value, breaking ties toward an even significand. This is
  IEEE 754-2019 roundTiesToEven.
  -/
  | nearest
  /--
  Round to the nearest representable value, breaking ties toward the neighbour of larger
  magnitude. This is IEEE 754-2019 roundTiesToAway.
  -/
  | nearestAway
  /-- Round toward zero. -/
  | towardZero
  /-- Round toward positive infinity. -/
  | up
  /-- Round toward negative infinity. -/
  | down
  /--
  Round away from zero, to the neighbour of larger magnitude whenever the result is inexact. This
  is GNU MPFR's `MPFR_RNDA`, which is not an IEEE 754 rounding-direction attribute.
  -/
  | away
  deriving DecidableEq, Repr

namespace IEEERoundingMode

/--
All constructors of `IEEERoundingMode`, in their shared traversal order.

Callers use it instead of repeating the enumeration, so update it when adding a constructor.
-/
def all : List IEEERoundingMode :=
  [.nearest, .nearestAway, .towardZero, .up, .down, .away]

/--
A concise, stable name for diagnostics and interchange files.

These strings are a file format read by the MPFR oracle drivers, so they do not follow the
constructor names: `nearest` is `"nearestEven"`, `up` is `"towardPositive"`, `down` is
`"towardNegative"`, and `away` is `"awayFromZero"`. `toString` prints the constructor names.
-/
def name : IEEERoundingMode → String
  | .nearest => "nearestEven"
  | .nearestAway => "nearestAway"
  | .towardZero => "towardZero"
  | .up => "towardPositive"
  | .down => "towardNegative"
  | .away => "awayFromZero"

/-- Print a mode as its constructor name, the spelling user code writes after `(mode := ...)`. -/
instance : ToString IEEERoundingMode where
  toString
    | .nearest => "nearest"
    | .nearestAway => "nearestAway"
    | .towardZero => "towardZero"
    | .up => "up"
    | .down => "down"
    | .away => "away"

/--
The quantization-policy rounding mode with the same direction.

`Numerics.RoundingMode` also contains stochastic rounding, which has no constructor in
`IEEERoundingMode`, so this map is an embedding that misses stochastic rounding.
-/
def toRoundingMode : IEEERoundingMode → Numerics.RoundingMode
  | .nearest => .nearest
  | .nearestAway => .nearestAway
  | .towardZero => .towardZero
  | .up => .up
  | .down => .down
  | .away => .away

/--
Whether this mode, read as a directed rounding, moves an inexact result of the given sign away
from zero.

Upward rounding does so for positive results, downward rounding for negative ones and `away` for
every result. Rounding toward zero never does. Neither nearest mode is directed, so both give
`false` for either sign, and tininess detection relies on that at the midpoint just below the
smallest normal number, which both nearest modes take up to the normal number.
-/
@[inline] def roundsAwayFromZero (mode : IEEERoundingMode) (negative : Bool) : Bool :=
  match mode with
  | .nearest | .nearestAway | .towardZero => false
  | .up => !negative
  | .down => negative
  | .away => true

/--
Whether an overflowing result of the given sign takes the format's native overflow value instead
of saturating at the largest finite magnitude, as `directedOverflow` reads it.

Both nearest modes always do, and a directed mode (rounding away from zero included) does if and
only if it rounds that sign away from zero (IEEE 754-2019 Section 7.4). The native overflow value is
the signed infinity in IEEE encodings, a NaN in finite encodings that have one, and the largest
finite value otherwise (`nativeOverflow`).
-/
@[inline] def overflowRoundsMagnitudeUp (mode : IEEERoundingMode) (negative : Bool) : Bool :=
  match mode with
  | .nearest | .nearestAway => true
  | .towardZero | .up | .down | .away =>
      mode.roundsAwayFromZero negative

/--
The mode that mirrors this one under negation: rounding `-x` with `mode` gives the negation of
rounding `x` with `mode.negate`.

Negation exchanges the two infinity directions and fixes the other four modes, whose choice
depends only on the magnitude.
-/
def negate : IEEERoundingMode → IEEERoundingMode
  | .nearest => .nearest
  | .nearestAway => .nearestAway
  | .towardZero => .towardZero
  | .up => .down
  | .down => .up
  | .away => .away

/-- Negation fixes nearest-even rounding. -/
@[simp] theorem negate_nearest : IEEERoundingMode.nearest.negate = .nearest := rfl

/-- Negation fixes nearest-away rounding. -/
@[simp] theorem negate_nearestAway : IEEERoundingMode.nearestAway.negate = .nearestAway := rfl

/-- Negation fixes rounding toward zero. -/
@[simp] theorem negate_towardZero : IEEERoundingMode.towardZero.negate = .towardZero := rfl

/-- Negation turns rounding toward positive infinity into rounding toward negative infinity. -/
@[simp] theorem negate_up : IEEERoundingMode.up.negate = .down := rfl

/-- Negation turns rounding toward negative infinity into rounding toward positive infinity. -/
@[simp] theorem negate_down : IEEERoundingMode.down.negate = .up := rfl

/-- Negation fixes rounding away from zero. -/
@[simp] theorem negate_away : IEEERoundingMode.away.negate = .away := rfl

/--
Sign that IEEE 754 gives an exact zero sum whose operands have the signs `leftSign` and
`rightSign`.

By IEEE 754-2019 Section 6.3, an exact zero sum of operands with opposite signs is positive in
every rounding direction except toward negative infinity, where it is negative. Two zeros of the
same sign keep that sign in every direction. Rounding away from zero follows the other
directions, as MPFR does, so its exact cancellation gives positive zero.

`zero` keeps a negative sign only in formats with a signed zero.
-/
@[inline] def zeroSumSign (mode : IEEERoundingMode) (leftSign rightSign : Bool) : Bool :=
  match mode with
  | .down => leftSign || rightSign
  | .nearest | .nearestAway | .towardZero | .up | .away =>
      leftSign && rightSign

/--
The magnitude rounding rule that this mode applies to a result of the given sign.

The nearest modes round the magnitude to nearest with the same tie rule, toward-zero truncates it,
and away-from-zero rounds it up. The two infinity directions round the magnitude up when they move
the result away from zero and truncate it otherwise.
-/
@[inline] def magnitudeRounding (mode : IEEERoundingMode) (negative : Bool) :
    Numerics.MagnitudeRounding :=
  match mode with
  | .nearest => .nearestEven
  | .nearestAway => .nearestAway
  | .towardZero => .down
  | .up => if negative then .down else .up
  | .down => if negative then .up else .down
  | .away => .up

/-- Negating twice returns the original mode. -/
@[simp] theorem negate_negate (mode : IEEERoundingMode) : mode.negate.negate = mode := by
  cases mode <;> rfl

/-- The negated mode rounds a result away from zero if and only if this mode rounds its negation. -/
theorem roundsAwayFromZero_negate (mode : IEEERoundingMode) (negative : Bool) :
    mode.negate.roundsAwayFromZero negative = mode.roundsAwayFromZero (!negative) := by
  cases mode <;> cases negative <;> rfl

/-- The negated mode carries an overflow upward if and only if this mode carries its negation. -/
theorem overflowRoundsMagnitudeUp_negate (mode : IEEERoundingMode) (negative : Bool) :
    mode.negate.overflowRoundsMagnitudeUp negative =
      mode.overflowRoundsMagnitudeUp (!negative) := by
  cases mode <;> cases negative <;> rfl

/-- The negated mode treats a magnitude of one sign as this mode treats the opposite sign. -/
theorem magnitudeRounding_negate (mode : IEEERoundingMode) (negative : Bool) :
    mode.negate.magnitudeRounding negative = mode.magnitudeRounding (!negative) := by
  cases mode <;> cases negative <;> rfl

/-- A mode rounds a magnitude up if and only if it moves a result of that sign away from zero. -/
theorem magnitudeRounding_eq_up_iff (mode : IEEERoundingMode) (negative : Bool) :
    mode.magnitudeRounding negative = .up ↔ mode.roundsAwayFromZero negative = true := by
  cases mode <;> cases negative <;> simp [magnitudeRounding, roundsAwayFromZero]

end IEEERoundingMode

end Model
end FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLib.Rounding

/-!
## The rounding-mode type

`open FloatLib.Rounding` brings the type `IEEERoundingMode` into scope without its namespace, so
your code can take a rounding direction as a parameter. The directions keep their leading dot:

```
open FloatLib.Rounding

def third (mode : IEEERoundingMode) : Binary32 := ExecFloat.Binary.div 1 3 (mode := mode)

#eval third .up
#eval Model.sqrt x (mode := .up) (status := true)
```

Conversions into binary formats take `Numerics.RoundingMode`, which also has stochastic rounding.
`(mode := .up)` names its upward direction too, and an `IEEERoundingMode` value goes through
`toRoundingMode`.
-/

export FloatLib.Floats.Formats.BinaryInterchange.Model (IEEERoundingMode)

end FloatLib.Rounding
