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

This type provides the five rounding-direction attributes of IEEE 754-2019: the two nearest modes,
which differ only at an exact tie, and the three directed modes. It also provides rounding away
from zero, GNU MPFR's `MPFR_RNDA`, which IEEE 754 does not define. The broader quantization-policy
vocabulary `Numerics.RoundingMode` also contains stochastic rounding.

This is the shared mode definition for executable rounding and its proofs. The helpers beside it
state how each direction treats the magnitude of a result, overflow, negation, and an exactly
cancelling sum. `IEEERoundingMode.magnitudeRounding` names the `Numerics.MagnitudeRounding` rule
that a direction applies to the magnitude of a result of known sign.

The constructors are `nearest` (ties to even), `nearestAway`, `towardZero`, `up`, `down`, and
`away`. Library code writes them with a leading dot, as in `.up`, and user code can
`open FloatLib.Rounding` to write the bare names.

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

Operations take a direction as the option `(mode := .up)`, nearest-even by default. After
`open FloatLib.Rounding`, user code can write the six constructors without the leading dot, as in
`(mode := up)`.
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
`IEEERoundingMode`, so this map is an embedding, not a bijection.
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

This is the directed magnitude-up predicate. Rounding toward positive infinity increases the
magnitude of positive results, rounding toward negative infinity that of negative results,
rounding away from zero that of every result, and rounding toward zero never does. The two nearest
modes are not directed and give `false` for both signs. Tininess detection relies on that answer
at the midpoint just below the smallest normal number, which both nearest modes take up to the
normal number.
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

Both nearest modes always do. A directed mode, rounding away from zero included, does so exactly
when it rounds that sign away from zero (IEEE 754-2019 Section 7.4). The native overflow value is
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
Sign that IEEE 754 gives the zero of an exactly cancelling sum whose operands have the signs
`leftSign` and `rightSign`.

IEEE 754-2019 Section 6.3 makes an exact zero sum of operands with opposite signs positive in
every rounding direction except toward negative infinity, where it is negative. A sum of two zeros
with the same sign keeps that sign in every direction. Rounding away from zero follows the rule of
the other directions, as MPFR does: its exact cancellation gives positive zero.

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

/-- The negated mode rounds a result away from zero exactly when this mode rounds its negation. -/
theorem roundsAwayFromZero_negate (mode : IEEERoundingMode) (negative : Bool) :
    mode.negate.roundsAwayFromZero negative = mode.roundsAwayFromZero (!negative) := by
  cases mode <;> cases negative <;> rfl

/-- The negated mode carries an overflow upward exactly when this mode carries its negation. -/
theorem overflowRoundsMagnitudeUp_negate (mode : IEEERoundingMode) (negative : Bool) :
    mode.negate.overflowRoundsMagnitudeUp negative =
      mode.overflowRoundsMagnitudeUp (!negative) := by
  cases mode <;> cases negative <;> rfl

/-- The negated mode treats a magnitude of one sign as this mode treats the opposite sign. -/
theorem magnitudeRounding_negate (mode : IEEERoundingMode) (negative : Bool) :
    mode.negate.magnitudeRounding negative = mode.magnitudeRounding (!negative) := by
  cases mode <;> cases negative <;> rfl

/-- A mode rounds a magnitude up exactly when it moves a result of that sign away from zero. -/
theorem magnitudeRounding_eq_up_iff (mode : IEEERoundingMode) (negative : Bool) :
    mode.magnitudeRounding negative = .up ↔ mode.roundsAwayFromZero negative = true := by
  cases mode <;> cases negative <;> simp [magnitudeRounding, roundsAwayFromZero]

end IEEERoundingMode

end Model
end FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLib.Rounding

/-!
## Bare rounding-mode names

`open FloatLib.Rounding` brings the type `IEEERoundingMode` and its six constructors into scope
without a namespace or a leading dot, so a directed or status operation can name its mode directly
and user code can take a mode as a parameter:

```
open FloatLib.Rounding

Model.sqrt x (mode := up) (status := true)

def third (mode : IEEERoundingMode) : Binary32 := ExecFloat.Binary.div 1 3 (mode := mode)
```

The names are opt-in because they are short words: in a scope that opens this namespace, a
pattern variable spelled `up` or `down` is read as the constructor, so bind such values under
other names, such as `upper` and `lower`. Library code never opens it and writes `.up`.
`Numerics.RoundingMode`, which also has stochastic rounding, has no bare names here.
-/

export FloatLib.Floats.Formats.BinaryInterchange.Model (IEEERoundingMode)

export FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode
  (nearest nearestAway towardZero up down away)

end FloatLib.Rounding
