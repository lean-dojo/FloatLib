/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibTests.Arb.Oracle
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Conversion
public import FloatLib.Floats.Formats.BinaryInterchange.Interval

/-!
# Arb comparisons for binary intervals and scalar rounding

The optional Arb/python-flint oracle returns rational bounds. Generic rational rounders convert
them outward to `Model fmt` endpoints.

For scalar rounding, refine the enclosure until both bounds round to the same destination bits
in the requested IEEE mode. If the precision budget is exhausted or an exact boundary prevents
agreement, return an error.

Lean checks parsing and the conversion of rational bounds. The enclosure itself depends on
Arb/python-flint; agreement of its rounded bounds is external evidence, not a kernel proof of the
transcendental result.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Interval

/-- Resource policy for adaptive Arb-backed scalar rounding. -/
structure ArbRoundingConfig where
  /-- Initial Arb working precision in bits. -/
  initialPrecBits : Nat := 200
  /-- Initial decimal digits retained in Arb's exact ball encoding. -/
  initialDigits : Nat := 200
  /-- Maximum number of enclosure refinements. -/
  maxAttempts : Nat := 8
  /-- Multiplicative precision increase after an ambiguous enclosure. -/
  growthFactor : Nat := 2
  deriving Repr, DecidableEq, Inhabited

/-- Decode a finite endpoint exactly, rejecting NaN and infinity before calling Arb. -/
def ensureFinite {fmt : FloatFormat} (x : Model fmt) (label : String) : IO Rat := do
  match Model.toRat? x with
  | some q => pure q
  | none =>
      throw <| IO.userError
        s!"Expected finite Model for {label}, got bits={x.toNatBits}."

/--
Call Arb on the exact rational interval represented by `X`.

This is the only step that crosses the external enclosure trust boundary.
-/
def arbBounds {fmt : FloatFormat} (func : String) (X : Interval fmt)
    (precBits digits : Nat := 200) : IO (Rat × Rat) := do
  let loQ ← ensureFinite X.lo "lo"
  let hiQ ← ensureFinite X.hi "hi"
  if !leB X.lo X.hi then
    throw <| IO.userError
      s!"Expected ordered Model interval, got lo={X.lo.toNatBits}, hi={X.hi.toNatBits}."
  let query : FloatLibTests.Arb.Query :=
    { func
      lo := Rat.toArbString loQ
      hi := Rat.toArbString hiQ
      precBits
      digits }
  let result ← FloatLibTests.Arb.run query
  match result.outputBall.toRatBoundsChecked with
  | .ok bounds => pure bounds
  | .error message =>
      throw <| IO.userError s!"Invalid Arb enclosure: {message}"

/--
Compute an arbitrary-format interval enclosure for a named unary function.

The Arb bounds are exact rationals; their conversion uses `roundRatQDown` and `roundRatQUp`, whose
extended-real enclosure inequalities are proved for every `FloatFormat`.
-/
def arbUnary {fmt : FloatFormat} (func : String) (X : Interval fmt)
    (precBits digits : Nat := 200) : IO (Interval fmt) := do
  let (lower, upper) ← arbBounds func X (precBits := precBits) (digits := digits)
  pure
    { lo := roundRatQDown fmt lower
      hi := roundRatQUp fmt upper }

/--
Round a finite point evaluation of a named Arb function in any IEEE rounding mode.

The oracle precision is increased until both endpoints of its exact rational enclosure round to the
same bit pattern. The function fails rather than guessing when the configured attempts do not
resolve a rounding boundary.
-/
def arbUnaryWithRounding {fmt : FloatFormat} (func : String) (x : Model fmt)
    (mode : IEEERoundingMode) (config : ArbRoundingConfig := {}) : IO (Model fmt) := do
  discard <| ensureFinite x "x"
  let growResource (value : Nat) : Nat :=
    max (value + 1) (value * config.growthFactor)
  let rec loop (remaining precBits digits : Nat) : IO (Model fmt) :=
    match remaining with
    | 0 =>
        throw <| IO.userError
          s!"Arb enclosure for {func} did not stabilize under {repr mode} rounding."
    | Nat.succ remaining => do
        let pointBounds : Interval fmt := point x
        let (lower, upper) ←
          arbBounds func pointBounds (precBits := precBits) (digits := digits)
        let lowerRounded := roundRatQWithRounding fmt mode lower
        let upperRounded := roundRatQWithRounding fmt mode upper
        if lowerRounded.toNatBits == upperRounded.toNatBits then
          pure lowerRounded
        else
          loop remaining (growResource precBits) (growResource digits)
  loop config.maxAttempts config.initialPrecBits config.initialDigits

/-! ## Interval wrappers -/

/-- Arb-backed interval enclosure for `exp`. -/
@[inline] def expArb {fmt : FloatFormat} (X : Interval fmt)
    (precBits digits : Nat := 200) : IO (Interval fmt) :=
  arbUnary "exp" X (precBits := precBits) (digits := digits)

/-- Arb-backed interval enclosure for `log` on its real domain. -/
@[inline] def logArb {fmt : FloatFormat} (X : Interval fmt)
    (precBits digits : Nat := 200) : IO (Interval fmt) :=
  arbUnary "log" X (precBits := precBits) (digits := digits)

/-- Arb-backed interval enclosure for `sinh`. -/
@[inline] def sinhArb {fmt : FloatFormat} (X : Interval fmt)
    (precBits digits : Nat := 200) : IO (Interval fmt) :=
  arbUnary "sinh" X (precBits := precBits) (digits := digits)

/-- Arb-backed interval enclosure for `cosh`. -/
@[inline] def coshArb {fmt : FloatFormat} (X : Interval fmt)
    (precBits digits : Nat := 200) : IO (Interval fmt) :=
  arbUnary "cosh" X (precBits := precBits) (digits := digits)

/-- Arb-backed interval enclosure for `tanh`. -/
@[inline] def tanhArb {fmt : FloatFormat} (X : Interval fmt)
    (precBits digits : Nat := 200) : IO (Interval fmt) :=
  arbUnary "tanh" X (precBits := precBits) (digits := digits)

/-- Arb-backed interval enclosure for `sin`. -/
@[inline] def sinArb {fmt : FloatFormat} (X : Interval fmt)
    (precBits digits : Nat := 200) : IO (Interval fmt) :=
  arbUnary "sin" X (precBits := precBits) (digits := digits)

/-- Arb-backed interval enclosure for `cos`. -/
@[inline] def cosArb {fmt : FloatFormat} (X : Interval fmt)
    (precBits digits : Nat := 200) : IO (Interval fmt) :=
  arbUnary "cos" X (precBits := precBits) (digits := digits)

/-- Arb-backed interval enclosure for `sqrt` on its real domain. -/
@[inline] def sqrtArb {fmt : FloatFormat} (X : Interval fmt)
    (precBits digits : Nat := 200) : IO (Interval fmt) :=
  arbUnary "sqrt" X (precBits := precBits) (digits := digits)

/-- Arb-backed interval enclosure for the logistic sigmoid. -/
@[inline] def sigmoidArb {fmt : FloatFormat} (X : Interval fmt)
    (precBits digits : Nat := 200) : IO (Interval fmt) :=
  arbUnary "sigmoid" X (precBits := precBits) (digits := digits)

/-- Arb-backed arbitrary-format enclosure of π. -/
@[inline] def piArb (fmt : FloatFormat) (precBits digits : Nat := 200) :
    IO (Interval fmt) :=
  arbUnary "pi" (point (posZero fmt)) (precBits := precBits) (digits := digits)

/-! ## Scalar wrappers with explicit rounding mode -/

/-- Arb-backed scalar `exp` with an explicit rounding mode. -/
@[inline] def expArbWithRounding {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode) (config : ArbRoundingConfig := {}) : IO (Model fmt) :=
  arbUnaryWithRounding "exp" x mode config

/-- Arb-backed scalar `log` with an explicit rounding mode. -/
@[inline] def logArbWithRounding {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode) (config : ArbRoundingConfig := {}) : IO (Model fmt) :=
  arbUnaryWithRounding "log" x mode config

/-- Arb-backed scalar `sinh` with an explicit rounding mode. -/
@[inline] def sinhArbWithRounding {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode) (config : ArbRoundingConfig := {}) : IO (Model fmt) :=
  arbUnaryWithRounding "sinh" x mode config

/-- Arb-backed scalar `cosh` with an explicit rounding mode. -/
@[inline] def coshArbWithRounding {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode) (config : ArbRoundingConfig := {}) : IO (Model fmt) :=
  arbUnaryWithRounding "cosh" x mode config

/-- Arb-backed scalar `tanh` with an explicit rounding mode. -/
@[inline] def tanhArbWithRounding {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode) (config : ArbRoundingConfig := {}) : IO (Model fmt) :=
  arbUnaryWithRounding "tanh" x mode config

/-- Arb-backed scalar `sin` with an explicit rounding mode. -/
@[inline] def sinArbWithRounding {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode) (config : ArbRoundingConfig := {}) : IO (Model fmt) :=
  arbUnaryWithRounding "sin" x mode config

/-- Arb-backed scalar `cos` with an explicit rounding mode. -/
@[inline] def cosArbWithRounding {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode) (config : ArbRoundingConfig := {}) : IO (Model fmt) :=
  arbUnaryWithRounding "cos" x mode config

/-- Arb-backed scalar `sqrt` with an explicit rounding mode. -/
@[inline] def sqrtArbWithRounding {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode) (config : ArbRoundingConfig := {}) : IO (Model fmt) :=
  arbUnaryWithRounding "sqrt" x mode config

/-- Arb-backed scalar logistic sigmoid with an explicit rounding mode. -/
@[inline] def sigmoidArbWithRounding {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode) (config : ArbRoundingConfig := {}) : IO (Model fmt) :=
  arbUnaryWithRounding "sigmoid" x mode config

/-- Arb-backed arbitrary-format π with an explicit rounding mode. -/
@[inline] def piArbWithRounding (fmt : FloatFormat) (mode : IEEERoundingMode)
    (config : ArbRoundingConfig := {}) : IO (Model fmt) :=
  arbUnaryWithRounding "pi" (posZero fmt) mode config

end Interval
end Model
end FloatLib.Floats.Formats.BinaryInterchange
