/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.DirectedRuntime
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Core
public import FloatLib.Numerics.Enclosure.Rational.Runtime

/-!
# The parts of a complex result before rounding

A correctly rounded complex function rounds each part of the exact result once. `Part` is one
part before that rounding: an encoding to deliver as it is (the NaNs, infinities and zeros of the
special cases in C23, Annex G), or a real number given by its exact comparison with every
rational. `Part.round` rounds it in any `IEEERoundingMode` with `AlgebraicRounding.roundSigned`.

The symmetries that C23 G.6 uses to state the functions act on parts before rounding, so they are
exact in every rounding direction: negation flips a sign and mirrors a comparison.
`Parts.ofUpperHalf` extends a function given where the imaginary sign bit is clear by
`f (conj z) = conj (f z)`, `Parts.ofQuadrant` adds the parity `f (-z) = ± f z`, and
`Parts.mulNegI` is the multiplication by `-i` in `casin z = -i casinh (i z)`. The sign of a zero
part selects the side of a branch cut this way (C23 7.3.3).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

/-- One part of a complex result before it is rounded. -/
inductive Part (fmt : FloatFormat) where
  /-- An encoding delivered as it is: a NaN, an infinity or a zero of a special case. -/
  | exact (value : Model fmt)
  /--
  A real number given by its exact comparison with every rational. A real equal to zero is
  delivered as the zero with the sign `zeroSign`.
  -/
  | real (compare : Rat → Ordering) (zeroSign : Bool)

namespace Part

variable {fmt : FloatFormat}

/--
Negate a part before rounding. An encoding flips its sign bit, and a real mirrors its
comparisons and the sign of its zero.
-/
def neg : Part fmt → Part fmt
  | .exact value => .exact (Model.neg value)
  | .real compare zeroSign => .real (fun boundary => (compare (-boundary)).swap) (!zeroSign)

/-- Round a part once, in the direction `mode`. An encoding is delivered unchanged. -/
def round (mode : Model.IEEERoundingMode) : Part fmt → Model fmt
  | .exact value => value
  | .real compare zeroSign => Model.AlgebraicRounding.roundSigned fmt mode compare zeroSign

end Part

/--
Decide a comparison with a boundary outside a rational enclosure of the real at once, and one
inside it by the exact comparator. A tight enclosure, computed once, answers almost every
comparison of a rounding search.
-/
def compareWithin (enclosure : Option Numerics.RationalInterval) (exact : Rat → Ordering)
    (boundary : Rat) : Ordering :=
  match enclosure with
  | some interval =>
      if boundary < interval.lo then .gt
      else if interval.hi < boundary then .lt
      else exact boundary
  | none => exact boundary

/-- Give a real part an enclosure that settles the comparisons outside it. -/
def Part.within {fmt : FloatFormat} (enclosure : Option Numerics.RationalInterval) :
    Part fmt → Part fmt
  | .real compare zeroSign => .real (compareWithin enclosure compare) zeroSign
  | part => part

/--
Whether an enclosure determines the rounding of its real in `fmt` unless the real is within
`2 ^ -(precision + 11)` of a rounding boundary, relatively: it excludes zero and is that narrow.
-/
def isTight (fmt : FloatFormat) (interval : Numerics.RationalInterval) : Bool :=
  (decide (0 < interval.lo) || decide (interval.hi < 0)) &&
    decide ((interval.hi - interval.lo) * 2 ^ (fmt.fracWidth + 12) ≤
      min |interval.lo| |interval.hi|)

/--
An enclosure at the working precision of `fmt`, or at four times that precision when the first
one is not tight, as for a result that cancels. Every returned enclosure is sound when `enclose`
is, and none of them is needed for correctness.
-/
def refineTwice (fmt : FloatFormat) (enclose : Nat → Option Numerics.RationalInterval) :
    Option Numerics.RationalInterval :=
  let precision := fmt.fracWidth + 28
  match enclose precision with
  | some interval =>
      if isTight fmt interval then some interval
      else
        match enclose (4 * precision + 64) with
        | some refined => some refined
        | none => some interval
  | none => enclose (4 * precision + 64)

/-- The real and imaginary parts of a complex result before rounding. -/
structure Parts (fmt : FloatFormat) where
  /-- Real part. -/
  re : Part fmt
  /-- Imaginary part. -/
  im : Part fmt

namespace Parts

variable {fmt : FloatFormat}

/-- Round each part once, in the direction `mode`. -/
def round (mode : Model.IEEERoundingMode) (w : Parts fmt) : ExecComplex fmt :=
  ⟨w.re.round mode, w.im.round mode⟩

/-- Conjugate before rounding. -/
def conj (w : Parts fmt) : Parts fmt := ⟨w.re, w.im.neg⟩

/-- Multiply by `-i` before rounding: `-i (u + i v) = v - i u`. -/
def mulNegI (w : Parts fmt) : Parts fmt := ⟨w.im, w.re.neg⟩

/--
Extend `core`, given where the imaginary sign bit is clear, to every input by
`f (conj z) = conj (f z)`.
-/
def ofUpperHalf (core : ExecComplex fmt → Parts fmt) (z : ExecComplex fmt) : Parts fmt :=
  if Model.signBit z.im then (core (ExecComplex.conj z)).conj else core z

/--
Extend `core`, given where both sign bits are clear, to every input by
`f (conj z) = conj (f z)` and the parity `f (-z) = -f z` (`odd`) or `f (-z) = f z`.

Negating the real part of the argument negates the real part of an odd function and the
imaginary part of an even one.
-/
def ofQuadrant (odd : Bool) (core : ExecComplex fmt → Parts fmt) : ExecComplex fmt → Parts fmt :=
  ofUpperHalf fun z =>
    if Model.signBit z.re then
      let w := core ⟨Model.neg z.re, z.im⟩
      if odd then ⟨w.re.neg, w.im⟩ else w.conj
    else core z

end Parts

/-- `i z`, exactly: the parts exchange and one sign flips. -/
def mulI {fmt : FloatFormat} (z : ExecComplex fmt) : ExecComplex fmt :=
  ⟨Model.neg z.im, z.re⟩

/--
The NaN that a special case propagates: the first NaN part of the argument, quieted, or the
invalid result of the format when neither part is a NaN.
-/
def propagatedNaN {fmt : FloatFormat} (z : ExecComplex fmt) : Model fmt :=
  if Model.isNaN z.re then Model.quietNaN z.re
  else if Model.isNaN z.im then Model.quietNaN z.im
  else Model.invalidResult fmt

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
