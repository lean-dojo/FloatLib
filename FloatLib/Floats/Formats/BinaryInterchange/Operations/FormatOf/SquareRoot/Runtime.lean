/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Comparison.Runtime
public import FloatLib.Floats.Formats.Posit.Algebraic.Root.Runtime

/-!
# The square root with operand and result in different formats

`formatOfSquareRoot` is the formatOf square root of IEEE 754-2019 §5.4.1: the operand may have
any binary format, and the root of its exact value is rounded once into the destination
format, in every rounding direction, with the flags and the ternary value of that rounding. A
square root of a `binary64` value rounded into `binary32` this way has no double rounding,
unlike `cast` after `sqrt`.

The root of a positive operand is located by exact comparisons of squares
(`RootRounding.compareRoot`) and rounded by `ComparisonRounding.deliver`. The special cases
are those of `Model.sqrt`: a zero gives the zero of the operand's sign, a negative nonzero
operand and `-∞` are invalid, `+∞` gives `+∞`, and a NaN gives that NaN quieted and converted
into the destination, with `invalid` when it was signaling.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Reduction.Internal (Factor)

/--
IEEE 754-2019 §5.4.1 formatOf-squareRoot: the square root of the exact value of an operand of
any format, rounded once into `destination` in `mode` (nearest-even by default), with the flags
and the ternary value of that rounding. See the module documentation for the special cases.
-/
def formatOfSquareRoot (destination : FloatFormat) {source : FloatFormat} (x : Model source)
    (mode : IEEERoundingMode := .nearest) : IEEEOutcome destination :=
  match (Factor.ofValue x : Factor destination) with
  | .finite exact =>
      if exact.significand == 0 then
        { value := zero destination (signBit x), status := .clear, ternary := .eq }
      else if exact.negative then outcomeWithInvalid (invalidResult destination) true
      else
        ComparisonRounding.deliver destination
          (Posit.Model.RootRounding.compareRoot exact.toRat 2) mode
  | .infinity negative =>
      if negative then outcomeWithInvalid (invalidResult destination) true
      else (Factor.infinity false).deliver mode false
  | factor => factor.deliver mode false

end Model
end FloatLib.Floats.Formats.BinaryInterchange
