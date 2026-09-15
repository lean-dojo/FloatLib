/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational

/-!
# Exact accumulation for standard MX dot products

OCP's *Microscaling Formats (MX) Specification*, version 1.0, September 2023, §6.1 leaves
internal precision and operation order implementation-defined. This implementation multiplies
decoded lanes and accumulates in exact rational arithmetic. `dotGeneral` rounds once to IEEE
binary32, after summing every block, as the scalar destination recommended by §6.2.
The two operands may use different concrete element profiles.

Finite values outside binary32 range remain exact until the final rounding, consistently with
the decoding choice permitted by §5.1. No lane product or partial block sum overflows or
underflows. E8M0 exponents are bounded; accumulator growth depends on the number of blocks.

Exceptional arithmetic uses canonical NaN propagation, `0 * infinity = NaN`, signed infinity
products, and `infinity + -infinity = NaN`. The reduction starts at positive zero and uses
increasing lane and block order. Every exact zero sum, including the empty dot, becomes positive
zero; a negative nonzero sum that underflows retains its negative sign. NaN payloads and
floating-point status flags are not returned by this value-only operation.

Reference: §§5.1, 6.1, and 6.2 of
<https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

namespace DotProduct

/-- Exact extended-rational addition with canonical NaN and opposite-infinity cancellation. -/
def add : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => .exceptional .nan
  | .infinity left, .infinity right =>
      if left == right then .infinity left else .exceptional .nan
  | .infinity sign, .finite _ | .finite _, .infinity sign => .infinity sign
  | .finite left, .finite right => .finite (left + right)

/-- Exact products; a finite zero times either infinity is invalid. -/
def mul : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => .exceptional .nan
  | .infinity left, .infinity right => .infinity (left != right)
  | .infinity sign, .finite value | .finite value, .infinity sign =>
      if value = 0 then .exceptional .nan else .infinity (sign != (value < 0))
  | .finite left, .finite right => .finite (left * right)

/-- Ordered exact reduction with a positive-zero identity. -/
def sum (values : List (NumericalValue Rat)) : NumericalValue Rat :=
  values.foldl add (.finite 0)

/-- One software nearest-even projection, with IEEE binary32 overflow and canonical specials. -/
def roundFloat32 : NumericalValue Rat → Model .binary32
  | .finite value =>
      Model.roundRat .binary32 (value.num < 0) value.num.natAbs value.den
  | .infinity sign => if sign then Model.negInf .binary32 else Model.posInf .binary32
  | .exceptional _ => Model.canonicalNaN .binary32

end DotProduct

/-- Exact §6.1 dot of two 32-lane blocks, possibly with different element profiles. -/
def dotExact {leftProfile rightProfile : Profile}
    (left : Block leftProfile) (right : Block rightProfile) : NumericalValue Rat :=
  DotProduct.sum (List.ofFn fun lane : Fin 32 =>
    DotProduct.mul ((left.decodeLane lane).map SignedRat.value)
      ((right.decodeLane lane).map SignedRat.value))

/-- One block dot with a single binary32 destination rounding. -/
def dot {leftProfile rightProfile : Profile}
    (left : Block leftProfile) (right : Block rightProfile) : Model .binary32 :=
  DotProduct.roundFloat32 (dotExact left right)

/-- Exact sum of all block dots; no block result is rounded before this reduction. -/
def dotGeneralExact {leftProfile rightProfile : Profile} {n : Nat}
    (left : Vector (Block leftProfile) n) (right : Vector (Block rightProfile) n) :
    NumericalValue Rat :=
  DotProduct.sum (List.ofFn fun block : Fin n => dotExact left[block.val] right[block.val])

/-- General §6.2 dot, rounded to binary32 once after exact accumulation across all blocks. -/
def dotGeneral {leftProfile rightProfile : Profile} {n : Nat}
    (left : Vector (Block leftProfile) n) (right : Vector (Block rightProfile) n) :
    Model .binary32 :=
  DotProduct.roundFloat32 (dotGeneralExact left right)

end FloatLib.Floats.Formats.OCP.MX.Standard
