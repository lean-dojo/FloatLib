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

OCP's *Microscaling Formats (MX) Specification*, version 1.0, September 2023, §6.1 leaves the
internal precision and the order of operations to the implementation. We multiply decoded lanes
and accumulate in exact rational arithmetic, and `dotGeneral` rounds once to IEEE binary32 after
summing every block, as the scalar destination recommended by §6.2. The two operands may use
different concrete element profiles.

Finite values outside the binary32 range stay exact until that final rounding, which matches the
decoding choice §5.1 permits. So no lane product or partial block sum ever overflows or underflows.
E8M0 exponents are bounded, and the accumulator grows with the number of blocks.

The rest comes down to a few rules:

* NaN propagates canonically.
* `0 * infinity = NaN`, and infinity products are signed.
* `infinity + -infinity = NaN`.
* The reduction starts at positive zero and runs in increasing lane and block order.
* Every exact zero sum, including the empty dot, is positive zero.
* A negative nonzero sum that underflows keeps its negative sign.

This operation returns values only, so it reports no NaN payloads and no floating-point status
flags.

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

/-- Exact products, where a finite zero times either infinity is invalid. -/
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

/-- Exact sum of all block dots. No block result is rounded before this reduction. -/
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
