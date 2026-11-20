/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Runtime

/-!
# Scaled products

IEEE 754-2019 §9.4 recommends three reductions that deliver a product together with a scale
factor, so that a long product neither overflows nor underflows on the way: `scaledProd`,
`scaledProdSum` and `scaledProdDiff`. The clause number is the one in the 754 working group's
list of changes from 754-2008
(<https://grouper.ieee.org/groups/msc/ANSI_IEEE-Std-754-2019/background/>), and the operation
names, results and special cases are those of their C binding, ISO/IEC TS 18661-4 (WG14 draft
N1797, 7.12.13a.5 to 7.12.13a.7 and F.10.10a.5 to F.10.10a.7): `scaled_prod`, `scaled_prodsum`
and `scaled_proddiff` compute a scaled product `pr` and a scale factor `sf` with
`pr × 2 ^ sf = ∏ pᵢ`, `∏ (pᵢ + qᵢ)` or `∏ (pᵢ - qᵢ)`.

The standard leaves the order of association, the width of intermediate results and the choice
of the scale factor to the implementation. Here every finite factor is formed without error (a
sum or a difference of two operands is exact in the dyadic domain), the factors are multiplied
without error, and the product is rounded once. The scale factor is the exponent of the leading
bit of the exact product, so the magnitude of `pr` lies in `[1, 2]`, where the format has its
full precision, and `2` only through a rounding carry.

Special cases (N1797 F.10.10a.5 to F.10.10a.7), with scale factor zero:

* a NaN operand gives a quiet NaN, the first signaling one before the first quiet one, and a
  signaling NaN raises `invalid`;
* a sum of two infinities of opposite signs, a difference of two infinities of one sign, and a
  zero factor beside an infinite one raise `invalid` and give a NaN;
* otherwise an infinite factor gives an infinity and a zero factor a zero, each with the product
  of the signs of all factors;
* the empty product is `1` with scale factor zero.

No operation raises `overflow`, `underflow` or `divideByZero`. `inexact` reports the one
rounding. The scale factor is an unbounded integer, so it is never out of range.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange

/--
A scaled product `product × β ^ scaleFactor` in the radix `β` of the carrier, with the
exceptions raised in computing it. The carrier `α` is `Model fmt` for the binary descriptor
model, a configured type for stored binary values, and a decimal `Datum`, whose radix is ten.
-/
structure ScaledProduct (α : Type) where
  /-- The scaled product, `pr` in the standard: magnitude in `[1, β]` for a finite nonzero
  product. -/
  product : α
  /-- The scale factor, `sf` in the standard: zero for a zero, an infinity and a NaN. -/
  scaleFactor : Int
  /-- Exceptions raised by the reduction. -/
  status : Numerics.IEEEStatus := {}
  deriving DecidableEq

/-- Carry the product through a conversion of the carrier. Scale factor and flags are kept. -/
def ScaledProduct.map {α β : Type} (convert : α → β) (outcome : ScaledProduct α) :
    ScaledProduct β :=
  { product := convert outcome.product, scaleFactor := outcome.scaleFactor
    status := outcome.status }

namespace Model
namespace Reduction.Internal

/-- One factor of a scaled product, formed without error. -/
inductive Factor (destination : FloatFormat) where
  /-- A finite factor, a zero with its sign included. -/
  | finite (value : Numerics.Dyadic)
  /-- An infinite factor with its sign. -/
  | infinity (negative : Bool)
  /-- A NaN operand, quieted and converted into the destination format. -/
  | nan (value : Model destination) (signaling : Bool)
  /-- A sum of two infinities of opposite signs. -/
  | invalid

/-- The factor that one operand is. -/
def Factor.ofValue {destination source : FloatFormat} (value : Model source) :
    Factor destination :=
  match toDyadic? value with
  | some exact => .finite exact
  | none =>
      if isNaN value then
        .nan (cast source destination (quietNaN value)) (isSignaling value)
      else
        .infinity (signBit value)

/--
The exact sum of two factors: a signaling NaN before a quiet one and the left before the right,
infinities of opposite signs invalid, and a zero sum negative only when both terms are.
-/
def Factor.add {destination : FloatFormat} : Factor destination → Factor destination →
    Factor destination
  | .invalid, _ | _, .invalid => .invalid
  | .nan left true, _ => .nan left true
  | .nan left false, .nan right signaling => if signaling then .nan right true else .nan left false
  | .nan left false, _ => .nan left false
  | _, .nan right signaling => .nan right signaling
  | .infinity left, .infinity right => if left == right then .infinity left else .invalid
  | .infinity negative, .finite _ | .finite _, .infinity negative => .infinity negative
  | .finite left, .finite right => .finite (addDyadic left right)

/--
Accumulator of a scaled product: the exact product of the finite factors, and what the
exceptional factors need for the result to be resolved after the traversal.
-/
structure ProductState (destination : FloatFormat) where
  /-- Exact product of the finite factors consumed so far. A zero factor makes it a zero with
  the product of the signs. -/
  exact : Numerics.Dyadic := { negative := false, significand := 1, exponent := 0 }
  /-- Whether an infinite factor has occurred. -/
  sawInfinity : Bool := false
  /-- Product of the signs of the infinite factors. -/
  infinityNegative : Bool := false
  /-- First signaling NaN in traversal order, quieted into the destination format. -/
  signalingNaN : Option (Model destination) := none
  /-- First quiet NaN in traversal order, converted into the destination format. -/
  quietNaN : Option (Model destination) := none
  /-- Whether a factor was a sum of infinities of opposite signs. -/
  generatedInvalid : Bool := false

/-- Consume one factor. -/
def ProductState.push {destination : FloatFormat} (state : ProductState destination) :
    Factor destination → ProductState destination
  | .finite value => { state with exact := Numerics.Dyadic.mul state.exact value }
  | .infinity negative =>
      { state with
        sawInfinity := true
        infinityNegative := Bool.xor state.infinityNegative negative }
  | .nan value true =>
      match state.signalingNaN with
      | some _ => state
      | none => { state with signalingNaN := some value }
  | .nan value false =>
      match state.quietNaN with
      | some _ => state
      | none => { state with quietNaN := some value }
  | .invalid => { state with generatedInvalid := true }

/--
Resolve the exceptional factors, or scale the exact product by the exponent of its leading bit
and round it once in `mode`.
-/
def ProductState.finish {destination : FloatFormat} (state : ProductState destination)
    (mode : IEEERoundingMode) : ScaledProduct (Model destination) :=
  let invalid := state.generatedInvalid ||
    (state.sawInfinity && state.exact.significand == 0)
  match state.signalingNaN with
  | some value => { product := value, scaleFactor := 0, status := { invalid := true } }
  | none =>
      match state.quietNaN with
      | some value => { product := value, scaleFactor := 0, status := { invalid } }
      | none =>
          if invalid then
            { product := invalidResult destination, scaleFactor := 0
              status := { invalid := true } }
          else if state.sawInfinity then
            let value :=
              nativeOverflow destination (Bool.xor state.infinityNegative state.exact.negative)
            { product := value, scaleFactor := 0
              status := if isInfinite value then .clear else { overflow := true, inexact := true } }
          else if state.exact.significand == 0 then
            { product := zero destination state.exact.negative, scaleFactor := 0 }
          else
            let scaled : Numerics.Dyadic :=
              { state.exact with exponent := -(state.exact.significand.log2 : Int) }
            let product := Internal.Directed.roundDyadic destination mode scaled
            { product
              scaleFactor := (state.exact.significand.log2 : Int) + state.exact.exponent
              status :=
                { inexact := (dyadicRoundingStatus destination mode scaled product).inexact } }

end Reduction.Internal

/--
IEEE 754-2019 §9.4 `scaledProd` (C `scaled_prod`, N1797 7.12.13a.5 and F.10.10a.5): a scaled
product `pr` and a scale factor `sf` with `pr × 2 ^ sf = ∏ values`, the product formed without
error and rounded once into `destination` in `mode` (nearest-even by default). See the module
documentation for the scale factor and the special cases.
-/
def scaledProd (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode := .nearest) :
    ScaledProduct (Model destination) :=
  (values.foldl (fun state value => state.push (Reduction.Internal.Factor.ofValue value))
    ({} : Reduction.Internal.ProductState destination)).finish mode

/--
The scaled product of the sums (`subtract := false`) or differences (`subtract := true`) of the
corresponding members of two arrays, the kernel of `scaledProdSum` and `scaledProdDiff`. Unequal
lengths are rejected before any arithmetic occurs.
-/
def Reduction.Internal.scaledProdOfSums (destination : FloatFormat)
    {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat)) (subtract : Bool)
    (mode : IEEERoundingMode) :
    Except Numerics.ReductionError (ScaledProduct (Model destination)) :=
  if left.size = right.size then
    .ok <| ((left.zip right).foldl
      (fun state pair =>
        state.push
          (Factor.add (Factor.ofValue pair.1)
            (Factor.ofValue (if subtract then neg pair.2 else pair.2))))
      ({} : ProductState destination)).finish mode
  else
    .error (.lengthMismatch left.size right.size)

/--
IEEE 754-2019 §9.4 `scaledProdSum` (C `scaled_prodsum`, N1797 7.12.13a.6 and F.10.10a.6): a
scaled product `pr` and a scale factor `sf` with `pr × 2 ^ sf = ∏ (leftᵢ + rightᵢ)`, each sum and
the product formed without error and the product rounded once into `destination` in `mode`
(nearest-even by default). Unequal lengths are an error.
-/
def scaledProdSum (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode := .nearest) :
    Except Numerics.ReductionError (ScaledProduct (Model destination)) :=
  Reduction.Internal.scaledProdOfSums destination left right false mode

/--
IEEE 754-2019 §9.4 `scaledProdDiff` (C `scaled_proddiff`, N1797 7.12.13a.7 and F.10.10a.7): a
scaled product `pr` and a scale factor `sf` with `pr × 2 ^ sf = ∏ (leftᵢ - rightᵢ)`, each
difference and the product formed without error and the product rounded once into `destination`
in `mode` (nearest-even by default). Unequal lengths are an error.
-/
def scaledProdDiff (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode := .nearest) :
    Except Numerics.ReductionError (ScaledProduct (Model destination)) :=
  Reduction.Internal.scaledProdOfSums destination left right true mode

end Model
end FloatLib.Floats.Formats.BinaryInterchange
