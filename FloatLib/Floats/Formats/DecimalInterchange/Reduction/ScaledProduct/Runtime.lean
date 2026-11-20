/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Reduction.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.ScaledProduct.Runtime
public import Mathlib.Data.Int.Log

/-!
# Decimal scaled products

IEEE 754-2019 §9.4 recommends three reductions that deliver a product together with a scale
factor, so that a long product neither overflows nor underflows on the way: `scaledProd`,
`scaledProdSum` and `scaledProdDiff`. The clause number is the one in the 754 working group's
list of changes from 754-2008
(<https://grouper.ieee.org/groups/msc/ANSI_IEEE-Std-754-2019/background/>), and the names,
results and special cases are those of their C binding, ISO/IEC TS 18661-4 (WG14 draft N1797,
7.12.13a.5 to 7.12.13a.7 and F.10.10a.5 to F.10.10a.7), which declares `scaled_prod`,
`scaled_prodsum` and `scaled_proddiff` for the decimal types too.

`Arithmetic.scaledProd`, `scaledProdSum` and `scaledProdDiff` are these reductions for every
decimal `Format` and every rounding direction. They compute a scale factor `sf` and a scaled
product `pr`, the rounding of `P / 10 ^ sf` into the format, where `P` is `∏ pᵢ`,
`∏ (pᵢ + qᵢ)` or `∏ (pᵢ - qᵢ)`. So `pr × 10 ^ sf = P` when that rounding is exact. Every factor
is formed without error (a sum or a difference of two operands is an exact rational number),
the factors are multiplied without error, and the product is rounded once by `project`, the
rounding of
`Arithmetic.mul`. The scale factor is the decimal exponent of the leading digit of the exact
product, so the exact scaled product has a magnitude in `[1, 10)`, where a format has its full
precision. The data may be of any decimal formats, since a `Datum` carries none.

The preferred quantum of `pr` is the sum of the quanta of the factors less the scale factor,
so an exact `pr × 10 ^ sf` is the member of its cohort that a chain of multiplications selects.
A factor that is a sum has the smaller of the two quanta, and an exact zero sum the sign that
`Arithmetic.add` gives it.

Special cases (N1797 F.10.10a.5 to F.10.10a.7), with scale factor zero:

* a NaN operand gives the first NaN in order, quieted, with `invalid` when an operand is a
  signaling NaN or the factors without the NaNs are invalid;
* a sum of two infinities of opposite signs, a difference of two infinities of one sign, and a
  zero factor beside an infinite one raise `invalid` and give a NaN;
* otherwise an infinite factor gives an infinity and a zero factor a zero, each with the product
  of the signs of all factors, the zero with the sum of the quanta as its preferred quantum;
* the empty product is `1` with scale factor zero.

`Reduction.ScaledProduct.Proof` proves that the result is one rounding of the exact scaled
product, and that a format that holds the decade from one to ten in its normal range raises
neither `overflow` nor `underflow`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

open BinaryInterchange (ScaledProduct)

namespace Reduction

namespace Term

/-- The opposite of a term. A NaN is kept. -/
def neg : Term → Term
  | .finite negative value quantum => .finite (!negative) (-value) quantum
  | .infinity negative => .infinity (!negative)
  | term => term

/--
The exact sum of two terms: the left NaN before the right, infinities of opposite signs
invalid, the quantum of a finite sum the smaller of the two quanta, and the sign of an exact
zero sum that of `Arithmetic.add` in the direction `mode`.
-/
def add (mode : RoundingMode) : Term → Term → Term
  | .nan s t p, .nan _ signaling _ => .nan s (t || signaling) p
  | .nan s t p, _ => .nan s t p
  | _, .nan s t p => .nan s t p
  | .invalid, _ | _, .invalid => .invalid
  | .infinity sx, .infinity sy => if sx = sy then .infinity sx else .invalid
  | .infinity s, .finite .. | .finite .., .infinity s => .infinity s
  | .finite sx vx qx, .finite sy vy qy =>
      .finite (if vx + vy = 0 then zeroSumSign mode sx sy else decide (vx + vy < 0)) (vx + vy)
        (min qx qy)

end Term

/-- The exact product of the factors consumed so far, and what the exceptional factors need. -/
structure Product where
  /-- Exact product of the finite factors. -/
  value : ℚ := 1
  /-- Sum of the quanta of the finite factors. -/
  quantum : Int := 0
  /-- Product of the signs of the finite and the infinite factors. -/
  negative : Bool := false
  /-- Whether an infinite factor has occurred. -/
  infinite : Bool := false
  /-- Sign and payload of the first NaN factor. -/
  nan : Option (Bool × Nat) := none
  /-- Whether a signaling NaN has occurred. -/
  signaling : Bool := false
  /-- Whether a factor was a sum of infinities of opposite signs. -/
  invalid : Bool := false

/-- A decimal outcome as a scaled product with the scale factor `scaleFactor`. -/
def scaled (outcome : Outcome) (scaleFactor : Int := 0) : ScaledProduct Datum :=
  { product := outcome.value, scaleFactor, status := outcome.status }

namespace Product

/-- Consume one factor. -/
def push (product : Product) : Term → Product
  | .finite s value quantum =>
      { product with
        value := product.value * value
        quantum := product.quantum + quantum
        negative := product.negative ^^ s }
  | .infinity s => { product with infinite := true, negative := product.negative ^^ s }
  | .nan s t p =>
      { product with nan := product.nan <|> some (s, p), signaling := product.signaling || t }
  | .invalid => { product with invalid := true }

/--
The outcome of a scaled product: the first NaN, the invalid operation for an invalid factor or
a zero beside an infinity, the infinity or the zero with the product of the signs, and
otherwise the exact product scaled by the power of ten of its leading digit and rounded once.
-/
def deliver (f : Format) (mode : RoundingMode) (product : Product) : ScaledProduct Datum :=
  let invalid := product.invalid || (product.infinite && decide (product.value = 0))
  match product.nan with
  | some (s, p) => scaled (nanResult f s p (product.signaling || invalid))
  | none =>
      if invalid then scaled invalidResult
      else if product.infinite then scaled { value := .infinity product.negative }
      else if product.value = 0 then
        scaled (project f mode 0 product.quantum product.negative)
      else
        let scale := Int.log 10 |product.value|
        scaled (project f mode (product.value / (10 : ℚ) ^ scale) (product.quantum - scale))
          scale

end Product

/-- The exact product of a list of factors. -/
def product (factors : List Term) : Product :=
  factors.foldl Product.push {}

end Reduction

open Reduction in
/--
IEEE 754-2019 §9.4 `scaledProd` (C `scaled_prod`, N1797 7.12.13a.5 and F.10.10a.5): a scale
factor `sf` and a scaled product `pr`, the rounding of `(∏ values) / 10 ^ sf` into `f` in
`mode`. The product is formed without error and rounded once, and `pr × 10 ^ sf = ∏ values`
when that rounding is exact. See the module documentation for the scale factor, the preferred
quantum and the special cases.
-/
def scaledProd (f : Format) (mode : RoundingMode) (values : Array Datum) :
    ScaledProduct Datum :=
  (product (values.toList.map Term.ofDatum)).deliver f mode

open Reduction in
/--
IEEE 754-2019 §9.4 `scaledProdSum` (C `scaled_prodsum`, N1797 7.12.13a.6 and F.10.10a.6): a
scale factor `sf` and a scaled product `pr`, the rounding of `(∏ (leftᵢ + rightᵢ)) / 10 ^ sf`
into `f` in `mode`. Each sum and the product are formed without error and the product is
rounded once, and `pr × 10 ^ sf` is the product when that rounding is exact. Arrays of
different lengths are rejected.
-/
def scaledProdSum (f : Format) (mode : RoundingMode) (left right : Array Datum) :
    Except Numerics.ReductionError (ScaledProduct Datum) :=
  if left.size = right.size then
    .ok ((product (List.zipWith (fun x y => (Term.ofDatum x).add mode (Term.ofDatum y))
      left.toList right.toList)).deliver f mode)
  else .error (.lengthMismatch left.size right.size)

open Reduction in
/--
IEEE 754-2019 §9.4 `scaledProdDiff` (C `scaled_proddiff`, N1797 7.12.13a.7 and F.10.10a.7): a
scale factor `sf` and a scaled product `pr`, the rounding of `(∏ (leftᵢ - rightᵢ)) / 10 ^ sf`
into `f` in `mode`. Each difference and the product are formed without error and the product
is rounded once, and `pr × 10 ^ sf` is the product when that rounding is exact. Arrays of
different lengths are rejected.
-/
def scaledProdDiff (f : Format) (mode : RoundingMode) (left right : Array Datum) :
    Except Numerics.ReductionError (ScaledProduct Datum) :=
  if left.size = right.size then
    .ok ((product (List.zipWith (fun x y => (Term.ofDatum x).add mode (Term.ofDatum y).neg)
      left.toList right.toList)).deliver f mode)
  else .error (.lengthMismatch left.size right.size)

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
