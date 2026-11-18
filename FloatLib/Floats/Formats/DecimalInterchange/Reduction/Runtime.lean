/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime
public import FloatLib.Numerics.Reduction

/-!
# Decimal reductions with one rounding

IEEE 754-2019 §9.4 recommends the reductions `sum`, `dot`, `sumSquare` and `sumAbs` on vectors.
The clause number is the one in the 754 working group's list of changes from 754-2008
(<https://grouper.ieee.org/groups/msc/ANSI_IEEE-Std-754-2019/background/>), and the names and
special cases are those of their C binding, ISO/IEC TS 18661-4 (WG14 draft N1797, 7.12.13a and
F.10.10a): `reduc_sum`, `reduc_sumprod`, `reduc_sumsq` and `reduc_sumabs`, which that document
declares for the decimal types too.

`Arithmetic.sum`, `dot`, `sumSquare` and `sumAbs` are these reductions for every decimal
`Format` and every rounding direction. The standard lets an implementation associate in any
order and evaluate in any wider format. These take the limit of that freedom: the terms are
added as exact rational numbers, and the sum is rounded once by `project`, the rounding of
`Arithmetic.add`. No intermediate result overflows or underflows. The data may be of any
decimal formats, since a `Datum` carries none.

The preferred quantum is the least quantum of the terms (the sum of the two quanta for a
product), as for a chain of additions, and an exact zero sum has the sign that such a chain
gives it: the common sign of the terms, and for terms of both signs `+0`, or `-0` when rounding
toward negative infinity. The empty sum is `+0`.

Special cases (N1797 F.10.10a.1 to F.10.10a.4):

* `sum` and `dot`: a NaN operand gives the first NaN in order, quieted, with `invalid` when an
  operand is a signaling NaN or, for `dot`, when a product has a zero and an infinite factor.
  Without a NaN, such a product and infinite terms of both signs are invalid, and infinite terms
  of one sign give that infinity.
* `sumAbs` and `sumSquare`: an infinite operand gives `+∞` even beside a quiet NaN. A signaling
  NaN gives a quiet NaN and `invalid`, and otherwise a NaN operand gives the first NaN.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

namespace Reduction

/-- One term of an exact sum of decimal data. -/
inductive Term where
  /-- A finite term: its sign, which decides an exact zero sum, its exact value and its quantum. -/
  | finite (negative : Bool) (value : ℚ) (quantum : Int)
  /-- An infinite term with its sign. -/
  | infinity (negative : Bool)
  /-- A NaN operand with its sign, whether it is signaling, and its payload. -/
  | nan (negative signaling : Bool) (payload : Nat)
  /-- The product of a zero and an infinity. -/
  | invalid

namespace Term

/-- The term that a datum is. -/
def ofDatum : Datum → Term
  | .finite s c q => .finite s (Datum.finiteValue s c q) q
  | .infinity s => .infinity s
  | .nan s t p => .nan s t p

/-- The magnitude of a term. A NaN is kept. -/
def abs : Term → Term
  | .finite _ value quantum => .finite false |value| quantum
  | .infinity _ => .infinity false
  | term => term

/--
The exact product of two terms: the left NaN before the right, a zero times an infinity
invalid, and the quantum of a finite product the sum of the quanta.
-/
def mul : Term → Term → Term
  | .nan s t p, .nan _ signaling _ => .nan s (t || signaling) p
  | .nan s t p, _ => .nan s t p
  | _, .nan s t p => .nan s t p
  | .invalid, _ | _, .invalid => .invalid
  | .infinity sx, .infinity sy => .infinity (sx ^^ sy)
  | .infinity sx, .finite sy value _ | .finite sx value _, .infinity sy =>
      if value = 0 then .invalid else .infinity (sx ^^ sy)
  | .finite sx vx qx, .finite sy vy qy => .finite (sx ^^ sy) (vx * vy) (qx + qy)

end Term

/-- The exact sum of the terms consumed so far, and what the exceptional terms need. -/
structure Total where
  /-- Exact sum of the finite terms. -/
  value : ℚ := 0
  /-- Least quantum of the finite terms. -/
  quantum : Option Int := none
  /-- The sign that an exact zero sum of the finite terms has. -/
  negative : Option Bool := none
  /-- Sign of the first infinite term. -/
  infinity : Option Bool := none
  /-- Whether infinite terms of both signs have occurred. -/
  opposite : Bool := false
  /-- Sign and payload of the first NaN term. -/
  nan : Option (Bool × Nat) := none
  /-- Whether a signaling NaN has occurred. -/
  signaling : Bool := false
  /-- Whether a product of a zero and an infinity has occurred. -/
  invalidProduct : Bool := false

namespace Total

/-- Consume one term. -/
def push (mode : RoundingMode) (total : Total) : Term → Total
  | .finite s value quantum =>
      { total with
        value := total.value + value
        quantum := some (total.quantum.elim quantum (min · quantum))
        negative := some (total.negative.elim s (zeroSumSign mode · s)) }
  | .infinity s =>
      match total.infinity with
      | none => { total with infinity := some s }
      | some first => if s = first then total else { total with opposite := true }
  | .nan s t p =>
      { total with nan := total.nan <|> some (s, p), signaling := total.signaling || t }
  | .invalid => { total with invalidProduct := true }

/--
The outcome of a sum: the first NaN, the invalid operation for a product of zero and infinity
or infinities of both signs, the infinity of the infinite terms, and otherwise the exact sum
rounded once.
-/
def deliver (f : Format) (mode : RoundingMode) (total : Total) : Outcome :=
  match total.nan with
  | some (s, p) => nanResult f s p (total.signaling || total.invalidProduct)
  | none =>
      if total.invalidProduct || total.opposite then invalidResult
      else
        match total.infinity with
        | some s => { value := .infinity s }
        | none =>
            project f mode total.value (total.quantum.getD 0) (total.negative.getD false)

/--
The outcome of a sum of magnitudes or of squares: an infinite term gives `+∞` before a quiet
NaN is looked at, and a signaling NaN gives a quiet NaN with `invalid`.
-/
def deliverMagnitude (f : Format) (mode : RoundingMode) (total : Total) : Outcome :=
  if total.signaling then total.deliver f mode
  else
    match total.infinity with
    | some _ => { value := .infinity false }
    | none => total.deliver f mode

end Total

/-- The exact sum of a list of terms. -/
def total (mode : RoundingMode) (terms : List Term) : Total :=
  terms.foldl (Total.push mode) {}

end Reduction

open Reduction in
/--
IEEE 754-2019 §9.4 `sum` (C `reduc_sum`, N1797 7.12.13a.1 and F.10.10a.1): the exact sum of an
array of decimal data, rounded once into `f` in `mode`. A NaN operand gives the first NaN,
infinities of both signs are invalid, infinities of one sign give that infinity, and the empty
sum is `+0`.
-/
def sum (f : Format) (mode : RoundingMode) (values : Array Datum) : Outcome :=
  (total mode (values.toList.map Term.ofDatum)).deliver f mode

open Reduction in
/--
IEEE 754-2019 §9.4 `sumAbs` (C `reduc_sumabs`, N1797 7.12.13a.2 and F.10.10a.2): the exact sum
of the magnitudes of an array of decimal data, rounded once into `f` in `mode`. An infinite
operand gives `+∞` even beside a quiet NaN, a signaling NaN gives a quiet NaN and `invalid`,
and the empty sum is `+0`.
-/
def sumAbs (f : Format) (mode : RoundingMode) (values : Array Datum) : Outcome :=
  (total mode (values.toList.map fun x => (Term.ofDatum x).abs)).deliverMagnitude f mode

open Reduction in
/--
IEEE 754-2019 §9.4 `sumSquare` (C `reduc_sumsq`, N1797 7.12.13a.3 and F.10.10a.3): the exact sum
of the squares of an array of decimal data, rounded once into `f` in `mode`. An infinite operand
gives `+∞` even beside a quiet NaN, a signaling NaN gives a quiet NaN and `invalid`, and the
empty sum is `+0`.
-/
def sumSquare (f : Format) (mode : RoundingMode) (values : Array Datum) : Outcome :=
  (total mode (values.toList.map fun x => (Term.ofDatum x).mul (Term.ofDatum x))).deliverMagnitude
    f mode

open Reduction in
/--
IEEE 754-2019 §9.4 `dot` (C `reduc_sumprod`, N1797 7.12.13a.4 and F.10.10a.4): the exact sum of
the products of two arrays of decimal data, rounded once into `f` in `mode`. A NaN operand gives
the first NaN, a product of a zero and an infinity and infinite products of both signs are
invalid, and infinite products of one sign give that infinity. Arrays of different lengths are
rejected.
-/
def dot (f : Format) (mode : RoundingMode) (left right : Array Datum) :
    Except Numerics.ReductionError Outcome :=
  if left.size = right.size then
    .ok ((total mode (List.zipWith (fun x y => (Term.ofDatum x).mul (Term.ofDatum y))
      left.toList right.toList)).deliver f mode)
  else .error (.lengthMismatch left.size right.size)

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
