/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Configured.Proof
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Views
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.Posit.Quire.Capacity
public import FloatLib.Floats.Formats.Posit.Quire.Accumulation
public meta import FloatLib.Floats.Formats.Posit.Quire.Info
public import FloatLib.Numerics.Reduction
public import FloatLib.Floats.Formats.Posit.Configured.Instances

/-!
# Exact dot products with a posit quire

How do we compute a dot product of posits without rounding each product? A quire is a wide
fixed-point accumulator paired with a posit format. The calculation has three steps: start at
zero, accumulate with `qMulAdd`, and round once with `qToP`. The reusable `dotProduct` below also
checks the input lengths, and the theorem at the end says when the accumulation is exact.

A quire paired with an `n`-bit posit has a `16n`-bit coefficient, 512 bits for Posit32. Overflow
or a NaR input produces NaR ("not a real"). The Posit Standard sizes the quire so that fewer than
`2^31` products of finite posits can never overflow, and `toRat?_accumulateProducts` applies the
library's proof of that guarantee to this loop. The correctly rounded binary reduction in
`BasicOperations` instead uses an unbounded software accumulator.
-/

@[expose] public section

namespace FloatLib.Examples.PositQuire

open FloatLib.Floats

/-- The input and output format for this example. -/
abbrev Posit32 :=
  ExecFloat.Posit (bits := 32)

/-- The exact accumulator paired with `Posit32`. -/
abbrev Quire32 :=
  ExecFloat.Posit.Quire (bits := 32)

/-- Accumulate the products in order, starting from the zero quire. -/
def accumulateProducts (pairs : List (Posit32 × Posit32)) : Quire32 :=
  -- qMulAdd forms the product in the quire. Multiplying two Posit32 values first would round it.
  pairs.foldl
    (fun quire (left, right) => ExecFloat.Posit.Quire.qMulAdd quire left right)
    ExecFloat.Posit.Quire.zero

/--
Compute a dot product and round once after accumulation. Unequal lengths return an error;
quire overflow and NaR operands produce a successful result whose posit value is NaR.
-/
def dotProduct (xs ys : List Posit32) :
    Except Numerics.ReductionError Posit32 :=
  if xs.length = ys.length then
    -- List.zip stops at the shorter list, so the length check must precede it.
    let accumulator := accumulateProducts (xs.zip ys)
    .ok (ExecFloat.Posit.Quire.qToP accumulator)
  else
    .error (.lengthMismatch xs.length ys.length)

/-! ## Check a small calculation and its failure case -/

private def left : List Posit32 :=
  [1.5, 2, -1]

private def right : List Posit32 :=
  [2, 0.5, 4]

private def result : Except Numerics.ReductionError Posit32 :=
  dotProduct left right
-- Except.ok 0

private def exactResult :
    Except Numerics.ReductionError (Option Rat) :=
  result.map ExecFloat.Posit.toRat?
-- Except.ok (some 0)

private def exactAccumulator : Option Rat :=
  ExecFloat.Posit.Quire.toRat? <| accumulateProducts (left.zip right)
-- some 0

/-
`1.5 * 2 + 2 * 0.5 - 1 * 4 = 3 + 1 - 4 = 0`. The products and partial sums were never rounded, and
the final `qToP` rounds an exact zero, which is still zero. `toRat?` on the quire returns `none`
only for NaR, so `some 0` confirms that the accumulator stayed finite.
-/

private def mismatchedResult : Except Numerics.ReductionError Posit32 :=
  dotProduct left [2, 0.5]
-- Except.error (ReductionError.lengthMismatch 3 2)

/-! ## Use the quire's semantic theorems -/

/-
Moving one posit into its quire preserves its exact meaning, including the NaR case. This is the
first lemma we reach for before reasoning about a longer accumulation.
-/
example (value : Posit32) :
    ExecFloat.Posit.Quire.toRat? (ExecFloat.Posit.Quire.pToQ value) =
      ExecFloat.Posit.toRat? value :=
  ExecFloat.Posit.Quire.toRat?_pToQ value

/--
`accumulateProducts` is exact for fewer than `2^31` pairs of finite inputs.

`exactProducts? pairs = some products` says no input is NaR and names the exact rational products.
The conclusion says the accumulator is not NaR and denotes their sum, so `dotProduct` then rounds
the mathematically exact dot product once.
-/
theorem toRat?_accumulateProducts
    (pairs : List (Posit32 × Posit32)) (products : List Rat)
    (hproducts : ExecFloat.Posit.Quire.exactProducts? pairs = some products)
    (hlength : pairs.length < 2 ^ 31) :
    ExecFloat.Posit.Quire.toRat? (accumulateProducts pairs) = some products.sum :=
  ExecFloat.Posit.Quire.toRat?_foldl_qMulAdd_zero pairs products hproducts hlength

end FloatLib.Examples.PositQuire
