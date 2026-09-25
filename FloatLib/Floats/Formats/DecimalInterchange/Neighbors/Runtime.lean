/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime

/-!
# Adjacent decimal values

IEEE 754-2019 §5.3.1 requires the nearest strictly greater or smaller value,
selecting the least quantum in its cohort. Normalizing the input to its finest
grid makes this a coefficient step. At a power of ten, the downward step uses
the finer grid. No rounding direction is consulted.

The adjacency and output-validity guarantees assume `x.Valid f`, as stated in
`Neighbors.Proof` and `Neighbors.Adjacency`. A raw `Datum` does not carry its
format; callers must establish this invariant before using these neighbor
operations. The normalization step need not preserve an out-of-format input.

Crossing the finite range or reaching a subnormal raises no exception. Only
signaling NaNs raise invalid; NaN propagation otherwise follows the arithmetic
payload policy.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- Positive successor of a finite value already on its least quantum. -/
def neighborAbove (f : Format) (c : Nat) (q : Int) : Datum :=
  if c + 1 < f.coefficientBound then .finite false (c + 1) q
  else if q < f.maxQuantum then .finite false f.payloadBound (q + 1)
  else .infinity false

/-- Positive predecessor, using the finer grid immediately below a radix power. -/
def neighborBelow (f : Format) (c : Nat) (q : Int) : Datum :=
  if f.minQuantum < q ∧ c = f.payloadBound then
    .finite false (f.coefficientBound - 1) (q - 1)
  else .finite false (c - 1) q

/-- For a valid non-NaN operand, the least representable value strictly greater than it,
except that positive infinity is unchanged. -/
def nextUp (f : Format) : Datum → Outcome
  | .nan s t p => nanResult f s p t
  | .infinity false => { value := .infinity false }
  | .infinity true => { value := f.maxFinite true }
  | .finite s c q =>
      if c = 0 then { value := .finite false 1 f.minQuantum }
      else
        let pair := roundedPair f .nearestEven false ((c : ℚ) * (10 : ℚ) ^ q)
        { value := if s then (neighborBelow f pair.1 pair.2).negate
            else neighborAbove f pair.1 pair.2 }

/-- For a valid non-NaN operand, the greatest representable value strictly smaller than it,
except that negative infinity is unchanged. -/
def nextDown (f : Format) (x : Datum) : Outcome :=
  let result := nextUp f x.negate
  { value := result.value.negate, status := result.status }

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
