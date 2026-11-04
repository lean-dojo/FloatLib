/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
public import Mathlib.Order.Prod.Lex.Basic
public import FloatLib.Numerics.Exact.Dyadic.Comparison.Runtime

/-!
# IEEE binary total ordering

`Model.totalOrder` orders complete exact values, so zero signs and NaN metadata take part. Finite
values go through the shared exponent-scalable exact dyadic comparator, while the specification
compares their exact rational denotations, and equal values are ordered by sign, then by
exponent, reversed for negative values. Binary interchange represents each nonzero finite value
uniquely. On unnormalized dyadics the exponent rule also gives a consistent order.

IEEE 754-2019 §5.10 fixes the order of NaNs by sign and signaling class and leaves the rest of the
NaN order implementation-defined, so FloatLib chose one: increasing fraction payload for positive
NaNs and decreasing fraction payload for negative NaNs. The complete fraction includes the quiet
bit. Class is compared first, so the same convention reads as increasing or decreasing trailing
payload. Neither predicate quiets NaNs or produces exception indicators.

`totalOrderMag` clears signs in the complete exact data. For signed-zero formats this agrees with
`totalOrder` after encoded absolute value, as §5.7.2 requires for IEEE formats. Clearing signs in
the exact data also works for unsigned-zero formats, whose reserved NaN word cannot have its sign
bit cleared without changing its classification. Both APIs accept every descriptor, and the IEEE
conformance claims apply to IEEE encodings.

## References

* IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019, §§5.7.2 and 5.10,
  DOI 10.1109/IEEESTD.2019.8766229.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

namespace ExactValue

/-- Lexicographic coordinates: value class, numerical value, sign or NaN class, and exponent
or payload. Every coordinate has its ordinary mathematical order. -/
abbrev TotalOrderKey := Nat ×ₗ (Rat ×ₗ (Nat ×ₗ Int))

/-- Tie coordinates for finite values: negative signs first, then sign-directed exponents. -/
def finiteTotalOrderKey (d : Numerics.Dyadic) : Nat ×ₗ Int :=
  toLex (if d.negative then 0 else 1, if d.negative then -d.exponent else d.exponent)

/--
Exact ordering coordinates. The five value classes are negative NaNs, negative infinity,
finite numbers, positive infinity, and positive NaNs, in that order.
-/
def totalOrderKey : ExactValue → TotalOrderKey
  | .finite d =>
      toLex (2, toLex (d.toRat, finiteTotalOrderKey d))
  | .infinity sign =>
      toLex (if sign then 1 else 3, toLex (0, toLex (0, 0)))
  | .nan sign signaling payload =>
      toLex (if sign then 0 else 4, toLex (0, toLex
        (if sign then (if signaling then 1 else 0) else (if signaling then 0 else 1),
         if sign then -(payload : Int) else (payload : Int))))

/-- IEEE total order on exact representations, including the exponent of a finite dyadic.
Finite comparison avoids shifts proportional to the exponent gap. -/
def totalOrder : ExactValue → ExactValue → Bool
  | .finite a, .finite b =>
      match Numerics.Dyadic.Internal.compareScalable a b with
      | .lt => true
      | .eq => decide (finiteTotalOrderKey a ≤ finiteTotalOrderKey b)
      | .gt => false
  | .finite _, .infinity sign => !sign
  | .infinity sign, .finite _ => sign
  | .nan sign _ _, .finite _ => sign
  | .finite _, .nan sign _ _ => !sign
  | x, y => decide (totalOrderKey x ≤ totalOrderKey y)

/-- Clear the sign while retaining the exponent, significand, and NaN class and payload. -/
def abs : ExactValue → ExactValue
  | .finite d => .finite { d with negative := false }
  | .infinity _ => .infinity false
  | .nan _ signaling payload => .nan false signaling payload

/-- Total ordering of exact magnitudes. Opposite signs with identical magnitudes are tied. -/
def totalOrderMag (x y : ExactValue) : Bool :=
  totalOrder (abs x) (abs y)

end ExactValue

/-- IEEE 754-2019 total ordering, using exact numerical values and complete NaN metadata. -/
@[inline] def totalOrder {fmt : FloatFormat} (x y : Model fmt) : Bool :=
  ExactValue.totalOrder (exactValue x) (exactValue y)

/-- IEEE magnitude ordering on complete exact data, generalized to every binary descriptor. -/
@[inline] def totalOrderMag {fmt : FloatFormat} (x y : Model fmt) : Bool :=
  ExactValue.totalOrderMag (exactValue x) (exactValue y)

end FloatLib.Floats.Formats.BinaryInterchange.Model
