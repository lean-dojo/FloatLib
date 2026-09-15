/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Comparison.Runtime
public import Mathlib.Data.Prod.Lex

/-!
# Total ordering of decimal datums

IEEE 754-2019 §5.10 orders negative NaNs first, then negative infinity,
negative finite values, positive finite values, positive infinity, and positive
NaNs. Within the finite parts, numerical value precedes quantum; quantum order
is reversed for negative datums, including negative zero.

For positive NaNs, signaling precedes quiet; this rule reverses for negative NaNs.
§5.10(d)(5)(iii) leaves the remaining payload order implementation-defined.
Here smaller payloads precede larger ones for positive NaNs, with the reverse
order for negative NaNs.

The key is injective on complete datums. It orders canonical BID/DPD members
after decoding; it deliberately cannot distinguish redundant encodings of the
same datum. These predicates never signal invalid.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Datum

/-- Class, numerical value (or NaN kind), then signed quantum (or NaN payload). -/
abbrev OrderKey := Nat ×ₗ (ℚ ×ₗ Int)

/-- An exact lexicographic key implementing the distinctions required by §5.10. -/
def orderKey : Datum → OrderKey
  | .finite s c q =>
      toLex (if s then 2 else 3,
        toLex (finiteValue s c q, if s then -q else q))
  | .infinity s => toLex (if s then 1 else 4, toLex (0, 0))
  | .nan s t p =>
      toLex (if s then 0 else 5,
        toLex ((if s then (if t then 1 else 0) else (if t then 0 else 1)),
          if s then -(p : Int) else (p : Int)))

/-- Non-signaling total order, distinguishing zero signs, cohort members and NaN metadata. -/
def totalOrder (x y : Datum) : Bool := decide (x.orderKey ≤ y.orderKey)

/-- Total order after clearing both signs, including NaN signs. -/
def totalOrderMag (x y : Datum) : Bool := x.abs.totalOrder y.abs

end FloatLib.Floats.Formats.DecimalInterchange.Datum
