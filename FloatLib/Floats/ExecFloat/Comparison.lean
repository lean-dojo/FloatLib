/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Carrier

/-!
# Optional comparison capability for `ExecFloat`

Comparison is format-defined rather than imposed by the universal carrier. IEEE binary formats
use an unordered result for NaN, while standard posits use their total signed-word order,
including NaR. Formats for which no comparison has been specified simply do not install this
capability.

The public functions in this module give clients one spelling independently of the numerical
family:

```lean
ExecFloat.compare left right
ExecFloat.compareEqual left right
ExecFloat.compareLess left right
```

`Option Ordering` retains the distinction between an ordered result and an unordered comparison.
The Boolean predicates then follow each format's installed comparison without assuming IEEE,
posit, real-number, or bitwise semantics.
-/

@[expose] public section

namespace FloatLib.Floats
namespace ExecFloat

open FloatLib.Numerics

universe u

variable (F : Type u) [EncodedFormat F]

/--
Format-defined comparison for executable values.

`none` means unordered. A format with a total order returns `some` for every pair.
-/
class Comparison where
  /-- Compare two values, returning `none` precisely when the format declares them unordered. -/
  compare : ExecFloat F → ExecFloat F → Option Ordering

variable {F : Type u} [EncodedFormat F]

/-- Compare two executable values according to their format's comparison semantics. -/
@[inline] def compare [self : Comparison F]
    (left right : ExecFloat F) : Option Ordering :=
  self.compare left right

/--
Format-defined numerical equality.

For an unordered comparison this is `false`; consequently IEEE NaNs compare unequal. A format
whose comparison is total may choose to include exceptional stored values in its equality.
-/
@[inline] def compareEqual [Comparison F]
    (left right : ExecFloat F) : Bool :=
  compare left right == some .eq

/--
Format-defined numerical inequality.

This is the Boolean complement of `compareEqual`, so unordered pairs compare unequal.
-/
@[inline] def compareNotEqual [Comparison F]
    (left right : ExecFloat F) : Bool :=
  !(compareEqual left right)

/-- Strict less-than; unordered comparisons return `false`. -/
@[inline] def compareLess [Comparison F]
    (left right : ExecFloat F) : Bool :=
  compare left right == some .lt

/-- Less-than-or-equal; unordered comparisons return `false`. -/
@[inline] def compareLessEqual [Comparison F]
    (left right : ExecFloat F) : Bool :=
  match compare left right with
  | some .lt | some .eq => true
  | none | some .gt => false

/-- Strict greater-than; unordered comparisons return `false`. -/
@[inline] def compareGreater [Comparison F]
    (left right : ExecFloat F) : Bool :=
  compare left right == some .gt

/-- Greater-than-or-equal; unordered comparisons return `false`. -/
@[inline] def compareGreaterEqual [Comparison F]
    (left right : ExecFloat F) : Bool :=
  match compare left right with
  | some .eq | some .gt => true
  | none | some .lt => false

end ExecFloat
end FloatLib.Floats
