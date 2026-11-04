/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Carrier

/-!
# Optional comparison capability for `ExecFloat`

Comparison is up to each format, and the universal carrier doesn't impose one. IEEE binary formats
return an unordered result for NaN, while standard posits use their total signed-word order, NaR
included. A format with no specified comparison doesn't install this capability.

The public functions here give you one spelling whatever the numerical family:

```lean
ExecFloat.compare left right
ExecFloat.compareEqual left right
ExecFloat.compareLess left right
```

`Option Ordering` keeps the distinction between an ordered result and an unordered comparison, and
the Boolean predicates then follow each format's installed comparison, without assuming IEEE, posit,
real-number, or bitwise semantics.
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
  /--
  Compare two values, returning `none` when, and only when, the format declares them unordered.
  -/
  compare : ExecFloat F → ExecFloat F → Option Ordering

variable {F : Type u} [EncodedFormat F]

/-- Compare two executable values according to their format's comparison semantics. -/
@[inline] def compare [self : Comparison F]
    (left right : ExecFloat F) : Option Ordering :=
  self.compare left right

/--
Format-defined numerical equality.

For an unordered comparison this is `false`, so IEEE NaNs compare unequal. A format whose comparison
is total may choose to include exceptional stored values in its equality.
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

/-- Strict less-than. Unordered comparisons return `false`. -/
@[inline] def compareLess [Comparison F]
    (left right : ExecFloat F) : Bool :=
  compare left right == some .lt

/-- Less-than-or-equal. Unordered comparisons return `false`. -/
@[inline] def compareLessEqual [Comparison F]
    (left right : ExecFloat F) : Bool :=
  match compare left right with
  | some .lt | some .eq => true
  | none | some .gt => false

/-- Strict greater-than. Unordered comparisons return `false`. -/
@[inline] def compareGreater [Comparison F]
    (left right : ExecFloat F) : Bool :=
  compare left right == some .gt

/-- Greater-than-or-equal. Unordered comparisons return `false`. -/
@[inline] def compareGreaterEqual [Comparison F]
    (left right : ExecFloat F) : Bool :=
  match compare left right with
  | some .eq | some .gt => true
  | none | some .lt => false

end ExecFloat
end FloatLib.Floats
