/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.BinaryGrid
public import FloatLib.Numerics.Enclosure.Interval.Runtime

/-!
# Interval multiply-add with one outward rounding

The product bounds and the addend are combined before rounding either endpoint. A finite
endpoint format can therefore enclose a small final result even when the intermediate product
would exceed its range. These operations enclose the real expression `x * y + z`.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

variable {α β : Type*} [Field β] [LinearOrder β] [IsStrictOrderedRing β]

/-- Exact endpoint bounds for a product followed by addition. -/
def fmaBounds (I J K : Interval β) : Interval β :=
  ⟨minOfFour (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi) + K.lo,
    maxOfFour (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi) + K.hi⟩

/--
Enclose `x * y + z`, rounding only the final lower and upper bounds.

Decoding or final endpoint overflow returns `none`. No representable intermediate product
is required.
-/
def fma? (R : OutwardRounding α β) (I J K : Interval α) : Option (Interval α) :=
  match I.decode? R.decode, J.decode? R.decode, K.decode? R.decode with
  | some a, some b, some c => encloseInterval? R (fmaBounds a b c)
  | _, _, _ => none

namespace BinaryGrid

/-- Integer multiply-add, aligning the addend before the two outward-rounded shifts. -/
def fma (precision : Nat) (I J K : Interval Int) : Interval Int :=
  let a := I.lo * J.lo
  let b := I.lo * J.hi
  let c := I.hi * J.lo
  let d := I.hi * J.hi
  ⟨roundDown precision (minOfFour a b c d + (K.lo <<< precision)),
    roundUp precision (maxOfFour a b c d + (K.hi <<< precision))⟩

end BinaryGrid
end FloatLib.Numerics.Interval
