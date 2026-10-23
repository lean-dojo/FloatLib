/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Nat.NthRoot.Defs

/-!
# Integer roots by seeded Newton iteration

Mathlib's `Nat.nthRoot` runs Newton's method from the radicand itself. For a large radicand and a
large degree the first steps then shrink the guess by a factor of only `(n - 1) / n` each. This
module starts instead from a power of two read off the radicand's binary logarithm. For a positive
radicand that seed lies above the root and within a factor of two of it.
Zero and one return themselves for every positive degree, before any seed is built or raised to a
power that could be enormous when the degree is large.

In `FloatLib.Kernels`, `IntegerRoot.root` answers degrees zero and one immediately, uses a
native-word square root for degree two, and calls this kernel for every degree from three.
Format-independent exact arithmetic, which cannot depend on the kernels, uses it directly. The
proof module identifies the result with `Nat.nthRoot`.
-/

@[expose] public section

namespace FloatLib.Numerics.IntegerRoot

/-- Floor `degree`-th root of `value`, with degree zero returning one as in `Nat.nthRoot`. -/
def newton (degree value : Nat) : Nat :=
  match degree with
  | 0 => 1
  | 1 => value
  | degree + 2 =>
    if value ≤ 1 then value
    else
      let initial := 2 ^ ((value.log2 + degree + 2) / (degree + 2))
      Nat.nthRoot.go degree value initial initial

end FloatLib.Numerics.IntegerRoot
