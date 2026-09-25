/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Runtime
public import Mathlib.Data.Nat.NthRoot.Defs

/-!
# Integer roots with a logarithmic initial bound

The floor root uses a power-of-two seed just above the root instead of the entire radicand.
Degree two shares the native-word and increasing-precision square-root kernel. The proof module
identifies every result with `Nat.nthRoot`, including its degree-zero convention.
-/

@[expose] public section

namespace FloatLib.Numerics.IntegerRoot

/-- Exact integer root, with degree zero returning one as in `Nat.nthRoot`. -/
def root (degree value : Nat) : Nat :=
  match degree with
  | 0 => 1
  | 1 => value
  | 2 => FixedWord.IntegerSquareRoot.sqrtNat value
  | degree + 3 =>
    let initial := 2 ^ ((value.log2 + degree + 3) / (degree + 3))
    Nat.nthRoot.go (degree + 1) value initial initial

end FloatLib.Numerics.IntegerRoot
