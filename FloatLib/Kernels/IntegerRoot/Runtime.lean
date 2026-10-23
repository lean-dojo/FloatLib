/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Runtime
public import FloatLib.Numerics.Exact.IntegerRoot.Runtime

/-!
# Integer roots with a logarithmic initial bound

Degrees zero and one are immediate. Degree two uses the native-word and increasing-precision
square-root kernel, and every degree from three uses `IntegerRoot.newton`, which starts Newton's
method from a power-of-two seed just above the root instead of the entire radicand. The proof
module identifies every result with `Nat.nthRoot`, including its degree-zero convention.
-/

@[expose] public section

namespace FloatLib.Numerics.IntegerRoot

/-- Floor `degree`-th root of `value`, with degree zero returning one as in `Nat.nthRoot`. -/
def root (degree value : Nat) : Nat :=
  match degree with
  | 0 => 1
  | 1 => value
  | 2 => FixedWord.IntegerSquareRoot.sqrtNat value
  | degree + 3 => newton (degree + 3) value

end FloatLib.Numerics.IntegerRoot
