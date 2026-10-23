/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Runtime
import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Proof

/-!
# Compiler certificate for the native integer square root

The logical `sqrt` is the Newton iteration, which the kernel can evaluate. Compiled code runs
`sqrtChecked`, whose floating-point candidate is accepted only after an exact square check. Both
compute `Nat.sqrt` on every word, so the substitution is registered with `@[csimp]`. Runtime modules
import this module to compile their calls through the checked path.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.IntegerSquareRoot

/-- Compile the native integer square root through the checked floating-point candidate. -/
-- grind: no rule; this equation selects a compiler implementation.
@[csimp] theorem sqrt_eq_sqrtChecked : sqrt = sqrtChecked := by
  funext value
  apply UInt64.toNat_inj.mp
  rw [sqrt_toNat, sqrtChecked_toNat]

end FloatLib.Numerics.FixedWord.IntegerSquareRoot
