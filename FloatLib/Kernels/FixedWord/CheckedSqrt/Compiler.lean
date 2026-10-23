/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.CheckedSqrt.Runtime
import FloatLib.Kernels.FixedWord.CheckedSqrt.Proof

/-!
# Compiler certificate for checked four-word square roots

`Internal.rootAndRemainder` proposes the floor root of a four-word radicand from a
floating-point root and two Newton corrections and accepts it only after an exact four-word square
check. The logical `rootAndRemainder` keeps the restoring loop for such radicands, so no
floating-point operation appears in a definition the kernel may evaluate. The two agree on every
input (`Internal.rootAndRemainder_eq` in `CheckedSqrt.Proof`), so `@[csimp]` installs the checked
path in compiled code. The proof module is imported privately, so executable clients get the
rewrite without re-exporting that development.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.CheckedSquareRoot

/-- Compile checked square roots through the four-word candidate as well. -/
-- grind: no rule; this equation selects a compiler implementation.
@[csimp] theorem rootAndRemainder_eq_internal :
    rootAndRemainder = Internal.rootAndRemainder := by
  funext radicand steps
  exact (Internal.rootAndRemainder_eq radicand steps).symm

end FloatLib.Numerics.FixedWord.CheckedSquareRoot
