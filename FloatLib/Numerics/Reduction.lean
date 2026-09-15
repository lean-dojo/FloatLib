/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Collection reductions

Scalar formats differ in their accumulation rules, but collection-shaped operations face the
same structural failures. Keeping those failures here lets binary dot products, posit quires, and
future reduction APIs report them without depending on one another.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- Why a collection reduction could not be evaluated. -/
inductive ReductionError where
  /-- The two input collections contain different numbers of elements. -/
  | lengthMismatch (leftLength rightLength : Nat)
  deriving Repr, DecidableEq

end FloatLib.Numerics
