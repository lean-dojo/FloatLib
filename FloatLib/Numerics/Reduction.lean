/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Collection reductions

Scalar formats differ in how they accumulate, but collection-shaped operations fail in the same
structural ways. We keep those failures here so that binary dot products, posit quires, and later
reduction APIs can report them without depending on one another.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- Why a collection reduction could not be evaluated. -/
inductive ReductionError where
  /-- The two input collections contain different numbers of elements. -/
  | lengthMismatch (leftLength rightLength : Nat)
  deriving Repr, DecidableEq

end FloatLib.Numerics
