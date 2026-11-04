/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.Reduction.Runtime

/-!
# A division-free enclosure for tangent comparisons

To compare `tan x` with a rational boundary `b`, it's enough to know the sign of `sin x - b * cos x`
and the sign of `cos x`. That linear combination of the reduced enclosures never divides by an
interval that might contain zero.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure

/-- Enclose the residual whose sign determines the tangent comparison once cosine's sign is known. -/
def sinSubCos (argument boundary : ℚ) (degree : Nat) : RationalInterval :=
  (sinReduced argument degree).sub ((cosReduced argument degree).scale boundary)

end FloatLib.Numerics.Enclosure
