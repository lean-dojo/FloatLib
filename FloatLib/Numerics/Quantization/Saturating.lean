/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Spec
public import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Saturating quantization

`clamp` restricts an exact scalar to declared finite endpoints. `spec` requires a code denoting
that clamped scalar exactly; it does not round an interior input onto a representable grid.
The relation has no result when the clamped scalar is unrepresentable, even if both endpoints
are representable. A concrete family must establish representability to obtain a total kernel.

The definitions are independent of radix, storage width, and overflow encodings.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Saturating

/-- Clamp to `[lower, upper]` when `lower ≤ upper`; otherwise return `lower`. -/
@[inline] def clamp {α : Type} [LinearOrder α] (lower upper value : α) : α :=
  max lower (min upper value)

/-- On a nonempty interval, clamping is Mathlib's interval projection with its bounds erased. -/
theorem clamp_eq_projIcc {α : Type} [LinearOrder α]
    (lower upper value : α) (hendpoints : lower ≤ upper) :
    clamp lower upper value = (Set.projIcc lower upper hendpoints value : α) :=
  rfl

/-- Clamping fixes values already inside the declared interval. -/
@[simp, grind =] theorem clamp_eq_self {α : Type} [LinearOrder α]
    {lower upper value : α} (hlower : lower ≤ value) (hupper : value ≤ upper) :
    clamp lower upper value = value := by
  rw [clamp, min_eq_right hupper, max_eq_right hlower]

/-- A clamped value is never below the lower endpoint. -/
theorem lower_le_clamp {α : Type} [LinearOrder α]
    (lower upper value : α) :
    lower ≤ clamp lower upper value :=
  le_max_left _ _

/-- When `lower ≤ upper`, a clamped value never exceeds `upper`. -/
theorem clamp_le_upper {α : Type} [LinearOrder α]
    {lower upper value : α} (hendpoints : lower ≤ upper) :
    clamp lower upper value ≤ upper := by
  exact max_le hendpoints (min_le_left _ _)

/--
Require exact representation of `clamp lower upper input`.

An unrepresentable clamped scalar has no permitted result. When `lower > upper`, the relation
requires representation of `lower` for every input, following `clamp`'s endpoint convention.
-/
def spec (system : NumericalSystem) [LinearOrder system.Scalar]
    (lower upper : system.Scalar) :
    Spec Unit system.Scalar system.Code :=
  Spec.represents system fun _ input => clamp lower upper input

end FloatLib.Numerics.Quantization.Saturating
