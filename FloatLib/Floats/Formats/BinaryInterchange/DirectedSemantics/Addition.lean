/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Bounds

/-!
# Directed addition soundness for conventional IEEE formats

Finite operands decode to exact dyadics. Their executable directed sum is the exact dyadic sum
rounded outward, except that exact cancellation selects the IEEE rounding-mode-specific signed
zero. Both signed zeros denote zero, so the same enclosure theorem covers cancellation and
overflow for conventional IEEE descriptors.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

section

/-- Downward-rounded addition is a lower bound on exact real addition for finite operands. -/
theorem toEReal_addDown_le
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    toEReal (addDown x y) ≤ ((toReal x + toReal y : ℝ) : EReal) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [← toReal_addDyadic_of_toDyadic?_some hdx hdy, addDown,
    addWithRounding_eq_of_toDyadic?_some .towardNegativeInfinity nofun hdx hdy]
  split_ifs with hzero
  · simp [Numerics.Dyadic.toReal, hzero]
  · exact toEReal_roundDyadicDown_le fmt _ hfmt

/-- Exact real addition is bounded above by upward-rounded addition for finite operands. -/
theorem le_toEReal_addUp
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    ((toReal x + toReal y : ℝ) : EReal) ≤ toEReal (addUp x y) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [← toReal_addDyadic_of_toDyadic?_some hdx hdy, addUp,
    addWithRounding_eq_of_toDyadic?_some .towardPositiveInfinity nofun hdx hdy]
  split_ifs with hzero
  · simp [Numerics.Dyadic.toReal, hzero]
  · exact le_toEReal_roundDyadicUp fmt _ hfmt

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
