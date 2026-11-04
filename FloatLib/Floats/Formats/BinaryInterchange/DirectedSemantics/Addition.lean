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

Finite operands decode to exact dyadics, and their executable directed sum is the exact dyadic sum
rounded outward, except at exact cancellation, where IEEE picks a signed zero that depends on the
rounding mode. Both signed zeros denote zero. So for conventional IEEE descriptors one enclosure
theorem covers cancellation and overflow.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

section

/-- Downward-rounded addition is a lower bound on exact real addition for finite operands. -/
theorem toEReal_add_down_le
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    toEReal (add x y (mode := .down)) ≤ ((toReal x + toReal y : ℝ) : EReal) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [← toReal_addDyadic_of_toDyadic?_some hdx hdy, add_eq_of_toDyadic?_some .down nofun hdx hdy]
  split_ifs with hzero
  · simp [Numerics.Dyadic.toReal, hzero]
  · exact toEReal_roundDyadicDown_le fmt _ hfmt

/-- Exact real addition is bounded above by upward-rounded addition for finite operands. -/
theorem le_toEReal_add_up
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    ((toReal x + toReal y : ℝ) : EReal) ≤ toEReal (add x y (mode := .up)) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [← toReal_addDyadic_of_toDyadic?_some hdx hdy, add_eq_of_toDyadic?_some .up nofun hdx hdy]
  split_ifs with hzero
  · simp [Numerics.Dyadic.toReal, hzero]
  · exact le_toEReal_roundDyadicUp fmt _ hfmt

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
