/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Bounds

/-!
# Directed multiplication soundness for conventional IEEE formats

For finite operands, `mul x y (mode := .down)` and `mul x y (mode := .up)` round the same exact
dyadic product in opposite directions. The extended-real statements hold even when outward
rounding overflows.

The bounds hold for every descriptor satisfying `fmt.isIEEE = true`, with no restriction to named
widths.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

section

/-- Downward-rounded multiplication is a lower bound on the exact real product. -/
theorem toEReal_mul_down_le
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    toEReal (mul x y (mode := .down)) ≤ ((toReal x * toReal y : ℝ) : EReal) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [← toReal_mulDyadic_of_toDyadic?_some hdx hdy, mul_eq_of_toDyadic?_some .down nofun hdx hdy]
  exact toEReal_roundDyadicDown_le fmt _ hfmt

/-- The exact real product is bounded above by upward-rounded multiplication. -/
theorem le_toEReal_mul_up
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    ((toReal x * toReal y : ℝ) : EReal) ≤ toEReal (mul x y (mode := .up)) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [← toReal_mulDyadic_of_toDyadic?_some hdx hdy, mul_eq_of_toDyadic?_some .up nofun hdx hdy]
  exact le_toEReal_roundDyadicUp fmt _ hfmt

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
