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

For finite operands, `mulDown` and `mulUp` round the same exact dyadic product in opposite
directions. The extended-real statements remain valid when outward rounding overflows.

The bounds hold for every descriptor satisfying `fmt.isIEEE = true`, with no restriction to named
widths. Both operands must be finite; the rounded product may be infinite.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

noncomputable section

/-- Downward-rounded multiplication is a lower bound on the exact real product. -/
theorem toEReal_mulDown_le
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    toEReal (mulDown x y) ≤ ((toReal x * toReal y : ℝ) : EReal) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [← toReal_mulDyadic_of_toDyadic?_some hdx hdy, mulDown,
    mulWithRounding_eq_of_toDyadic?_some .towardNegativeInfinity nofun hdx hdy]
  exact toEReal_roundDyadicDown_le fmt _ hfmt

/-- The exact real product is bounded above by upward-rounded multiplication. -/
theorem le_toEReal_mulUp
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    ((toReal x * toReal y : ℝ) : EReal) ≤ toEReal (mulUp x y) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [← toReal_mulDyadic_of_toDyadic?_some hdx hdy, mulUp,
    mulWithRounding_eq_of_toDyadic?_some .towardPositiveInfinity nofun hdx hdy]
  exact le_toEReal_roundDyadicUp fmt _ hfmt

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
