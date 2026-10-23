/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Bounds

/-!
# Directed division soundness for conventional IEEE formats

For finite operands and a nonzero divisor, `div x y (mode := .down)` and `div x y (mode := .up)`
round the exact rational quotient in opposite directions. The extended-real statements hold even
when outward rounding overflows.

The bounds hold for every descriptor satisfying `fmt.isIEEE = true`, with no restriction to named
widths.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

section

/-- The exact scaled rational quotient of two finite values denotes their real quotient. -/
theorem signedScaledRatToReal_of_toDyadic?_some
    {fmt : FloatFormat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hdx : toDyadic? x = some dx) (hdy : toDyadic? y = some dy) :
    signedScaledRatToReal (Bool.xor dx.negative dy.negative) dx.significand dy.significand
        (dx.exponent - dy.exponent) =
      toReal x / toReal y := by
  rw [signedScaledRatToReal_eq_div_toReal dx dy]
  simp [toReal_eq, hdx, hdy]

/-- Downward-rounded division is a lower bound on the exact real quotient. -/
theorem toEReal_div_down_le
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false) :
    toEReal (div x y (mode := .down)) ≤ ((toReal x / toReal y : ℝ) : EReal) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [← signedScaledRatToReal_of_toDyadic?_some hdx hdy,
    div_eq_of_toDyadic?_some .down nofun hdx hdy hy0]
  exact toEReal_roundRatDownScaled_le fmt _ _ _ _ hfmt
    (significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdy hy0)

/-- The exact real quotient is bounded above by upward-rounded division. -/
theorem le_toEReal_div_up
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false) :
    ((toReal x / toReal y : ℝ) : EReal) ≤ toEReal (div x y (mode := .up)) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  rw [← signedScaledRatToReal_of_toDyadic?_some hdx hdy,
    div_eq_of_toDyadic?_some .up nofun hdx hdy hy0]
  exact le_toEReal_roundRatUpScaled fmt _ _ _ _ hfmt
    (significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdy hy0)

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
