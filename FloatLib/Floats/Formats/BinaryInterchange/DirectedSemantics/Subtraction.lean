/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Addition

/-!
# Directed subtraction soundness for conventional IEEE formats

Subtraction reuses directed addition after exact sign-bit negation of the right operand. Generic
finite-value negation semantics turn the resulting sum bounds into real subtraction bounds.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

noncomputable section

/-- Downward-rounded subtraction is a lower bound on exact real subtraction. -/
theorem toEReal_subDown_le
    {fmt : FloatFormat} (x y : Model fmt) (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    toEReal (subDown x y) ≤ ((toReal x - toReal y : ℝ) : EReal) := by
  have hyNeg : isFinite (neg y) = true := by
    simpa using hy
  change toEReal (addDown x (neg y)) ≤ ((toReal x - toReal y : ℝ) : EReal)
  simpa [toReal_neg y hy, sub_eq_add_neg] using
    toEReal_addDown_le x (neg y) hfmt hx hyNeg

/-- Exact real subtraction is bounded above by upward-rounded subtraction. -/
theorem le_toEReal_subUp
    {fmt : FloatFormat} (x y : Model fmt) (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    ((toReal x - toReal y : ℝ) : EReal) ≤ toEReal (subUp x y) := by
  have hyNeg : isFinite (neg y) = true := by
    simpa using hy
  change ((toReal x - toReal y : ℝ) : EReal) ≤ toEReal (addUp x (neg y))
  simpa [toReal_neg y hy, sub_eq_add_neg] using
    le_toEReal_addUp x (neg y) hfmt hx hyNeg

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
