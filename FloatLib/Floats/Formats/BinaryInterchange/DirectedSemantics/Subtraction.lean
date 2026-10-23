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

section

/-- Downward-rounded subtraction is a lower bound on exact real subtraction. -/
theorem toEReal_sub_down_le
    {fmt : FloatFormat} (x y : Model fmt) (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    toEReal (sub x y (mode := .down)) ≤ ((toReal x - toReal y : ℝ) : EReal) := by
  have hyNeg : isFinite (neg y) = true := by
    simpa using hy
  change toEReal (add x (neg y) (mode := .down)) ≤ ((toReal x - toReal y : ℝ) : EReal)
  simpa [toReal_neg y hy, sub_eq_add_neg] using
    toEReal_add_down_le x (neg y) hfmt hx hyNeg

/-- Exact real subtraction is bounded above by upward-rounded subtraction. -/
theorem le_toEReal_sub_up
    {fmt : FloatFormat} (x y : Model fmt) (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    ((toReal x - toReal y : ℝ) : EReal) ≤ toEReal (sub x y (mode := .up)) := by
  have hyNeg : isFinite (neg y) = true := by
    simpa using hy
  change ((toReal x - toReal y : ℝ) : EReal) ≤ toEReal (add x (neg y) (mode := .up))
  simpa [toReal_neg y hy, sub_eq_add_neg] using
    le_toEReal_add_up x (neg y) hfmt hx hyNeg

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
