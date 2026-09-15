/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Semantics
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Proof

/-!
# Bfloat16 consequences of the generic theory

The general format-rounding theorem specializes to two useful bfloat16 facts. Widening to binary32
is exact because both formats have the same normal exponent range and binary32 adds fraction bits.
Addition performs exact dyadic addition followed by one bfloat16 nearest-even rounding step.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats

/-- Widening a finite bfloat16 value to binary32 preserves its exact real value. -/
theorem toReal_cast_bfloat16_binary32
    {x : Model FloatFormat.bfloat16} (hx : isFinite x = true) :
    toReal (cast FloatFormat.bfloat16 FloatFormat.binary32 x) = toReal x := by
  exact cast_exact_of_compatibleWidening x
    (by decide) (by decide) (by decide) (by decide) hx

/-- Bfloat16 rounding viewed as a real function. -/
noncomputable abbrev bf16Round (x : ℝ) : ℝ :=
  roundAt FloatFormat.bfloat16 x

/-- Finite bfloat16 addition is exact real addition followed by one nearest-even rounding step. -/
theorem bfloat16_add_eq_bf16Round
    {x y : Model FloatFormat.bfloat16}
    (hx : isFinite x = true) (hy : isFinite y = true) (hfin : isFinite (add x y) = true) :
    toReal (add x y) = bf16Round (toReal x + toReal y) := by
  exact toReal_add_eq_roundAt x y (by decide) hx hy hfin

end Model
end FloatLib.Floats.Formats.BinaryInterchange
