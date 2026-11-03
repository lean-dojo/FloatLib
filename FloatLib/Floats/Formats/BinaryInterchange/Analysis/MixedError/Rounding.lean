/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError
public meta import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Extension

/-!
# Local rounding of model operations

`Analysis.MixedError` states each rounded model operation together with the propagation of its
operands' errors. An error analysis that chooses the propagation rule itself needs the rounding
alone: for an IEEE descriptor, a finite result has relative error `u` against the exact operation
on the computed operands, with no absolute part for sums and differences and the underflow error
for products, quotients, square roots and fused multiply-adds. A quotient keeps a finite divisor
and a square root a finite operand in its domain. Finite operands whose exact result has an
enclosure `(1 + r) * |x₀| + a` at most the largest finite value have a finite result, a quotient
also needing a divisor that is not an executable zero. These are the descriptor-model
counterparts of `Configured.MixedError.Rounding`.

Importing this module registers them with `roundoff`, which then proves mixed bounds with a
relative error for model computations, as it does for configured ones. Without it a model
computation gets its absolute bound, read as a mixed bound with no relative part.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

variable {fmt : FloatFormat} {x y z : Model fmt} {x₀ r a : ℝ}

/-- For an IEEE descriptor, a finite sum has relative error `u` against the exact sum of its
operands. -/
theorem add_rounding (hfmt : fmt.isIEEE = true) (hout : isFinite (add x y) = true) :
    MixedError (toReal (add x y)) (toReal x + toReal y) (unitRoundoffAt fmt) 0 :=
  MixedError.of_abs_sub_le_mul (unitRoundoffAt_pos fmt).le
    (abs_toReal_add_sub_le_unitRoundoffAt x y hfmt hout)

/-- For an IEEE descriptor, a finite difference has relative error `u` against the exact difference.
-/
theorem sub_rounding (hfmt : fmt.isIEEE = true) (hout : isFinite (sub x y) = true) :
    MixedError (toReal (sub x y)) (toReal x - toReal y) (unitRoundoffAt fmt) 0 :=
  MixedError.of_abs_sub_le_mul (unitRoundoffAt_pos fmt).le
    (abs_toReal_sub_sub_le_unitRoundoffAt x y hfmt hout)

/-- For an IEEE descriptor, a finite product has the mixed error of one rounding. -/
theorem mul_rounding (hfmt : fmt.isIEEE = true) (hout : isFinite (mul x y) = true) :
    MixedError (toReal (mul x y)) (toReal x * toReal y) (unitRoundoffAt fmt)
      (underflowErrorAt fmt) :=
  mixedError_toReal_of_eq_roundAt (toReal_mul_eq_roundAt x y hfmt hout)

/-- For an IEEE descriptor, a finite quotient by a finite divisor has the mixed error of one
rounding. -/
theorem div_rounding (hfmt : fmt.isIEEE = true) (hy : isFinite y = true)
    (hout : isFinite (div x y) = true) :
    MixedError (toReal (div x y)) (toReal x / toReal y) (unitRoundoffAt fmt)
      (underflowErrorAt fmt) :=
  mixedError_toReal_of_eq_roundAt (toReal_div_eq_roundAt x y hfmt hy hout)

/-- For an IEEE descriptor, the square root of a finite zero or positive value has the mixed error
of one rounding. -/
theorem sqrt_rounding (hfmt : fmt.isIEEE = true) (hx : isFinite x = true)
    (hdomain : isZero x = true ∨ signBit x = false) :
    MixedError (toReal (sqrt x)) (Real.sqrt (toReal x)) (unitRoundoffAt fmt)
      (underflowErrorAt fmt) :=
  mixedError_toReal_of_eq_roundAt (toReal_sqrt_eq_roundAt x hfmt hx hdomain)

/-- For an IEEE descriptor, a finite fused multiply-add rounds once: it has the mixed error of one
rounding against the exact `x * y + z`. -/
theorem fma_rounding (hfmt : fmt.isIEEE = true) (hout : isFinite (fma x y z) = true) :
    MixedError (toReal (fma x y z)) (toReal x * toReal y + toReal z) (unitRoundoffAt fmt)
      (underflowErrorAt fmt) :=
  mixedError_toReal_of_eq_roundAt (toReal_fma_eq_roundAt x y z hfmt hout)

/-- For an IEEE descriptor, finite operands whose exact sum has an enclosure at most the largest
finite value have a finite sum. -/
theorem isFinite_add_of_mixedError (hfmt : fmt.isIEEE = true) (hx : isFinite x = true)
    (hy : isFinite y = true) (bound : MixedError (toReal x + toReal y) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ toReal (posMaxFinite fmt)) : isFinite (add x y) = true :=
  isFinite_add_of_abs_toReal_add_le_posMaxFinite x y hfmt hx hy (bound.abs_le.trans range)

/-- For an IEEE descriptor, finite operands whose exact difference has an enclosure at most the
largest finite value have a finite difference. -/
theorem isFinite_sub_of_mixedError (hfmt : fmt.isIEEE = true) (hx : isFinite x = true)
    (hy : isFinite y = true) (bound : MixedError (toReal x - toReal y) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ toReal (posMaxFinite fmt)) : isFinite (sub x y) = true :=
  isFinite_sub_of_abs_toReal_sub_le_posMaxFinite x y hfmt hx hy (bound.abs_le.trans range)

/-- For an IEEE descriptor, finite operands whose exact product has an enclosure at most the largest
finite value have a finite product. -/
theorem isFinite_mul_of_mixedError (hfmt : fmt.isIEEE = true) (hx : isFinite x = true)
    (hy : isFinite y = true) (bound : MixedError (toReal x * toReal y) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ toReal (posMaxFinite fmt)) : isFinite (mul x y) = true := by
  refine isFinite_mul_of_abs_mul_le_posMaxFinite x y hfmt hx hy ?_
  rw [← abs_mul]
  exact bound.abs_le.trans range

/-- For an IEEE descriptor, finite operands, the divisor nonzero, whose exact quotient has an
enclosure below the largest finite value have a finite quotient. -/
theorem isFinite_div_of_mixedError (hfmt : fmt.isIEEE = true) (hx : isFinite x = true)
    (hy : isFinite y = true) (hzero : isZero y = false)
    (bound : MixedError (toReal x / toReal y) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ toReal (posMaxFinite fmt)) : isFinite (div x y) = true :=
  isFinite_div_of_abs_div_le_posMaxFinite x y hfmt hx hy hzero (bound.abs_le.trans range)

attribute [roundoff_rule] add_rounding sub_rounding mul_rounding div_rounding sqrt_rounding
  fma_rounding isFinite_add_of_mixedError isFinite_sub_of_mixedError isFinite_mul_of_mixedError
  isFinite_div_of_mixedError

end FloatLib.Floats.Formats.BinaryInterchange.Model
