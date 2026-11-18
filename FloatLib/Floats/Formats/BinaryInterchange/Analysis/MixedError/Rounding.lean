/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.Roundoff.Extension
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError.Attribute
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedPrecision

/-!
# Local rounding of model operations

`Analysis.MixedError` states each rounded model operation together with the propagation of its
operands' errors. An error analysis that picks the propagation rule itself needs the rounding
alone, and that is what this file gives, as the descriptor-model counterparts of
`Configured.MixedError.Rounding`.

For an IEEE descriptor, a finite result has relative error `u` against the exact operation on the
computed operands. Sums and differences have no absolute part. Products, quotients, square roots
and fused multiply-adds add the underflow error. A quotient keeps a finite divisor and a square
root a finite operand in its domain. Finite operands whose exact result has an enclosure
`(1 + r) * |x₀| + a` at most the largest finite value have a finite result, and a quotient also
needs a divisor that is not an executable zero.

A sum, a difference, a product or a fused multiply-add in a rounding attribute other than the
default one saturates on overflow, so a finite result does not make it a rounding of the exact
result. Its rules (`add_rounding_mode`, `sub_rounding_mode`, `mul_rounding_mode` and
`fma_rounding_mode` of `Analysis.MixedError.Attribute`) ask that the exact result be within the
largest finite magnitude, and state the unit roundoff of the attribute, for each of the six
attributes. The same enclosure makes the result finite (`isFinite_add_of_mixedError_mode` and
its `sub`, `mul` and `fma` forms).

Cast rules cover every destination encoding. A finite cast to a non-saturating format has one
rounding; a fully finite format adds its explicit clipping loss. Exact grid extension removes
rounding when the destination can represent the source value. Encoding policies select these
rules in both error and finiteness searches, so an IEEE-only rule cannot obstruct an FP8 cast.

Importing this module registers these theorems with `roundoff`, which then proves mixed bounds
with a relative error for model computations, as it does for configured ones. Without it a model
computation gets its absolute bound, read as a mixed bound with no relative part.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

variable {fmt : FloatFormat} {x y z : Model fmt} {x₀ r a : ℝ}

/-- Read a binary exponent through real power, whose exponent `roundoff` analyzes.
In particular an exponent computed from rounded data is not silently treated as stored data. -/
theorem bpow_eq_rpow (e : ℤ) : Flocq.bpow binaryRadix e = (2 : ℝ) ^ (e : ℝ) := by
  rw [Real.rpow_intCast]
  rfl

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

/-- Every finite cast has one rounding and, for fully finite encodings, the explicit clipping
loss. -/
theorem cast_rounding_policy {src dst : FloatFormat} {x : Model src}
    (hx : isFinite x = true) (hout : isFinite (cast src dst x) = true) :
    MixedError (toReal (cast src dst x)) (toReal x) (unitRoundoffAt dst)
      (underflowErrorAt dst +
        if dst.encoding = .finite then max 0 (|toReal x| - toReal (posMaxFinite dst)) else 0) :=
  ⟨(unitRoundoffAt_pos dst).le,
    add_nonneg (underflowErrorAt_pos dst).le (by split <;> positivity),
    abs_toReal_cast_sub_le_policy x hx hout⟩

/-- Finite casts to non-saturating encodings, including FP8 with NaNs, round once. -/
theorem cast_rounding_of_no_saturation {src dst : FloatFormat} {x : Model src}
    (hdst : dst.encoding ≠ .finite) (hx : isFinite x = true)
    (hout : isFinite (cast src dst x) = true) :
    MixedError (toReal (cast src dst x)) (toReal x) (unitRoundoffAt dst)
      (underflowErrorAt dst) := by
  simpa only [hdst, ite_false, add_zero] using cast_rounding_policy hx hout

/-- A finite cast to an IEEE destination rounds once, regardless of the source encoding. -/
theorem cast_rounding {src dst : FloatFormat} {x : Model src}
    (hdst : dst.isIEEE = true) (hout : isFinite (cast src dst x) = true) :
    MixedError (toReal (cast src dst x)) (toReal x) (unitRoundoffAt dst)
      (underflowErrorAt dst) :=
  cast_rounding_of_no_saturation
    (by simp [((FloatFormat.isIEEE_eq_true_iff dst).mp hdst).1])
    (isFinite_of_isFinite_cast hdst hout) hout

/-- A finite nearest-even exponent scaling has one rounding when exactness cannot be used. -/
theorem scale_rounding {e : ℤ} (hfmt : fmt.isIEEE = true)
    (hout : isFinite (scale x e) = true) :
    MixedError (toReal (scale x e)) (toReal x * Flocq.bpow binaryRadix e)
      (unitRoundoffAt fmt) (underflowErrorAt fmt) :=
  mixedError_toReal_of_eq_roundAt (toReal_scale_eq_roundAt x e hfmt hout)

/-- A cast whose input enclosure fits the destination's finite range is finite. -/
theorem isFinite_cast_of_mixedError {src dst : FloatFormat} {x : Model src}
    (hdst : dst.isIEEE = true) (hx : isFinite x = true)
    (bound : MixedError (toReal x) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ toReal (posMaxFinite dst)) :
    isFinite (cast src dst x) = true :=
  isFinite_cast_of_abs_toReal_le_posMaxFinite x hdst hx (bound.abs_le.trans range)

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

/-- For an IEEE descriptor and every rounding attribute, finite operands whose exact sum
has an enclosure at most the largest finite value have a finite sum in that attribute. -/
theorem isFinite_add_of_mixedError_mode {mode : IEEERoundingMode} (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (bound : MixedError (toReal x + toReal y) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ toReal (posMaxFinite fmt)) :
    isFinite (add x y (mode := mode)) = true :=
  (add_finite_roundAt hfmt hx hy (bound.abs_le.trans range)).1

/-- For an IEEE descriptor and every rounding attribute, finite operands whose exact
difference has an enclosure at most the largest finite value have a finite difference in that
attribute. -/
theorem isFinite_sub_of_mixedError_mode {mode : IEEERoundingMode} (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (bound : MixedError (toReal x - toReal y) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ toReal (posMaxFinite fmt)) :
    isFinite (sub x y (mode := mode)) = true :=
  (sub_finite_roundAt hfmt hx hy (bound.abs_le.trans range)).1

/-- For an IEEE descriptor and every rounding attribute, finite operands whose exact
product has an enclosure at most the largest finite value have a finite product in that
attribute. -/
theorem isFinite_mul_of_mixedError_mode {mode : IEEERoundingMode} (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (bound : MixedError (toReal x * toReal y) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ toReal (posMaxFinite fmt)) :
    isFinite (mul x y (mode := mode)) = true :=
  (mul_finite_roundAt hfmt hx hy (bound.abs_le.trans range)).1

/-- For an IEEE descriptor and every rounding attribute, finite operands whose exact
`x * y + z` has an enclosure at most the largest finite value have a finite fused multiply-add in
that attribute. -/
theorem isFinite_fma_of_mixedError_mode {mode : IEEERoundingMode} (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (bound : MixedError (toReal x * toReal y + toReal z) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ toReal (posMaxFinite fmt)) :
    isFinite (fma x y z (mode := mode)) = true :=
  (fma_finite_roundAt hfmt hx hy hz (bound.abs_le.trans range)).1

attribute [roundoff_rule] add_rounding sub_rounding mul_rounding div_rounding sqrt_rounding
  fma_rounding add_rounding_mode sub_rounding_mode mul_rounding_mode fma_rounding_mode
  isFinite_add_of_mixedError isFinite_sub_of_mixedError isFinite_mul_of_mixedError
  isFinite_div_of_mixedError
  isFinite_add_of_mixedError_mode isFinite_sub_of_mixedError_mode isFinite_mul_of_mixedError_mode
  isFinite_fma_of_mixedError_mode cast_rounding isFinite_cast_of_mixedError
  cast_rounding_of_no_saturation cast_rounding_policy
  cast_exact_of_gridExtension cast_exact_of_gridExtension_policy
  toReal_mul_cast_exact toReal_mul_pow_two_exact
  toReal_scale_exact scale_rounding
  bpow_eq_rpow toReal_zero

end FloatLib.Floats.Formats.BinaryInterchange.Model
