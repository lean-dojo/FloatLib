/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.Exponent
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Multiplication

/-!
# Exact products and scaling in mixed precision

Two finite binary significands need at most the sum of their precisions for their exact product.
The destination must also contain the product's dyadic grid; a normal-range product suffices.
These facts concern arbitrary descriptors. Executable IEEE multiplication additionally requires
finite results, since the real grid has no upper exponent limit.

The same grid argument makes multiplication by a power of two exact when the result stays normal.
Nonnegative shifts preserve even subnormal grid points. Cast exactness is reused from
`Conversion.Cast.Proof`, so there is no separate theorem family for each pair of storage formats.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats.Formats FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics (binaryRadix)

variable {left right dst : FloatFormat} {x y : ℝ}

/-- In the normal range, the precision-selected exponent is above the subnormal floor. -/
theorem minSubnormalExponent_le_of_normal (fmt : FloatFormat) {x : ℝ}
    (hnormal : minNormalAt fmt ≤ |x|) :
    fmt.minSubnormalExponent ≤ magnitude binaryRadix x - (fmt.fracWidth + 1 : ℕ) := by
  have hmag := (bpow_lt_bpow_iff binaryRadix fmt.minNormalExponent
    (magnitude binaryRadix x)).mp (hnormal.trans_lt (abs_lt_bpow_magnitude binaryRadix x))
  have hexp := minSubnormalExponent_add_precision_sub_one fmt
  change fmt.minSubnormalExponent + (fmt.fracWidth + 1 : ℕ) - 1 =
    fmt.minNormalExponent at hexp
  omega

/-- A product fits a destination grid when its precision contains both significands and its
subnormal floor is at most the sum of the operand grid exponents. -/
theorem genericFormat_mul_of_precision
    (hx : GenericRepresentable binaryRadix (fexpOf left) x)
    (hy : GenericRepresentable binaryRadix (fexpOf right) y)
    (hprec : (left.fracWidth + 1) + (right.fracWidth + 1) ≤ dst.fracWidth + 1)
    (hmin : dst.minSubnormalExponent ≤
      cexp binaryRadix (fexpOf left) x + cexp binaryRadix (fexpOf right) y) :
    GenericRepresentable binaryRadix (fexpOf dst) (x * y) := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  obtain ⟨mx, hxrepr⟩ := exists_int_mul_bpow_cexp_of_generic hx
  obtain ⟨my, hyrepr⟩ := exists_int_mul_bpow_cexp_of_generic hy
  apply genericRepresentable_of_toReal_of_cexp_le
    ({ mantissa := mx * my, exponent :=
      cexp binaryRadix (fexpOf left) x + cexp binaryRadix (fexpOf right) y } :
      FloatRep binaryRadix) _ ?_ ?_
  · change x * y = ((mx * my : ℤ) : ℝ) *
      Flocq.bpow binaryRadix
        (cexp binaryRadix (fexpOf left) x + cexp binaryRadix (fexpOf right) y)
    conv_lhs => rw [hxrepr, hyrepr]
    rw [bpow.add_exp, Int.cast_mul]
    ring
  · change max (magnitude binaryRadix (x * y) - (dst.fracWidth + 1 : ℕ))
      dst.minSubnormalExponent ≤
        cexp binaryRadix (fexpOf left) x + cexp binaryRadix (fexpOf right) y
    refine max_le ?_ hmin
    have hm := magnitude_mul_le_add binaryRadix hx0 hy0
    have hl : magnitude binaryRadix x - (left.fracWidth + 1 : ℕ) ≤
        cexp binaryRadix (fexpOf left) x := le_max_left _ _
    have hr : magnitude binaryRadix y - (right.fracWidth + 1 : ℕ) ≤
        cexp binaryRadix (fexpOf right) y := le_max_left _ _
    omega

/-- A normal-range product needs only the sum of the operand precisions. Zero is also exact. -/
theorem genericFormat_mul_of_normal
    (hx : GenericRepresentable binaryRadix (fexpOf left) x)
    (hy : GenericRepresentable binaryRadix (fexpOf right) y)
    (hprec : (left.fracWidth + 1) + (right.fracWidth + 1) ≤ dst.fracWidth + 1)
    (hnormal : x * y = 0 ∨ minNormalAt dst ≤ |x * y|) :
    GenericRepresentable binaryRadix (fexpOf dst) (x * y) := by
  rcases hnormal with hzero | hnormal
  · simp [hzero]
  have hp0 : x * y ≠ 0 := abs_pos.mp ((bpow.pos _ _).trans_le hnormal)
  have hm := magnitude_mul_le_add binaryRadix (mul_ne_zero_iff.mp hp0).1
    (mul_ne_zero_iff.mp hp0).2
  have hl : magnitude binaryRadix x - (left.fracWidth + 1 : ℕ) ≤
      cexp binaryRadix (fexpOf left) x := le_max_left _ _
  have hr : magnitude binaryRadix y - (right.fracWidth + 1 : ℕ) ≤
      cexp binaryRadix (fexpOf right) y := le_max_left _ _
  have hd := minSubnormalExponent_le_of_normal dst hnormal
  exact genericFormat_mul_of_precision hx hy hprec (by omega)

/-- Multiplying exactly widened operands introduces no rounding when the destination has
the sum of their precisions, the product is zero or normal, and the result is finite. A finite
product forces finite widened operands. -/
theorem toReal_mul_cast_exact (x : Model left) (y : Model right)
    (hdst : dst.isIEEE = true)
    (hlmin : dst.minSubnormalExponent ≤ left.minSubnormalExponent)
    (hrmin : dst.minSubnormalExponent ≤ right.minSubnormalExponent)
    (hprec : (left.fracWidth + 1) + (right.fracWidth + 1) ≤ dst.fracWidth + 1)
    (hnormal : toReal x * toReal y = 0 ∨ minNormalAt dst ≤ |toReal x * toReal y|)
    (hout : isFinite (mul (cast left dst x) (cast right dst y)) = true) :
    toReal (mul (cast left dst x) (cast right dst y)) = toReal x * toReal y := by
  obtain ⟨hx, hy⟩ := isFinite_of_isFinite_mul hdst hout
  rw [toReal_mul_eq_roundAt _ _ hdst hout,
    cast_exact_of_gridExtension x hdst (by omega) hlmin hx,
    cast_exact_of_gridExtension y hdst (by omega) hrmin hy]
  exact round_preserves_generic nearestEven _ (genericFormat_mul_of_normal
    (toReal_genericFormat_of_isFinite x (isFinite_of_isFinite_cast hdst hx))
    (toReal_genericFormat_of_isFinite y (isFinite_of_isFinite_cast hdst hy)) hprec hnormal)

/-- A power-of-two shift preserves the grid when its result is zero or normal.
Nonnegative shifts need no lower-range condition. -/
theorem genericFormat_mul_bpow (fmt : FloatFormat) {x : ℝ}
    (hx : GenericRepresentable binaryRadix (fexpOf fmt) x) (e : ℤ)
    (hrange : 0 ≤ e ∨ x = 0 ∨ minNormalAt fmt ≤ |x * Flocq.bpow binaryRadix e|) :
    GenericRepresentable binaryRadix (fexpOf fmt) (x * Flocq.bpow binaryRadix e) := by
  have hprec : (0 : ℤ) < (fmt.fracWidth + 1 : ℕ) := by positivity
  rcases hrange with he | hx0 | hnormal
  · exact genericRepresentable_flt_mul_bpow_of_nonneg _ _ hprec hx e he
  · simp [hx0]
  · have hx0 : x ≠ 0 := by
      intro hx0
      simpa [hx0] using (bpow.pos binaryRadix fmt.minNormalExponent).trans_le hnormal
    have hm := minSubnormalExponent_le_of_normal fmt hnormal
    rw [magnitude_mul_bpow binaryRadix x e hx0] at hm
    exact genericRepresentable_flt_mul_bpow _ _ hprec hx e (by omega)

/-- Multiplication by an exactly represented power of two introduces no rounding if the
result is finite, which forces finite operands, and the shift is nonnegative or the result stays
normal (including zero). -/
theorem toReal_mul_pow_two_exact {fmt : FloatFormat} (x y : Model fmt) (e : ℤ)
    (hfmt : fmt.isIEEE = true)
    (hy : toReal y = Flocq.bpow binaryRadix e)
    (hrange : 0 ≤ e ∨ toReal x = 0 ∨ minNormalAt fmt ≤ |toReal x * Flocq.bpow binaryRadix e|)
    (hout : isFinite (mul x y) = true) :
    toReal (mul x y) = toReal x * toReal y := by
  rw [toReal_mul_eq_roundAt x y hfmt hout, hy]
  exact round_preserves_generic nearestEven _
    (genericFormat_mul_bpow fmt
      (toReal_genericFormat_of_isFinite x (isFinite_of_isFinite_mul hfmt hout).1) e hrange)

/-- A finite scaled value has a finite operand, in every encoding and rounding direction: scaling
returns an infinity unchanged and a NaN quieted. -/
theorem isFinite_of_isFinite_scale {fmt : FloatFormat} {x : Model fmt} {e : ℤ}
    {mode : IEEERoundingMode} (hout : isFinite (scale x e mode) = true) :
    isFinite x = true := by
  rw [← value_scale] at hout
  cases hexact : exactValue x with
  | finite d => exact isFinite_eq_true_of_toDyadic?_some (exactValue_eq_finite_iff.mp hexact)
  | infinity negative =>
      rwa [scale_status_of_infinity x e mode negative hexact] at hout
  | nan negative signaling payload =>
      rwa [scale_status_of_nan x e mode negative signaling payload hexact,
        isFinite_quietNaN] at hout

/-- Nearest-even exponent scaling rounds the exact real product by `2^e` once.
The exponent need not itself describe a representable floating-point value, and a finite result
forces a finite operand. -/
theorem toReal_scale_eq_roundAt {fmt : FloatFormat} (x : Model fmt) (e : ℤ)
    (hfmt : fmt.isIEEE = true) (hout : isFinite (scale x e) = true) :
    toReal (scale x e) = roundAt fmt (toReal x * Flocq.bpow binaryRadix e) := by
  have hx := isFinite_of_isFinite_scale hout
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hx
  have hscale : scale x e = roundDyadic fmt { d with exponent := d.exponent + e } := by
    have h := congrArg IEEEOutcome.value
      (scale_status_of_finite x e .nearest d (exactValue_eq_finite_of_toDyadic?_eq_some hd))
    exact h
  rw [hscale] at hout ⊢
  rw [toReal_roundDyadic_eq_roundAt fmt hfmt _ hout, toReal_eq, hd]
  congr 1
  simp only [Dyadic.toReal_mk, bpow.add_exp]
  rw [show d = Numerics.Dyadic.mk d.negative d.significand d.exponent from rfl,
    Dyadic.toReal_mk]
  ring

/-- Exponent scaling introduces no error if the result is finite and the shift is nonnegative,
the input is zero, or the scaled result stays normal. -/
theorem toReal_scale_exact {fmt : FloatFormat} (x : Model fmt) (e : ℤ)
    (hfmt : fmt.isIEEE = true)
    (hrange : 0 ≤ e ∨ toReal x = 0 ∨ minNormalAt fmt ≤ |toReal x * Flocq.bpow binaryRadix e|)
    (hout : isFinite (scale x e) = true) :
    toReal (scale x e) = toReal x * Flocq.bpow binaryRadix e := by
  rw [toReal_scale_eq_roundAt x e hfmt hout]
  exact round_preserves_generic nearestEven _
    (genericFormat_mul_bpow fmt
      (toReal_genericFormat_of_isFinite x (isFinite_of_isFinite_scale hout)) e hrange)

end FloatLib.Floats.Formats.BinaryInterchange.Model
