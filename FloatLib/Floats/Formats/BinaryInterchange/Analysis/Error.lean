/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Algebra.Order.Algebra
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.DivisionSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SqrtSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Subtraction
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Proof
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Addition
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Relative

/-!
# Error bounds for executable binary floats

These bounds relate operations on `Model fmt` to exact real arithmetic. `toReal` interprets finite
values in `ℝ`, and the format parameter picks the matching Flocq-style grid. That real-valued grid
has no upper exponent bound, so the executable operation theorems apply when the result is finite.

Infinities and NaNs have no real value, which is why each operation theorem asks for a finite
result. For addition, subtraction, multiplication, fused multiply-add and casts into an IEEE
destination, a finite result forces finite operands. Division keeps a finite divisor, because a
finite dividend over an infinity gives a signed zero, and square root keeps its finite nonnegative
domain. Both signed zeros have real value zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

/-- One unit in the last place at `x` for the precision and gradual-underflow grid of `fmt`. -/
noncomputable abbrev ulpAt (fmt : FloatFormat) (x : ℝ) : ℝ :=
  ulp Numerics.binaryRadix (fexpOf fmt) x

/-- Half an ULP at `x` for the precision and gradual-underflow grid of `fmt`. -/
noncomputable abbrev halfUlpAt (fmt : FloatFormat) (x : ℝ) : ℝ :=
  ulpAt fmt x / 2

/-- The least positive normal magnitude of `fmt`. -/
noncomputable abbrev minNormalAt (fmt : FloatFormat) : ℝ :=
  FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
    (FloatFormat.minNormalExponent fmt)

/-- The exponent-selection function of every executable format is monotone. -/
instance (fmt : FloatFormat) : MonotoneExp (fexpOf fmt) := by
  simpa [fexpOf] using
    (fltMonotoneExp (FloatFormat.minSubnormalExponent fmt)
      (Int.ofNat (fmt.fracWidth + 1)))

/--
Nearest-even rounding to `fmt` has at most half an ULP of absolute error.

The format-specific `halfUlpAt` follows the subnormal grid near zero, so this bound is useful even
where a uniform relative-error bound is impossible.
-/
theorem abs_roundAt_sub_le (fmt : FloatFormat) (x : ℝ) :
    |roundAt fmt x - x| ≤ halfUlpAt fmt x := by
  simpa [roundAt, halfUlpAt, ulpAt] using
    (error_bound_ulp
      (β := Numerics.binaryRadix) (fexp := fexpOf fmt) nearestEven x)

/-- The exact real input lies in the half-ULP enclosure around its rounded value. -/
theorem roundAt_mem_Icc (fmt : FloatFormat) (x : ℝ) :
    x ∈ Set.Icc
      (roundAt fmt x - halfUlpAt fmt x)
      (roundAt fmt x + halfUlpAt fmt x) := by
  have h := (abs_le.mp (abs_roundAt_sub_le fmt x))
  constructor <;> linarith

/--
The FLT normal-range threshold `minSubnormalExponent + precision - 1` is the minimum normal
exponent, so `minNormalAt fmt` is the FLT threshold of `fexpOf fmt`.
-/
theorem minSubnormalExponent_add_precision_sub_one (fmt : FloatFormat) :
    FloatFormat.minSubnormalExponent fmt + Int.ofNat (fmt.fracWidth + 1) - 1 =
      FloatFormat.minNormalExponent fmt := by
  simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
    Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
  ring

/--
Normal-range nearest-even rounding has the standard relative error bound
`2^(1-precision) / 2`.
-/
theorem relativeError_roundAt_le_of_normal (fmt : FloatFormat) (x : ℝ)
    (hx : x ≠ 0) (hnormal : minNormalAt fmt ≤ |x|) :
    ErrorBounds.relativeError x (roundAt fmt x) hx ≤
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (1 - Int.ofNat (fmt.fracWidth + 1)) / 2 := by
  have hprec : (0 : Int) < Int.ofNat (fmt.fracWidth + 1) :=
    Int.natCast_pos.mpr (Nat.succ_pos fmt.fracWidth)
  have hnormal' :
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (FloatFormat.minSubnormalExponent fmt + Int.ofNat (fmt.fracWidth + 1) - 1) ≤
        |x| := by
    rw [minSubnormalExponent_add_precision_sub_one]
    exact hnormal
  simpa [roundAt, fexpOf] using
    (relative_error_round_FLT_normal
      (β := Numerics.binaryRadix)
      (FloatFormat.minSubnormalExponent fmt)
      (Int.ofNat (fmt.fracWidth + 1))
      hprec nearestEven x hx hnormal')

/--
One IEEE addition with a finite result, which forces finite operands, is within half an ULP of the
exact sum. Near zero the bound follows the subnormal grid.
-/
theorem abs_toReal_add_sub_le {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hout : isFinite (add x y) = true) :
    |toReal (add x y) - (toReal x + toReal y)| ≤
      halfUlpAt fmt (toReal x + toReal y) := by
  rw [toReal_add_eq_roundAt x y hfmt hout]
  exact abs_roundAt_sub_le fmt (toReal x + toReal y)

/--
One IEEE subtraction with a finite result, which forces finite operands, is within half an ULP of
the exact difference. Near zero the bound follows the subnormal grid.
-/
theorem abs_toReal_sub_sub_le {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hout : isFinite (sub x y) = true) :
    |toReal (sub x y) - (toReal x - toReal y)| ≤
      halfUlpAt fmt (toReal x - toReal y) := by
  rw [toReal_sub_eq_roundAt x y hfmt hout]
  exact abs_roundAt_sub_le fmt (toReal x - toReal y)

/--
One IEEE multiplication with a finite result, which forces finite operands, is within half an ULP
of the exact product. Near zero the bound follows the subnormal grid.
-/
theorem abs_toReal_mul_sub_le {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hout : isFinite (mul x y) = true) :
    |toReal (mul x y) - toReal x * toReal y| ≤
      halfUlpAt fmt (toReal x * toReal y) := by
  rw [toReal_mul_eq_roundAt x y hfmt hout]
  exact abs_roundAt_sub_le fmt (toReal x * toReal y)

/--
One IEEE division by a finite divisor is within half an ULP of the exact quotient when the result
is finite, which forces a finite dividend and a nonzero divisor.
-/
theorem abs_toReal_div_sub_le {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hy : isFinite y = true) (hout : isFinite (div x y) = true) :
    |toReal (div x y) - toReal x / toReal y| ≤
      halfUlpAt fmt (toReal x / toReal y) := by
  rw [toReal_div_eq_roundAt x y hfmt hy hout]
  exact abs_roundAt_sub_le fmt (toReal x / toReal y)

/--
Absolute error of one finite executable square root on a nonnegative input, including either
signed zero.
-/
theorem abs_toReal_sqrt_sub_le {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true)
    (hdomain : isZero x = true ∨ signBit x = false) :
    |toReal (sqrt x) - Real.sqrt (toReal x)| ≤
      halfUlpAt fmt (Real.sqrt (toReal x)) := by
  rw [toReal_sqrt_eq_roundAt x hfmt hx hdomain]
  exact abs_roundAt_sub_le fmt (Real.sqrt (toReal x))

/--
One IEEE fused multiply-add, rounded once, is within half an ULP of `x * y + z` when the result is
finite, which forces finite operands.
-/
theorem abs_toReal_fma_sub_le {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hout : isFinite (fma x y z) = true) :
    |toReal (fma x y z) - (toReal x * toReal y + toReal z)| ≤
      halfUlpAt fmt (toReal x * toReal y + toReal z) := by
  rw [toReal_fma_eq_roundAt x y z hfmt hout]
  exact abs_roundAt_sub_le fmt (toReal x * toReal y + toReal z)

/--
A finite value whose magnitude fits in the destination's finite range stays finite under
conversion. With `abs_toReal_cast_sub_le` this discharges the output hypothesis from the input.
-/
theorem isFinite_cast_of_abs_toReal_le_posMaxFinite {src dst : FloatFormat} (x : Model src)
    (hdst : dst.isIEEE = true) (hx : isFinite x = true)
    (hbound : |toReal x| ≤ toReal (posMaxFinite dst)) :
    isFinite (cast src dst x) = true := by
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hx
  have hinf := isInf_eq_false_of_isFinite_eq_true x hx
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hx
  have hreal : toReal x = d.toReal := by rw [toReal_eq, hd]
  have hround := isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite
    dst hdst d (by simpa only [← hreal] using hbound)
  unfold cast Internal.Nearest.cast
  simp only [hnan, hinf, Bool.false_eq_true, ↓reduceDIte]
  split
  · next heq => cases heq; exact hx
  · split
    · split
      · split
        · split
          · exact isFinite_widenExact x _ _ _ _ hx
          · simpa only [finiteDyadic_eq_of_toDyadic _ hd] using hround
        · simpa only [finiteDyadic_eq_of_toDyadic _ hd] using hround
      · simpa only [finiteDyadic_eq_of_toDyadic _ hd] using hround
    · simpa only [finiteDyadic_eq_of_toDyadic _ hd] using hround

/--
A cast into an IEEE destination is within half a destination ULP of the source value when the
delivered result is finite, which forces a finite source. The source may be any binary
descriptor.
-/
theorem abs_toReal_cast_sub_le {src dst : FloatFormat} (x : Model src)
    (hdst : dst.isIEEE = true) (hout : isFinite (cast src dst x) = true) :
    |toReal (cast src dst x) - toReal x| ≤ halfUlpAt dst (toReal x) := by
  rw [cast_eq_roundAt hdst x hout]
  exact abs_roundAt_sub_le dst (toReal x)

/-- The exact sum lies in the half-ULP enclosure around a finite executable addition. -/
theorem add_exact_mem_Icc {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hout : isFinite (add x y) = true) :
    toReal x + toReal y ∈ Set.Icc
      (toReal (add x y) - halfUlpAt fmt (toReal x + toReal y))
      (toReal (add x y) + halfUlpAt fmt (toReal x + toReal y)) := by
  rw [toReal_add_eq_roundAt x y hfmt hout]
  exact roundAt_mem_Icc fmt (toReal x + toReal y)

/-- The exact difference lies in the half-ULP enclosure around a finite executable subtraction. -/
theorem sub_exact_mem_Icc {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hout : isFinite (sub x y) = true) :
    toReal x - toReal y ∈ Set.Icc
      (toReal (sub x y) - halfUlpAt fmt (toReal x - toReal y))
      (toReal (sub x y) + halfUlpAt fmt (toReal x - toReal y)) := by
  rw [toReal_sub_eq_roundAt x y hfmt hout]
  exact roundAt_mem_Icc fmt (toReal x - toReal y)

/-- The exact product lies in the half-ULP enclosure around a finite executable multiplication. -/
theorem mul_exact_mem_Icc {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hout : isFinite (mul x y) = true) :
    toReal x * toReal y ∈ Set.Icc
      (toReal (mul x y) - halfUlpAt fmt (toReal x * toReal y))
      (toReal (mul x y) + halfUlpAt fmt (toReal x * toReal y)) := by
  rw [toReal_mul_eq_roundAt x y hfmt hout]
  exact roundAt_mem_Icc fmt (toReal x * toReal y)

/--
The exact quotient lies in the half-ULP enclosure around a finite executable division by a finite
divisor.
-/
theorem div_exact_mem_Icc {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hy : isFinite y = true) (hout : isFinite (div x y) = true) :
    toReal x / toReal y ∈ Set.Icc
      (toReal (div x y) - halfUlpAt fmt (toReal x / toReal y))
      (toReal (div x y) + halfUlpAt fmt (toReal x / toReal y)) := by
  rw [toReal_div_eq_roundAt x y hfmt hy hout]
  exact roundAt_mem_Icc fmt (toReal x / toReal y)

/-- The exact square root lies in the half-ULP enclosure around executable square root. -/
theorem sqrt_exact_mem_Icc {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true)
    (hdomain : isZero x = true ∨ signBit x = false) :
    Real.sqrt (toReal x) ∈ Set.Icc
      (toReal (sqrt x) - halfUlpAt fmt (Real.sqrt (toReal x)))
      (toReal (sqrt x) + halfUlpAt fmt (Real.sqrt (toReal x))) := by
  rw [toReal_sqrt_eq_roundAt x hfmt hx hdomain]
  exact roundAt_mem_Icc fmt (Real.sqrt (toReal x))

/-- The exact multiply-add lies in the half-ULP enclosure around a finite executable FMA. -/
theorem fma_exact_mem_Icc {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hout : isFinite (fma x y z) = true) :
    toReal x * toReal y + toReal z ∈ Set.Icc
      (toReal (fma x y z) - halfUlpAt fmt (toReal x * toReal y + toReal z))
      (toReal (fma x y z) + halfUlpAt fmt (toReal x * toReal y + toReal z)) := by
  rw [toReal_fma_eq_roundAt x y z hfmt hout]
  exact roundAt_mem_Icc fmt (toReal x * toReal y + toReal z)

/--
The source real value lies in the half-ULP enclosure around a finite cast into an IEEE
destination. The source may be any binary descriptor.
-/
theorem cast_exact_mem_Icc {src dst : FloatFormat} (x : Model src)
    (hdst : dst.isIEEE = true) (hout : isFinite (cast src dst x) = true) :
    toReal x ∈ Set.Icc
      (toReal (cast src dst x) - halfUlpAt dst (toReal x))
      (toReal (cast src dst x) + halfUlpAt dst (toReal x)) := by
  rw [cast_eq_roundAt hdst x hout]
  exact roundAt_mem_Icc dst (toReal x)

/--
The residual of finite nearest-even addition lies on the precision and gradual-underflow grid of
`fmt`. This is representability on the real grid, which has no upper exponent bound, so the
theorem does not construct a finite `Model fmt` with that value. A finite sum forces finite
operands, so `hout` is the only finiteness assumption.
-/
theorem genericFormat_toReal_add_sub {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hout : isFinite (add x y) = true) :
    genericFormat Numerics.binaryRadix (fexpOf fmt)
      (toReal (add x y) - (toReal x + toReal y)) := by
  obtain ⟨hx, hy⟩ := isFinite_of_isFinite_add hfmt hout
  rw [toReal_add_eq_roundAt x y hfmt hout]
  exact add_round_error_generic
    (toReal_genericFormat_of_isFinite x hx)
    (toReal_genericFormat_of_isFinite y hy)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
