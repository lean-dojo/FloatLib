/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Sterbenz
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Classification.Predicates
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Proof
public import FloatLib.Numerics.MixedError.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Mixed error of binary arithmetic

Fix an IEEE descriptor `fmt` and write `u = unitRoundoffAt fmt` and `η = underflowErrorAt fmt`.
If the operands of a finite operation approximate exact reals `x₀` and `y₀` in the sense of
`MixedError`, we bound the decoded result against the same operation on `x₀` and `y₀`. The
constants are written out in terms of the operand constants, `u` and `η`, so a whole computation
is bounded by applying one theorem per operation.

Each bound composes the propagated operand error with the error of the final rounding, as in
`MixedError.trans`. Addition and subtraction round without an underflow term, so `η` does not
appear in their bounds. A sum of same-sign values, or a difference of values of opposite signs,
keeps a relative bound. With cancellation, the propagated operand error becomes absolute.

On finite operands, Sterbenz subtraction, `x - x`, negation, exact widening, `maximum` and
`minimum` do not round, so they carry only the operand errors. Sums and differences with a zero,
products with a zero or with a value of magnitude one, and the square root of a zero are exact
too. They are stated with the arithmetic semantics (`toReal_add_of_isZero_left` and its
siblings), and so are their decoded forms (`toRat?_sub_self`, `toRat?_add_of_representable` and
their siblings).

For sums, a left-to-right sum whose seed and terms have nonnegative exact values has relative error
growing like `(1 + u) ^ n` in the number `n` of additions. When the terms carry different errors,
each relative error is weighted by its own term. A sum of terms of either sign has an absolute
bound in terms of `Σ |term₀ i|`. Three smaller facts close the file: the partial sums of a finite
sum are finite, a sum of zeros keeps the value of its seed, and a sum from zero over a list without
repeated indices, in which every term but the one at `j` decodes to zero, is exact whatever its
length.

## Main results

* `Model.mixedError_roundAt`: the standard model as a mixed error.
* `Model.mixedError_toReal_add_of_mul_nonneg`: same-sign addition keeps relative error.
* `Model.mixedError_toReal_mul`, `Model.mixedError_toReal_div`: relative error of products and
  quotients.
* `Model.mixedError_toReal_foldl_add`, `Model.mixedError_toReal_foldl_add_weighted`: relative
  error of a sum of nonnegative terms.
* `Model.mixedError_toReal_foldl_add_absolute`: absolute error of a sum with cancellation.
* `Model.toRat?_foldl_add_eq_single`: a one-hot sum over a list without repeats is exact.
* `Model.isFinite_of_mem_scanl_add`: a finite sum has finite partial sums.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

variable {fmt : FloatFormat} {x y z : Model fmt} {x₀ y₀ z₀ r a rx ax ry ay rz az m : ℝ}

/-! ## Rounding -/

/--
Nearest-even rounding onto the grid of `fmt` has relative error `unitRoundoffAt fmt` and
absolute error `underflowErrorAt fmt`.
-/
theorem mixedError_roundAt (fmt : FloatFormat) (t : ℝ) :
    MixedError (roundAt fmt t) t (unitRoundoffAt fmt) (underflowErrorAt fmt) :=
  ⟨(unitRoundoffAt_pos fmt).le, (underflowErrorAt_pos fmt).le,
    abs_roundAt_sub_le_unitRoundoffAt fmt t⟩

/--
A value equal to the nearest-even rounding of `t` has the mixed error of rounding. Applied to a
correctly rounded function, this gives its implementation contract.
-/
theorem mixedError_toReal_of_eq_roundAt {v : Model fmt} {t : ℝ}
    (h : toReal v = roundAt fmt t) :
    MixedError (toReal v) t (unitRoundoffAt fmt) (underflowErrorAt fmt) :=
  h ▸ mixedError_roundAt fmt t

/--
In the normal range, nearest-even rounding has the pure relative error `unitRoundoffAt fmt`, with
absolute part zero.
-/
theorem mixedError_roundAt_of_minNormalAt_le (fmt : FloatFormat) {t : ℝ}
    (ht : minNormalAt fmt ≤ |t|) :
    MixedError (roundAt fmt t) t (unitRoundoffAt fmt) 0 := by
  refine MixedError.of_abs_sub_le_mul (unitRoundoffAt_pos fmt).le ?_
  calc |roundAt fmt t - t| ≤ ulpAt fmt t / 2 := abs_roundAt_sub_le fmt t
    _ ≤ Flocq.bpow Numerics.binaryRadix (1 - Int.ofNat (fmt.fracWidth + 1)) * |t| / 2 := by
      gcongr
      exact ulpAt_le_of_minNormalAt_le fmt ht
    _ = unitRoundoffAt fmt * |t| := by rw [← two_mul_unitRoundoffAt]; ring

/--
A natural number rounds with the pure relative error `unitRoundoffAt fmt`, with absolute part
zero: it is zero or at least the least positive normal magnitude.
-/
theorem mixedError_roundAt_natCast (fmt : FloatFormat) (n : ℕ) :
    MixedError (roundAt fmt n) n (unitRoundoffAt fmt) 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, roundAt_zero]
    exact (MixedError.refl 0).mono (unitRoundoffAt_pos fmt).le le_rfl
  · refine mixedError_roundAt_of_minNormalAt_le fmt ((minNormalAt_le_one fmt).trans ?_)
    rw [Nat.abs_cast]
    exact_mod_cast hn

/-! ## Addition and subtraction -/

/--
With `u = unitRoundoffAt fmt`, a finite sum has relative error `u` and absolute error
`(1 + u) * (rx * |x₀| + ax + (ry * |y₀| + ay))`. With cancellation, this absolute part can exceed
the exact sum.
-/
theorem mixedError_toReal_add (hfmt : fmt.isIEEE = true) (hout : isFinite (add x y) = true)
    (ex : MixedError (toReal x) x₀ rx ax) (ey : MixedError (toReal y) y₀ ry ay) :
    MixedError (toReal (add x y)) (x₀ + y₀) (unitRoundoffAt fmt)
      ((1 + unitRoundoffAt fmt) * (rx * |x₀| + ax + (ry * |y₀| + ay))) := by
  simpa only [mul_zero, zero_add, add_zero] using
    (MixedError.of_abs_sub_le_mul (unitRoundoffAt_pos fmt).le
      (abs_toReal_add_sub_le_unitRoundoffAt x y hfmt hout)).trans (ex.add ey)

/--
A finite sum of two values whose exact values have the same sign has relative error
`(1 + u) * max rx ry + u` and absolute error `(1 + u) * (ax + ay)`, with `u = unitRoundoffAt fmt`.
-/
theorem mixedError_toReal_add_of_mul_nonneg (hfmt : fmt.isIEEE = true)
    (hout : isFinite (add x y) = true)
    (ex : MixedError (toReal x) x₀ rx ax) (ey : MixedError (toReal y) y₀ ry ay)
    (hsign : 0 ≤ x₀ * y₀) :
    MixedError (toReal (add x y)) (x₀ + y₀)
      ((1 + unitRoundoffAt fmt) * max rx ry + unitRoundoffAt fmt)
      ((1 + unitRoundoffAt fmt) * (ax + ay)) := by
  simpa only [add_zero] using
    (MixedError.of_abs_sub_le_mul (unitRoundoffAt_pos fmt).le
      (abs_toReal_add_sub_le_unitRoundoffAt x y hfmt hout)).trans
      (ex.add_of_mul_nonneg ey hsign)

/--
With `u = unitRoundoffAt fmt`, a finite difference has relative error `u` and absolute error
`(1 + u) * (rx * |x₀| + ax + (ry * |y₀| + ay))`. With cancellation, this absolute part can exceed
the exact difference.
-/
theorem mixedError_toReal_sub (hfmt : fmt.isIEEE = true) (hout : isFinite (sub x y) = true)
    (ex : MixedError (toReal x) x₀ rx ax) (ey : MixedError (toReal y) y₀ ry ay) :
    MixedError (toReal (sub x y)) (x₀ - y₀) (unitRoundoffAt fmt)
      ((1 + unitRoundoffAt fmt) * (rx * |x₀| + ax + (ry * |y₀| + ay))) := by
  simpa only [mul_zero, zero_add, add_zero] using
    (MixedError.of_abs_sub_le_mul (unitRoundoffAt_pos fmt).le
      (abs_toReal_sub_sub_le_unitRoundoffAt x y hfmt hout)).trans (ex.sub ey)

/--
A finite difference of two values whose exact values have opposite signs has relative error
`(1 + u) * max rx ry + u` and absolute error `(1 + u) * (ax + ay)`, with `u = unitRoundoffAt fmt`.
-/
theorem mixedError_toReal_sub_of_mul_nonpos (hfmt : fmt.isIEEE = true)
    (hout : isFinite (sub x y) = true)
    (ex : MixedError (toReal x) x₀ rx ax) (ey : MixedError (toReal y) y₀ ry ay)
    (hsign : x₀ * y₀ ≤ 0) :
    MixedError (toReal (sub x y)) (x₀ - y₀)
      ((1 + unitRoundoffAt fmt) * max rx ry + unitRoundoffAt fmt)
      ((1 + unitRoundoffAt fmt) * (ax + ay)) := by
  simpa only [add_zero] using
    (MixedError.of_abs_sub_le_mul (unitRoundoffAt_pos fmt).le
      (abs_toReal_sub_sub_le_unitRoundoffAt x y hfmt hout)).trans
      (ex.sub_of_mul_nonpos ey hsign)

/--
Sterbenz subtraction adds no rounding error: for finite values of the same sign within a factor
of two, the difference has the pure absolute bound `rx * |x₀| + ax + (ry * |y₀| + ay)` of
`MixedError.sub`.
-/
theorem mixedError_toReal_sub_of_sterbenz (hfmt : fmt.isIEEE = true) (hx : isFinite x = true)
    (hy : isFinite y = true) (ex : MixedError (toReal x) x₀ rx ax)
    (ey : MixedError (toReal y) y₀ ry ay) (hsign : 0 ≤ toReal x * toReal y)
    (hxy : |toReal x| ≤ 2 * |toReal y|) (hyx : |toReal y| ≤ 2 * |toReal x|) :
    MixedError (toReal (sub x y)) (x₀ - y₀) 0 (rx * |x₀| + ax + (ry * |y₀| + ay)) := by
  rw [toReal_sub_eq_of_sterbenz_of_same_sign hfmt hx hy hsign hxy hyx]
  exact ex.sub ey

/-- Subtracting a finite value from itself has zero mixed error against `x₀ - x₀`, whatever the
error of the value. -/
theorem mixedError_toReal_sub_self (hfmt : fmt.isIEEE = true) (hx : isFinite x = true) :
    MixedError (toReal (sub x x)) (x₀ - x₀) 0 0 :=
  MixedError.of_eq (by rw [toReal_sub_self hfmt hx, sub_self])

/-! ## Multiplication, division and fused multiply-add -/

/--
A finite product has relative error `(1 + u) * (rx + ry + rx * ry) + u` and absolute error
`(1 + u) * ((1 + ry) * ax * |y₀| + (1 + rx) * ay * |x₀| + ax * ay) + η`, with
`u = unitRoundoffAt fmt` and `η = underflowErrorAt fmt`.
-/
theorem mixedError_toReal_mul (hfmt : fmt.isIEEE = true) (hout : isFinite (mul x y) = true)
    (ex : MixedError (toReal x) x₀ rx ax) (ey : MixedError (toReal y) y₀ ry ay) :
    MixedError (toReal (mul x y)) (x₀ * y₀)
      ((1 + unitRoundoffAt fmt) * (rx + ry + rx * ry) + unitRoundoffAt fmt)
      ((1 + unitRoundoffAt fmt) * ((1 + ry) * ax * |y₀| + (1 + rx) * ay * |x₀| + ax * ay) +
        underflowErrorAt fmt) := by
  rw [toReal_mul_eq_roundAt x y hfmt hout]
  exact (mixedError_roundAt fmt _).trans (ex.mul ey)

/--
A finite quotient by a finite divisor with pure relative error `ry < 1` (absolute part zero) has
relative error `(1 + u) * ((rx + ry) / (1 - ry)) + u` and absolute error
`(1 + u) * (ax / ((1 - ry) * |y₀|)) + η`, with `u = unitRoundoffAt fmt` and
`η = underflowErrorAt fmt`. The finite divisor is a separate premise: a finite value over an
infinity is a finite zero.
-/
theorem mixedError_toReal_div (hfmt : fmt.isIEEE = true) (hy : isFinite y = true)
    (hout : isFinite (div x y) = true)
    (ex : MixedError (toReal x) x₀ rx ax) (ey : MixedError (toReal y) y₀ ry 0) (hry : ry < 1) :
    MixedError (toReal (div x y)) (x₀ / y₀)
      ((1 + unitRoundoffAt fmt) * ((rx + ry) / (1 - ry)) + unitRoundoffAt fmt)
      ((1 + unitRoundoffAt fmt) * (ax / ((1 - ry) * |y₀|)) + underflowErrorAt fmt) := by
  rw [toReal_div_eq_roundAt x y hfmt hy hout]
  exact (mixedError_roundAt fmt _).trans (ex.div ey hry)

/--
A finite fused multiply-add rounds once. With `u = unitRoundoffAt fmt` and
`η = underflowErrorAt fmt`, it approximates the exact `x₀ * y₀ + z₀` with relative error `u` and
absolute error `(1 + u)` times the error bounds of the product, as in `MixedError.mul`, and of the
addend, plus `η`.
-/
theorem mixedError_toReal_fma (hfmt : fmt.isIEEE = true) (hout : isFinite (fma x y z) = true)
    (ex : MixedError (toReal x) x₀ rx ax) (ey : MixedError (toReal y) y₀ ry ay)
    (ez : MixedError (toReal z) z₀ rz az) :
    MixedError (toReal (fma x y z)) (x₀ * y₀ + z₀) (unitRoundoffAt fmt)
      ((1 + unitRoundoffAt fmt) * ((rx + ry + rx * ry) * |x₀ * y₀| +
        ((1 + ry) * ax * |y₀| + (1 + rx) * ay * |x₀| + ax * ay) + (rz * |z₀| + az)) +
        underflowErrorAt fmt) := by
  rw [toReal_fma_eq_roundAt x y z hfmt hout]
  simpa only [mul_zero, zero_add] using (mixedError_roundAt fmt _).trans ((ex.mul ey).add ez)

/-! ## Square root -/

/--
The square root of a finite value that is zero or has a clear sign bit, approximating a
nonnegative exact value, has relative error `(1 + u) * r + u` and absolute error
`(1 + u) * √a + η`, with `u = unitRoundoffAt fmt` and `η = underflowErrorAt fmt`. Both sign
conditions are premises: one on the encoded input, the other on the exact value.
-/
theorem mixedError_toReal_sqrt (hfmt : fmt.isIEEE = true) (hx : isFinite x = true)
    (hdomain : isZero x = true ∨ signBit x = false) (ex : MixedError (toReal x) x₀ r a)
    (hx₀ : 0 ≤ x₀) :
    MixedError (toReal (sqrt x)) (√x₀) ((1 + unitRoundoffAt fmt) * r + unitRoundoffAt fmt)
      ((1 + unitRoundoffAt fmt) * √a + underflowErrorAt fmt) := by
  rw [toReal_sqrt_eq_roundAt x hfmt hx hdomain]
  exact (mixedError_roundAt fmt _).trans (ex.sqrt hx₀)

/--
The square root of a finite value that is zero or has a clear sign bit, approximating an exact
value at least `m > 0`, has relative error `(1 + u) * r + u` and absolute error
`(1 + u) * (a / √m) + η`, with `u = unitRoundoffAt fmt` and `η = underflowErrorAt fmt`.
-/
theorem mixedError_toReal_sqrt_of_le (hfmt : fmt.isIEEE = true) (hx : isFinite x = true)
    (hdomain : isZero x = true ∨ signBit x = false) (ex : MixedError (toReal x) x₀ r a)
    (hm : 0 < m) (hmx : m ≤ x₀) :
    MixedError (toReal (sqrt x)) (√x₀) ((1 + unitRoundoffAt fmt) * r + unitRoundoffAt fmt)
      ((1 + unitRoundoffAt fmt) * (a / √m) + underflowErrorAt fmt) := by
  rw [toReal_sqrt_eq_roundAt x hfmt hx hdomain]
  exact (mixedError_roundAt fmt _).trans (ex.sqrt_of_le hm hmx)

/-! ## Conversion -/

/--
A finite cast to an IEEE destination has relative error `(1 + u) * r + u` and absolute error
`(1 + u) * a + η`, with `u = unitRoundoffAt dst` and `η = underflowErrorAt dst`.
-/
theorem mixedError_toReal_cast {src dst : FloatFormat} {x : Model src}
    (hdst : dst.isIEEE = true) (hout : isFinite (cast src dst x) = true)
    (ex : MixedError (toReal x) x₀ r a) :
    MixedError (toReal (cast src dst x)) x₀ ((1 + unitRoundoffAt dst) * r + unitRoundoffAt dst)
      ((1 + unitRoundoffAt dst) * a + underflowErrorAt dst) := by
  rw [cast_eq_roundAt hdst x hout]
  exact (mixedError_roundAt dst _).trans ex

/--
A finite cast into an IEEE destination whose grid contains the source's, with at least the
source's fraction width and a least subnormal exponent no larger, is exact and keeps the error of
its operand. The finite result is a premise: a finer grid can still have a smaller finite range.
-/
theorem mixedError_toReal_cast_of_gridExtension {src dst : FloatFormat} {x : Model src}
    (hdst : dst.isIEEE = true) (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hmin : dst.minSubnormalExponent ≤ src.minSubnormalExponent)
    (hout : isFinite (cast src dst x) = true) (ex : MixedError (toReal x) x₀ r a) :
    MixedError (toReal (cast src dst x)) x₀ r a := by
  rwa [cast_exact_of_gridExtension x hdst hfrac hmin hout]

/--
A widening cast of a finite value, with the same exponent width, bias and encoding and at least
the source's fraction width, is exact and keeps the error of its operand.
-/
theorem mixedError_toReal_cast_of_compatibleWidening {src dst : FloatFormat} {x : Model src}
    (hexp : src.expWidth = dst.expWidth) (hbias : src.exponentBias = dst.exponentBias)
    (hencoding : src.encoding = dst.encoding) (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hx : isFinite x = true) (ex : MixedError (toReal x) x₀ r a) :
    MixedError (toReal (cast src dst x)) x₀ r a := by
  rwa [cast_exact_of_compatibleWidening x hexp hbias hencoding hfrac hx]

/-! ## Negation, `maximum` and `minimum` -/

/-- Negation of a finite value is exact and keeps its error. -/
theorem mixedError_toReal_neg (hx : isFinite x = true) (ex : MixedError (toReal x) x₀ r a) :
    MixedError (toReal (neg x)) (-x₀) r a := by
  rw [toReal_neg x hx]
  exact ex.neg

/-- The IEEE `maximum` of finite values is exact and carries the larger operand error. -/
theorem mixedError_toReal_maximum (hx : isFinite x = true) (hy : isFinite y = true)
    (ex : MixedError (toReal x) x₀ rx ax) (ey : MixedError (toReal y) y₀ ry ay) :
    MixedError (toReal (maximum x y)) (max x₀ y₀) 0 (max (rx * |x₀| + ax) (ry * |y₀| + ay)) := by
  rw [toReal_maximum_eq_max_of_isFinite x y hx hy]
  exact ex.max ey

/--
The IEEE `maximum` of finite values with nonnegative exact values has relative error `max rx ry`
and absolute error `max ax ay`.
-/
theorem mixedError_toReal_maximum_of_nonneg (hx : isFinite x = true) (hy : isFinite y = true)
    (ex : MixedError (toReal x) x₀ rx ax) (ey : MixedError (toReal y) y₀ ry ay)
    (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) :
    MixedError (toReal (maximum x y)) (max x₀ y₀) (max rx ry) (max ax ay) := by
  rw [toReal_maximum_eq_max_of_isFinite x y hx hy]
  exact ex.max_of_nonneg ey hx₀ hy₀

/-- The IEEE `minimum` of finite values is exact and carries the larger operand error. -/
theorem mixedError_toReal_minimum (hx : isFinite x = true) (hy : isFinite y = true)
    (ex : MixedError (toReal x) x₀ rx ax) (ey : MixedError (toReal y) y₀ ry ay) :
    MixedError (toReal (minimum x y)) (min x₀ y₀) 0 (max (rx * |x₀| + ax) (ry * |y₀| + ay)) := by
  rw [toReal_minimum_eq_min_of_isFinite x y hx hy]
  exact ex.min ey

/--
The IEEE `minimum` of finite values with nonpositive exact values has relative error `max rx ry`
and absolute error `max ax ay`.
-/
theorem mixedError_toReal_minimum_of_nonpos (hx : isFinite x = true) (hy : isFinite y = true)
    (ex : MixedError (toReal x) x₀ rx ax) (ey : MixedError (toReal y) y₀ ry ay)
    (hx₀ : x₀ ≤ 0) (hy₀ : y₀ ≤ 0) :
    MixedError (toReal (minimum x y)) (min x₀ y₀) (max rx ry) (max ax ay) := by
  rw [toReal_minimum_eq_min_of_isFinite x y hx hy]
  exact ex.min_of_nonpos ey hx₀ hy₀

/-! ## Sums of nonnegative terms -/

section Sum

variable {ι : Type*} {l : List ι} {term : ι → Model fmt} {term₀ rel err : ι → ℝ}
  {seed : Model fmt} {seed₀ d e R A B : ℝ} {n : ℕ}

/-- Every partial sum of a finite left-to-right sum is finite, whatever the signs of the terms. -/
theorem isFinite_of_mem_scanl_add (hfmt : fmt.isIEEE = true)
    (hsum : isFinite (l.foldl (fun acc i => add acc (term i)) seed) = true) {v : Model fmt}
    (hv : v ∈ l.scanl (fun acc i => add acc (term i)) seed) : isFinite v = true := by
  induction l generalizing seed v with
  | nil => simp_all
  | cons i l ih =>
    rw [List.foldl_cons] at hsum
    have hhead : isFinite (add seed (term i)) = true := ih hsum (by cases l <;> simp)
    rw [List.scanl_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact (isFinite_of_isFinite_add hfmt hhead).1
    · exact ih hsum hv

/--
The step of `mixedError_toReal_foldl_add`, one addition of a left-to-right sum of nonnegative
terms. With `u = unitRoundoffAt fmt`, an accumulator with relative error
`(1 + u) ^ n * (1 + R) - 1` and absolute error
`(1 + u) ^ n * d`, plus a term with relative error `r ≤ R` and absolute error `e`, gives the same
form with `n + 1` and `d + e`.
-/
theorem mixedError_toReal_foldl_add_step (hfmt : fmt.isIEEE = true)
    (hout : isFinite (add x y) = true)
    (ex : MixedError (toReal x) x₀ ((1 + unitRoundoffAt fmt) ^ n * (1 + R) - 1)
      ((1 + unitRoundoffAt fmt) ^ n * d))
    (ey : MixedError (toReal y) y₀ r e) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) (hrR : r ≤ R) :
    MixedError (toReal (add x y)) (x₀ + y₀)
      ((1 + unitRoundoffAt fmt) ^ (n + 1) * (1 + R) - 1)
      ((1 + unitRoundoffAt fmt) ^ (n + 1) * (d + e)) := by
  have hu := (unitRoundoffAt_pos fmt).le
  have he := ey.a_nonneg
  have hpow : 1 ≤ (1 + unitRoundoffAt fmt) ^ n := one_le_pow₀ (by linarith)
  have hR : r ≤ (1 + unitRoundoffAt fmt) ^ n * (1 + R) - 1 := by
    nlinarith [ex.r_nonneg, ey.r_nonneg]
  refine (mixedError_toReal_add_of_mul_nonneg hfmt hout ex ey
    (mul_nonneg hx₀ hy₀)).mono (le_of_eq ?_) ?_
  · rw [max_eq_left hR, pow_succ]
    ring
  · rw [pow_succ]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ 1 + unitRoundoffAt fmt) he)
      (sub_nonneg.2 hpow)]

/-- `mixedError_toReal_foldl_add` from an accumulator that already carries `n` additions. -/
private theorem mixedError_toReal_foldl_add_pow_add (hfmt : fmt.isIEEE = true) (hrR : r ≤ R)
    (hterm : ∀ i ∈ l, isFinite (term i) = true)
    (eterm : ∀ i ∈ l, MixedError (toReal (term i)) (term₀ i) r (err i))
    (hterm₀ : ∀ i ∈ l, 0 ≤ term₀ i)
    (hfinite : ∀ v ∈ l.scanl (fun acc i => add acc (term i)) seed, isFinite v = true)
    (eseed : MixedError (toReal seed) seed₀ ((1 + unitRoundoffAt fmt) ^ n * (1 + R) - 1)
      ((1 + unitRoundoffAt fmt) ^ n * d))
    (hseed₀ : 0 ≤ seed₀) :
    MixedError (toReal (l.foldl (fun acc i => add acc (term i)) seed))
      (seed₀ + (l.map term₀).sum)
      ((1 + unitRoundoffAt fmt) ^ (n + l.length) * (1 + R) - 1)
      ((1 + unitRoundoffAt fmt) ^ (n + l.length) * (d + (l.map err).sum)) := by
  induction l generalizing seed seed₀ d n with
  | nil => simpa using eseed
  | cons i l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hterm eterm hterm₀
    simp only [List.scanl_cons, List.mem_cons, forall_eq_or_imp] at hfinite
    have hnext : isFinite (add seed (term i)) = true := hfinite.2 _ (by cases l <;> simp)
    have := ih hterm.2 eterm.2 hterm₀.2 hfinite.2
      (mixedError_toReal_foldl_add_step hfmt hnext eseed eterm.1 hseed₀
        hterm₀.1 hrR) (add_nonneg hseed₀ hterm₀.1)
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, List.length_cons]
    rwa [show n + (l.length + 1) = n + 1 + l.length by omega, ← add_assoc seed₀,
      ← add_assoc d]

/--
A left-to-right sum `l.foldl (fun acc i => add acc (term i)) seed` with nonnegative exact seed and
terms keeps relative accuracy. With `u = unitRoundoffAt fmt`, relative error `r` on the seed and
every term, and absolute errors `d` and `err i`, the result has relative error
`(1 + u) ^ l.length * (1 + r) - 1` and absolute error `(1 + u) ^ l.length * (d + Σ err i)`.
For `r = 0` and an exact seed, `d = 0`, this reads
`|Ŝ - S| ≤ ((1 + u) ^ n - 1) * S + (1 + u) ^ n * Σ err i`. Every partial sum must be finite, which
`isFinite_of_mem_scanl_add` derives from a finite result.
-/
theorem mixedError_toReal_foldl_add (hfmt : fmt.isIEEE = true)
    (hfinite : ∀ v ∈ l.scanl (fun acc i => add acc (term i)) seed, isFinite v = true)
    (hterm : ∀ i ∈ l, isFinite (term i) = true) (eseed : MixedError (toReal seed) seed₀ r d)
    (eterm : ∀ i ∈ l, MixedError (toReal (term i)) (term₀ i) r (err i))
    (hseed₀ : 0 ≤ seed₀) (hterm₀ : ∀ i ∈ l, 0 ≤ term₀ i) :
    MixedError (toReal (l.foldl (fun acc i => add acc (term i)) seed))
      (seed₀ + (l.map term₀).sum)
      ((1 + unitRoundoffAt fmt) ^ l.length * (1 + r) - 1)
      ((1 + unitRoundoffAt fmt) ^ l.length * (d + (l.map err).sum)) := by
  simpa using mixedError_toReal_foldl_add_pow_add hfmt le_rfl hterm eterm hterm₀ hfinite
    (n := 0) (by simpa using eseed) hseed₀

/--
A left-to-right sum from a seed of real value zero, of terms with nonnegative exact values,
relative error `r` and absolute errors `err i`, has relative error
`(1 + u) ^ (l.length - 1) * (1 + r) - 1` and absolute error `(1 + u) ^ (l.length - 1) * Σ err i`,
with `u = unitRoundoffAt fmt`. The first addition is exact, so `n` terms take `n - 1` roundings,
with natural subtraction: the empty sum has exponent `0`.
-/
theorem mixedError_toReal_foldl_add_of_toReal_eq_zero (hfmt : fmt.isIEEE = true)
    (hseed : toReal seed = 0)
    (hfinite : ∀ v ∈ l.scanl (fun acc i => add acc (term i)) seed, isFinite v = true)
    (hterm : ∀ i ∈ l, isFinite (term i) = true)
    (eterm : ∀ i ∈ l, MixedError (toReal (term i)) (term₀ i) r (err i))
    (hr : 0 ≤ r) (hterm₀ : ∀ i ∈ l, 0 ≤ term₀ i) :
    MixedError (toReal (l.foldl (fun acc i => add acc (term i)) seed)) (l.map term₀).sum
      ((1 + unitRoundoffAt fmt) ^ (l.length - 1) * (1 + r) - 1)
      ((1 + unitRoundoffAt fmt) ^ (l.length - 1) * (l.map err).sum) := by
  cases l with
  | nil => simpa [hseed] using (⟨hr, le_rfl, by simp⟩ : MixedError 0 0 r 0)
  | cons i l =>
    simp only [List.mem_cons, forall_eq_or_imp] at hterm eterm hterm₀
    simp only [List.scanl_cons, List.mem_cons, forall_eq_or_imp] at hfinite
    have hnext : isFinite (add seed (term i)) = true := hfinite.2 _ (by cases l <;> simp)
    have hfirst : toReal (add seed (term i)) = toReal (term i) := by
      rw [toReal_add_eq_roundAt _ _ hfmt hnext, hseed, zero_add,
        roundAt_toReal_eq _ hterm.1]
    simpa using mixedError_toReal_foldl_add hfmt hfinite.2 hterm.2 (hfirst ▸ eterm.1) eterm.2
      hterm₀.1 hterm₀.2

/--
A left-to-right sum of terms with nonnegative exact values and their own mixed errors
`(rel i, err i)`, from a seed with nonnegative exact value and pure absolute error `d`, has
relative error `(1 + u) ^ l.length - 1` and absolute error
`(1 + u) ^ l.length * (d + Σ (rel i * term₀ i + err i))`, with `u = unitRoundoffAt fmt`. Each
relative error is weighted by its own term instead of being bounded by the largest one.
-/
theorem mixedError_toReal_foldl_add_weighted (hfmt : fmt.isIEEE = true)
    (hfinite : ∀ v ∈ l.scanl (fun acc i => add acc (term i)) seed, isFinite v = true)
    (hterm : ∀ i ∈ l, isFinite (term i) = true) (eseed : MixedError (toReal seed) seed₀ 0 d)
    (eterm : ∀ i ∈ l, MixedError (toReal (term i)) (term₀ i) (rel i) (err i))
    (hseed₀ : 0 ≤ seed₀) (hterm₀ : ∀ i ∈ l, 0 ≤ term₀ i) :
    MixedError (toReal (l.foldl (fun acc i => add acc (term i)) seed))
      (seed₀ + (l.map term₀).sum) ((1 + unitRoundoffAt fmt) ^ l.length - 1)
      ((1 + unitRoundoffAt fmt) ^ l.length *
        (d + (l.map fun i => rel i * term₀ i + err i).sum)) := by
  simpa using mixedError_toReal_foldl_add hfmt hfinite hterm eseed
    (fun i hi => (eterm i hi).absolute_of_abs_le (abs_of_nonneg (hterm₀ i hi)).le) hseed₀ hterm₀

/--
The bound of `mixedError_toReal_foldl_add_weighted` from a seed of real value zero, with no seed
error and `l.length - 1` in place of `l.length`, in natural subtraction: the first addition is
exact.
-/
theorem mixedError_toReal_foldl_add_weighted_of_toReal_eq_zero (hfmt : fmt.isIEEE = true)
    (hseed : toReal seed = 0)
    (hfinite : ∀ v ∈ l.scanl (fun acc i => add acc (term i)) seed, isFinite v = true)
    (hterm : ∀ i ∈ l, isFinite (term i) = true)
    (eterm : ∀ i ∈ l, MixedError (toReal (term i)) (term₀ i) (rel i) (err i))
    (hterm₀ : ∀ i ∈ l, 0 ≤ term₀ i) :
    MixedError (toReal (l.foldl (fun acc i => add acc (term i)) seed)) (l.map term₀).sum
      ((1 + unitRoundoffAt fmt) ^ (l.length - 1) - 1)
      ((1 + unitRoundoffAt fmt) ^ (l.length - 1) *
        (l.map fun i => rel i * term₀ i + err i).sum) := by
  simpa using mixedError_toReal_foldl_add_of_toReal_eq_zero hfmt hseed hfinite hterm
    (fun i hi => (eterm i hi).absolute_of_abs_le (abs_of_nonneg (hterm₀ i hi)).le) le_rfl hterm₀

/-! ## Sums with cancellation -/

/--
The step of `mixedError_toReal_foldl_add_absolute`, one addition of a left-to-right sum of terms of
either sign. With `u = unitRoundoffAt fmt`, an accumulator with absolute error
`((1 + u) ^ n - 1) * A + (1 + u) ^ n * B`, where `|x₀| ≤ A`, plus a term with mixed error
`(r, e)`, gives the same form with `n + 1`, `A + |y₀|` and `B + (r * |y₀| + e)`.
-/
theorem mixedError_toReal_foldl_add_absolute_step (hfmt : fmt.isIEEE = true)
    (hout : isFinite (add x y) = true)
    (ex : MixedError (toReal x) x₀ 0
      (((1 + unitRoundoffAt fmt) ^ n - 1) * A + (1 + unitRoundoffAt fmt) ^ n * B))
    (hA : |x₀| ≤ A) (ey : MixedError (toReal y) y₀ r e) :
    MixedError (toReal (add x y)) (x₀ + y₀) 0
      (((1 + unitRoundoffAt fmt) ^ (n + 1) - 1) * (A + |y₀|) +
        (1 + unitRoundoffAt fmt) ^ (n + 1) * (B + (r * |y₀| + e))) := by
  have hu := (unitRoundoffAt_pos fmt).le
  have hpow : 1 ≤ (1 + unitRoundoffAt fmt) ^ n := one_le_pow₀ (by linarith)
  have he : 0 ≤ r * |y₀| + e := add_nonneg (mul_nonneg ey.r_nonneg (abs_nonneg _)) ey.a_nonneg
  have hgap : 0 ≤ (1 + unitRoundoffAt fmt) * ((1 + unitRoundoffAt fmt) ^ n - 1) *
      (|y₀| + (r * |y₀| + e)) := by
    have := sub_nonneg.2 hpow
    positivity
  refine ((mixedError_toReal_add hfmt hout ex ey).absolute_of_abs_le
    ((abs_add_le x₀ y₀).trans (add_le_add hA le_rfl))).mono le_rfl ?_
  rw [pow_succ]
  nlinarith

/--
`mixedError_toReal_foldl_add_absolute` from an accumulator that already carries `n` additions.
-/
private theorem mixedError_toReal_foldl_add_absolute_pow_add (hfmt : fmt.isIEEE = true)
    (hterm : ∀ i ∈ l, isFinite (term i) = true)
    (eterm : ∀ i ∈ l, MixedError (toReal (term i)) (term₀ i) (rel i) (err i))
    (hfinite : ∀ v ∈ l.scanl (fun acc i => add acc (term i)) seed, isFinite v = true)
    (eseed : MixedError (toReal seed) seed₀ 0
      (((1 + unitRoundoffAt fmt) ^ n - 1) * A + (1 + unitRoundoffAt fmt) ^ n * B))
    (hA : |seed₀| ≤ A) :
    MixedError (toReal (l.foldl (fun acc i => add acc (term i)) seed))
      (seed₀ + (l.map term₀).sum) 0
      (((1 + unitRoundoffAt fmt) ^ (n + l.length) - 1) * (A + (l.map fun i => |term₀ i|).sum) +
        (1 + unitRoundoffAt fmt) ^ (n + l.length) *
          (B + (l.map fun i => rel i * |term₀ i| + err i).sum)) := by
  induction l generalizing seed seed₀ A B n with
  | nil => simpa using eseed
  | cons i l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hterm eterm
    simp only [List.scanl_cons, List.mem_cons, forall_eq_or_imp] at hfinite
    have hnext : isFinite (add seed (term i)) = true := hfinite.2 _ (by cases l <;> simp)
    have := ih hterm.2 eterm.2 hfinite.2
      (mixedError_toReal_foldl_add_absolute_step hfmt hnext eseed hA eterm.1)
      ((abs_add_le _ _).trans (add_le_add hA le_rfl))
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, List.length_cons]
    rwa [show n + (l.length + 1) = n + 1 + l.length by omega, ← add_assoc seed₀, ← add_assoc A,
      ← add_assoc B]

/--
A left-to-right sum of terms of any sign, with mixed errors `(rel i, err i)` and a seed with pure
absolute error `d`, has the pure absolute bound
`((1 + u) ^ n - 1) * (|seed₀| + Σ |term₀ i|) + (1 + u) ^ n * (d + Σ (rel i * |term₀ i| + err i))`
for `n = l.length` additions and `u = unitRoundoffAt fmt`, provided every partial sum is finite.
With cancellation this can exceed the exact sum, so no relative bound is claimed.
-/
theorem mixedError_toReal_foldl_add_absolute (hfmt : fmt.isIEEE = true)
    (hfinite : ∀ v ∈ l.scanl (fun acc i => add acc (term i)) seed, isFinite v = true)
    (hterm : ∀ i ∈ l, isFinite (term i) = true) (eseed : MixedError (toReal seed) seed₀ 0 d)
    (eterm : ∀ i ∈ l, MixedError (toReal (term i)) (term₀ i) (rel i) (err i)) :
    MixedError (toReal (l.foldl (fun acc i => add acc (term i)) seed))
      (seed₀ + (l.map term₀).sum) 0
      (((1 + unitRoundoffAt fmt) ^ l.length - 1) * (|seed₀| + (l.map fun i => |term₀ i|).sum) +
        (1 + unitRoundoffAt fmt) ^ l.length *
          (d + (l.map fun i => rel i * |term₀ i| + err i).sum)) := by
  simpa using mixedError_toReal_foldl_add_absolute_pow_add hfmt hterm eterm hfinite (n := 0)
    (by simpa using eseed) le_rfl

/--
The bound of `mixedError_toReal_foldl_add_absolute` from a seed of real value zero, with no seed
terms and `l.length - 1` in place of `l.length`, in natural subtraction: the first addition is
exact.
-/
theorem mixedError_toReal_foldl_add_absolute_of_toReal_eq_zero (hfmt : fmt.isIEEE = true)
    (hseed : toReal seed = 0)
    (hfinite : ∀ v ∈ l.scanl (fun acc i => add acc (term i)) seed, isFinite v = true)
    (hterm : ∀ i ∈ l, isFinite (term i) = true)
    (eterm : ∀ i ∈ l, MixedError (toReal (term i)) (term₀ i) (rel i) (err i)) :
    MixedError (toReal (l.foldl (fun acc i => add acc (term i)) seed)) (l.map term₀).sum 0
      (((1 + unitRoundoffAt fmt) ^ (l.length - 1) - 1) * (l.map fun i => |term₀ i|).sum +
        (1 + unitRoundoffAt fmt) ^ (l.length - 1) *
          (l.map fun i => rel i * |term₀ i| + err i).sum) := by
  cases l with
  | nil => simp [hseed]
  | cons i l =>
    simp only [List.mem_cons, forall_eq_or_imp] at hterm eterm
    simp only [List.scanl_cons, List.mem_cons, forall_eq_or_imp] at hfinite
    have hnext : isFinite (add seed (term i)) = true := hfinite.2 _ (by cases l <;> simp)
    have hfirst : toReal (add seed (term i)) = toReal (term i) := by
      rw [toReal_add_eq_roundAt _ _ hfmt hnext, hseed, zero_add,
        roundAt_toReal_eq _ hterm.1]
    simpa only [List.foldl_cons, List.map_cons, List.sum_cons, List.length_cons,
      Nat.add_sub_cancel] using mixedError_toReal_foldl_add_absolute hfmt hfinite.2 hterm.2
        (hfirst ▸ eterm.1.absolute_of_abs_le le_rfl) eterm.2

/-! ## Exact sums -/

/-- Adding terms that decode to zero leaves the decoded value of the seed unchanged. -/
theorem toRat?_foldl_add_of_eq_zero (hfmt : fmt.isIEEE = true) {q : ℚ}
    (hseed : toRat? seed = some q) (hterm : ∀ i ∈ l, toRat? (term i) = some 0) :
    toRat? (l.foldl (fun acc i => add acc (term i)) seed) = some q := by
  induction l generalizing seed with
  | nil => exact hseed
  | cons i l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hterm
    exact ih (toRat?_add_of_toRat?_eq_some_zero_right hfmt hseed hterm.1) hterm.2

/--
A left-to-right sum over a list `l` without repeated indices (`l.Nodup`) that contains `j`, from
a seed that decodes to zero, whose terms all decode to zero except the one at `j`, decodes to that
term's value, whatever its length. With a term `1` or `-1` this is a one-hot sum.
-/
theorem toRat?_foldl_add_eq_single (hfmt : fmt.isIEEE = true) {j : ι} {q : ℚ} (hl : l.Nodup)
    (hj : j ∈ l) (hseed : toRat? seed = some 0) (hterm : toRat? (term j) = some q)
    (hzero : ∀ i ∈ l, i ≠ j → toRat? (term i) = some 0) :
    toRat? (l.foldl (fun acc i => add acc (term i)) seed) = some q := by
  induction l generalizing seed with
  | nil => simp at hj
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldl_cons]
    by_cases hij : i = j
    · subst hij
      exact toRat?_foldl_add_of_eq_zero hfmt
        (toRat?_add_of_toRat?_eq_some_zero_left hfmt hseed hterm)
        fun k hk => hzero k (List.mem_cons_of_mem _ hk) fun h => hl.1 (h ▸ hk)
    · exact ih hl.2 ((List.mem_cons.1 hj).resolve_left (Ne.symm hij))
        (toRat?_add_of_toRat?_eq_some_zero_left hfmt hseed (hzero i (by simp) hij))
        fun k hk => hzero k (List.mem_cons_of_mem _ hk)

end Sum

section FinSum

variable {n : ℕ} {term : Fin n → Model fmt} {term₀ rel err : Fin n → ℝ} {seed : Model fmt}
  {seed₀ d : ℝ}

/-- Every partial sum of a finite sum computed by `Fin.foldl` is finite. -/
theorem isFinite_of_mem_finRange_scanl_add (hfmt : fmt.isIEEE = true)
    (hsum : isFinite (Fin.foldl n (fun acc i => add acc (term i)) seed) = true) {v : Model fmt}
    (hv : v ∈ (List.finRange n).scanl (fun acc i => add acc (term i)) seed) :
    isFinite v = true :=
  isFinite_of_mem_scanl_add hfmt (by rwa [Fin.foldl_eq_finRange_foldl] at hsum) hv

/-- The bound of `mixedError_toReal_foldl_add` for a sum of `n` terms computed by `Fin.foldl`. -/
theorem mixedError_toReal_fin_foldl_add (hfmt : fmt.isIEEE = true)
    (hfinite : ∀ v ∈ (List.finRange n).scanl (fun acc i => add acc (term i)) seed,
      isFinite v = true)
    (hterm : ∀ i, isFinite (term i) = true) (eseed : MixedError (toReal seed) seed₀ r d)
    (eterm : ∀ i, MixedError (toReal (term i)) (term₀ i) r (err i))
    (hseed₀ : 0 ≤ seed₀) (hterm₀ : ∀ i, 0 ≤ term₀ i) :
    MixedError (toReal (Fin.foldl n (fun acc i => add acc (term i)) seed)) (seed₀ + ∑ i, term₀ i)
      ((1 + unitRoundoffAt fmt) ^ n * (1 + r) - 1)
      ((1 + unitRoundoffAt fmt) ^ n * (d + ∑ i, err i)) := by
  rw [Fin.foldl_eq_finRange_foldl, Fin.sum_univ_def, Fin.sum_univ_def]
  simpa using mixedError_toReal_foldl_add hfmt hfinite (fun i _ => hterm i) eseed
    (fun i _ => eterm i) hseed₀ fun i _ => hterm₀ i

/--
The bound of `mixedError_toReal_foldl_add_of_toReal_eq_zero` for a sum of `n` terms computed by
`Fin.foldl`.
-/
theorem mixedError_toReal_fin_foldl_add_of_toReal_eq_zero (hfmt : fmt.isIEEE = true)
    (hseed : toReal seed = 0)
    (hfinite : ∀ v ∈ (List.finRange n).scanl (fun acc i => add acc (term i)) seed,
      isFinite v = true)
    (hterm : ∀ i, isFinite (term i) = true)
    (eterm : ∀ i, MixedError (toReal (term i)) (term₀ i) r (err i))
    (hr : 0 ≤ r) (hterm₀ : ∀ i, 0 ≤ term₀ i) :
    MixedError (toReal (Fin.foldl n (fun acc i => add acc (term i)) seed)) (∑ i, term₀ i)
      ((1 + unitRoundoffAt fmt) ^ (n - 1) * (1 + r) - 1)
      ((1 + unitRoundoffAt fmt) ^ (n - 1) * ∑ i, err i) := by
  rw [Fin.foldl_eq_finRange_foldl, Fin.sum_univ_def, Fin.sum_univ_def]
  simpa using mixedError_toReal_foldl_add_of_toReal_eq_zero hfmt hseed hfinite
    (fun i _ => hterm i) (fun i _ => eterm i) hr fun i _ => hterm₀ i

/--
The bound of `mixedError_toReal_foldl_add_weighted` for a sum of `n` terms computed by
`Fin.foldl`.
-/
theorem mixedError_toReal_fin_foldl_add_weighted (hfmt : fmt.isIEEE = true)
    (hfinite : ∀ v ∈ (List.finRange n).scanl (fun acc i => add acc (term i)) seed,
      isFinite v = true)
    (hterm : ∀ i, isFinite (term i) = true) (eseed : MixedError (toReal seed) seed₀ 0 d)
    (eterm : ∀ i, MixedError (toReal (term i)) (term₀ i) (rel i) (err i))
    (hseed₀ : 0 ≤ seed₀) (hterm₀ : ∀ i, 0 ≤ term₀ i) :
    MixedError (toReal (Fin.foldl n (fun acc i => add acc (term i)) seed)) (seed₀ + ∑ i, term₀ i)
      ((1 + unitRoundoffAt fmt) ^ n - 1)
      ((1 + unitRoundoffAt fmt) ^ n * (d + ∑ i, (rel i * term₀ i + err i))) := by
  rw [Fin.foldl_eq_finRange_foldl]
  simp only [Fin.sum_univ_def]
  simpa using mixedError_toReal_foldl_add_weighted hfmt hfinite (fun i _ => hterm i) eseed
    (fun i _ => eterm i) hseed₀ fun i _ => hterm₀ i

/--
The bound of `mixedError_toReal_foldl_add_weighted_of_toReal_eq_zero` for a sum of `n` terms
computed by `Fin.foldl`.
-/
theorem mixedError_toReal_fin_foldl_add_weighted_of_toReal_eq_zero (hfmt : fmt.isIEEE = true)
    (hseed : toReal seed = 0)
    (hfinite : ∀ v ∈ (List.finRange n).scanl (fun acc i => add acc (term i)) seed,
      isFinite v = true)
    (hterm : ∀ i, isFinite (term i) = true)
    (eterm : ∀ i, MixedError (toReal (term i)) (term₀ i) (rel i) (err i))
    (hterm₀ : ∀ i, 0 ≤ term₀ i) :
    MixedError (toReal (Fin.foldl n (fun acc i => add acc (term i)) seed)) (∑ i, term₀ i)
      ((1 + unitRoundoffAt fmt) ^ (n - 1) - 1)
      ((1 + unitRoundoffAt fmt) ^ (n - 1) * ∑ i, (rel i * term₀ i + err i)) := by
  rw [Fin.foldl_eq_finRange_foldl]
  simp only [Fin.sum_univ_def]
  simpa using mixedError_toReal_foldl_add_weighted_of_toReal_eq_zero hfmt hseed hfinite
    (fun i _ => hterm i) (fun i _ => eterm i) fun i _ => hterm₀ i

/--
The bound of `mixedError_toReal_foldl_add_absolute` for a sum of `n` terms computed by
`Fin.foldl`.
-/
theorem mixedError_toReal_fin_foldl_add_absolute (hfmt : fmt.isIEEE = true)
    (hfinite : ∀ v ∈ (List.finRange n).scanl (fun acc i => add acc (term i)) seed,
      isFinite v = true)
    (hterm : ∀ i, isFinite (term i) = true) (eseed : MixedError (toReal seed) seed₀ 0 d)
    (eterm : ∀ i, MixedError (toReal (term i)) (term₀ i) (rel i) (err i)) :
    MixedError (toReal (Fin.foldl n (fun acc i => add acc (term i)) seed)) (seed₀ + ∑ i, term₀ i)
      0 (((1 + unitRoundoffAt fmt) ^ n - 1) * (|seed₀| + ∑ i, |term₀ i|) +
        (1 + unitRoundoffAt fmt) ^ n * (d + ∑ i, (rel i * |term₀ i| + err i))) := by
  rw [Fin.foldl_eq_finRange_foldl]
  simp only [Fin.sum_univ_def]
  simpa using mixedError_toReal_foldl_add_absolute hfmt hfinite (fun i _ => hterm i) eseed
    fun i _ => eterm i

/--
The bound of `mixedError_toReal_foldl_add_absolute_of_toReal_eq_zero` for a sum of `n` terms
computed by `Fin.foldl`.
-/
theorem mixedError_toReal_fin_foldl_add_absolute_of_toReal_eq_zero (hfmt : fmt.isIEEE = true)
    (hseed : toReal seed = 0)
    (hfinite : ∀ v ∈ (List.finRange n).scanl (fun acc i => add acc (term i)) seed,
      isFinite v = true)
    (hterm : ∀ i, isFinite (term i) = true)
    (eterm : ∀ i, MixedError (toReal (term i)) (term₀ i) (rel i) (err i)) :
    MixedError (toReal (Fin.foldl n (fun acc i => add acc (term i)) seed)) (∑ i, term₀ i) 0
      (((1 + unitRoundoffAt fmt) ^ (n - 1) - 1) * ∑ i, |term₀ i| +
        (1 + unitRoundoffAt fmt) ^ (n - 1) * ∑ i, (rel i * |term₀ i| + err i)) := by
  rw [Fin.foldl_eq_finRange_foldl]
  simp only [Fin.sum_univ_def]
  simpa using mixedError_toReal_foldl_add_absolute_of_toReal_eq_zero hfmt hseed hfinite
    (fun i _ => hterm i) fun i _ => eterm i

/-- `toRat?_foldl_add_of_eq_zero` for a sum computed by `Fin.foldl`. -/
theorem toRat?_fin_foldl_add_of_eq_zero (hfmt : fmt.isIEEE = true) {q : ℚ}
    (hseed : toRat? seed = some q) (hterm : ∀ i, toRat? (term i) = some 0) :
    toRat? (Fin.foldl n (fun acc i => add acc (term i)) seed) = some q := by
  rw [Fin.foldl_eq_finRange_foldl]
  exact toRat?_foldl_add_of_eq_zero hfmt hseed fun i _ => hterm i

/--
`toRat?_foldl_add_eq_single` for a sum computed by `Fin.foldl`, which visits every index once:
a one-hot sum of any length is exact.
-/
theorem toRat?_fin_foldl_add_eq_single (hfmt : fmt.isIEEE = true) {j : Fin n} {q : ℚ}
    (hseed : toRat? seed = some 0) (hterm : toRat? (term j) = some q)
    (hzero : ∀ i, i ≠ j → toRat? (term i) = some 0) :
    toRat? (Fin.foldl n (fun acc i => add acc (term i)) seed) = some q := by
  rw [Fin.foldl_eq_finRange_foldl]
  exact toRat?_foldl_add_eq_single hfmt (List.nodup_finRange n) (List.mem_finRange j) hseed hterm
    fun i _ => hzero i

end FinSum

end Model
end FloatLib.Floats.Formats.BinaryInterchange
