/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.PowerProof
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.ValueProof

/-!
# Correct rounding of the complex elementary functions at named formats

The theorems of `Complex.Elementary` hold for every IEEE descriptor, every rounding direction
and every finite argument. This module states them at named formats, checks that their premises
have instances, and evaluates some values in Lean's kernel.

* Each part of `exp`, `sin` and `tanh` in binary32 and binary64 is the rounding of the part of
  Mathlib's `Complex.exp`, `Complex.sin` and `Complex.tanh`, in any direction.
* The functions with a branch cut round a value that solves their equation: `asinh` in
  binary128 a value whose `Complex.sinh` is the argument, `acos` in bfloat16 one whose
  `Complex.cos` is, and so on for `sqrt`, `rsqrt`, `log`, `log1p`, `atanh`, `atan`, `asin` and
  `acosh`. Off the cuts `sqrt`, `rsqrt`, `log`, `log1p`, `atanh` and `atan` round Mathlib's
  principal power, `Complex.log` and `Complex.arctan`, and where C23 Annex G states them the
  inverse sines and cosines round the principal expressions of Kahan's Table 1.
* The finite arguments that the rounding theorems exclude, the zeros of `log`, `log1p`, `expm1`
  and `rsqrt` and the poles of `log1p`, `atanh` and `atan`, have their own theorems, so every
  finite argument of the eighteen functions of one argument is covered.
* The symmetries that head the tables of Annex G hold at every argument, a NaN or an infinity
  included: conjugation for the eighteen functions and parity for the ten odd or even ones.
* A finite argument and a certified power exist: the kernel evaluates `sqrt (-3 + 4 i)`,
  `exp (1 + i)`, `(3 + 4 i) ^ 2` and `(-4) ^ (1 / 4)` rounded up in binary32, and the
  certificate of `(1.5 + 2.5 i) ^ (0.5 + 0.25 i)`, whose parts are decided by enclosures.
* The kernel evaluates certified powers of the other kinds in binary32 as well:
  `(-1 + 2 ^ -100 i) ^ (3 / 2)` next to the negative real axis, `(3 + 4 i) ^ 32768` beyond the
  largest finite number, `(3 + 4 i) ^ (-32768 + 12288 i)` below the least positive one, and
  `(1 + i) ^ (2 ^ 40)` on the real axis.

The instances are single values. The theorems they instantiate hold for all arguments.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.ComplexElementary

open FloatLib.Floats.Formats.BinaryInterchange ExecComplex

/-! ## The theorems at named formats -/

/-- In binary32 the real part of `exp` is the rounding of the real part of `Complex.exp`. -/
example (z : ExecComplex FloatFormat.binary32) (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode) :
    (exp z mode).re = Model.roundReal FloatFormat.binary32 mode (Complex.exp (toComplex z)).re
      (expExact z).reZero := by
  rw [exp_eq (by decide) hz mode, Exact.round, expExact_value hz]

/-- In binary64 the imaginary part of `sin` is the rounding of that of `Complex.sin`. -/
example (z : ExecComplex FloatFormat.binary64) (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode) :
    (sin z mode).im = Model.roundReal FloatFormat.binary64 mode (Complex.sin (toComplex z)).im
      (sinExact z).imZero := by
  rw [sin_eq (by decide) hz mode, Exact.round, sinExact_value hz]

/-- In binary64 the real part of `tanh` is the rounding of that of `Complex.tanh`. -/
example (z : ExecComplex FloatFormat.binary64) (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode) :
    (tanh z mode).re = Model.roundReal FloatFormat.binary64 mode (Complex.tanh (toComplex z)).re
      (tanhExact z).reZero := by
  rw [tanh_eq (by decide) hz mode, Exact.round, tanhExact_value hz]

/-- In binary128 `asinh` rounds a value whose hyperbolic sine is the argument. -/
example (z : ExecComplex FloatFormat.binary128) (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode) :
    asinh z mode = (asinhExact z).round _ mode ∧
      Complex.sinh (asinhExact z).value = toComplex z :=
  ⟨asinh_eq (by decide) hz mode, sinh_asinhExact_value (by decide) hz⟩

/-- In bfloat16 `acos` rounds a value whose cosine is the argument. -/
example (z : ExecComplex FloatFormat.bfloat16) (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode) :
    acos z mode = (acosExact z).round _ mode ∧ Complex.cos (acosExact z).value = toComplex z :=
  ⟨acos_eq (by decide) hz mode, cos_acosExact_value (by decide) hz⟩

/-- A certified power in binary16 is correctly rounded. -/
example (z w : ExecComplex FloatFormat.binary16) (hz : isFinite z = true)
    (hw : isFinite w = true) (hne : toComplex z ≠ 0) (mode : Model.IEEERoundingMode)
    (h : powCertified z w mode = true) : pow z w mode = (powExact z w).round _ mode :=
  pow_eq (by decide) hz hw hne mode _ h

/-- In binary16 `sqrt` rounds a square root of the argument, the principal one where the
imaginary sign bit is clear. -/
example (z : ExecComplex FloatFormat.binary16) (hz : isFinite z = true)
    (hsign : Model.signBit z.im = false) (mode : Model.IEEERoundingMode) :
    sqrt z mode = (sqrtExact z).round _ mode ∧ (sqrtExact z).value ^ 2 = toComplex z ∧
      (sqrtExact z).value = toComplex z ^ (2⁻¹ : ℂ) :=
  ⟨sqrt_eq (by decide) hz mode, sqrtExact_value_sq (by decide) hz,
    sqrtExact_value hz (Or.inl hsign)⟩

/-- In binary16 `rsqrt` rounds a reciprocal square root of a nonzero argument, the reciprocal of
the principal root off the negative real axis. -/
example (z : ExecComplex FloatFormat.binary16) (hz : isFinite z = true)
    (hne : toComplex z ≠ 0) (hcut : (toComplex z).arg ≠ Real.pi)
    (mode : Model.IEEERoundingMode) :
    rsqrt z mode = (rsqrtExact z).round _ mode ∧ (rsqrtExact z).value ^ 2 * toComplex z = 1 ∧
      (rsqrtExact z).value = (toComplex z ^ (2⁻¹ : ℂ))⁻¹ :=
  ⟨rsqrt_eq (by decide) hz hne mode, rsqrtExact_value_sq (by decide) hz hne,
    rsqrtExact_value hz (Or.inr hcut)⟩

/-- In binary32 `log` rounds a logarithm of a nonzero argument, the principal one where the
imaginary sign bit is clear. -/
example (z : ExecComplex FloatFormat.binary32) (hz : isFinite z = true)
    (hne : toComplex z ≠ 0) (hsign : Model.signBit z.im = false)
    (mode : Model.IEEERoundingMode) :
    log z mode = (logExact z).round _ mode ∧ Complex.exp (logExact z).value = toComplex z ∧
      (logExact z).value = Complex.log (toComplex z) :=
  ⟨log_eq (by decide) hz hne mode, exp_logExact_value hz hne, logExact_value hz (Or.inl hsign)⟩

/-- In binary32 `log1p` rounds a logarithm of `1 + z`, the principal one where the imaginary sign
bit is clear. -/
example (z : ExecComplex FloatFormat.binary32) (hz : isFinite z = true)
    (hne : toComplex z ≠ 0) (hpole : 1 + toComplex z ≠ 0) (hsign : Model.signBit z.im = false)
    (mode : Model.IEEERoundingMode) :
    log1p z mode = (log1pExact z).round _ mode ∧
      Complex.exp (log1pExact z).value = 1 + toComplex z ∧
      (log1pExact z).value = Complex.log (1 + toComplex z) :=
  ⟨log1p_eq (by decide) hz hne hpole mode, exp_log1pExact_value hz hpole,
    log1pExact_value hz (Or.inl hsign)⟩

/-- In binary64 `expm1` rounds `Complex.exp w - 1`. -/
example (z : ExecComplex FloatFormat.binary64) (hz : isFinite z = true)
    (hne : toComplex z ≠ 0) (mode : Model.IEEERoundingMode) :
    (expm1 z mode).re = Model.roundReal FloatFormat.binary64 mode
      (Complex.exp (toComplex z) - 1).re (expm1Exact z).reZero := by
  rw [expm1_eq (by decide) hz hne mode, Exact.round, expm1Exact_value hz]

/-- In binary64 the real part of `cos` is the rounding of that of `Complex.cos`. -/
example (z : ExecComplex FloatFormat.binary64) (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode) :
    (cos z mode).re = Model.roundReal FloatFormat.binary64 mode (Complex.cos (toComplex z)).re
      (cosExact z).reZero := by
  rw [cos_eq (by decide) hz mode, Exact.round, cosExact_value hz]

/-- In binary32 the imaginary part of `tan` is the rounding of that of `Complex.tan`. -/
example (z : ExecComplex FloatFormat.binary32) (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode) :
    (tan z mode).im = Model.roundReal FloatFormat.binary32 mode (Complex.tan (toComplex z)).im
      (tanExact z).imZero := by
  rw [tan_eq (by decide) hz mode, Exact.round, tanExact_value hz]

/-- In binary64 `atanh` rounds a value whose hyperbolic tangent is the argument. -/
example (z : ExecComplex FloatFormat.binary64) (hz : isFinite z = true)
    (hpos : toComplex z ≠ 1) (hneg : toComplex z ≠ -1) (mode : Model.IEEERoundingMode) :
    atanh z mode = (atanhExact z).round _ mode ∧
      Complex.tanh (atanhExact z).value = toComplex z :=
  ⟨atanh_eq (by decide) hz hpos hneg mode, tanh_atanhExact_value (by decide) hz hpos hneg⟩

/-- In binary64 `atan` rounds a value whose tangent is the argument. -/
example (z : ExecComplex FloatFormat.binary64) (hz : isFinite z = true)
    (hpos : toComplex z ≠ Complex.I) (hneg : toComplex z ≠ -Complex.I)
    (mode : Model.IEEERoundingMode) :
    atan z mode = (atanExact z).round _ mode ∧ Complex.tan (atanExact z).value = toComplex z :=
  ⟨atan_eq (by decide) hz hpos hneg mode, tan_atanExact_value (by decide) hz hpos hneg⟩

/-- In binary64, off the imaginary axis, `atan` rounds Mathlib's `Complex.arctan` and `atanh`,
off the real axis, half the principal logarithm of `(1 + w) / (1 - w)`. -/
example (z : ExecComplex FloatFormat.binary64) (hz : isFinite z = true)
    (hre : (toComplex z).re ≠ 0) (him : (toComplex z).im ≠ 0) (mode : Model.IEEERoundingMode) :
    (atan z mode = (atanExact z).round _ mode ∧
      (atanExact z).value = Complex.arctan (toComplex z)) ∧
    (atanh z mode = (atanhExact z).round _ mode ∧
      (atanhExact z).value = Complex.log ((1 + toComplex z) / (1 - toComplex z)) / 2) := by
  have hI : toComplex z ≠ Complex.I := fun h => hre (by rw [h]; rfl)
  have hnegI : toComplex z ≠ -Complex.I := fun h => hre (by rw [h]; simp)
  have hone : toComplex z ≠ 1 := fun h => him (by rw [h]; rfl)
  have hnegOne : toComplex z ≠ -1 := fun h => him (by rw [h]; simp)
  exact ⟨⟨atan_eq (by decide) hz hI hnegI mode, atanExact_value hz (Or.inr fun h => hre h.1) hnegI⟩,
    atanh_eq (by decide) hz hone hnegOne mode,
    atanhExact_value hz (Or.inr fun h => him h.1) hone⟩

/-- In binary32 `asin` rounds a value whose sine is the argument. -/
example (z : ExecComplex FloatFormat.binary32) (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode) :
    asin z mode = (asinExact z).round _ mode ∧ Complex.sin (asinExact z).value = toComplex z :=
  ⟨asin_eq (by decide) hz mode, sin_asinExact_value (by decide) hz⟩

/-- In binary32 `acosh` rounds a value whose hyperbolic cosine is the argument. -/
example (z : ExecComplex FloatFormat.binary32) (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode) :
    acosh z mode = (acoshExact z).round _ mode ∧
      Complex.cosh (acoshExact z).value = toComplex z :=
  ⟨acosh_eq (by decide) hz mode, cosh_acoshExact_value (by decide) hz⟩

/-- In binary64, where both sign bits are clear, `asinh` rounds the principal expression
`log (w + √(1 + w²))` and `acosh` rounds `2 log (√((w + 1) / 2) + √((w - 1) / 2))`, in Mathlib's
principal logarithm and square root, and `acos` rounds `-i` times the latter. -/
example (z : ExecComplex FloatFormat.binary64) (hz : isFinite z = true)
    (hre : Model.signBit z.re = false) (him : Model.signBit z.im = false)
    (mode : Model.IEEERoundingMode) :
    (asinh z mode = (asinhExact z).round _ mode ∧
      (asinhExact z).value =
        Complex.log (toComplex z + (1 + toComplex z ^ 2) ^ (2⁻¹ : ℂ))) ∧
    (acosh z mode = (acoshExact z).round _ mode ∧
      (acoshExact z).value = 2 * Complex.log (((toComplex z + 1) / 2) ^ (2⁻¹ : ℂ) +
        ((toComplex z - 1) / 2) ^ (2⁻¹ : ℂ))) ∧
    (acosExact z).value = -Complex.I * (acoshExact z).value :=
  ⟨⟨asinh_eq (by decide) hz mode, asinhExact_value hre him⟩,
    ⟨acosh_eq (by decide) hz mode, acoshExact_value him⟩,
    by rw [acosExact_value him, acoshExact_value him]⟩

/-- In binary32, where the real sign bit is clear and the imaginary one set, `asin` rounds the
principal expression `-i log (i w + √(1 - w²))`. -/
example (z : ExecComplex FloatFormat.binary32) (hz : isFinite z = true)
    (hre : Model.signBit z.re = false) (him : Model.signBit z.im = true)
    (mode : Model.IEEERoundingMode) :
    asin z mode = (asinExact z).round _ mode ∧
      (asinExact z).value = -Complex.I *
        Complex.log (Complex.I * toComplex z + (1 - toComplex z ^ 2) ^ (2⁻¹ : ℂ)) :=
  ⟨asin_eq (by decide) hz mode, asinExact_value (by decide) hz hre him⟩

/-- The exact inverse sines and cosines are principal values: the real parts are not negative,
and the imaginary parts lie in `[-π / 2, π / 2]` and in `[0, π]`. -/
example (w : ℂ) :
    0 ≤ (asinhValue w).re ∧ |(asinhValue w).im| ≤ Real.pi / 2 ∧ 0 ≤ (acoshValue w).re ∧
      (acoshValue w).im ∈ Set.Icc 0 Real.pi :=
  ⟨asinhValue_re_nonneg w, abs_asinhValue_im_le w, acoshValue_re_nonneg w, acoshValue_im_mem w⟩

/-! ## The poles and zeros: every finite argument is covered -/

/-- Every finite binary64 argument of `log` is covered by a theorem: a zero by `log_zero`, the
pole, and every other argument by `log_eq`. -/
example (z : ExecComplex FloatFormat.binary64) (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode) :
    log z mode = (logExact z).round _ mode ∨ (log z mode).re = Model.negInf _ := by
  by_cases hzero : toComplex z = 0
  · exact Or.inr (by rw [log_zero hz hzero mode])
  · exact Or.inl (log_eq (by decide) hz hzero mode)

/-- Every finite binary32 argument of `log1p` and of `expm1` is covered: a zero is returned
unchanged, `log1p (-1 ± 0 i) = -∞ ± 0 i`, and every other result is correctly rounded. -/
example (z : ExecComplex FloatFormat.binary32) (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode) :
    (log1p z mode = z ∨ log1p z mode = ⟨Model.negInf _, Model.zero _ (Model.signBit z.im)⟩ ∨
      log1p z mode = (log1pExact z).round _ mode) ∧
    (expm1 z mode = z ∨ expm1 z mode = (expm1Exact z).round _ mode) := by
  refine ⟨?_, ?_⟩
  · by_cases hzero : toComplex z = 0
    · exact Or.inl (log1p_zero hz hzero mode)
    · by_cases hpole : 1 + toComplex z = 0
      · exact Or.inr (Or.inl (log1p_neg_one hz (by linear_combination hpole) mode))
      · exact Or.inr (Or.inr (log1p_eq (by decide) hz hzero hpole mode))
  · by_cases hzero : toComplex z = 0
    · exact Or.inl (expm1_zero hz hzero mode)
    · exact Or.inr (expm1_eq (by decide) hz hzero mode)

/-- Every finite bfloat16 argument of `atanh` is covered: the poles `±1` and the others. -/
example (z : ExecComplex FloatFormat.bfloat16) (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode) :
    atanh z mode = ⟨Model.posInf _, Model.zero _ (Model.signBit z.im)⟩ ∨
      atanh z mode = ⟨Model.negInf _, Model.zero _ (Model.signBit z.im)⟩ ∨
      atanh z mode = (atanhExact z).round _ mode := by
  by_cases hpos : toComplex z = 1
  · exact Or.inl (atanh_one hz hpos mode)
  · by_cases hneg : toComplex z = -1
    · exact Or.inr (Or.inl (atanh_neg_one hz hneg mode))
    · exact Or.inr (Or.inr (atanh_eq (by decide) hz hpos hneg mode))

/-- Every finite binary16 argument of `atan` is covered: the poles `±i` and the others. -/
example (z : ExecComplex FloatFormat.binary16) (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode) :
    atan z mode = ⟨Model.zero _ (Model.signBit z.re), Model.posInf _⟩ ∨
      atan z mode = ⟨Model.zero _ (Model.signBit z.re), Model.negInf _⟩ ∨
      atan z mode = (atanExact z).round _ mode := by
  by_cases hpos : toComplex z = Complex.I
  · exact Or.inl (atan_I hz hpos mode)
  · by_cases hneg : toComplex z = -Complex.I
    · exact Or.inr (Or.inl (atan_neg_I hz hneg mode))
    · exact Or.inr (Or.inr (atan_eq (by decide) hz hpos hneg mode))

/-- Every finite binary128 argument of `rsqrt` is covered: a zero gives `+∞ + NaN i`. -/
example (z : ExecComplex FloatFormat.binary128) (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode) :
    rsqrt z mode = (rsqrtExact z).round _ mode ∨
      ((rsqrt z mode).re = Model.posInf _ ∧ Model.isNaN (rsqrt z mode).im = true) := by
  by_cases hzero : toComplex z = 0
  · exact Or.inr (rsqrt_zero (by decide) hz hzero mode)
  · exact Or.inl (rsqrt_eq (by decide) hz hzero mode)

/-! ## The symmetries of Annex G at every argument -/

/-- In binary64, rounding to nearest, each function commutes with conjugation at every argument,
a NaN or an infinity included: the first line of each table of C23 Annex G. -/
example (z : ExecComplex FloatFormat.binary64) :
    sqrt (ExecComplex.conj z) = ExecComplex.conj (sqrt z) ∧
      rsqrt (ExecComplex.conj z) = ExecComplex.conj (rsqrt z) ∧
      exp (ExecComplex.conj z) = ExecComplex.conj (exp z) ∧
      expm1 (ExecComplex.conj z) = ExecComplex.conj (expm1 z) ∧
      log (ExecComplex.conj z) = ExecComplex.conj (log z) ∧
      log1p (ExecComplex.conj z) = ExecComplex.conj (log1p z) ∧
      sin (ExecComplex.conj z) = ExecComplex.conj (sin z) ∧
      cos (ExecComplex.conj z) = ExecComplex.conj (cos z) ∧
      tan (ExecComplex.conj z) = ExecComplex.conj (tan z) ∧
      sinh (ExecComplex.conj z) = ExecComplex.conj (sinh z) ∧
      cosh (ExecComplex.conj z) = ExecComplex.conj (cosh z) ∧
      tanh (ExecComplex.conj z) = ExecComplex.conj (tanh z) ∧
      asin (ExecComplex.conj z) = ExecComplex.conj (asin z) ∧
      acos (ExecComplex.conj z) = ExecComplex.conj (acos z) ∧
      atan (ExecComplex.conj z) = ExecComplex.conj (atan z) ∧
      asinh (ExecComplex.conj z) = ExecComplex.conj (asinh z) ∧
      acosh (ExecComplex.conj z) = ExecComplex.conj (acosh z) ∧
      atanh (ExecComplex.conj z) = ExecComplex.conj (atanh z) :=
  ⟨sqrt_conj (by decide) z rfl,
    rsqrt_conj (by decide) z rfl,
    exp_conj (by decide) z rfl,
    expm1_conj (by decide) z rfl,
    log_conj (by decide) z rfl,
    log1p_conj (by decide) z rfl,
    sin_conj (by decide) z rfl,
    cos_conj (by decide) z rfl,
    tan_conj (by decide) z rfl,
    sinh_conj (by decide) z rfl,
    cosh_conj (by decide) z rfl,
    tanh_conj (by decide) z rfl,
    asin_conj (by decide) z rfl,
    acos_conj (by decide) z rfl,
    atan_conj (by decide) z rfl,
    asinh_conj (by decide) z rfl,
    acosh_conj (by decide) z rfl,
    atanh_conj (by decide) z rfl⟩

/-- In binary32, rounding toward zero, the odd functions are odd at every argument, and `cosh`
and `cos` are even in every direction, also the directed ones. -/
example (z : ExecComplex FloatFormat.binary32) :
    sinh (ExecComplex.neg z) .towardZero = ExecComplex.neg (sinh z .towardZero) ∧
      tanh (ExecComplex.neg z) .towardZero = ExecComplex.neg (tanh z .towardZero) ∧
      asinh (ExecComplex.neg z) .towardZero = ExecComplex.neg (asinh z .towardZero) ∧
      atanh (ExecComplex.neg z) .towardZero = ExecComplex.neg (atanh z .towardZero) ∧
      sin (ExecComplex.neg z) .towardZero = ExecComplex.neg (sin z .towardZero) ∧
      tan (ExecComplex.neg z) .towardZero = ExecComplex.neg (tan z .towardZero) ∧
      asin (ExecComplex.neg z) .towardZero = ExecComplex.neg (asin z .towardZero) ∧
      atan (ExecComplex.neg z) .towardZero = ExecComplex.neg (atan z .towardZero) ∧
      cosh (ExecComplex.neg z) .up = cosh z .up ∧
      cos (ExecComplex.neg z) .down = cos z .down :=
  ⟨sinh_neg (by decide) z rfl,
    tanh_neg (by decide) z rfl,
    asinh_neg (by decide) z rfl,
    atanh_neg (by decide) z rfl,
    sin_neg (by decide) z rfl,
    tan_neg (by decide) z rfl,
    asin_neg (by decide) z rfl,
    atan_neg (by decide) z rfl,
    cosh_neg (by decide) z .up, cos_neg (by decide) z .down⟩

/-- Rounding the negated real upward is the negation of rounding the real downward, with the
overflow results and the opposite sign of an exact zero. -/
example (x : ℝ) :
    Model.roundReal FloatFormat.binary64 .up (-x) true =
      Model.neg (Model.roundReal FloatFormat.binary64 .down x false) :=
  Model.roundReal_neg (by decide) .up x false

/-! ## Values in the kernel -/

/-- `-3 + 4 i` in binary32. -/
def base : ExecComplex FloatFormat.binary32 :=
  ⟨Model.ofNatBits 0xC0400000, Model.ofNatBits 0x40800000⟩

/-- The premise of the theorems has an instance: `-3 + 4 i` is finite. -/
theorem base_finite : isFinite base = true := by
  decide +kernel

/-- `sqrt (-3 + 4 i) = 1 + 2 i`. -/
example : sqrt base = ⟨Model.ofNatBits 0x3F800000, Model.ofNatBits 0x40000000⟩ := by
  decide +kernel

/-- `exp (1 + i) = 1.468694 + 2.2873552 i` in binary32. -/
example : exp (fmt := FloatFormat.binary32)
    ⟨Model.ofNatBits 0x3F800000, Model.ofNatBits 0x3F800000⟩ =
      ⟨Model.ofNatBits 0x3FBBFE2A, Model.ofNatBits 0x40126407⟩ := by
  decide +kernel

/-- A subnormal argument of binary32: `(3 + 5 i) * 2 ^ -149`. -/
def tiny : ExecComplex FloatFormat.binary32 := ⟨Model.ofNatBits 3, Model.ofNatBits 5⟩

/-- At a subnormal argument each part lies next to a part of the argument, and a directed
rounding tells on which side: `sinh z = z + z³ / 6`, `expm1 z = z + z² / 2`,
`log1p z = z - z² / 2`, `atan z = z - z³ / 3`, `asinh z = z - z³ / 6` and
`tanh z = z - z³ / 3` to the next order. The enclosures of a small argument decide each of them
with no exact comparison. -/
example :
    sinh tiny .towardZero = ⟨Model.ofNatBits 2, Model.ofNatBits 5⟩ ∧
      expm1 tiny .up = ⟨Model.ofNatBits 3, Model.ofNatBits 6⟩ ∧
      log1p tiny .down = ⟨Model.ofNatBits 3, Model.ofNatBits 4⟩ ∧
      atan tiny .towardZero = ⟨Model.ofNatBits 3, Model.ofNatBits 4⟩ ∧
      asinh tiny .up = ⟨Model.ofNatBits 4, Model.ofNatBits 5⟩ ∧
      tanh tiny .towardZero = ⟨Model.ofNatBits 3, Model.ofNatBits 4⟩ := by
  decide +kernel

/-- `(3 + 4 i) ^ 2 = -7 + 24 i`, certified. -/
example : powChecked (fmt := FloatFormat.binary32)
    ⟨Model.ofNatBits 0x40400000, Model.ofNatBits 0x40800000⟩
    ⟨Model.ofNatBits 0x40000000, Model.ofNatBits 0⟩ =
      (⟨Model.ofNatBits 0xC0E00000, Model.ofNatBits 0x41C00000⟩, true) := by
  decide +kernel

/-- `(-4) ^ (1 / 4) = 1 + i` rounded up, certified: the base has the complex rational fourth
root `1 + i`, so no enclosure has to decide a part that lies on a rounding boundary. -/
example : powChecked (fmt := FloatFormat.binary32)
    ⟨Model.ofNatBits 0xC0800000, Model.ofNatBits 0⟩
    ⟨Model.ofNatBits 0x3E800000, Model.ofNatBits 0⟩ .up =
      (⟨Model.ofNatBits 0x3F800000, Model.ofNatBits 0x3F800000⟩, true) := by
  decide +kernel

/-- The certificate of `(1.5 + 2.5 i) ^ (0.5 + 0.25 i)`, a power that enclosures decide. -/
example : powCertified (fmt := FloatFormat.binary32)
    ⟨Model.ofNatBits 0x3FC00000, Model.ofNatBits 0x40200000⟩
    ⟨Model.ofNatBits 0x3F000000, Model.ofNatBits 0x3E800000⟩ = true := by
  decide +kernel

/-- `(-1 + 2 ^ -100 i) ^ (3 / 2)` rounded down, certified. The base lies next to the negative
real axis, so the real part of the power lies next to zero, `-(3 / 2) 2 ^ -100` and a relative
`2 ^ -200` more, and the imaginary part as close below one in magnitude: the angle from the
nearest axis keeps the relative accuracy that decides both. -/
example : powChecked (fmt := FloatFormat.binary32)
    ⟨Model.ofNatBits 0xBF800000, Model.ofNatBits 0x0D800000⟩
    ⟨Model.ofNatBits 0x3FC00000, Model.ofNatBits 0⟩ .down =
      (⟨Model.ofNatBits 0x8DC00001, Model.ofNatBits 0xBF800000⟩, true) := by
  decide +kernel

/-- `(3 + 4 i) ^ 32768` toward zero is the largest finite number in both parts, certified:
the power is too long to form, and its exponent `32768 log 5` alone puts it beyond the range. -/
example : powChecked (fmt := FloatFormat.binary32)
    ⟨Model.ofNatBits 0x40400000, Model.ofNatBits 0x40800000⟩
    ⟨Model.ofNatBits 0x47000000, Model.ofNatBits 0⟩ .towardZero =
      (⟨Model.ofNatBits 0x7F7FFFFF, Model.ofNatBits 0x7F7FFFFF⟩, true) := by
  decide +kernel

/-- `(3 + 4 i) ^ (-32768 + 12288 i)` has two negative parts below every positive number of the
format: rounded down they are the least negative number, and rounded up the negative zero. -/
example :
    powChecked (fmt := FloatFormat.binary32)
        ⟨Model.ofNatBits 0x40400000, Model.ofNatBits 0x40800000⟩
        ⟨Model.ofNatBits 0xC7000000, Model.ofNatBits 0x46400000⟩ .down =
          (⟨Model.ofNatBits 0x80000001, Model.ofNatBits 0x80000001⟩, true) ∧
      powChecked (fmt := FloatFormat.binary32)
        ⟨Model.ofNatBits 0x40400000, Model.ofNatBits 0x40800000⟩
        ⟨Model.ofNatBits 0xC7000000, Model.ofNatBits 0x46400000⟩ .up =
          (⟨Model.ofNatBits 0x80000000, Model.ofNatBits 0x80000000⟩, true) := by
  decide +kernel

/-- `(1 + i) ^ (2 ^ 40) = 2 ^ (2 ^ 39)`, certified: the base lies on a diagonal and the exponent
is even, so the power is real. Its real part overflows and its imaginary part is the zero. -/
example :
    powChecked (fmt := FloatFormat.binary32)
        ⟨Model.ofNatBits 0x3F800000, Model.ofNatBits 0x3F800000⟩
        ⟨Model.ofNatBits 0x53800000, Model.ofNatBits 0⟩ =
          (⟨Model.ofNatBits 0x7F800000, Model.ofNatBits 0⟩, true) ∧
      powChecked (fmt := FloatFormat.binary32)
        ⟨Model.ofNatBits 0x3F800000, Model.ofNatBits 0x3F800000⟩
        ⟨Model.ofNatBits 0x53800000, Model.ofNatBits 0⟩ .towardZero =
          (⟨Model.ofNatBits 0x7F7FFFFF, Model.ofNatBits 0⟩, true) := by
  decide +kernel

end FloatLibTests.Conformance.BinaryInterchange.ComplexElementary
