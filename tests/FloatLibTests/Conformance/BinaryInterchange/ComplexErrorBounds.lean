/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Util.CollectAxioms
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.ErrorBounds
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Roundoff
public import FloatLib.Tactic.Roundoff

/-!
# Error bounds of whole complex operations

The normwise bounds of `Complex.ErrorBounds` at named formats and on concrete values, and the
bounds that `roundoff` derives for the components of complex programs through the rules of
`Complex.Roundoff`.

* The `√5 u` bound of the conventional product at binary32 and bfloat16 for all complex
  arguments, and on a concrete binary16 product whose finiteness premise the kernel decides.
* The `2u` bound of the product with fused multiply-adds at E5M2, whose three bits of precision
  are below the five that the conventional bound asks for.
* One instance of each premise of the division and magnitude bounds (`DivNormal`,
  `MagnitudeNormal`) at binary32, so that neither theorem is vacuous, and the executable
  division bound in the form `√2 γ₇`.
* `roundoff` on a product, a fused product, a Horner step, a quotient and a magnitude.

The instances are single values. The bounds they instantiate hold for every descriptor with the
stated precision and all arguments.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.ComplexErrorBounds

open FloatLib.Floats FloatLib.Floats.Formats FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics ExecComplex

/-! ## The normwise bounds at named formats -/

/-- Binary32 has 24 bits of precision: the conventional product is within `√5 u` of the exact
one, up to the underflow term, for all complex arguments. -/
example (x y : ℂ) :
    ‖roundedMul FloatFormat.binary32 x y - x * y‖ ≤
      √5 * Model.unitRoundoffAt FloatFormat.binary32 * ‖x * y‖ +
        5 * Model.underflowErrorAt FloatFormat.binary32 :=
  norm_roundedMul_sub_le _ (by decide) x y

/-- Bfloat16 has eight bits of precision. -/
example (x y : ℂ) :
    ‖roundedMul FloatFormat.bfloat16 x y - x * y‖ ≤
      √5 * Model.unitRoundoffAt FloatFormat.bfloat16 * ‖x * y‖ +
        5 * Model.underflowErrorAt FloatFormat.bfloat16 :=
  norm_roundedMul_sub_le _ (by decide) x y

/-- E5M2 has three bits of precision. The bound of the product with fused multiply-adds has no
precision premise. -/
example (x y : ℂ) :
    ‖roundedMulFma FloatFormat.e5m2 x y - x * y‖ ≤
      2 * Model.unitRoundoffAt FloatFormat.e5m2 * ‖x * y‖ +
        5 * Model.underflowErrorAt FloatFormat.e5m2 :=
  norm_roundedMulFma_sub_le _ x y

/-! ## A concrete binary16 product -/

/-- `1.5 + 2 i` in binary16. -/
def left : ExecComplex FloatFormat.binary16 := ⟨Model.ofNatBits 0x3E00, Model.ofNatBits 0x4000⟩
/-- `0.75 - 1.25 i` in binary16. -/
def right : ExecComplex FloatFormat.binary16 := ⟨Model.ofNatBits 0x3A00, Model.ofNatBits 0xBD00⟩

/-- Every intermediate value of the conventional product is finite. -/
theorem product_finite : MulFinite left right := by
  unfold MulFinite
  decide +kernel

/-- The fused product is finite. -/
theorem fused_finite : isFinite (mulFma left right) = true := by
  decide +kernel

/-- The executable product is within `√5 u` of the exact product of the decoded operands. -/
example :
    ‖toComplex (left * right) - toComplex left * toComplex right‖ ≤
      √5 * Model.unitRoundoffAt FloatFormat.binary16 * ‖toComplex left * toComplex right‖ +
        5 * Model.underflowErrorAt FloatFormat.binary16 :=
  norm_toComplex_mul_sub_le left right (by decide) (by decide) product_finite

/-- Its components are within the componentwise bound. -/
example := abs_toComplex_mul_sub_le left right (by decide) product_finite

/-- The executable fused product is within `2u`. -/
example :
    ‖toComplex (mulFma left right) - toComplex left * toComplex right‖ ≤
      2 * Model.unitRoundoffAt FloatFormat.binary16 * ‖toComplex left * toComplex right‖ +
        5 * Model.underflowErrorAt FloatFormat.binary16 :=
  norm_toComplex_mulFma_sub_le left right (by decide) fused_finite

/-- A finite sum is componentwise and normwise within `u`. -/
example (x y : ExecComplex FloatFormat.binary16) (hout : isFinite (x + y) = true) :
    ‖toComplex (x + y) - (toComplex x + toComplex y)‖ ≤
      Model.unitRoundoffAt FloatFormat.binary16 * ‖toComplex x + toComplex y‖ :=
  norm_toComplex_add_sub_le x y (by decide) hout

/-- A finite difference is normwise within `u`. -/
example (x y : ExecComplex FloatFormat.binary16) (hout : isFinite (x - y) = true) :
    ‖toComplex (x - y) - (toComplex x - toComplex y)‖ ≤
      Model.unitRoundoffAt FloatFormat.binary16 * ‖toComplex x - toComplex y‖ :=
  norm_toComplex_sub_sub_le x y (by decide) hout

/-! ## The premises of the division and magnitude bounds hold -/

/-- An integer of magnitude at most `2 ^ 24` is a binary32 grid point. -/
theorem roundAt_intCast (n : ℤ) (hn : |(n : ℝ)| ≤ 2 ^ 24) :
    Model.roundAt FloatFormat.binary32 n = n :=
  Model.roundAt_intCast_of_abs_le FloatFormat.binary32 hn

/-- Two is a binary32 grid point. -/
theorem roundAt_two : Model.roundAt FloatFormat.binary32 2 = 2 := by
  simpa using roundAt_intCast 2 (by norm_num)

/-- Four is a binary32 grid point. -/
theorem roundAt_four : Model.roundAt FloatFormat.binary32 4 = 4 := by
  simpa using roundAt_intCast 4 (by norm_num)

/-- `(2 + 2 i) / (1 + i)` in binary32: the ratio is one, every product and quotient is a small
integer, and the imaginary numerator cancels to zero. No rounding underflows. -/
theorem divNormal_example : DivNormal FloatFormat.binary32 ⟨2, 2⟩ ⟨1, 1⟩ := by
  have h1 := Model.minNormalAt_le_one FloatFormat.binary32
  constructor <;>
    norm_num [Model.NoUnderflowAt, Model.roundAt_one, roundAt_two, roundAt_four] <;>
    first | exact h1 | exact h1.trans (by norm_num)

/-- The division bound applies to `(2 + 2 i) / (1 + i)`. -/
example :
    ‖roundedDiv FloatFormat.binary32 ⟨2, 2⟩ ⟨1, 1⟩ - (⟨2, 2⟩ : ℂ) / ⟨1, 1⟩‖ ≤
      √2 * ((1 + Model.unitRoundoffAt FloatFormat.binary32) ^ 4 /
        (1 - Model.unitRoundoffAt FloatFormat.binary32) ^ 3 - 1) * ‖(⟨2, 2⟩ : ℂ) / ⟨1, 1⟩‖ := by
  have hgrid : ∀ n : ℤ, |(n : ℝ)| ≤ 2 ^ 24 →
      Flocq.GenericRepresentable binaryRadix (Model.fexpOf FloatFormat.binary32) n := fun n hn => by
    have h := Model.genericFormat_roundAt FloatFormat.binary32 (n : ℝ)
    rwa [roundAt_intCast n hn] at h
  refine norm_roundedDiv_sub_le FloatFormat.binary32 (by simp [Complex.ext_iff])
    (by simpa using hgrid 2 (by norm_num)) (by simpa using hgrid 2 (by norm_num))
    (by simpa using hgrid 1 (by norm_num)) (by simpa using hgrid 1 (by norm_num)) ?_
  rw [ite_eq_right (by norm_num)]
  exact divNormal_example

/-- `|1 + i|` in binary32: both ratios and their squares are one, and the root is `√2`. -/
theorem magnitudeNormal_example : MagnitudeNormal FloatFormat.binary32 ⟨1, 1⟩ := by
  have h1 := Model.minNormalAt_le_one FloatFormat.binary32
  have hroot : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
  constructor <;>
    norm_num [Model.NoUnderflowAt, Model.roundAt_one, roundAt_two, roundedNormSq] <;>
    first | exact h1 | exact h1.trans (hroot.trans (le_abs_self _))

/-- The magnitude bound applies to `|1 + i|`. -/
example :
    |roundedMagnitude FloatFormat.binary32 ⟨1, 1⟩ - ‖(⟨1, 1⟩ : ℂ)‖| ≤
      ((1 + Model.unitRoundoffAt FloatFormat.binary32) ^ 4 - 1) * ‖(⟨1, 1⟩ : ℂ)‖ +
        Model.underflowErrorAt FloatFormat.binary32 :=
  abs_roundedMagnitude_sub_le _ _ magnitudeNormal_example

/-! ## The executable division and magnitude -/

/-- Seven unit roundoffs of binary32 are below one. -/
theorem seven_unitRoundoff_lt : 7 * Model.unitRoundoffAt FloatFormat.binary32 < 1 := by
  rw [Model.unitRoundoffAt_eq]
  norm_num [FloatFormat.binary32]

/-- A binary32 quotient with finite intermediate values and no underflow is within `√2 γ₇` of
the exact quotient of the decoded operands: the constant of the theorem is at most
`γ₇ = 7u / (1 - 7u)`. -/
example (x y : ExecComplex FloatFormat.binary32) (hfinite : DivFinite x y)
    (hnormal : if |(toComplex y).re| < |(toComplex y).im| then
        DivNormal FloatFormat.binary32 ⟨(toComplex x).im, (toComplex x).re⟩
          ⟨(toComplex y).im, (toComplex y).re⟩
      else DivNormal FloatFormat.binary32 (toComplex x) (toComplex y)) :
    ‖toComplex (x / y) - toComplex x / toComplex y‖ ≤
      √2 * (7 * Model.unitRoundoffAt FloatFormat.binary32 /
        (1 - 7 * Model.unitRoundoffAt FloatFormat.binary32)) * ‖toComplex x / toComplex y‖ :=
  (norm_toComplex_div_sub_le x y (by decide) hfinite hnormal).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (pow_four_div_pow_three_sub_one_le (Model.unitRoundoffAt_pos _).le seven_unitRoundoff_lt)
        (Real.sqrt_nonneg 2))
      (norm_nonneg _))

/-- A binary32 magnitude with finite intermediate values and no underflow of its inner
roundings is within `(1 + u)⁴ - 1` of the exact magnitude, up to one underflow term. -/
example (z : ExecComplex FloatFormat.binary32) (hfinite : MagnitudeFinite z)
    (hnormal : MagnitudeNormal FloatFormat.binary32 (toComplex z)) :
    |Model.toReal (magnitude z) - ‖toComplex z‖| ≤
      ((1 + Model.unitRoundoffAt FloatFormat.binary32) ^ 4 - 1) * ‖toComplex z‖ +
        Model.underflowErrorAt FloatFormat.binary32 :=
  abs_toReal_magnitude_sub_le z (by decide) hfinite hnormal

/-! ## `roundoff` on complex programs -/

/-- The real part of a product: the reference is `a c - b d` on the decoded components, and the
bound is the three half-ulps. -/
roundoff mixed theorem product_re :=
  fun (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y : ExecComplex fmt) =>
    Model.toReal (x * y).re

example (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y : ExecComplex fmt) :=
  show _ → MixedError _ (x.re.toReal * y.re.toReal - x.im.toReal * y.im.toReal) 0
    (Model.halfUlpAt fmt (x.re.toReal * y.re.toReal) +
      Model.halfUlpAt fmt (x.im.toReal * y.im.toReal) +
      Model.halfUlpAt fmt (Model.toReal (x.re.mul y.re) - Model.toReal (x.im.mul y.im))) from
    product_re fmt hfmt x y

/-- The imaginary part of a fused product: two roundings. -/
roundoff mixed theorem fused_im :=
  fun (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y : ExecComplex fmt) =>
    Model.toReal (mulFma x y).im

example (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y : ExecComplex fmt) :=
  show _ → MixedError _ (x.re.toReal * y.im.toReal + x.im.toReal * y.re.toReal) 0
    (Model.halfUlpAt fmt (x.im.toReal * y.re.toReal) +
      Model.halfUlpAt fmt (x.re.toReal * y.im.toReal + Model.toReal (x.im.mul y.re))) from
    fused_im fmt hfmt x y

/-- One step of Horner's rule on complex values: a product, a second product and a sum. -/
roundoff theorem horner_im :=
  fun (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y z : ExecComplex fmt) =>
    Model.toReal (x * y * z + x).im

/-- A quotient: the reference and the bound keep the branch that the divisor selects. -/
roundoff theorem quotient_re :=
  fun (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y : ExecComplex fmt) =>
    Model.toReal (x / y).re

/-- A quotient in the mixed form. -/
roundoff mixed theorem quotient_im :=
  fun (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y : ExecComplex fmt) =>
    Model.toReal (x / y).im

/-- A magnitude of a finite value with a nonzero scale. -/
roundoff theorem magnitude_abs :=
  fun (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt) =>
    Model.toReal (magnitude z)

/-- Negation, conjugation and subtraction add one rounding. -/
roundoff theorem conj_neg_sub :=
  fun (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y : ExecComplex fmt) =>
    Model.toReal (conj (-(x - y))).im

-- The bounds and the generated theorems rest on the three standard axioms only.
run_cmd do
  for name in [``norm_roundedMul_sub_le, ``norm_toComplex_mul_sub_le, ``abs_roundedMul_sub_le,
      ``norm_roundedMulFma_sub_le, ``norm_toComplex_mulFma_sub_le,
      ``norm_toComplex_add_sub_le, ``norm_toComplex_sub_sub_le,
      ``norm_roundedDiv_sub_le, ``norm_toComplex_div_sub_le, ``abs_roundedMagnitude_sub_le,
      ``abs_toReal_magnitude_sub_le, ``pow_four_div_pow_three_sub_one_le,
      ``Model.roundedSubError_cases, ``Model.roundedSubError_le_of_mul_nonpos,
      ``Model.one_add_mul_abs_roundAt_sub_le, ``product_finite, ``divNormal_example,
      ``magnitudeNormal_example, ``product_re, ``fused_im, ``horner_im, ``quotient_re,
      ``quotient_im, ``magnitude_abs, ``conj_neg_sub] do
    let axioms ← Lean.collectAxioms name
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unexpected axiom {dependency}"

end FloatLibTests.Conformance.BinaryInterchange.ComplexErrorBounds
