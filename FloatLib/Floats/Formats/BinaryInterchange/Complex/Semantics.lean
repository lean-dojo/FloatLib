/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.DivisionSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Subtraction
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SqrtSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Proof
public import Mathlib.Basic.Complex.Basic

/-!
# Real and complex semantics of `ExecComplex`

The component map `toComplex` interprets finite executable values as mathematical complex numbers.
Addition and subtraction round each component once. Multiplication records all six rounding sites:
four scalar products, the subtraction forming the real component, and the addition forming the
imaginary component. Each intermediate rounding appears in the corresponding theorem.

Division records the chosen component ratio and every subsequent rounding. Squared magnitude
records two rounded squares and their rounded sum; magnitude applies this to scaled components.
Neither an exact field operation nor a whole-operation error bound is asserted.

The finiteness assumptions rule out overflow to infinity and NaN. They are explicit because the
real-number semantics does not assign real values to infinities or NaNs.

## Reference

- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, second edition, SIAM, 2002,
  Section 3.6. https://doi.org/10.1137/1.9780898718027
- IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019.
  https://doi.org/10.1109/IEEESTD.2019.8766229
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

noncomputable section

/-- Interpret both finite components as real numbers and assemble a mathematical complex value. -/
noncomputable def toComplex {fmt : FloatFormat} (z : ExecComplex fmt) : ℂ :=
  ⟨Model.toReal z.re, Model.toReal z.im⟩

/-- Componentwise nearest-even semantics for complex addition. -/
noncomputable def roundedAdd (fmt : FloatFormat) (x y : ℂ) : ℂ :=
  ⟨Model.roundAt fmt (x.re + y.re), Model.roundAt fmt (x.im + y.im)⟩

/-- Componentwise nearest-even semantics for complex subtraction. -/
noncomputable def roundedSub (fmt : FloatFormat) (x y : ℂ) : ℂ :=
  ⟨Model.roundAt fmt (x.re - y.re), Model.roundAt fmt (x.im - y.im)⟩

/--
The rounded real semantics of the evaluation order used by `ExecComplex.mul`.

This is not exact complex multiplication: each product is rounded before the final rounded
subtraction or addition.
-/
noncomputable def roundedMul (fmt : FloatFormat) (x y : ℂ) : ℂ :=
  ⟨Model.roundAt fmt
      (Model.roundAt fmt (x.re * y.re) - Model.roundAt fmt (x.im * y.im)),
    Model.roundAt fmt
      (Model.roundAt fmt (x.re * y.im) + Model.roundAt fmt (x.im * y.re))⟩

/-- Negation of finite executable components agrees exactly with complex negation. -/
theorem toComplex_neg {fmt : FloatFormat} (z : ExecComplex fmt)
    (hz : isFinite z = true) :
    toComplex (-z) = -toComplex z := by
  obtain ⟨hzre, hzim⟩ := (isFinite_eq_true_iff z).1 hz
  apply Complex.ext
  · exact Model.toReal_neg z.re hzre
  · exact Model.toReal_neg z.im hzim

/-- Complex conjugation is exact on finite components, including formats with unsigned zero. -/
theorem toComplex_conj {fmt : FloatFormat} (z : ExecComplex fmt)
    (hz : isFinite z = true) :
    toComplex (conj z) = starRingEnd ℂ (toComplex z) := by
  obtain ⟨_, hzim⟩ := (isFinite_eq_true_iff z).1 hz
  apply Complex.ext
  · rfl
  · exact Model.toReal_neg z.im hzim

/-- Executable complex addition refines componentwise rounded mathematical addition. -/
theorem toComplex_add_eq_roundedAdd {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (x + y) = true) :
    toComplex (x + y) = roundedAdd fmt (toComplex x) (toComplex y) := by
  obtain ⟨hxre, hxim⟩ := (isFinite_eq_true_iff x).1 hx
  obtain ⟨hyre, hyim⟩ := (isFinite_eq_true_iff y).1 hy
  obtain ⟨hore, hoim⟩ := (isFinite_eq_true_iff (x + y)).1 hout
  apply Complex.ext
  · exact Model.toReal_add_eq_roundAt x.re y.re hfmt hxre hyre hore
  · exact Model.toReal_add_eq_roundAt x.im y.im hfmt hxim hyim hoim

/-- Executable complex subtraction refines componentwise rounded mathematical subtraction. -/
theorem toComplex_sub_eq_roundedSub {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (x - y) = true) :
    toComplex (x - y) = roundedSub fmt (toComplex x) (toComplex y) := by
  obtain ⟨hxre, hxim⟩ := (isFinite_eq_true_iff x).1 hx
  obtain ⟨hyre, hyim⟩ := (isFinite_eq_true_iff y).1 hy
  obtain ⟨hore, hoim⟩ := (isFinite_eq_true_iff (x - y)).1 hout
  apply Complex.ext
  · exact Model.toReal_sub_eq_roundAt x.re y.re hfmt hxre hyre hore
  · exact Model.toReal_sub_eq_roundAt x.im y.im hfmt hxim hyim hoim

/--
All scalar intermediates required to interpret one executable complex multiplication over `ℝ`.

The predicate includes finite inputs, four finite component products, and finite final components.
It is the natural domain of the exact evaluation-order refinement theorem below.
-/
def MulFinite {fmt : FloatFormat} (x y : ExecComplex fmt) : Prop :=
  isFinite x = true ∧
  isFinite y = true ∧
  Model.isFinite (Model.mul x.re y.re) = true ∧
  Model.isFinite (Model.mul x.im y.im) = true ∧
  Model.isFinite (Model.mul x.re y.im) = true ∧
  Model.isFinite (Model.mul x.im y.re) = true ∧
  isFinite (x * y) = true

/--
For an IEEE descriptor and finite inputs, intermediate values, and result, complex multiplication
agrees with `roundedMul`: four rounded products followed by a rounded subtraction and addition.
-/
theorem toComplex_mul_eq_roundedMul {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true)
    (h : MulFinite x y) :
    toComplex (x * y) = roundedMul fmt (toComplex x) (toComplex y) := by
  rcases h with ⟨hx, hy, hac, hbd, had, hbc, hout⟩
  obtain ⟨hxre, hxim⟩ := (isFinite_eq_true_iff x).1 hx
  obtain ⟨hyre, hyim⟩ := (isFinite_eq_true_iff y).1 hy
  obtain ⟨hore, hoim⟩ := (isFinite_eq_true_iff (x * y)).1 hout
  apply Complex.ext
  · change
      Model.toReal (Model.sub (Model.mul x.re y.re) (Model.mul x.im y.im)) =
        Model.roundAt fmt
          (Model.roundAt fmt
              (Model.toReal x.re * Model.toReal y.re) -
            Model.roundAt fmt
              (Model.toReal x.im * Model.toReal y.im))
    rw [Model.toReal_sub_eq_roundAt _ _ hfmt hac hbd hore]
    rw [Model.toReal_mul_eq_roundAt x.re y.re hfmt hxre hyre hac]
    rw [Model.toReal_mul_eq_roundAt x.im y.im hfmt hxim hyim hbd]
  · change
      Model.toReal (Model.add (Model.mul x.re y.im) (Model.mul x.im y.re)) =
        Model.roundAt fmt
          (Model.roundAt fmt
              (Model.toReal x.re * Model.toReal y.im) +
            Model.roundAt fmt
              (Model.toReal x.im * Model.toReal y.re))
    rw [Model.toReal_add_eq_roundAt _ _ hfmt had hbc hoim]
    rw [Model.toReal_mul_eq_roundAt x.re y.im hfmt hxre hyim had]
    rw [Model.toReal_mul_eq_roundAt x.im y.re hfmt hxim hyre hbc]

/-- Two separately rounded squares followed by a rounded sum. -/
noncomputable def roundedNormSq (fmt : FloatFormat) (z : ℂ) : ℝ :=
  Model.roundAt fmt (Model.roundAt fmt (z.re * z.re) + Model.roundAt fmt (z.im * z.im))

/-- Finite inputs, both rounded squares, and their rounded sum. -/
structure NormSqFinite {fmt : FloatFormat} (z : ExecComplex fmt) : Prop where
  /-- Both input components are finite. -/
  input : isFinite z = true
  /-- The rounded real square is finite. -/
  re_square : Model.isFinite (Model.mul z.re z.re) = true
  /-- The rounded imaginary square is finite. -/
  im_square : Model.isFinite (Model.mul z.im z.im) = true
  /-- The rounded sum is finite. -/
  result : Model.isFinite (normSq z) = true

/-- Squared magnitude agrees with its three scalar rounding sites, including underflow. -/
theorem toReal_normSq_eq_roundedNormSq {fmt : FloatFormat} (z : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (h : NormSqFinite z) :
    Model.toReal (normSq z) = roundedNormSq fmt (toComplex z) := by
  obtain ⟨hre, him⟩ := (isFinite_eq_true_iff z).1 h.input
  unfold normSq roundedNormSq toComplex
  rw [Model.toReal_add_eq_roundAt _ _ hfmt h.re_square h.im_square h.result,
    Model.toReal_mul_eq_roundAt _ _ hfmt hre hre h.re_square,
    Model.toReal_mul_eq_roundAt _ _ hfmt him him h.im_square]

namespace Internal

private theorem toReal_abs {fmt : FloatFormat} (x : Model fmt) (hfmt : fmt.isIEEE = true)
    (hx : Model.isFinite x = true) : Model.toReal (Model.abs x) = |Model.toReal x| := by
  have hsigned := FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt
  obtain ⟨d, hd⟩ := Model.exists_toDyadic?_of_isFinite hx
  have hsign := Model.sign_eq_signBit_of_toDyadic?_some hd
  have hreal : Model.toReal x = d.toReal := by simp [Model.toReal_eq, hd]
  have hp := FloatLib.Floats.Formats.Flocq.bpow.pos Numerics.binaryRadix d.exponent
  cases hs : Model.signBit x with
  | false =>
    have hn : 0 ≤ Model.toReal x := by
      rw [hreal]
      simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
        hsign.trans hs, Bool.false_eq_true, ↓reduceIte]
      exact mul_nonneg (Nat.cast_nonneg _) hp.le
    simpa [Model.abs, Model.copySign, hsigned, hs] using (abs_of_nonneg hn).symm
  | true =>
    have hn : Model.toReal x ≤ 0 := by
      rw [hreal]
      simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
        hsign.trans hs, ↓reduceIte, Int.cast_neg]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hp.le
    have habs : Model.abs x = Model.neg x := by
      simp [Model.abs, Model.copySign, Model.neg, hsigned, hs]
    rw [habs, Model.toReal_neg x hx, abs_of_nonpos hn]

/-- The executable pivot comparison agrees with the exact component magnitudes. -/
theorem imagDominant_eq_true_iff {fmt : FloatFormat} (z : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (hz : isFinite z = true) :
    imagDominant z = true ↔ |(toComplex z).re| < |(toComplex z).im| := by
  obtain ⟨hre, him⟩ := (isFinite_eq_true_iff z).1 hz
  simp only [imagDominant, decide_eq_true_eq]
  rw [Model.compare_eq_some_lt_iff_toReal_lt_of_isFinite _ _
      (by simpa using hre) (by simpa using him),
    toReal_abs z.re hfmt hre, toReal_abs z.im hfmt him]
  rfl

/-- Selecting a component and clearing its sign preserves finiteness. -/
theorem isFinite_magnitudeScale {fmt : FloatFormat} (z : ExecComplex fmt)
    (hz : isFinite z = true) : Model.isFinite (magnitudeScale z) = true := by
  obtain ⟨hre, him⟩ := (isFinite_eq_true_iff z).1 hz
  unfold magnitudeScale
  split <;> simp_all

/-- For a finite IEEE complex value, the common scale is the larger absolute component. -/
theorem toReal_magnitudeScale {fmt : FloatFormat} (z : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (hz : isFinite z = true) :
    Model.toReal (magnitudeScale z) = max |(toComplex z).re| |(toComplex z).im| := by
  obtain ⟨hre, him⟩ := (isFinite_eq_true_iff z).1 hz
  unfold magnitudeScale
  split
  next h =>
    rw [toReal_abs z.im hfmt him, max_eq_right ((imagDominant_eq_true_iff z hfmt hz).1 h).le]
    rfl
  next h =>
    have hle := le_of_not_gt (mt (imagDominant_eq_true_iff z hfmt hz).2 h)
    rw [toReal_abs z.re hfmt hre, max_eq_left hle]
    rfl

private theorem isZero_eq_true_iff_toReal_eq_zero {fmt : FloatFormat} (x : Model fmt)
    (hx : Model.isFinite x = true) :
    Model.isZero x = true ↔ Model.toReal x = 0 := by
  refine ⟨Model.toReal_eq_zero_of_isZero x, ?_⟩
  intro hreal
  obtain ⟨d, hd⟩ := Model.exists_toDyadic?_of_isFinite hx
  have hdreal : d.toReal = 0 := by simpa [Model.toReal_eq, hd] using hreal
  have hmant : d.significand = 0 := by
    have hs := (mul_eq_zero.mp hdreal).resolve_right
      (FloatLib.Floats.Formats.Flocq.bpow.ne_zero Numerics.binaryRadix d.exponent)
    cases hsign : d.negative <;>
      simpa [Numerics.Dyadic.signedSignificand, hsign] using hs
  exact Model.isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hd hmant

/-- The nine scalar rounding sites of ratio division with a real-component pivot. -/
noncomputable def roundedDivRealDominant (fmt : FloatFormat) (x y : ℂ) : ℂ :=
  let ratio := Model.roundAt fmt (y.im / y.re)
  let denominator := Model.roundAt fmt (y.re + Model.roundAt fmt (y.im * ratio))
  ⟨Model.roundAt fmt ((Model.roundAt fmt (x.re + Model.roundAt fmt (x.im * ratio))) /
      denominator),
    Model.roundAt fmt ((Model.roundAt fmt (x.im - Model.roundAt fmt (x.re * ratio))) /
      denominator)⟩

/-- Scalar domain obligations for the selected branch of ratio division. -/
structure DivBranchFinite {fmt : FloatFormat} (x y : ExecComplex fmt) : Prop where
  /-- The pivot used to form the ratio is nonzero. -/
  pivot_nonzero : Model.isZero y.re = false
  /-- The rounded component ratio is finite. -/
  ratio : Model.isFinite (Model.div y.im y.re) = true
  /-- The product used to form the denominator is finite. -/
  denominator_product : Model.isFinite (Model.mul y.im (Model.div y.im y.re)) = true
  /-- The rounded denominator is finite. -/
  denominator : Model.isFinite (Model.add y.re (Model.mul y.im (Model.div y.im y.re))) = true
  /-- The rounded denominator used by both final divisions is nonzero. -/
  denominator_nonzero :
    Model.isZero (Model.add y.re (Model.mul y.im (Model.div y.im y.re))) = false
  /-- The product used in the real numerator is finite. -/
  re_product : Model.isFinite (Model.mul x.im (Model.div y.im y.re)) = true
  /-- The product used in the imaginary numerator is finite. -/
  im_product : Model.isFinite (Model.mul x.re (Model.div y.im y.re)) = true
  /-- The rounded real numerator is finite. -/
  re_numerator : Model.isFinite (Model.add x.re (Model.mul x.im (Model.div y.im y.re))) = true
  /-- The rounded imaginary numerator is finite. -/
  im_numerator : Model.isFinite (Model.sub x.im (Model.mul x.re (Model.div y.im y.re))) = true
  /-- Both final quotients are finite. -/
  result : isFinite (divRealDominant x y) = true

/--
The real-pivot division branch evaluates its stated rounded expression when the IEEE inputs and
all scalar intermediates are finite, and both the pivot and rounded denominator are nonzero.
-/
theorem toComplex_divRealDominant {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (hx : isFinite x = true) (hy : isFinite y = true)
    (h : DivBranchFinite x y) :
    toComplex (divRealDominant x y) =
      roundedDivRealDominant fmt (toComplex x) (toComplex y) := by
  obtain ⟨hxre, hxim⟩ := (isFinite_eq_true_iff x).1 hx
  obtain ⟨hyre, hyim⟩ := (isFinite_eq_true_iff y).1 hy
  obtain ⟨hore, hoim⟩ := (isFinite_eq_true_iff _).1 h.result
  have hr := Model.toReal_div_eq_roundAt y.im y.re hfmt hyim hyre h.pivot_nonzero h.ratio
  have hd := Model.toReal_add_eq_roundAt _ _ hfmt hyre h.denominator_product h.denominator
  rw [Model.toReal_mul_eq_roundAt _ _ hfmt hyim h.ratio h.denominator_product, hr] at hd
  apply Complex.ext
  · change Model.toReal (Model.div _ _) = _
    rw [Model.toReal_div_eq_roundAt _ _ hfmt h.re_numerator h.denominator
        h.denominator_nonzero hore,
      Model.toReal_add_eq_roundAt _ _ hfmt hxre h.re_product h.re_numerator,
      Model.toReal_mul_eq_roundAt _ _ hfmt hxim h.ratio h.re_product, hr, hd]
    rfl
  · change Model.toReal (Model.div _ _) = _
    rw [Model.toReal_div_eq_roundAt _ _ hfmt h.im_numerator h.denominator
        h.denominator_nonzero hoim,
      Model.toReal_sub_eq_roundAt _ _ hfmt hxim h.im_product h.im_numerator,
      Model.toReal_mul_eq_roundAt _ _ hfmt hxre h.ratio h.im_product, hr, hd]
    rfl

end Internal

/--
Ratio-division semantics, branching on the exact magnitudes of the denominator components.

In the imaginary-dominant branch the final rounded quotient is conjugated, as in the executable
code. This is a rounded expression, not exact division in `ℂ`.
-/
noncomputable def roundedDiv (fmt : FloatFormat) (x y : ℂ) : ℂ :=
  if |y.re| < |y.im| then
    starRingEnd ℂ (Internal.roundedDivRealDominant fmt ⟨x.im, x.re⟩ ⟨y.im, y.re⟩)
  else Internal.roundedDivRealDominant fmt x y

/--
Finite inputs and all scalar domain obligations in the selected division branch.

The pivot and the rounded denominator must both be nonzero; every intermediate and both final
quotients must be finite. No obligation is imposed on the branch that is not executed.
-/
structure DivFinite {fmt : FloatFormat} (x y : ExecComplex fmt) : Prop where
  /-- Both numerator components are finite. -/
  left : isFinite x = true
  /-- Both denominator components are finite. -/
  right : isFinite y = true
  /-- Domain obligations after choosing the larger denominator component as pivot. -/
  branch : if Internal.imagDominant y then
      Internal.DivBranchFinite (Internal.swap x) (Internal.swap y)
    else Internal.DivBranchFinite x y

/-- The selected division branch produces finite components under `DivFinite`. -/
theorem isFinite_div {fmt : FloatFormat} (x y : ExecComplex fmt) (h : DivFinite x y) :
    isFinite (x / y) = true := by
  change isFinite (div x y) = true
  unfold div
  split
  next hb =>
    have hbranch := h.branch
    rw [ite_eq_left hb] at hbranch
    simpa [isFinite, conj] using hbranch.result
  next hb =>
    have hbranch := h.branch
    rw [ite_eq_right hb] at hbranch
    exact hbranch.result

/-- Division agrees with the selected ratio formula and all nine scalar rounding sites. -/
theorem toComplex_div_eq_roundedDiv {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (h : DivFinite x y) :
    toComplex (x / y) = roundedDiv fmt (toComplex x) (toComplex y) := by
  change toComplex (div x y) = _
  unfold div roundedDiv
  have hbranch := h.branch
  split
  next hb =>
    rw [ite_eq_left ((Internal.imagDominant_eq_true_iff y hfmt h.right).1 hb)]
    rw [ite_eq_left hb] at hbranch
    rw [toComplex_conj _ hbranch.result,
      Internal.toComplex_divRealDominant _ _ hfmt
        (by simpa [isFinite, Internal.swap, Bool.and_comm] using h.left)
        (by simpa [isFinite, Internal.swap, Bool.and_comm] using h.right) hbranch]
    rfl
  next hb =>
    rw [ite_eq_right (mt (Internal.imagDominant_eq_true_iff y hfmt h.right).2 hb)]
    rw [ite_eq_right hb] at hbranch
    exact Internal.toComplex_divRealDominant x y hfmt h.left h.right hbranch

/-- Infinity determines magnitude when neither component is a signaling NaN. -/
theorem magnitude_eq_posInf_of_isInf {fmt : FloatFormat} (z : ExecComplex fmt)
    (hre : Model.isSNaN z.re = false) (him : Model.isSNaN z.im = false)
    (hinf : Model.isInf z.re = true ∨ Model.isInf z.im = true) :
    magnitude z = Model.posInf fmt := by
  have hfinite : isFinite z = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hz
    obtain ⟨hzre, hzim⟩ := (isFinite_eq_true_iff z).1 hz
    rcases hinf with hr | hi
    · have := Model.isInf_eq_false_of_isFinite_eq_true z.re hzre
      simp [hr] at this
    · have := Model.isInf_eq_false_of_isFinite_eq_true z.im hzim
      simp [hi] at this
  rcases hinf with hr | hi
  · simp [magnitude, hfinite, hr, hre, him]
  · simp [magnitude, hfinite, hi, hre, him]

/--
Rounded semantics of magnitude with the exact scale `max |re| |im|`.

The two divisions, two squares, sum, square root, and rescaling product each round separately.
Zero scale returns zero without any division.
-/
noncomputable def roundedMagnitude (fmt : FloatFormat) (z : ℂ) : ℝ :=
  let scale := max |z.re| |z.im|
  if scale = 0 then 0
  else
    let ratios : ℂ :=
      ⟨Model.roundAt fmt (z.re / scale), Model.roundAt fmt (z.im / scale)⟩
    Model.roundAt fmt (scale * Model.roundAt fmt (Real.sqrt (roundedNormSq fmt ratios)))

/--
Finite input and output of scaled magnitude, with obligations only on the nonzero-scale branch.

The rounded component ratios, their squares, and their sum must be finite. The sum must be a
valid scalar square-root input (zero of either sign, or a clear sign bit). Square-root finiteness
then follows from the scalar theorem.

These intermediate-range conditions do not follow merely from finite inputs or from the exact
norm fitting in the format. The semantic theorem separately requires the conventional IEEE bias.
-/
structure MagnitudeFinite {fmt : FloatFormat} (z : ExecComplex fmt) : Prop where
  /-- Both input components are finite. -/
  input : isFinite z = true
  /-- Restoring the scale gives a finite result. -/
  result : Model.isFinite (magnitude z) = true
  /-- Scaled squares and square-root domain, needed only for a nonzero scale. -/
  scaled : Model.isZero (Internal.magnitudeScale z) = false →
    NormSqFinite (Internal.magnitudeRatios z) ∧
      (Model.isZero (normSq (Internal.magnitudeRatios z)) = true ∨
        Model.signBit (normSq (Internal.magnitudeRatios z)) = false)

/-- Scaled magnitude agrees with its seven scalar rounding sites, or the zero branch. -/
theorem toReal_magnitude_eq_roundedMagnitude {fmt : FloatFormat} (z : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (h : MagnitudeFinite z) :
    Model.toReal (magnitude z) = roundedMagnitude fmt (toComplex z) := by
  have hsfinite := Internal.isFinite_magnitudeScale z h.input
  have hsreal := Internal.toReal_magnitudeScale z hfmt h.input
  have hszero := Internal.isZero_eq_true_iff_toReal_eq_zero
    (Internal.magnitudeScale z) hsfinite
  rw [hsreal] at hszero
  unfold magnitude roundedMagnitude
  rw [ite_eq_left h.input]
  dsimp only
  split
  next hz =>
    rw [ite_eq_left (hszero.1 hz), hsreal, hszero.1 hz]
  next hz =>
    rw [ite_eq_right (mt hszero.2 hz)]
    obtain ⟨hnorm, hdomain⟩ := h.scaled (Bool.eq_false_of_not_eq_true hz)
    have hsqrt := Model.isFinite_sqrt_of_isFinite _ hfmt hnorm.result hdomain
    have hout : Model.isFinite
        (Model.mul (Internal.magnitudeScale z)
          (Model.sqrt (normSq (Internal.magnitudeRatios z)))) = true := by
      simpa [magnitude, h.input, hz] using h.result
    rw [Model.toReal_mul_eq_roundAt _ _ hfmt hsfinite hsqrt hout,
      Model.toReal_sqrt_eq_roundAt _ hfmt hnorm.result hdomain,
      toReal_normSq_eq_roundedNormSq _ hfmt hnorm, hsreal]
    obtain ⟨hre, him⟩ := (isFinite_eq_true_iff z).1 h.input
    obtain ⟨hrre, hrim⟩ := (isFinite_eq_true_iff _).1 hnorm.input
    have hratios : toComplex (Internal.magnitudeRatios z) =
        (⟨Model.roundAt fmt ((toComplex z).re /
            max |(toComplex z).re| |(toComplex z).im|),
          Model.roundAt fmt ((toComplex z).im /
            max |(toComplex z).re| |(toComplex z).im|)⟩ : ℂ) := by
      apply Complex.ext
      · change Model.toReal (Model.div z.re _) = _
        rw [Model.toReal_div_eq_roundAt _ _ hfmt hre hsfinite
          (Bool.eq_false_of_not_eq_true hz) hrre, hsreal]
        rfl
      · change Model.toReal (Model.div z.im _) = _
        rw [Model.toReal_div_eq_roundAt _ _ hfmt him hsfinite
          (Bool.eq_false_of_not_eq_true hz) hrim, hsreal]
        rfl
    rw [hratios]

end
end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
