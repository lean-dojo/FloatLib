/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.External.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Extrema.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Report
public import FloatLib.Floats.Formats.P3109.Arithmetic.Kernel
public import FloatLib.Tactic.ReferencePaths

public import FloatLib.Floats.Formats.P3109.KernelPath.Selection
public import FloatLib.Floats.Formats.P3109.KernelPath.Root
public import FloatLib.Floats.Formats.P3109.KernelPath.Queries
public import FloatLib.Floats.Formats.P3109.Arithmetic.Square
public import FloatLib.Floats.Formats.P3109.KernelPath.Flat
public import FloatLib.Floats.Formats.P3109.KernelPath.Mixed
public import FloatLib.Floats.Formats.P3109.Arithmetic.Instances
public import FloatLib.Tactic.KernelOptimize

/-!
# Kernel rules for P3109 arithmetic

P3109 Interim Report v4.1 (14 September 2026), §§4.7, 4.10 to 4.13 and 4.16, an unapproved
draft. These are the equations that `float_decide` rewrites a P3109 computation with, so that
Lean's kernel evaluates it on natural-number encodings and builds no rational. Each holds for
every valid descriptor of every operand and of the destination, every rounding mode with every
supplied random word, every saturation mode and every operand:

* `Add_eq_kernel`, `Subtract_eq_kernel`, `Multiply_eq_kernel`, `Divide_eq_kernel`,
  `FMA_eq_kernel`, `FAA_eq_kernel`, `Recip_eq_kernel`, `CopySign_eq_kernel`, `Negate_eq_kernel`,
  `Abs_eq_kernel`, `Sqrt_eq_kernel`, `RSqrt_eq_kernel`, `Hypot_eq_kernel`, `square_eq_kernel`:
  the public operation is the value that stores the flat operation of `KernelPath.Flat` on the
  encodings;
* `Minimum_eq_kernel` to `MaximumFinite_eq_kernel`, the ten extrema of §4.11, which one command
  declares from the proof that each selects an operand, and `Clamp_eq_kernel`;
* `CompareLess_eq_kernel` to `CompareGreaterEqual_eq_kernel` and `compare_eq_kernel`: the
  comparisons of §4.12 and the order behind `==` and `<` are the flat comparisons;
* `isZero_eq`, `IsNaN_eq_kernel` to `IsOne_eq_kernel`, `NextGreaterThan_eq_kernel`,
  `NextLessThan_eq_kernel`: the queries of §4.13 and the neighbours of §4.16 are flat tests and
  codes, and the zero test is its own rule;
* `reference_add`, `reference_sub`, `reference_mul`, `reference_div`, `reference_fma`,
  `reference_sqrt`: the reference operation of a format, which `x + y` and its siblings are
  rewritten to, is the public operation into the same format under the default policy
  (nearest-even, no saturation);
* `convert_eq_kernel`: the projection of the exact value of a code of one format into another
  format is the flat conversion of the encoding;
* `Convert_binary_eq_kernel`: the mixed conversion of a value of a binary interchange format
  into a P3109 format is the flat conversion of the binary word, for every binary descriptor.
  The rules of the mixed arithmetic on operands of any kinds are in `P3109.KernelPath.Mixed`;
* `ofRat_eq_kernel`: the projection of a rational is the flat projection of its numerator and
  denominator, and `ofNat_eq_kernel` and `ofScientific_eq_kernel` project a natural-number
  literal and a decimal literal as they are written, with no normalization of the ratio;
* `toNatBits_ofNatBits_kernel`: the encoding of a stored natural number is that number reduced
  to the width, so a nested computation stays on natural numbers.

A stochastic mode is evaluated on the random word it carries: these equations say nothing about
a distribution.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.KernelPath

open FloatLib.Floats.Formats.P3109

variable {format leftFormat rightFormat thirdFormat : Format}

/-- The encoding of the value that stores `bits` is `bits` reduced to the width, in the form
that the kernel computes. -/
@[kernel_optimize] theorem toNatBits_ofNatBits_kernel (bits : Nat) :
    (ExecFloat.P3109.ofNatBits (format := format) bits).toNatBits =
      Nat.mod bits (Nat.pow 2 format.bitWidth) :=
  ExecFloat.P3109.toNatBits_ofNatBits bits

/-- P3109 interim report v4.1, §4.10.3: `Add` is the flat addition on the encodings. -/
@[kernel_optimize (cost := 320)] theorem Add_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (y : ExecFloat.P3109 rightFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.Add x y target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.add leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) 0 x.toNatBits y.toNatBits) := by
  rw [Flat.add_eq, add_eq]

/-- P3109 interim report v4.1, §4.10.3: `Subtract` is the flat addition with the second sign
    flipped. -/
@[kernel_optimize (cost := 320)] theorem Subtract_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (y : ExecFloat.P3109 rightFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.Subtract x y target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.add leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) 1 x.toNatBits y.toNatBits) := by
  rw [Flat.add_eq, sub_eq]

/-- P3109 interim report v4.1, §4.10.4: `Multiply` is the flat multiplication on the encodings. -/
@[kernel_optimize (cost := 320)] theorem Multiply_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (y : ExecFloat.P3109 rightFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.Multiply x y target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.mul leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits y.toNatBits) := by
  rw [Flat.mul_eq, mul_eq]

/-- P3109 interim report v4.1, §4.10.5: `Divide` is the flat division on the encodings. -/
@[kernel_optimize (cost := 320)] theorem Divide_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (y : ExecFloat.P3109 rightFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.Divide x y target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.div leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits y.toNatBits) := by
  rw [Flat.div_eq, div_eq]

/-- P3109 interim report v4.1, §4.10.6: `FMA` is the flat fused multiply-add on the encodings. -/
@[kernel_optimize (cost := 400)] theorem FMA_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (y : ExecFloat.P3109 rightFormat) (z : ExecFloat.P3109 thirdFormat) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.FMA x y z target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.fma leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          thirdFormat.bitWidth thirdFormat.precision (sgOf thirdFormat) (exOf thirdFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits y.toNatBits
          z.toNatBits) := by
  rw [Flat.fma_eq, fma_eq]

/-- P3109 interim report v4.1, §4.10.1: `Negate` is the flat conversion with the sign flipped. -/
@[kernel_optimize (cost := 250)] theorem Negate_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.Negate x target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.convert leftFormat.bitWidth leftFormat.precision (sgOf leftFormat)
          (exOf leftFormat) target.bitWidth target.precision (sgOf target) (exOf target)
          (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation) 1
          x.toNatBits) := by
  rw [Flat.convert_eq, negate_eq]

/-- P3109 interim report v4.1, §4.10.1: `Abs` is the flat conversion with the sign cleared. -/
@[kernel_optimize (cost := 250)] theorem Abs_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.Abs x target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.convert leftFormat.bitWidth leftFormat.precision (sgOf leftFormat)
          (exOf leftFormat) target.bitWidth target.precision (sgOf target) (exOf target)
          (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation) 2
          x.toNatBits) := by
  rw [Flat.convert_eq, abs_eq]

/-- P3109 interim report v4.1, §4.10.8: `Recip` is the flat reciprocal on the encoding. -/
@[kernel_optimize (cost := 300)] theorem Recip_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.Recip x target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.recip leftFormat.bitWidth leftFormat.precision (sgOf leftFormat)
          (exOf leftFormat) target.bitWidth target.precision (sgOf target) (exOf target)
          (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation)
          x.toNatBits) := by
  rw [Flat.recip_eq, recip_eq]

/-- P3109 interim report v4.1, §4.10.7: `FAA` is the flat fused add-add on the encodings. -/
@[kernel_optimize (cost := 400)] theorem FAA_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (y : ExecFloat.P3109 rightFormat) (z : ExecFloat.P3109 thirdFormat) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.FAA x y z target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.faa leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          thirdFormat.bitWidth thirdFormat.precision (sgOf thirdFormat) (exOf thirdFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits y.toNatBits
          z.toNatBits) := by
  rw [Flat.faa_eq, faa_eq]

/-- P3109 interim report v4.1, §4.10.2: `CopySign` is the flat copy of a sign on the
encodings. -/
@[kernel_optimize (cost := 300)] theorem CopySign_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (y : ExecFloat.P3109 rightFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.CopySign x y target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.copySign leftFormat.bitWidth leftFormat.precision (sgOf leftFormat)
          (exOf leftFormat) rightFormat.bitWidth rightFormat.precision (sgOf rightFormat)
          (exOf rightFormat) target.bitWidth target.precision (sgOf target) (exOf target)
          (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits
          y.toNatBits) := by
  rw [Flat.copySign_eq, copySign_eq]

/-- P3109 interim report v4.1, §4.10.8: `Sqrt` is the flat square root on the encoding. -/
@[kernel_optimize (cost := 340)] theorem Sqrt_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.Sqrt x target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.sqrt leftFormat.bitWidth leftFormat.precision (sgOf leftFormat)
          (exOf leftFormat) target.bitWidth target.precision (sgOf target) (exOf target)
          (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation)
          x.toNatBits) := by
  rw [Flat.sqrt_eq, sqrt_eq]

/-- P3109 interim report v4.1, §4.10.8: `RSqrt` is the flat reciprocal square root on the
encoding. -/
@[kernel_optimize (cost := 340)] theorem RSqrt_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.RSqrt x target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.rsqrt leftFormat.bitWidth leftFormat.precision (sgOf leftFormat)
          (exOf leftFormat) target.bitWidth target.precision (sgOf target) (exOf target)
          (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation)
          x.toNatBits) := by
  rw [Flat.rsqrt_eq, rsqrt_eq]

/-- P3109 interim report v4.1, §4.10.14: `Hypot` is the flat hypotenuse on the encodings. -/
@[kernel_optimize (cost := 380)] theorem Hypot_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (y : ExecFloat.P3109 rightFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.Hypot x y target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.hypot leftFormat.bitWidth leftFormat.precision (sgOf leftFormat)
          (exOf leftFormat) rightFormat.bitWidth rightFormat.precision (sgOf rightFormat)
          (exOf rightFormat) target.bitWidth target.precision (sgOf target) (exOf target)
          (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits
          y.toNatBits) := by
  rw [Flat.hypot_eq, hypot_eq]

/-- P3109 interim report v4.1, §4.12: `CompareLess` is the flat strict comparison of the
encodings. -/
@[kernel_optimize (cost := 150)] theorem CompareLess_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (y : ExecFloat.P3109 rightFormat) :
    ExecFloat.P3109.CompareLess x y =
      Flat.less leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
        rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
        x.toNatBits y.toNatBits := by
  rw [Flat.less_eq, compareLess_eq]

/-- P3109 interim report v4.1, §4.12: `CompareEqual` is the flat equality of the encodings. -/
@[kernel_optimize (cost := 150)] theorem CompareEqual_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (y : ExecFloat.P3109 rightFormat) :
    ExecFloat.P3109.CompareEqual x y =
      Flat.equal leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
        rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
        x.toNatBits y.toNatBits := by
  rw [Flat.equal_eq, compareEqual_eq]

/-- P3109 interim report v4.1, §4.12: `CompareLessEqual` is the flat comparison of the
encodings. -/
@[kernel_optimize (cost := 160)] theorem CompareLessEqual_eq_kernel
    (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat) :
    ExecFloat.P3109.CompareLessEqual x y =
      Flat.lessEqual leftFormat.bitWidth leftFormat.precision (sgOf leftFormat)
        (exOf leftFormat) rightFormat.bitWidth rightFormat.precision (sgOf rightFormat)
        (exOf rightFormat) x.toNatBits y.toNatBits := by
  rw [Flat.lessEqual_eq, compareLessEqual_eq]

/-- P3109 interim report v4.1, §4.12: `CompareGreater` is the flat strict comparison with the
encodings exchanged. -/
@[kernel_optimize (cost := 150)] theorem CompareGreater_eq_kernel
    (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat) :
    ExecFloat.P3109.CompareGreater x y =
      Flat.less rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
        leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
        y.toNatBits x.toNatBits := by
  rw [Flat.less_eq, compareGreater_eq]

/-- P3109 interim report v4.1, §4.12: `CompareGreaterEqual` is the flat comparison with the
encodings exchanged. -/
@[kernel_optimize (cost := 160)] theorem CompareGreaterEqual_eq_kernel
    (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat) :
    ExecFloat.P3109.CompareGreaterEqual x y =
      Flat.lessEqual rightFormat.bitWidth rightFormat.precision (sgOf rightFormat)
        (exOf rightFormat) leftFormat.bitWidth leftFormat.precision (sgOf leftFormat)
        (exOf leftFormat) y.toNatBits x.toNatBits := by
  rw [Flat.lessEqual_eq, compareGreaterEqual_eq]

/-- The order behind `==` and `<` on P3109 values (§4.12) is the flat comparisons of the
encodings. -/
@[kernel_optimize (cost := 450)] theorem compare_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (y : ExecFloat.P3109 rightFormat) :
    ExecFloat.P3109.compare x y =
      Bool.casesOn (motive := fun _ => Option Ordering)
        (Flat.less leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          x.toNatBits y.toNatBits)
        (Bool.casesOn (motive := fun _ => Option Ordering)
          (Flat.less rightFormat.bitWidth rightFormat.precision (sgOf rightFormat)
            (exOf rightFormat) leftFormat.bitWidth leftFormat.precision (sgOf leftFormat)
            (exOf leftFormat) y.toNatBits x.toNatBits)
          (Bool.casesOn (motive := fun _ => Option Ordering)
            (Flat.equal leftFormat.bitWidth leftFormat.precision (sgOf leftFormat)
              (exOf leftFormat) rightFormat.bitWidth rightFormat.precision (sgOf rightFormat)
              (exOf rightFormat) x.toNatBits y.toNatBits)
            none (some Ordering.eq))
          (some Ordering.gt))
        (some Ordering.lt) := by
  rw [Flat.less_eq, Flat.less_eq, Flat.equal_eq, compare_eq]

attribute [kernel_optimize (cost := 20)] isZero_eq

/-- P3109 interim report v4.1, §4.13: `IsNaN` is the flat test of the NaN code. -/
@[kernel_optimize (cost := 30)] theorem IsNaN_eq_kernel (x : ExecFloat.P3109 format) :
    x.IsNaN = Flat.isNaN format.bitWidth (sgOf format) x.toNatBits := by
  rw [Flat.isNaN_eq, isNaN_eq]

/-- P3109 interim report v4.1, §4.13: `IsInfinite` is the flat test of the infinity codes. -/
@[kernel_optimize (cost := 40)] theorem IsInfinite_eq_kernel (x : ExecFloat.P3109 format) :
    x.IsInfinite = Flat.isInfinite format.bitWidth (sgOf format) (exOf format) x.toNatBits := by
  rw [Flat.isInfinite_eq, isInfinite_eq]

/-- P3109 interim report v4.1, §4.13: `IsFinite` is the flat test of the code. -/
@[kernel_optimize (cost := 50)] theorem IsFinite_eq_kernel (x : ExecFloat.P3109 format) :
    x.IsFinite = Flat.isFinite format.bitWidth (sgOf format) (exOf format) x.toNatBits := by
  rw [Flat.isFinite_eq, isFinite_eq]

/-- P3109 interim report v4.1, §4.13: `IsSignMinus` is the flat test of the sign half. -/
@[kernel_optimize (cost := 30)] theorem IsSignMinus_eq_kernel (x : ExecFloat.P3109 format) :
    x.IsSignMinus = Flat.isSignMinus format.bitWidth (sgOf format) x.toNatBits := by
  rw [Flat.isSignMinus_eq, isSignMinus_eq]

/-- P3109 interim report v4.1, §4.13: `IsNormal` is the flat test of the magnitude code. -/
@[kernel_optimize (cost := 70)] theorem IsNormal_eq_kernel (x : ExecFloat.P3109 format) :
    x.IsNormal =
      Flat.isNormal format.bitWidth format.precision (sgOf format) (exOf format)
        x.toNatBits := by
  rw [Flat.isNormal_eq, isNormal_eq]

/-- P3109 interim report v4.1, §4.13: `IsSubnormal` is the flat test of the magnitude code. -/
@[kernel_optimize (cost := 70)] theorem IsSubnormal_eq_kernel (x : ExecFloat.P3109 format) :
    x.IsSubnormal =
      Flat.isSubnormal format.bitWidth format.precision (sgOf format) (exOf format)
        x.toNatBits := by
  rw [Flat.isSubnormal_eq, isSubnormal_eq]

/-- P3109 interim report v4.1, §4.13: `IsOne` is the flat comparison of the numerator and the
denominator of the code. -/
@[kernel_optimize (cost := 80)] theorem IsOne_eq_kernel (x : ExecFloat.P3109 format) :
    x.IsOne =
      Flat.isOne format.bitWidth format.precision (sgOf format) (exOf format) x.toNatBits := by
  rw [Flat.isOne_eq, isOne_eq]

/-- P3109 interim report v4.1, §4.16: `NextGreaterThan` stores the flat successor of the
code. -/
@[kernel_optimize (cost := 60)] theorem NextGreaterThan_eq_kernel
    (x : ExecFloat.P3109 format) :
    x.NextGreaterThan =
      ExecFloat.P3109.ofNatBits (Flat.nextUp format.bitWidth (sgOf format) x.toNatBits) := by
  rw [Flat.nextUp_eq, nextGreaterThan_eq]

/-- P3109 interim report v4.1, §4.16: `NextLessThan` stores the flat predecessor of the code. -/
@[kernel_optimize (cost := 60)] theorem NextLessThan_eq_kernel (x : ExecFloat.P3109 format) :
    x.NextLessThan =
      ExecFloat.P3109.ofNatBits (Flat.nextDown format.bitWidth (sgOf format) x.toNatBits) := by
  rw [Flat.nextDown_eq, nextLessThan_eq]

/-- The square of a value is the flat multiplication of its encoding by itself. -/
@[kernel_optimize (cost := 320)] theorem square_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.square x target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.mul leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits x.toNatBits) := by
  rw [Flat.mul_eq, ← mul_eq]
  rfl

/-- P3109 interim report v4.1, §4.9.1: the conversion of a binary interchange value into a
P3109 format is the flat `convertBinary` on its encoding. -/
@[kernel_optimize (cost := 300)] theorem Convert_binary_eq_kernel
    {fmt : BinaryInterchange.FloatFormat} (x : BinaryInterchange.Model fmt) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Arithmetic.Mixed.Convert (Arithmetic.Destination.p3109 target) x mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.convertBinary fmt target.bitWidth target.precision (sgOf target) (exOf target)
          (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation)
          x.toNatBits) := by
  rw [Flat.convertBinary_eq, convertBinary_eq]

set_option hygiene false in
/-- `extremum_rule Name Op mx mag var selects` declares the kernel rule `Name` of the extremum
`Op` of §4.11 from the proof `selects` that it selects with the options `mx`, `mag` and
`var`. -/
local macro "extremum_rule " name:ident op:ident mx:num mag:num var:num selects:term : command =>
  `(/-- P3109 interim report v4.1, §4.11: this extremum of two values of independent formats is
    the flat `extremum`, with its three options, on the encodings, projected once into the
    destination. -/
    @[kernel_optimize (cost := 330)] theorem $name (x : ExecFloat.P3109 leftFormat)
        (y : ExecFloat.P3109 rightFormat) (target : Format) (mode : RoundingMode)
        (saturation : SaturationMode) :
        $op x y target mode saturation =
          ExecFloat.P3109.ofNatBits
            (Flat.extremum $mx $mag $var leftFormat.bitWidth leftFormat.precision
              (sgOf leftFormat) (exOf leftFormat) rightFormat.bitWidth rightFormat.precision
              (sgOf rightFormat) (exOf rightFormat) target.bitWidth target.precision
              (sgOf target) (exOf target) (modeIndex mode) (modeWidth mode) (modeRandom mode)
              (satIndex saturation) x.toNatBits y.toNatBits) := by
      rw [Flat.extremum_eq]
      exact binary_eq_extremum $selects x y target mode saturation)

extremum_rule Minimum_eq_kernel ExecFloat.P3109.Minimum 0 0 0 minimum_selects
extremum_rule Maximum_eq_kernel ExecFloat.P3109.Maximum 1 0 0 maximum_selects
extremum_rule MinimumNumber_eq_kernel ExecFloat.P3109.MinimumNumber 0 0 1 minimum_selects.number
extremum_rule MaximumNumber_eq_kernel ExecFloat.P3109.MaximumNumber 1 0 1 maximum_selects.number
extremum_rule MinimumMagnitude_eq_kernel ExecFloat.P3109.MinimumMagnitude 0 1 0
  minimumMagnitude_selects
extremum_rule MaximumMagnitude_eq_kernel ExecFloat.P3109.MaximumMagnitude 1 1 0
  maximumMagnitude_selects
extremum_rule MinimumMagnitudeNumber_eq_kernel ExecFloat.P3109.MinimumMagnitudeNumber 0 1 1
  minimumMagnitude_selects.number
extremum_rule MaximumMagnitudeNumber_eq_kernel ExecFloat.P3109.MaximumMagnitudeNumber 1 1 1
  maximumMagnitude_selects.number
extremum_rule MinimumFinite_eq_kernel ExecFloat.P3109.MinimumFinite 0 0 2
  minimum_selects.number.finite
extremum_rule MaximumFinite_eq_kernel ExecFloat.P3109.MaximumFinite 1 0 2
  maximum_selects.number.finite

/-- P3109 interim report v4.1, §4.11.4: `Clamp` is the flat clamp on the encodings. -/
@[kernel_optimize (cost := 420)] theorem Clamp_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (y : ExecFloat.P3109 rightFormat) (z : ExecFloat.P3109 thirdFormat) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.Clamp x y z target mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.clamp leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          thirdFormat.bitWidth thirdFormat.precision (sgOf thirdFormat) (exOf thirdFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits y.toNatBits
          z.toNatBits) := by
  rw [Flat.clamp_eq, clamp_eq]

/-- P3109 interim report v4.1, §4.7.3: the projection of a rational is the flat projection of
    the ratio of its
numerator and its denominator. -/
@[kernel_optimize (cost := 250)] theorem ofRat_eq_kernel (value : Rat) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.ofRat (format := format) value mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.project format.bitWidth format.precision (sgOf format) (exOf format)
          (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation) 0
          (Int.casesOn (motive := fun _ => Nat) value.num (fun _ => 0) (fun _ => 1))
          value.num.natAbs value.den) := by
  have hs : Int.casesOn (motive := fun _ => Nat) value.num (fun _ => 0) (fun _ => 1) ≤ 1 := by
    cases value.num <;> simp
  rw [Flat.project_eq, ← projectRat_eq _ _ _ _ _ _ _ hs (fun _ _ => value.den_nz)]
  unfold ExecFloat.P3109.ofRat closed
  congr 2
  have hnum : (if Int.casesOn (motive := fun _ => Nat) value.num (fun _ => 0) (fun _ => 1) = 0
      then ((value.num.natAbs : Nat) : Rat) else -((value.num.natAbs : Nat) : Rat)) =
        (value.num : Rat) := by
    cases hnum : value.num with
    | ofNat n => simp
    | negSucc n =>
        simp only [Nat.one_ne_zero, ite_false, Int.natAbs_negSucc]
        push_cast [Int.negSucc_eq]
        ring
  rw [hnum, Rat.num_div_den]

/-- P3109 interim report v4.1, §4.7.3: the projection of the ratio of two natural numbers with a
    nonzero
denominator is the flat projection of the two numbers as they are, in any common scale. -/
theorem ofRat_ratio (n d : Nat) (hd : d ≠ 0) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.ofRat (format := format) ((n : Rat) / (d : Rat)) mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.project format.bitWidth format.precision (sgOf format) (exOf format)
          (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation) 0 0 n d) := by
  rw [Flat.project_eq, ← projectRat_eq _ _ _ _ _ _ _ (Nat.zero_le 1) (fun _ _ => hd)]
  unfold ExecFloat.P3109.ofRat closed
  simp

/-- A natural-number literal of a P3109 format is the flat projection of the number over one,
nearest-even with no saturation.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7 and 4.10.3–4.10.8.
-/
@[kernel_optimize] theorem ofNat_eq_kernel (value : Nat) :
    (OfNat.ofNat value : ExecFloat.P3109 format) =
      ExecFloat.P3109.ofNatBits
        (Flat.project format.bitWidth format.precision (sgOf format) (exOf format)
          (modeIndex .nearest) (modeWidth .nearest) (modeRandom .nearest) (satIndex .none)
          0 0 value 1) := by
  rw [← ofRat_ratio value 1 Nat.one_ne_zero]
  change ExecFloat.P3109.ofRat (value : Rat) = _
  simp

/-- A decimal literal of a P3109 format is the flat projection of its mantissa over or times the
power of ten, nearest-even with no saturation and with no normalization of the ratio.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7 and 4.10.3–4.10.8.
-/
@[kernel_optimize] theorem ofScientific_eq_kernel (mantissa : Nat) (exponentSign : Bool)
    (exponent : Nat) :
    (OfScientific.ofScientific mantissa exponentSign exponent : ExecFloat.P3109 format) =
      ExecFloat.P3109.ofNatBits
        (Bool.casesOn (motive := fun _ => Nat) exponentSign
          (Flat.project format.bitWidth format.precision (sgOf format) (exOf format)
            (modeIndex .nearest) (modeWidth .nearest) (modeRandom .nearest) (satIndex .none)
            0 0 (Nat.mul mantissa (Nat.pow 10 exponent)) 1)
          (Flat.project format.bitWidth format.precision (sgOf format) (exOf format)
            (modeIndex .nearest) (modeWidth .nearest) (modeRandom .nearest) (satIndex .none)
            0 0 mantissa (Nat.pow 10 exponent))) := by
  cases exponentSign
  · change _ = ExecFloat.P3109.ofNatBits
      (Flat.project _ _ _ _ _ _ _ _ 0 0 (mantissa * 10 ^ exponent) 1)
    rw [← ofRat_ratio _ 1 Nat.one_ne_zero]
    change ExecFloat.P3109.ofRat (OfScientific.ofScientific mantissa false exponent : Rat) = _
    rw [show (OfScientific.ofScientific mantissa false exponent : Rat) =
      ((mantissa * 10 ^ exponent : Nat) : Rat) from Rat.ofScientific_false_def]
    simp
  · change _ = ExecFloat.P3109.ofNatBits (Flat.project _ _ _ _ _ _ _ _ 0 0 mantissa (10 ^ exponent))
    rw [← ofRat_ratio _ _ (Nat.ne_of_gt (Nat.pow_pos (by decide)))]
    change ExecFloat.P3109.ofRat (OfScientific.ofScientific mantissa true exponent : Rat) = _
    rw [show (OfScientific.ofScientific mantissa true exponent : Rat) =
      mkRat mantissa (10 ^ exponent) from Rat.ofScientific_true_def, Rat.mkRat_eq_div]
    push_cast
    rfl

/-- P3109 interim report v4.1, §4.7.3: projecting the exact value of a code of one format into
    another format
is the flat conversion of the encoding. -/
@[kernel_optimize (cost := 250)] theorem convert_eq_kernel (x : ExecFloat.P3109 leftFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.projectRat (format := target) x.toClosedRat mode saturation =
      ExecFloat.P3109.ofNatBits
        (Flat.convert leftFormat.bitWidth leftFormat.precision (sgOf leftFormat)
          (exOf leftFormat) target.bitWidth target.precision (sgOf target) (exOf target)
          (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation) 0
          x.toNatBits) := by
  rw [Flat.convert_eq, convert_eq]

/-! ## The operations of one format

`x + y` and its siblings are rewritten to the reference operation of the format
(`ExecFloat.KernelPath.DirectReference`). These equations name it as the public operation, which
the rules above evaluate on encodings.
-/

section Reference

open FloatLib.Floats.ExecFloat

variable [Backend.PolicyFor (Codebook.Family format.codebook)]

/-- The reference addition of a P3109 format is `Add` into it, nearest-even, no saturation.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7 and 4.10.3–4.10.8.
-/
@[kernel_optimize] theorem reference_add [Backend.Portfolio (P3109.Plan.reference format .add)]
    (x y : ExecFloat.P3109 format) : Spec.add x y = P3109.Add x y := rfl

/-- The reference subtraction of a P3109 format is `Subtract` into it, nearest-even, no
saturation.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7 and 4.10.3–4.10.8.
-/
@[kernel_optimize] theorem reference_sub [Backend.Portfolio (P3109.Plan.reference format .sub)]
    (x y : ExecFloat.P3109 format) : Spec.sub x y = P3109.Subtract x y := rfl

/-- The reference multiplication of a P3109 format is `Multiply` into it, nearest-even, no
saturation.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7 and 4.10.3–4.10.8.
-/
@[kernel_optimize] theorem reference_mul [Backend.Portfolio (P3109.Plan.reference format .mul)]
    (x y : ExecFloat.P3109 format) : Spec.mul x y = P3109.Multiply x y := rfl

/-- The reference division of a P3109 format is `Divide` into it, nearest-even, no saturation.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7 and 4.10.3–4.10.8.
-/
@[kernel_optimize] theorem reference_div [Backend.Portfolio (P3109.Plan.reference format .div)]
    (x y : ExecFloat.P3109 format) : Spec.div x y = P3109.Divide x y := rfl

/-- The reference fused multiply-add of a P3109 format is `FMA` into it, nearest-even, no
saturation.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7 and 4.10.3–4.10.8.
-/
@[kernel_optimize] theorem reference_fma [Backend.Portfolio (P3109.Plan.reference format .fma)]
    (x y z : ExecFloat.P3109 format) : Spec.fma x y z = P3109.FMA x y z := rfl

/-- The reference square root of a P3109 format is `Sqrt` into it, nearest-even, no saturation.

Reference: P3109 Interim Report v4.1 (unapproved draft), §4.10.8.
-/
@[kernel_optimize] theorem reference_sqrt [Backend.Portfolio (P3109.Plan.reference format .sqrt)]
    (x : ExecFloat.P3109 format) : Spec.sqrt x = P3109.Sqrt x := rfl

end Reference

end FloatLib.Floats.Formats.P3109.KernelPath

/-!
# Parameterized P3109 reference execution

P3109 Interim Report v4.1, §§4.8–4.16 and 5.8 (unapproved draft).
Each candidate is the existing operation itself at its full function type,
including independent descriptors, policies and exact-decoder instances.
The kernel uses its defining equation, with arithmetic reusing the prepared
decoder and projectors from `Arithmetic.Kernel`. These registrations prove
execution equality; the operation's mathematical scope is given by the
imported proofs. They add no stochastic distribution or timing-bound claim.
-/

open FloatLib.Floats.ExecFloat

namespace FloatLib.Floats.ExecFloat.P3109

reference_paths Negate
reference_paths Abs
reference_paths CopySign
reference_paths Add
reference_paths Subtract
reference_paths Multiply
reference_paths Divide
reference_paths Recip
reference_paths FMA
reference_paths FAA
reference_paths Sqrt
reference_paths RSqrt
reference_paths Hypot
reference_paths Minimum
reference_paths Maximum
reference_paths MinimumNumber
reference_paths MaximumNumber
reference_paths MinimumMagnitude
reference_paths MaximumMagnitude
reference_paths MinimumMagnitudeNumber
reference_paths MaximumMagnitudeNumber
reference_paths MinimumFinite
reference_paths MaximumFinite
reference_paths Clamp
reference_paths CompareLess
reference_paths CompareLessEqual
reference_paths CompareEqual
reference_paths CompareGreater
reference_paths CompareGreaterEqual
reference_paths IsZero
reference_paths IsNaN
reference_paths IsInfinite
reference_paths IsFinite
reference_paths IsSignMinus
reference_paths IsOne
reference_paths IsNormal
reference_paths IsSubnormal
reference_paths NextGreaterThan
reference_paths NextLessThan

end FloatLib.Floats.ExecFloat.P3109

namespace FloatLib.Floats.Formats.P3109.Format

reference_paths BitwidthOf
reference_paths PrecisionOf
reference_paths SignednessOf
reference_paths DomainOf
reference_paths ExponentBitwidthOf
reference_paths TrailingSignificandBitwidthOf
reference_paths ExponentBiasOf
reference_paths MaxFiniteOf
reference_paths MinFiniteOf
reference_paths MinPositiveOf
reference_paths MaxSubnormalOf
reference_paths MinNormalOf

end FloatLib.Floats.Formats.P3109.Format

namespace FloatLib.Floats.Formats.P3109.Arithmetic.Mixed

reference_paths Convert
reference_paths Recip
reference_paths Add
reference_paths Subtract
reference_paths Multiply
reference_paths Divide
reference_paths FMA
reference_paths FAA
reference_paths ScaledAdd
reference_paths ScaledSubtract
reference_paths ScaledMultiply

end FloatLib.Floats.Formats.P3109.Arithmetic.Mixed

namespace FloatLib.Floats.Formats.P3109.Arithmetic.External

reference_paths BitwidthOf
reference_paths PrecisionOf
reference_paths SignednessOf
reference_paths DomainOf
reference_paths ExponentBitwidthOf
reference_paths TrailingSignificandBitwidthOf
reference_paths ExponentBiasOf
reference_paths MaxFiniteOf
reference_paths MinFiniteOf
reference_paths MinPositiveOf
reference_paths MaxSubnormalOf
reference_paths MinNormalOf

end FloatLib.Floats.Formats.P3109.Arithmetic.External
