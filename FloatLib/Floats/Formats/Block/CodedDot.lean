/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Block.CodedDot
public import FloatLib.Floats.Formats.Block.Reduction
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable
public import FloatLib.Floats.Formats.P3109.Arithmetic.Runtime
public import FloatLib.Tactic.ReferencePaths
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Dot products of stored block-scaled tensors

`Tensor.dotExact a b order` multiplies the decoded positions of two stored tensors, which may have
different formats, and accumulates the products in exact extended-rational arithmetic over the
positions of `order`. `OCP.MX.Dot fmt a b order reduction` uses the supplied reduction state and
rounds its decoded result once, to nearest even, into any binary descriptor. The default reduction
is exact. OCP MX 1.0, section 6.1, leaves internal precision to the implementation:
`Reduction.binary` supplies actual finite binary words as the intermediate states.

The products and sums are those of the closed extended-rational arithmetic
`P3109.Arithmetic.Multiply` and `P3109.Arithmetic.Add`, which this module shares with the P3109
    block
operations. The rules for values that are not finite are those of the extended rationals:

* NaN is absorbing, and so is a position that uses a scale with no finite value;
* zero times an infinity is NaN, and other products of infinities are signed;
* infinities of opposite sign sum to NaN;
* the sum starts at zero and runs in the order of `order`.

## Main results

* `Tensor.dotExact_finite`: with finite positions, the exact dot is the sum of the products.
* `Tensor.dotExact_eq_nan_of_left`, `Tensor.dotExact_eq_nan_of_right`,
  `Tensor.dotExact_eq_nan_of_scale`: one NaN position, or one scale with no finite value at a
  position of `order`, makes the dot NaN.
* `Tensor.toReal_Dot_eq_roundAt`, `Tensor.abs_toReal_Dot_sub_le`: for an IEEE descriptor and a
  finite result, the dot is one nearest-even rounding of the exact real sum, so its error is at
  most half an ulp for any number of positions and blocks.
* `Tensor.toReal_DotGeneral_eq_roundAt`: the same final-rounding contract for an ordered list
  of blocks, with the sum of the block sums as reference (OCP MX v1.0, §6.2).
* `Tensor.sum_value_mul_value`: block factorization. When the scales of both tensors are constant
  on the groups of `group`, the sum of the products of the rational values is the sum over the
  groups of the product of the two scales and the dot product of the stored elements.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Numerics FloatLib.Floats.Formats.BinaryInterchange

/-! ## Exact extended-rational arithmetic -/

namespace Extended

/-- One nearest-even projection into a binary descriptor, with its overflow and canonical
specials. -/
def round (fmt : FloatFormat) : NumericalValue Rat → Model fmt
  | .finite value => Model.roundRat fmt (value.num < 0) value.num.natAbs value.den
  | .infinity sign => if sign then Model.negInf fmt else Model.posInf fmt
  | .exceptional _ => Model.canonicalNaN fmt

private theorem signed_ratio_real (value : Rat) :
    Model.signedScaledRatToReal (value.num < 0) value.num.natAbs value.den 0 =
      (value : ℝ) := by
  rw [Rat.cast_def]
  by_cases h : value.num < 0
  · simp [Model.signedScaledRatToReal, Model.scaledRatToReal, Model.bpow, h, abs_of_neg h,
      neg_div]
  · simp [Model.signedScaledRatToReal, Model.scaledRatToReal, Model.bpow, h,
      abs_of_nonneg (le_of_not_gt h)]

/-- For an IEEE descriptor and a finite result, the projection of a finite exact value is its
nearest-even rounding. -/
theorem toReal_round_finite (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (value : Rat)
    (hfinite : Model.isFinite (round fmt (.finite value)) = true) :
    Model.toReal (round fmt (.finite value)) = Model.roundAt fmt (value : ℝ) := by
  by_cases hzero : value = 0
  · subst value
    simp [round]
  · rw [round, Model.roundRat,
      Model.toReal_roundRatScaled_eq_roundAt _ _ _ _ _ hfmt hfinite, signed_ratio_real]

end Extended

variable {ι γ γ' : Type} {F : CodedFormat ι γ} {G : CodedFormat ι γ'}

namespace Tensor

/--
OCP MX v1.0, §6.1: dot product with a supplied intermediate reduction and one
nearest-even final rounding into `fmt`. Operand codecs, scale levels, length,
order, reduction state and output descriptor are independent parameters.
The default exact reduction incurs no intermediate rounding.
-/
def _root_.FloatLib.Floats.Formats.OCP.MX.Dot
    (fmt : FloatFormat) (a : Tensor F) (b : Tensor G) (order : List ι)
    (reduction : Reduction := .exact) : Model fmt :=
  Extended.round fmt (reduction.run (products a b order))

open OCP.MX (Dot)

/--
OCP MX v1.0, §6.2: dot product over ordered blocks, with the supplied reduction
over their flattened positions and one nearest-even final rounding. The standard
recommends binary32 output and equal padded block lengths; other descriptors and
block shapes are extensions.
-/
def _root_.FloatLib.Floats.Formats.OCP.MX.DotGeneral
    (fmt : FloatFormat) (a : Tensor F) (b : Tensor G) (blocks : List (List ι))
    (reduction : Reduction := .exact) : Model fmt :=
  Dot fmt a b blocks.flatten reduction

/-- With no position the default exact reduction delivers positive zero. -/
@[simp] theorem Dot_nil (fmt : FloatFormat) (a : Tensor F) (b : Tensor G) :
    Dot fmt a b [] = Model.zero fmt false := by
  simp [Dot, products, Reduction.run, Reduction.fold, Reduction.exact, Extended.round]

/-- For an IEEE descriptor, a finite dot is one nearest-even rounding of the exact real sum of
the products. -/
theorem toReal_Dot_eq_roundAt (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (a : Tensor F)
    (b : Tensor G) (order : List ι)
    (ha : ∀ i ∈ order, (a.decode i).isFinite = true)
    (hb : ∀ i ∈ order, (b.decode i).isFinite = true)
    (hfinite : Model.isFinite (Dot fmt a b order) = true) :
    Model.toReal (Dot fmt a b order) =
      Model.roundAt fmt (((order.map fun i => a.value i * b.value i).sum : ℚ) : ℝ) := by
  change Model.isFinite (Extended.round fmt (dotExact a b order)) = true at hfinite
  change Model.toReal (Extended.round fmt (dotExact a b order)) = _
  rw [dotExact_finite a b order ha hb] at hfinite ⊢
  exact Extended.toReal_round_finite fmt hfmt _ hfinite

/--
For an IEEE descriptor, the error of a finite dot is at most half an ulp of the exact sum. This
includes subnormal results and cancellation, and neither the number nor the order of the
positions adds error.
-/
theorem abs_toReal_Dot_sub_le (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (a : Tensor F)
    (b : Tensor G) (order : List ι)
    (ha : ∀ i ∈ order, (a.decode i).isFinite = true)
    (hb : ∀ i ∈ order, (b.decode i).isFinite = true)
    (hfinite : Model.isFinite (Dot fmt a b order) = true) :
    |Model.toReal (Dot fmt a b order) -
        (((order.map fun i => a.value i * b.value i).sum : ℚ) : ℝ)| ≤
      Model.halfUlpAt fmt (((order.map fun i => a.value i * b.value i).sum : ℚ) : ℝ) := by
  rw [toReal_Dot_eq_roundAt fmt hfmt a b order ha hb hfinite]
  exact Model.abs_roundAt_sub_le fmt _

/--
OCP MX v1.0, §6.2: finite blocks are reduced as the sum of their exact dot products,
then rounded once. This holds for any number, size and order of blocks.
-/
theorem toReal_DotGeneral_eq_roundAt (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (a : Tensor F) (b : Tensor G) (blocks : List (List ι))
    (ha : ∀ block ∈ blocks, ∀ i ∈ block, (a.decode i).isFinite = true)
    (hb : ∀ block ∈ blocks, ∀ i ∈ block, (b.decode i).isFinite = true)
    (hfinite : Model.isFinite (OCP.MX.DotGeneral fmt a b blocks) = true) :
    Model.toReal (OCP.MX.DotGeneral fmt a b blocks) =
      Model.roundAt fmt
        (((blocks.map fun block =>
          (block.map fun i => a.value i * b.value i).sum).sum : ℚ) : ℝ) := by
  have h := toReal_Dot_eq_roundAt fmt hfmt a b blocks.flatten
    (fun i hi => by
      obtain ⟨block, hblock, hi⟩ := List.mem_flatten.mp hi
      exact ha block hblock i hi)
    (fun i hi => by
      obtain ⟨block, hblock, hi⟩ := List.mem_flatten.mp hi
      exact hb block hblock i hi) hfinite
  simpa [OCP.MX.DotGeneral, List.map_flatten, List.sum_flatten, List.map_map,
    Function.comp_def] using h

end Tensor

end FloatLib.Floats.Formats.Block

namespace FloatLib.Floats.Formats.OCP.MX

reference_paths Dot DotGeneral

attribute [kernel_optimize unfold] FloatLib.Floats.Formats.Block.Tensor.products

end FloatLib.Floats.Formats.OCP.MX
