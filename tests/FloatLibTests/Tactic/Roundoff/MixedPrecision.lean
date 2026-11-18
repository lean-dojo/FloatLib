/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Util.CollectAxioms
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError.Rounding
public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Tactic.Roundoff

/-!
# Mixed-precision schedules selected by `roundoff`

The statement checks distinguish exact widening and wide products from narrowing and ordinary
single-format multiplication. The product family has arbitrary source and destination descriptors.
Concrete descriptor checks cover bfloat16, binary16, both FP8 encodings and the MX element formats.
The smallest bfloat16 subnormal supplies a counterexample to precision-only product exactness.
FMA rounds once, while loss scaling keeps the explicit lower-range and finite-result premises.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffMixedPrecision

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

roundoff mixed theorem widening :=
  fun (x : Model FloatFormat.bfloat16) =>
    Model.toReal (Model.cast FloatFormat.bfloat16 FloatFormat.binary32 x)

example (x : Model FloatFormat.bfloat16) :=
  show _ → MixedError _ x.toReal 0 0 from widening x

/-- Product precision also proves that each separate operand or bias cast is exact. -/
roundoff mixed theorem widening_from_product_precision :=
  fun (src dst : FloatFormat) (hdst : dst.isIEEE = true)
    (hprec : (src.fracWidth + 1) + (src.fracWidth + 1) ≤ dst.fracWidth + 1)
    (hmin : dst.minSubnormalExponent ≤ src.minSubnormalExponent) (x : Model src) =>
      Model.toReal (Model.cast src dst x)

example (src dst : FloatFormat) (hdst : dst.isIEEE = true)
    (hprec : (src.fracWidth + 1) + (src.fracWidth + 1) ≤ dst.fracWidth + 1)
    (hmin : dst.minSubnormalExponent ≤ src.minSubnormalExponent) (x : Model src) :=
  show _ → MixedError _ x.toReal 0 0 from
    widening_from_product_precision src dst hdst hprec hmin x

roundoff mixed theorem narrowing :=
  fun (x : Model FloatFormat.binary32) =>
    Model.toReal (Model.cast FloatFormat.binary32 FloatFormat.bfloat16 x)

example (x : Model FloatFormat.binary32) :=
  show _ → MixedError _ x.toReal (Model.unitRoundoffAt FloatFormat.bfloat16)
    (Model.underflowErrorAt FloatFormat.bfloat16) from narrowing x

/-- Every non-saturating destination has the same one-rounding cast family. -/
roundoff mixed theorem narrowing_policy :=
  fun (src dst : FloatFormat) (hnarrow : dst.fracWidth < src.fracWidth)
    (hpolicy : dst.encoding ≠ .finite) (x : Model src) =>
      Model.toReal (Model.cast src dst x)

example (src dst : FloatFormat) (hnarrow : dst.fracWidth < src.fracWidth)
    (hpolicy : dst.encoding ≠ .finite) (x : Model src) :=
  show _ → MixedError _ x.toReal (Model.unitRoundoffAt dst)
    (Model.underflowErrorAt dst) from narrowing_policy src dst hnarrow hpolicy x

/-- Fully finite formats retain the saturation displacement instead of treating finiteness
as evidence that one ordinary rounding suffices. -/
roundoff mixed theorem saturating_cast :=
  fun (x : Model FloatFormat.binary32) =>
    Model.toReal (Model.cast FloatFormat.binary32 FloatFormat.e2m1 x)

example (x : Model FloatFormat.binary32) :=
  show _ → MixedError _ x.toReal (Model.unitRoundoffAt FloatFormat.e2m1)
    (Model.underflowErrorAt FloatFormat.e2m1 +
      max 0 (|x.toReal| - Model.toReal (Model.posMaxFinite FloatFormat.e2m1))) from
    saturating_cast x

/-- Grid inclusion is exact across arbitrary encoding policies once clipping is excluded. -/
roundoff mixed theorem widening_policy :=
  fun (src dst : FloatFormat)
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hmin : dst.minSubnormalExponent ≤ src.minSubnormalExponent)
    (x : Model src) =>
      Model.toReal (Model.cast src dst x)

example (src dst : FloatFormat)
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hmin : dst.minSubnormalExponent ≤ src.minSubnormalExponent)
    (x : Model src) :=
  show _ → MixedError _ x.toReal 0 0 from widening_policy src dst hfrac hmin x

/-- The general exact-cast rule applies to a non-IEEE destination with a different exponent
width. -/
roundoff mixed theorem mx_to_fp8 :=
  fun (x : Model FloatFormat.e2m1) =>
    Model.toReal (Model.cast FloatFormat.e2m1 FloatFormat.e4m3 x)

example (x : Model FloatFormat.e2m1) :=
  show _ → MixedError _ x.toReal 0 0 from mx_to_fp8 x

/-- A concrete FP8 narrowing selects one rounding rather than an IEEE-only fallback. -/
roundoff mixed theorem fp8_cast :=
  fun (x : Model FloatFormat.binary32) =>
    Model.toReal (Model.cast FloatFormat.binary32 FloatFormat.e4m3 x)

example (x : Model FloatFormat.binary32) :=
  show _ → MixedError _ x.toReal (Model.unitRoundoffAt FloatFormat.e4m3)
    (Model.underflowErrorAt FloatFormat.e4m3) from fp8_cast x

/-- The FP8 families with NaNs are non-saturating; the MX finite encodings saturate. -/
example :
    [FloatFormat.e4m3, .e5m2, .e4m3fnuz, .e5m2fnuz].all
        (fun fmt => fmt.encoding != .finite) = true ∧
      [FloatFormat.e2m1, .e2m3, .e3m2].all
        (fun fmt => fmt.encoding == .finite) = true := by
  decide

/-- The ordinary FP8 rounding case, its finite endpoint, and its NaN overflow policy. -/
example :
    (Model.cast .binary32 .e4m3 (Model.ofRat .binary32 (1 / 3))).toRat? = some (11 / 32) ∧
    (Model.cast .binary32 .e4m3 (Model.ofRat .binary32 448)).toRat? = some 448 ∧
    (Model.cast .binary32 .e4m3 (Model.ofRat .binary32 1000)).isNaN = true := by
  decide +kernel

/-- Nearest-even FP8 ties at the subnormal and overflow boundaries match the evaluator. -/
example :
    (Model.cast .binary32 .e4m3 (Model.ofRat .binary32 (1 / 1024))).toRat? = some 0 ∧
    (Model.cast .binary32 .e4m3 (Model.ofRat .binary32 (3 / 1024))).toRat? = some (1 / 256) ∧
    (Model.cast .binary32 .e4m3 (Model.ofRat .binary32 464)).toRat? = some 448 ∧
    (Model.cast .binary32 .e4m3 (Model.ofRat .binary32 465)).isNaN = true := by
  decide +kernel

/-- Saturation has a finite result even when it loses almost the entire input magnitude. -/
example :
    let x := Model.ofRat FloatFormat.binary32 1000
    let y := Model.cast FloatFormat.binary32 FloatFormat.e2m1 x
    x.toRat? = some 1000 ∧ y.toRat? = some 6 ∧ Model.isFinite y = true := by
  decide +kernel

/-- Exact products are selected even when the precision hypothesis reverses the operand order. -/
roundoff mixed theorem product :=
  fun (left right dst : FloatFormat) (hdst : dst.isIEEE = true)
    (hprec : (right.fracWidth + 1) + (left.fracWidth + 1) ≤ dst.fracWidth + 1)
    (hlmin : dst.minSubnormalExponent ≤ left.minSubnormalExponent)
    (hrmin : dst.minSubnormalExponent ≤ right.minSubnormalExponent)
    (x : Model left) (y : Model right) =>
      Model.toReal (Model.mul (Model.cast left dst x) (Model.cast right dst y))

example (left right dst : FloatFormat) (hdst : dst.isIEEE = true)
    (hprec : (right.fracWidth + 1) + (left.fracWidth + 1) ≤ dst.fracWidth + 1)
    (hlmin : dst.minSubnormalExponent ≤ left.minSubnormalExponent)
    (hrmin : dst.minSubnormalExponent ≤ right.minSubnormalExponent)
    (x : Model left) (y : Model right) :=
  show _ → MixedError _ (x.toReal * y.toReal) 0 0 from
    product left right dst hdst hprec hlmin hrmin x y

/-- Every listed narrow descriptor meets the precision and lower-grid conditions for a
binary32 product of two of its values. Product range is a separate premise. -/
example :
    [FloatFormat.bfloat16, .binary16, .e4m3, .e5m2, .e2m1, .e2m3, .e3m2].all
      (fun src => decide
        ((src.fracWidth + 1) + (src.fracWidth + 1) ≤ FloatFormat.binary32.fracWidth + 1 ∧
          FloatFormat.binary32.minSubnormalExponent ≤ src.minSubnormalExponent)) = true := by
  decide

roundoff mixed theorem ordinary_product :=
  fun (x y : Model FloatFormat.binary32) => Model.toReal (Model.mul x y)

example (x y : Model FloatFormat.binary32) :=
  show _ → MixedError _ (x.toReal * y.toReal) (Model.unitRoundoffAt FloatFormat.binary32)
    (Model.underflowErrorAt FloatFormat.binary32) from ordinary_product x y

/-- Cast-policy selection leaves an ordinary symbolic format's existing obligations intact. -/
roundoff mixed theorem symbolic_add :=
  fun (fmt : FloatFormat) (x y : Model fmt) => Model.toReal (Model.add x y)

example (fmt : FloatFormat) (x y : Model fmt) :=
  show _ → MixedError _ (x.toReal + y.toReal) (Model.unitRoundoffAt fmt) 0 from
    symbolic_add fmt x y

/-- A sum of the model in a directed attribute states the unit roundoff of that attribute, when
the exact sum is within the largest finite magnitude. -/
roundoff mixed theorem directed_add :=
  fun (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y : Model fmt) =>
    Model.toReal (Model.add x y (mode := .down))

example (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y : Model fmt) :=
  show _ → MixedError _ (x.toReal + y.toReal) (Model.unitRoundoffIn fmt .down) 0 from
    directed_add fmt hfmt x y

/-- Two operations of the model rounded upward: the range condition of the sum is stated on the
exact operands, with the error of the product, and not on the computed product. -/
roundoff mixed theorem directed_affine :=
  fun (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y z : Model fmt) =>
    Model.toReal (Model.add (Model.mul x y (mode := .up)) z (mode := .up))

example (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y z : Model fmt)
    (hproduct : |x.toReal * y.toReal| ≤ (Model.posMaxFinite fmt).toReal)
    (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hsum : |x.toReal * y.toReal + z.toReal| +
      (Model.unitRoundoffIn fmt .up * |x.toReal * y.toReal| + Model.underflowErrorIn fmt .up) ≤
        (Model.posMaxFinite fmt).toReal)
    (hz : z.isFinite = true) :
    MixedError (Model.toReal (Model.add (Model.mul x y (mode := .up)) z (mode := .up)))
      (x.toReal * y.toReal + z.toReal) (Model.unitRoundoffIn fmt .up)
      ((1 + Model.unitRoundoffIn fmt .up) *
        (Model.unitRoundoffIn fmt .up * |x.toReal * y.toReal| + Model.underflowErrorIn fmt .up)) :=
  directed_affine fmt hfmt x y z ⟨hproduct, hx, hy, hsum, hz⟩

/-- The closed form of the same computation rounded downward: each rounding has the unit
roundoff of its attribute. -/
roundoff closed theorem directed_affine_closed :=
  fun (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y z : Model fmt) =>
    Model.toReal (Model.add (Model.mul x y (mode := .down)) z (mode := .down))

example (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y z : Model fmt) :=
  show _ → |Model.toReal (Model.add (Model.mul x y (mode := .down)) z (mode := .down)) -
        (x.toReal * y.toReal + z.toReal)| ≤
      |x.toReal| * ((1 + Model.unitRoundoffIn fmt .down) ^ 2 - 1) * |y.toReal| +
          |z.toReal| * Model.unitRoundoffIn fmt .down +
        Model.underflowErrorIn fmt .down * (1 + Model.unitRoundoffIn fmt .down)
    from directed_affine_closed fmt hfmt x y z

/-- Its backward form: the result is the exact computation on perturbed inputs. -/
roundoff (backward := true) theorem directed_affine_backward :=
  fun (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y z : Model fmt) =>
    Model.toReal (Model.add (Model.mul x y (mode := .down)) z (mode := .down))

example (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y z : Model fmt) :=
  show _ → ∃ δx δz : ℝ, |δx| ≤ (1 + Model.unitRoundoffIn fmt .down) ^ 2 - 1 ∧
      |δz| ≤ Model.unitRoundoffIn fmt .down ∧
      |Model.toReal (Model.add (Model.mul x y (mode := .down)) z (mode := .down)) -
          (x.toReal * (1 + δx) * y.toReal + z.toReal * (1 + δz))| ≤
        Model.underflowErrorIn fmt .down * (1 + Model.unitRoundoffIn fmt .down)
    from directed_affine_backward fmt hfmt x y z

/-- The absolute analysis of a fused multiply-add of the model in any attribute. -/
roundoff theorem directed_fma :=
  fun (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mode : Model.IEEERoundingMode)
      (x y z : Model fmt) =>
    Model.toReal (Model.fma x y z (mode := mode))

example (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mode : Model.IEEERoundingMode)
    (x y z : Model fmt) :=
  show _ → |Model.toReal (Model.fma x y z (mode := mode)) -
        (x.toReal * y.toReal + z.toReal)| ≤
      0 + (Model.unitRoundoffIn fmt mode * |x.toReal * y.toReal + z.toReal| +
        Model.underflowErrorIn fmt mode)
    from directed_fma fmt hfmt mode x y z

roundoff mixed theorem wide_fma :=
  fun (x y : Model FloatFormat.bfloat16) (z : Model FloatFormat.binary32) =>
    Model.toReal (Model.fma
      (Model.cast FloatFormat.bfloat16 FloatFormat.binary32 x)
      (Model.cast FloatFormat.bfloat16 FloatFormat.binary32 y) z)

example (x y : Model FloatFormat.bfloat16) (z : Model FloatFormat.binary32) :=
  show _ → MixedError _ (x.toReal * y.toReal + z.toReal)
    (Model.unitRoundoffAt FloatFormat.binary32) (Model.underflowErrorAt FloatFormat.binary32) from
    wide_fma x y z

roundoff mixed theorem loss_scale :=
  fun (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x : Model fmt) (e : ℤ) =>
    Model.toReal (Model.scale x e)

example (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x : Model fmt) (e : ℤ) :=
  show _ → MixedError _ (x.toReal * (2 : ℝ) ^ (e : ℝ)) 0 0 from loss_scale fmt hfmt x e

roundoff mixed theorem loss_scale_mul :=
  fun (x y : Model FloatFormat.binary32) (e : ℤ)
    (hy : y.toReal = FloatLib.Floats.Formats.Flocq.bpow binaryRadix e) =>
    Model.toReal (Model.mul x y)

example (x y : Model FloatFormat.binary32) (e : ℤ)
    (hy : y.toReal = FloatLib.Floats.Formats.Flocq.bpow binaryRadix e) :=
  show _ → MixedError _ (x.toReal * y.toReal) 0 0 from loss_scale_mul x y e hy

/-- The normal-range premise cannot be omitted even for bfloat16 inputs and binary32 output. -/
example :
    let tiny : Model FloatFormat.bfloat16 := Model.ofNatBits 1
    let wide := Model.cast FloatFormat.bfloat16 FloatFormat.binary32 tiny
    tiny.toRat? = some (1 / 2 ^ 133) ∧ (Model.mul wide wide).toRat? = some 0 := by
  decide +kernel

/-- A negative shift can round a subnormal to zero. -/
example :
    let tiny : Model FloatFormat.binary32 := Model.ofNatBits 1
    (Model.scale tiny (-1)).toRat? = some 0 := by
  decide +kernel

/-- A positive shift of a subnormal remains exact while finite. -/
example :
    let tiny : Model FloatFormat.binary32 := Model.ofNatBits 1
    (Model.scale tiny 1).toRat? = some (1 / 2 ^ 148) := by
  decide +kernel

roundoff mixed theorem wide_dot :=
  fun (xs : List (Model FloatFormat.bfloat16 × Model FloatFormat.bfloat16)) =>
    Model.toReal (xs.foldl (fun acc pair => Model.add acc
      (Model.mul (Model.cast _ FloatFormat.binary32 pair.1)
        (Model.cast _ FloatFormat.binary32 pair.2))) (Model.zero _ false))

/-- A user helper must not hide the exact-cast pattern from the rule index. -/
def widen (x : BFloat16) : Binary32 :=
  ExecFloat.Binary.ofModel (Model.cast .bfloat16 .binary32 (ExecFloat.Binary.toModel x))

roundoff mixed theorem configured_product :=
  fun (x y : BFloat16) => ExecFloat.Binary.toReal (widen x * widen y)

example (x y : BFloat16) :=
  show _ → _ ∧ MixedError _ (ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal y) 0 0 from
    configured_product x y

-- Check the transitive trust of both the analytic family and generated schedules.
run_cmd do
  for name in [``Model.genericFormat_mul_of_precision, ``Model.toReal_mul_cast_exact,
      ``Model.toReal_scale_exact, ``widening, ``widening_from_product_precision,
      ``Model.toReal_roundDyadic_policy, ``Model.cast_policy,
      ``Model.cast_exact_of_gridExtension_policy, ``Model.abs_toReal_cast_sub_le_policy,
      ``narrowing, ``narrowing_policy, ``saturating_cast, ``widening_policy, ``mx_to_fp8,
      ``fp8_cast, ``product, ``symbolic_add, ``wide_fma, ``directed_affine_closed,
      ``directed_affine_backward, ``directed_fma,
      ``loss_scale, ``loss_scale_mul, ``wide_dot, ``configured_product] do
    let axioms ← Lean.collectAxioms name
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unexpected axiom {dependency}"

end FloatLibTests.Conformance.BinaryInterchange.RoundoffMixedPrecision
