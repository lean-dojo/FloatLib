/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime

/-!
# Executable complex numbers over an arbitrary binary format

`ExecComplex fmt` stores one `Model fmt` for each Cartesian component. The format parameter is
not fixed to binary32: the same definition supports binary16, bfloat16, binary64, binary128,
binary256, and custom exponent/fraction widths.

Complex multiplication uses four scalar multiplications followed by one subtraction and one
addition. This explicit evaluation order matters in floating-point arithmetic and is reflected by
the semantic theorem in `Complex.Semantics`.

Division uses the larger denominator component to form a ratio. Magnitude scales both components
before squaring. These evaluation orders avoid squaring large unscaled components, but do not
guarantee finite intermediates or correct rounding of the exact complex operation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange

/-- A complex value whose real and imaginary components share the binary format `fmt`. -/
structure ExecComplex (fmt : FloatFormat) where
  /-- Real component. -/
  re : Model fmt
  /-- Imaginary component. -/
  im : Model fmt
  deriving DecidableEq, Repr

namespace ExecComplex

/-- A complex value is finite exactly when both encoded components are finite. -/
@[inline] def isFinite {fmt : FloatFormat} (z : ExecComplex fmt) : Bool :=
  Model.isFinite z.re && Model.isFinite z.im

/-- Componentwise sign negation. -/
@[inline] def neg {fmt : FloatFormat} (z : ExecComplex fmt) : ExecComplex fmt :=
  ⟨Model.neg z.re, Model.neg z.im⟩

/-- Componentwise floating-point addition. -/
@[inline] def add {fmt : FloatFormat} (x y : ExecComplex fmt) : ExecComplex fmt :=
  ⟨Model.add x.re y.re, Model.add x.im y.im⟩

/-- Componentwise floating-point subtraction. -/
@[inline] def sub {fmt : FloatFormat} (x y : ExecComplex fmt) : ExecComplex fmt :=
  ⟨Model.sub x.re y.re, Model.sub x.im y.im⟩

namespace Internal

/-- Real component of the specified non-fused complex product. -/
@[noinline] def mulReal {fmt : FloatFormat} (x y : ExecComplex fmt) : Model fmt :=
  Model.sub (Model.mul x.re y.re) (Model.mul x.im y.im)

/-- Imaginary component of the specified non-fused complex product. -/
@[noinline] def mulImag {fmt : FloatFormat} (x y : ExecComplex fmt) : Model fmt :=
  Model.add (Model.mul x.re y.im) (Model.mul x.im y.re)

end Internal

/--
Floating-point complex multiplication with an explicit non-fused evaluation order.

Each of the four component products is rounded in `fmt`; the real subtraction and imaginary
addition are then rounded once more in the same format.
-/
@[inline] def mul {fmt : FloatFormat} (x y : ExecComplex fmt) : ExecComplex fmt :=
  ⟨Internal.mulReal x y, Internal.mulImag x y⟩

/-- Conjugation negates the imaginary component using the format's zero and NaN conventions. -/
@[inline] def conj {fmt : FloatFormat} (z : ExecComplex fmt) : ExecComplex fmt :=
  ⟨z.re, Model.neg z.im⟩

/-- Squared magnitude with two rounded squares followed by a rounded sum. -/
@[inline] def normSq {fmt : FloatFormat} (z : ExecComplex fmt) : Model fmt :=
  Model.add (Model.mul z.re z.re) (Model.mul z.im z.im)

namespace Internal

/-- Exchange coordinates when the imaginary denominator component has larger magnitude. -/
@[inline] def swap {fmt : FloatFormat} (z : ExecComplex fmt) : ExecComplex fmt :=
  ⟨z.im, z.re⟩

/-- The strict comparison chooses the real component on a tie or an unordered comparison. -/
@[inline] def imagDominant {fmt : FloatFormat} (z : ExecComplex fmt) : Bool :=
  decide (Model.compare (Model.abs z.re) (Model.abs z.im) = some .lt)

/--
Ratio division with the real denominator component as pivot.

Every multiplication, sum, difference, and quotient is rounded separately.
-/
@[inline] def divRealDominant {fmt : FloatFormat}
    (x y : ExecComplex fmt) : ExecComplex fmt :=
  let ratio := Model.div y.im y.re
  let denominator := Model.add y.re (Model.mul y.im ratio)
  ⟨Model.div (Model.add x.re (Model.mul x.im ratio)) denominator,
    Model.div (Model.sub x.im (Model.mul x.re ratio)) denominator⟩

/-- Larger component magnitude, with the real component selected on ties. -/
@[inline] def magnitudeScale {fmt : FloatFormat} (z : ExecComplex fmt) : Model fmt :=
  if imagDominant z then Model.abs z.im else Model.abs z.re

/-- Components divided by their common magnitude scale, each rounded once. -/
@[inline] def magnitudeRatios {fmt : FloatFormat} (z : ExecComplex fmt) : ExecComplex fmt :=
  let scale := magnitudeScale z
  ⟨Model.div z.re scale, Model.div z.im scale⟩

end Internal

/--
Complex division by a component-ratio formula.

When the imaginary denominator component is larger, both inputs exchange coordinates and the
computed quotient is conjugated. This includes an exact sign change after the final imaginary
division. Scalar kernels determine exceptional results; there is no complex infinity recovery.
Finite inputs alone do not exclude overflow, underflow, or a zero rounded denominator.
-/
@[inline] def div {fmt : FloatFormat} (x y : ExecComplex fmt) : ExecComplex fmt :=
  if Internal.imagDominant y then
    conj (Internal.divRealDominant (Internal.swap x) (Internal.swap y))
  else
    Internal.divRealDominant x y

/--
Magnitude computed by scaling before squaring and restoring the scale after square root.

A zero scale returns positive zero on finite IEEE inputs. All finite arithmetic uses the component
kernels; the result need not be one rounding of the exact norm. An infinite component gives positive
infinity even when the other component is a quiet NaN. If either component is a signaling NaN,
or neither is infinite, nonfinite inputs use the scalar sum of absolute components and its NaN
selection and quieting policy.

The format must also have enough range for the normalized intermediate sum. For example,
`FloatFormat.custom 2 2 2 .ieee` maps `(0.5, 0.5)` to infinity because the normalized sum `2`
overflows, although the nearest rounded exact norm is `0.75`. This custom bias also fails
`fmt.isIEEE`; the finite rounded-semantics theorem does not apply.
-/
@[inline] def magnitude {fmt : FloatFormat} (z : ExecComplex fmt) : Model fmt :=
  if isFinite z then
    let scale := Internal.magnitudeScale z
    if Model.isZero scale then scale
    else Model.mul scale (Model.sqrt (normSq (Internal.magnitudeRatios z)))
  else if (Model.isInf z.re || Model.isInf z.im) &&
      !(Model.isSNaN z.re || Model.isSNaN z.im) then
    Model.posInf fmt
  else Model.add (Model.abs z.re) (Model.abs z.im)

instance {fmt : FloatFormat} : Neg (ExecComplex fmt) := ⟨neg⟩
instance {fmt : FloatFormat} : Add (ExecComplex fmt) := ⟨add⟩
instance {fmt : FloatFormat} : Sub (ExecComplex fmt) := ⟨sub⟩
instance {fmt : FloatFormat} : Mul (ExecComplex fmt) := ⟨mul⟩
instance {fmt : FloatFormat} : Div (ExecComplex fmt) := ⟨div⟩

/-- Boolean finiteness separates into the corresponding facts for both components. -/
theorem isFinite_eq_true_iff {fmt : FloatFormat} (z : ExecComplex fmt) :
    isFinite z = true ↔
      Model.isFinite z.re = true ∧ Model.isFinite z.im = true := by
  simp [isFinite]

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
