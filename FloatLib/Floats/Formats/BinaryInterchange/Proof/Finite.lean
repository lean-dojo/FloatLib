/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Operation.Proof.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Constants
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Division
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Multiplication
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.SquareRoot
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Subtraction
public import FloatLib.Floats.Formats.BinaryInterchange.Proof.Core

/-!
# Finite proof-indexed binary-interchange arithmetic

The finite `Model.At` view supports constructors, decoding theorems, directed rounding bounds,
and arithmetic operations. Each arithmetic wrapper contains the corresponding executable result
together with an erased proof of its real index. Rounded arithmetic requires conventional IEEE
descriptors and a finite result.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

namespace At

/-- Regard a finite refinement through the total numerical-value interface. -/
@[inline] def toValue {fmt : FloatFormat} {r : ℝ} (x : At fmt r) :
    AtValue fmt (.finite r) :=
  x

/-- Construct the proof-indexed view of a finite executable float. -/
@[inline] def ofFinite {fmt : FloatFormat} (x : Model fmt)
    (hfinite : isFinite x = true) : At fmt (toReal x) :=
  ⟨x, numericalSystem_represents_of_isFinite x hfinite⟩

/-- The format's policy-aware zero with its exact real interpretation. -/
@[inline] def zero (fmt : FloatFormat) (sign : Bool) : At fmt 0 :=
  ⟨Model.zero fmt sign, by
    apply (represents_iff _ _).2
    exact
      ⟨isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt sign),
        toReal_zero fmt sign⟩⟩

/-- Positive one with its exact real interpretation. -/
@[inline] def one (fmt : FloatFormat) : At fmt 1 :=
  ⟨Model.posOne fmt, by simp [represents_iff]⟩

/-- Negative one with its exact real interpretation. -/
@[inline] def negOne (fmt : FloatFormat) : At fmt (-1) :=
  ⟨Model.negOne fmt, by simp [represents_iff]⟩

/-- The bundled executable value represents its real index. -/
theorem represents {fmt : FloatFormat} {r : ℝ} (x : At fmt r) :
    Represents x.1 r :=
  x.2

/-- Every proof-indexed executable float is finite. -/
@[simp] theorem isFinite {fmt : FloatFormat} {r : ℝ} (x : At fmt r) :
    Model.isFinite x.1 = true :=
  isFinite_of_represents x.2

/-- Decoding a proof-indexed executable float recovers its real index. -/
@[simp] theorem toReal {fmt : FloatFormat} {r : ℝ} (x : At fmt r) :
    Model.toReal x.1 = r :=
  toReal_eq_of_represents x.2

/-- The extended-real interpretation of a proof-indexed executable float is its real index. -/
@[simp] theorem toEReal {fmt : FloatFormat} {r : ℝ} (x : At fmt r) :
    Model.toEReal x.1 = (r : EReal) := by
  rw [Model.toEReal_eq_coe_toReal_of_isFinite x.1 (isFinite x), toReal x]

/-- Downward-rounded addition of represented inputs is a lower bound on their exact sum. -/
theorem toEReal_addDown_le {fmt : FloatFormat} {r s : ℝ}
    (x : At fmt r) (y : At fmt s) (hfmt : fmt.isIEEE = true) :
    Model.toEReal (Model.addDown x.1 y.1) ≤ ((r + s : ℝ) : EReal) := by
  simpa using
    Model.toEReal_addDown_le x.1 y.1 hfmt (isFinite x) (isFinite y)

/-- Upward-rounded addition of represented inputs is an upper bound on their exact sum. -/
theorem le_toEReal_addUp {fmt : FloatFormat} {r s : ℝ}
    (x : At fmt r) (y : At fmt s) (hfmt : fmt.isIEEE = true) :
    ((r + s : ℝ) : EReal) ≤ Model.toEReal (Model.addUp x.1 y.1) := by
  simpa using
    Model.le_toEReal_addUp x.1 y.1 hfmt (isFinite x) (isFinite y)

/--
Downward-rounded subtraction of represented inputs is a lower bound on their exact difference.
-/
theorem toEReal_subDown_le {fmt : FloatFormat} {r s : ℝ}
    (x : At fmt r) (y : At fmt s) (hfmt : fmt.isIEEE = true) :
    Model.toEReal (Model.subDown x.1 y.1) ≤ ((r - s : ℝ) : EReal) := by
  simpa using
    Model.toEReal_subDown_le x.1 y.1 hfmt (isFinite x) (isFinite y)

/-- Upward-rounded subtraction of represented inputs is an upper bound on their exact difference. -/
theorem le_toEReal_subUp {fmt : FloatFormat} {r s : ℝ}
    (x : At fmt r) (y : At fmt s) (hfmt : fmt.isIEEE = true) :
    ((r - s : ℝ) : EReal) ≤ Model.toEReal (Model.subUp x.1 y.1) := by
  simpa using
    Model.le_toEReal_subUp x.1 y.1 hfmt (isFinite x) (isFinite y)

/--
Downward-rounded multiplication of represented inputs is a lower bound on their exact product.
-/
theorem toEReal_mulDown_le {fmt : FloatFormat} {r s : ℝ}
    (x : At fmt r) (y : At fmt s) (hfmt : fmt.isIEEE = true) :
    Model.toEReal (Model.mulDown x.1 y.1) ≤ ((r * s : ℝ) : EReal) := by
  simpa using
    Model.toEReal_mulDown_le x.1 y.1 hfmt (isFinite x) (isFinite y)

/-- Upward-rounded multiplication of represented inputs is an upper bound on their exact product. -/
theorem le_toEReal_mulUp {fmt : FloatFormat} {r s : ℝ}
    (x : At fmt r) (y : At fmt s) (hfmt : fmt.isIEEE = true) :
    ((r * s : ℝ) : EReal) ≤ Model.toEReal (Model.mulUp x.1 y.1) := by
  simpa using
    Model.le_toEReal_mulUp x.1 y.1 hfmt (isFinite x) (isFinite y)

/-- Downward-rounded division bounds the exact quotient when the represented divisor is nonzero. -/
theorem toEReal_divDown_le {fmt : FloatFormat} {r s : ℝ}
    (x : At fmt r) (y : At fmt s) (hfmt : fmt.isIEEE = true)
    (hy0 : Model.isZero y.1 = false) :
    Model.toEReal (Model.divDown x.1 y.1) ≤ ((r / s : ℝ) : EReal) := by
  simpa using
    Model.toEReal_divDown_le x.1 y.1 hfmt (isFinite x) (isFinite y) hy0

/-- Upward-rounded division bounds the exact quotient when the represented divisor is nonzero. -/
theorem le_toEReal_divUp {fmt : FloatFormat} {r s : ℝ}
    (x : At fmt r) (y : At fmt s) (hfmt : fmt.isIEEE = true)
    (hy0 : Model.isZero y.1 = false) :
    ((r / s : ℝ) : EReal) ≤ Model.toEReal (Model.divUp x.1 y.1) := by
  simpa using
    Model.le_toEReal_divUp x.1 y.1 hfmt (isFinite x) (isFinite y) hy0

/-- Downward-rounded square root bounds the exact square root of a nonnegative represented value. -/
theorem toEReal_sqrtDown_le {fmt : FloatFormat} {r : ℝ}
    (x : At fmt r) (hfmt : fmt.isIEEE = true) (hr : 0 ≤ r) :
    Model.toEReal (Model.sqrtDown x.1) ≤ ((Real.sqrt r : ℝ) : EReal) := by
  simpa using
    Model.toEReal_sqrtDown_le_of_nonnegative x.1 hfmt (isFinite x)
      (show 0 ≤ Model.toReal x.1 by simpa using hr)

/-- Upward-rounded square root bounds the exact square root of a nonnegative represented value. -/
theorem le_toEReal_sqrtUp {fmt : FloatFormat} {r : ℝ}
    (x : At fmt r) (hfmt : fmt.isIEEE = true) (hr : 0 ≤ r) :
    ((Real.sqrt r : ℝ) : EReal) ≤ Model.toEReal (Model.sqrtUp x.1) := by
  simpa using
    Model.le_toEReal_sqrtUp_of_nonnegative x.1 hfmt (isFinite x)
      (show 0 ≤ Model.toReal x.1 by simpa using hr)

/-- Negation transports the real index exactly. -/
@[inline] def neg {fmt : FloatFormat} {r : ℝ} (x : At fmt r) : At fmt (-r) :=
  ⟨Model.neg x.1, Operation.Finite1.denote (neg_refines fmt) x.2⟩

/-- Addition transports real indices through one nearest-even rounding step. -/
@[inline] def add {fmt : FloatFormat} {r s : ℝ} (x : At fmt r) (y : At fmt s)
    (hfmt : fmt.isIEEE = true)
    (hfinite : Model.isFinite (Model.add x.1 y.1) = true) :
    At fmt (roundAt fmt (r + s)) :=
  ⟨Model.add x.1 y.1,
    Operation.Finite2If.denote (add_refines fmt hfmt) x.2 y.2 hfinite⟩

/-- Subtraction transports real indices through one nearest-even rounding step. -/
@[inline] def sub {fmt : FloatFormat} {r s : ℝ} (x : At fmt r) (y : At fmt s)
    (hfmt : fmt.isIEEE = true)
    (hfinite : Model.isFinite (Model.sub x.1 y.1) = true) :
    At fmt (roundAt fmt (r - s)) :=
  ⟨Model.sub x.1 y.1,
    Operation.Finite2If.denote (sub_refines fmt hfmt) x.2 y.2 hfinite⟩

/-- Multiplication transports real indices through one nearest-even rounding step. -/
@[inline] def mul {fmt : FloatFormat} {r s : ℝ} (x : At fmt r) (y : At fmt s)
    (hfmt : fmt.isIEEE = true)
    (hfinite : Model.isFinite (Model.mul x.1 y.1) = true) :
    At fmt (roundAt fmt (r * s)) :=
  ⟨Model.mul x.1 y.1,
    Operation.Finite2If.denote (mul_refines fmt hfmt) x.2 y.2 hfinite⟩

/-- Fused multiply-add transports real indices through one nearest-even rounding step. -/
@[inline] def fma {fmt : FloatFormat} {r s t : ℝ}
    (x : At fmt r) (y : At fmt s) (z : At fmt t)
    (hfmt : fmt.isIEEE = true)
    (hfinite : Model.isFinite (Model.fma x.1 y.1 z.1) = true) :
    At fmt (roundAt fmt (r * s + t)) :=
  ⟨Model.fma x.1 y.1 z.1,
    Operation.Finite3If.denote (fma_refines fmt hfmt) x.2 y.2 z.2 hfinite⟩

/-- A cross-format cast transports its real index through destination rounding. -/
@[inline] def cast {src dst : FloatFormat} {r : ℝ} (x : At src r)
    (hsrc : src.isIEEE = true) (hdst : dst.isIEEE = true)
    (hfinite : Model.isFinite (Model.cast src dst x.1) = true) :
    At dst (roundAt dst r) :=
  ⟨Model.cast src dst x.1,
    Operation.Finite1If.denote (cast_refines src dst hsrc hdst) x.2 hfinite⟩

/-- Lifting a finite model value records that value as the carrier. -/
@[simp] theorem value_ofFinite {fmt : FloatFormat} (x : Model fmt)
    (hfinite : Model.isFinite x = true) :
    (ofFinite x hfinite).1 = x :=
  rfl

/-- The carrier of a negated witness is the model negation. -/
@[simp] theorem value_neg {fmt : FloatFormat} {r : ℝ} (x : At fmt r) :
    (neg x).1 = Model.neg x.1 :=
  rfl

/-- The carrier of a finite sum witness is the model sum. -/
@[simp] theorem value_add {fmt : FloatFormat} {r s : ℝ} (x : At fmt r) (y : At fmt s)
    (hfmt : fmt.isIEEE = true)
    (hfinite : Model.isFinite (Model.add x.1 y.1) = true) :
    (add x y hfmt hfinite).1 = Model.add x.1 y.1 :=
  rfl

/-- The carrier of a finite difference witness is the model difference. -/
@[simp] theorem value_sub {fmt : FloatFormat} {r s : ℝ} (x : At fmt r) (y : At fmt s)
    (hfmt : fmt.isIEEE = true)
    (hfinite : Model.isFinite (Model.sub x.1 y.1) = true) :
    (sub x y hfmt hfinite).1 = Model.sub x.1 y.1 :=
  rfl

/-- The carrier of a finite product witness is the model product. -/
@[simp] theorem value_mul {fmt : FloatFormat} {r s : ℝ} (x : At fmt r) (y : At fmt s)
    (hfmt : fmt.isIEEE = true)
    (hfinite : Model.isFinite (Model.mul x.1 y.1) = true) :
    (mul x y hfmt hfinite).1 = Model.mul x.1 y.1 :=
  rfl

/-- The carrier of a finite fused multiply-add witness is the model fused multiply-add. -/
@[simp] theorem value_fma {fmt : FloatFormat} {r s t : ℝ}
    (x : At fmt r) (y : At fmt s) (z : At fmt t)
    (hfmt : fmt.isIEEE = true)
    (hfinite : Model.isFinite (Model.fma x.1 y.1 z.1) = true) :
    (fma x y z hfmt hfinite).1 = Model.fma x.1 y.1 z.1 :=
  rfl

/-- The carrier of a finite cast witness is the model cast. -/
@[simp] theorem value_cast {src dst : FloatFormat} {r : ℝ} (x : At src r)
    (hsrc : src.isIEEE = true) (hdst : dst.isIEEE = true)
    (hfinite : Model.isFinite (Model.cast src dst x.1) = true) :
    (cast x hsrc hdst hfinite).1 = Model.cast src dst x.1 :=
  rfl

end At
end Model
end FloatLib.Floats.Formats.BinaryInterchange
