/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Model.Packing.Special

/-!
# Executable exact-intermediate finite arithmetic

Storage and accumulation may use different precisions. For example, `mulAddFinite?` can read FP8
operands and accumulate their product in FP32. These operations separate the exact intermediate
calculation from destination rounding:

* inputs are decoded to exact dyadics;
* addition and multiplication occur in the exact integer intermediate;
* the result is rounded once into the selected destination format and policy.

The checked operations return `Option`. `none` means that an input was NaN or infinity, or that
division encountered a zero denominator. A successful result can still overflow according to the
selected output policy. This avoids inventing arithmetic rules for
storage formats whose standards specify encodings and conversions but no standalone arithmetic.
A hardware-specific layer can add its documented exceptional-value behavior and prove refinement
to these finite paths.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

/-- Exact dyadic product used before destination-format rounding. -/
@[inline] def mulDyadic (x y : Numerics.Dyadic) : Numerics.Dyadic :=
  { negative := Bool.xor x.negative y.negative
    significand := x.significand * y.significand
    exponent := x.exponent + y.exponent }

/-- Add two finite values exactly and round once into their common format. -/
def addFinite? (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (x y : Model fmt) : Option (Model fmt) := do
  let dx ← Model.toDyadic? x
  let dy ← Model.toDyadic? y
  pure (Policy.roundDyadic fmt policy entropy (Model.addDyadic dx dy))

/-- Subtract two finite values exactly and round once into their common format. -/
@[inline] def subFinite? (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (x y : Model fmt) : Option (Model fmt) :=
  addFinite? fmt policy entropy x (Model.neg y)

/--
Logical specification of finite multiplication.

Compiled format-specific dispatchers may replace the public entry point, but tables and proofs use
this definition directly so their initialization cannot recurse through the compiled dispatcher.
-/
def mulFiniteSpec? (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (x y : Model fmt) : Option (Model fmt) := do
  let dx ← Model.toDyadic? x
  let dy ← Model.toDyadic? y
  pure (Policy.roundDyadic fmt policy entropy (mulDyadic dx dy))

private theorem mulFiniteSpec_isSome
    (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (x y : Model fmt) :
    (mulFiniteSpec? fmt policy entropy x y).isSome =
      (Model.isFinite x && Model.isFinite y) := by
  unfold mulFiniteSpec?
  rw [← Model.toDyadic?_isSome_eq_isFinite x,
    ← Model.toDyadic?_isSome_eq_isFinite y]
  cases Model.toDyadic? x <;> cases Model.toDyadic? y <;> rfl

private theorem roundDyadic_mant_zero
    (fmt : FloatFormat) (sign : Bool) (exp : Int) :
    Model.roundDyadic fmt { negative := sign, significand := 0, exponent := exp } =
      Model.zero fmt sign := by
  by_cases hfmt : fmt.isIEEE = true
  · have hencoding : fmt.encoding = .ieee :=
      ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
    cases sign <;>
      simp [Model.roundDyadic, hfmt, Model.ieeeRoundDyadic, Model.zero,
        FloatFormat.supportsSignedZero, hencoding,
        Model.posZero_eq_ofModel_zero, Model.negZero_eq_ofModel_zero]
  · simp [Model.roundDyadic, hfmt, Model.roundDyadicGeneral]

private theorem mulFiniteSpec_nearestEven_eq_mul_of_finite
    (fmt : FloatFormat) (entropy : Nat) (x y : Model fmt)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true) :
    mulFiniteSpec? fmt QuantizationPolicy.nearestEven entropy x y =
      some (Model.mul x y) := by
  obtain ⟨dx, hdx⟩ := Model.exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := Model.exists_toDyadic?_of_isFinite hy
  unfold mulFiniteSpec?
  rw [hdx, hdy]
  change some (Policy.roundDyadic fmt .nearestEven entropy (mulDyadic dx dy)) =
    some (Model.mul x y)
  apply congrArg some
  rw [Policy.roundDyadic_nearestEven_eq_execFloat]
  rw [show Model.mul x y = Model.Spec.mul x y by
    exact Model.Proof.mul_eq_spec x y]
  unfold Model.Spec.mul
  rw [hdx, hdy]
  by_cases hxzero : dx.significand = 0
  · simpa [hxzero, mulDyadic] using
      roundDyadic_mant_zero fmt (Bool.xor dx.negative dy.negative) (dx.exponent + dy.exponent)
  · by_cases hyzero : dy.significand = 0
    · simpa [hyzero, mulDyadic] using
        roundDyadic_mant_zero fmt (Bool.xor dx.negative dy.negative) (dx.exponent + dy.exponent)
    · simp [hxzero, hyzero, mulDyadic]

/--
Compiled finite multiplication.

Nearest-even finite multiplication reuses the canonical `Model.mul`, including its native
word and exhaustive tiny-table backends. Every other policy retains the generic exact dyadic
implementation.
-/
@[inline] def mulFiniteImpl? (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (x y : Model fmt) : Option (Model fmt) :=
  if _hpolicy : policy = .nearestEven then
    if Model.isFinite x && Model.isFinite y then
      some (Model.mul x y)
    else
      none
  else
    mulFiniteSpec? fmt policy entropy x y

/-- Multiply two finite values exactly and round once into their common format. -/
@[inline] def mulFinite? (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (x y : Model fmt) : Option (Model fmt) :=
  mulFiniteSpec? fmt policy entropy x y

/--
The compiled nearest-even finite path is extensionally equal to generic exact multiplication.

This theorem installs the canonical operation in generated code while proofs continue to unfold
`mulFinite?` to the format-independent policy specification.
-/
@[csimp] theorem mulFinite_eq_mulFiniteImpl :
    @mulFinite? = @mulFiniteImpl? := by
  funext fmt policy entropy x y
  unfold mulFinite? mulFiniteImpl?
  split <;> rename_i _hpolicy
  · subst policy
    split <;> rename_i hfinite
    · exact mulFiniteSpec_nearestEven_eq_mul_of_finite fmt entropy x y
        ((Bool.and_eq_true _ _).mp hfinite).1 ((Bool.and_eq_true _ _).mp hfinite).2
    · cases hspec :
        mulFiniteSpec? fmt QuantizationPolicy.nearestEven entropy x y with
      | none => rfl
      | some result =>
          exfalso
          apply hfinite
          rw [← mulFiniteSpec_isSome fmt QuantizationPolicy.nearestEven entropy x y]
          simp [hspec]
  · rfl

/-- Exact finite `x * y + z`, followed by one rounding step. -/
def fmaFinite? (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (x y z : Model fmt) : Option (Model fmt) := do
  let dx ← Model.toDyadic? x
  let dy ← Model.toDyadic? y
  let dz ← Model.toDyadic? z
  pure (Policy.roundDyadic fmt policy entropy
    (Model.addDyadic (mulDyadic dx dy) dz))

/-- Divide two finite values and round the exact rational quotient once. -/
def divFinite? (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (x y : Model fmt) : Option (Model fmt) := do
  let dx ← Model.toDyadic? x
  let dy ← Model.toDyadic? y
  if dy.significand == 0 then
    none
  else
    let sign := Bool.xor dx.negative dy.negative
    let exponentDifference := dx.exponent - dy.exponent
    let (numerator, denominator) :=
      match exponentDifference with
      | .ofNat shift => (Nat.shiftLeft dx.significand shift, dy.significand)
      | .negSucc shift => (dx.significand, Nat.shiftLeft dy.significand (shift + 1))
    Policy.roundRat fmt policy entropy sign numerator denominator

/--
Fused multiply-add from one storage format into a potentially wider accumulator format.

For example, `x` and `y` may be FP8 while `acc` is BF16, FP16,
FP32, or a custom wider format. There is no intermediate rounding of the product.
-/
def mulAddFinite? (storage accumulator : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (x y : Model storage) (acc : Model accumulator) : Option (Model accumulator) := do
  let dx ← Model.toDyadic? x
  let dy ← Model.toDyadic? y
  let da ← Model.toDyadic? acc
  pure (Policy.roundDyadic accumulator policy entropy
    (Model.addDyadic (mulDyadic dx dy) da))

end FloatLib.Floats.Formats.BinaryInterchange.Model
