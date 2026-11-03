/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.ProductRound.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Core.Proof

/-!
# Shared proofs for native normal operand pairs

Several one-word kernels start the same way: they reject zero, subnormal and exceptional
operands, then expose two normalized significands and their biased exponents.
`Small.Core.Runtime` has the executable decoder, and this module proves its common contract once.

`View` records the generic decoder results together with the bounds the fixed-word rounders need,
so the multiplication and division proofs don't repeat the storage-field and exceptional-value
arguments. No executable definition depends on this module.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeNormalPair

open NativeSmallWord

/-- Fields and decoder facts of two successfully decoded normal operands. -/
structure View {fmt : FloatFormat} (x y : Model fmt) where
  /-- XOR of the operand signs, as supplied to multiplicative kernels. -/
  sign : Bool
  /-- Biased exponent of the left operand. -/
  xExponent : UInt64
  /-- Biased exponent of the right operand. -/
  yExponent : UInt64
  /-- Normalized significand of the left operand. -/
  xMantissa : UInt64
  /-- Normalized significand of the right operand. -/
  yMantissa : UInt64
  /-- The native sign calculation agrees with the model fields. -/
  sign_eq :
    sign = Bool.xor (Model.signBit x) (Model.signBit y)
  /-- The generic finite decoder sees the same left operand fields. -/
  xDecode :
    FiniteKernel.decode? x =
      some {
        sign := Model.signBit x
        exponent := xExponent.toNat
        mantissa := xMantissa.toNat }
  /-- The generic finite decoder sees the same right operand fields. -/
  yDecode :
    FiniteKernel.decode? y =
      some {
        sign := Model.signBit y
        exponent := yExponent.toNat
        mantissa := yMantissa.toNat }
  /-- The left biased exponent is a nonzero stored exponent. -/
  xExponentBounds :
    0 < xExponent.toNat ∧ xExponent.toNat < 2 ^ fmt.expWidth
  /-- The right biased exponent is a nonzero stored exponent. -/
  yExponentBounds :
    0 < yExponent.toNat ∧ yExponent.toNat < 2 ^ fmt.expWidth
  /-- The left significand has its implicit leading bit. -/
  xMantissaBounds :
    2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧
      xMantissa.toNat < 2 ^ (fmt.fracWidth + 1)
  /-- The right significand has its implicit leading bit. -/
  yMantissaBounds :
    2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧
      yMantissa.toNat < 2 ^ (fmt.fracWidth + 1)

/-- The left significand of a view is nonzero. -/
theorem View.xMantissa_toNat_ne_zero {fmt : FloatFormat} {x y : Model fmt} (view : View x y) :
    view.xMantissa.toNat ≠ 0 :=
  Nat.ne_of_gt ((Nat.two_pow_pos fmt.fracWidth).trans_le view.xMantissaBounds.1)

/-- The right significand of a view is nonzero. -/
theorem View.yMantissa_toNat_ne_zero {fmt : FloatFormat} {x y : Model fmt} (view : View x y) :
    view.yMantissa.toNat ≠ 0 :=
  Nat.ne_of_gt ((Nat.two_pow_pos fmt.fracWidth).trans_le view.yMantissaBounds.1)

/--
A native normal field decode agrees with the generic finite decoder.

This holds in every encoding: a nonzero exponent field below all ones is never a NaN, since the
unsigned-zero NaN has a zero exponent field.
-/
theorem decode_normal {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt)
    (hnonzero :
      NativeSmallWord.exponentField fmt (NativeSmallWord.toWord x) ≠ 0)
    (hnonexceptional :
      NativeSmallWord.exponentField fmt (NativeSmallWord.toWord x) ≠
        NativeSmallWord.exponentMask fmt) :
    FiniteKernel.decode? x =
      some {
        sign := Model.signBit x
        exponent :=
          (NativeSmallWord.exponentField fmt
            (NativeSmallWord.toWord x)).toNat
        mantissa :=
          (NativeSmallWord.fractionField fmt
              (NativeSmallWord.toWord x) |||
            NativeSmallWord.hiddenBit fmt).toNat } := by
  have hexponent :
      (NativeSmallWord.exponentField fmt
          (NativeSmallWord.toWord x)).toNat =
        Model.expField x :=
    NativeSmallWord.exponentField_toNat hwidth x
  have hgenericNonzero : Model.expField x ≠ 0 := by
    intro h
    apply hnonzero
    apply UInt64.toNat_inj.mp
    rw [hexponent, h]
    rfl
  have hgenericFinite : Model.expField x ≠ fmt.expAllOnesNat :=
    fun h => hnonexceptional ((NativeSmallWord.exponentField_eq_exponentMask_iff hwidth x).mpr h)
  have hfinite : Model.isFinite x = true := by
    unfold Model.isFinite
    cases hencoding : fmt.encoding with
    | ieee => simpa [Model.IEEE.isFinite] using hgenericFinite
    | finite => rfl
    | finiteMaxNaN => simp [Model.isNaN, hencoding, hgenericFinite]
    | finiteUnsignedZero =>
        simp only [Model.isNaN, hencoding, Bool.not_eq_eq_eq_not, Bool.not_true,
          beq_eq_false_iff_ne, ne_eq]
        intro hbits
        apply hgenericNonzero
        have hbitsNat : x.toNatBits = 2 ^ (fmt.expWidth + fmt.fracWidth) := by
          rw [Model.toNatBits, hbits, FloatFormat.signMask_toNat]
          congr 1
          unfold FloatFormat.bitWidth
          omega
        rw [Model.expField_eq_internal_apply, Model.Internal.expField, hbitsNat,
          Nat.shiftRight_eq_div_pow, pow_add,
          Nat.mul_div_cancel _ (Nat.two_pow_pos _), FloatFormat.expAllOnesNat,
          Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
  unfold FiniteKernel.decode?
  simp only [hfinite, Bool.not_true, Bool.false_eq_true, ite_false,
    FiniteKernel.decodeMantissa, beq_iff_eq, hgenericNonzero]
  rw [← hexponent]
  simp only [Model.pow2_eq_two_pow]
  rw [← NativeSmallWord.normalMantissa_toNat hwidth x]

/-- The facts a `View` records about one normal operand. -/
private theorem normalOperand {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) (x : Model fmt)
    (hzero : exponentField fmt (toWord x) ≠ 0)
    (hexceptional : exponentField fmt (toWord x) ≠ exponentMask fmt) :
    FiniteKernel.decode? x =
        some {
          sign := Model.signBit x
          exponent := (exponentField fmt (toWord x)).toNat
          mantissa := (fractionField fmt (toWord x) ||| hiddenBit fmt).toNat } ∧
      (0 < (exponentField fmt (toWord x)).toNat ∧
        (exponentField fmt (toWord x)).toNat < 2 ^ fmt.expWidth) ∧
      (2 ^ fmt.fracWidth ≤ (fractionField fmt (toWord x) ||| hiddenBit fmt).toNat ∧
        (fractionField fmt (toWord x) ||| hiddenBit fmt).toNat < 2 ^ (fmt.fracWidth + 1)) :=
  ⟨decode_normal hwidth x hzero hexceptional, exponentField_bounds_of_ne_zero hwidth x hzero,
    normalMantissa_bounds_of_width hwidth x⟩

/--
A successful `withNormalPair?` call yields a `View` whose fields are the ones passed to the kernel.

Since the kernel stays generic, the view serves any binary operation.
-/
theorem view_of_success
    {fmt : FloatFormat} {α : Type}
    (hwidth : fmt.bitWidth ≤ 64)
    (x y : Model fmt)
    (kernel :
      Bool → UInt64 → UInt64 → UInt64 → UInt64 → Option α)
    (result : α)
    (hresult :
      NativeSmallWord.withNormalPair? x y kernel = some result) :
    ∃ view : View x y,
      kernel view.sign view.xExponent view.yExponent
          view.xMantissa view.yMantissa =
        some result := by
  let xBits := NativeSmallWord.toWord x
  let yBits := NativeSmallWord.toWord y
  let xExponent := NativeSmallWord.exponentField fmt xBits
  let yExponent := NativeSmallWord.exponentField fmt yBits
  let allOnes := NativeSmallWord.exponentMask fmt
  let xMantissa :=
    NativeSmallWord.fractionField fmt xBits ||| hiddenBit fmt
  let yMantissa :=
    NativeSmallWord.fractionField fmt yBits ||| hiddenBit fmt
  let sign :=
    Bool.xor
      (NativeSmallWord.signField fmt xBits)
      (NativeSmallWord.signField fmt yBits)
  by_cases hxZero : xExponent = 0
  · simp [NativeSmallWord.withNormalPair?, NativeSmallWord.withNormalPairWord?,
      xBits, xExponent, hxZero] at hresult
  by_cases hxExceptional : xExponent = allOnes
  · simp [NativeSmallWord.withNormalPair?, NativeSmallWord.withNormalPairWord?,
      xBits, xExponent, allOnes, hxExceptional] at hresult
  by_cases hyZero : yExponent = 0
  · simp [NativeSmallWord.withNormalPair?, NativeSmallWord.withNormalPairWord?,
      yBits, yExponent, hyZero] at hresult
  by_cases hyExceptional : yExponent = allOnes
  · simp [NativeSmallWord.withNormalPair?, NativeSmallWord.withNormalPairWord?,
      yBits, yExponent, allOnes, hyExceptional] at hresult
  have hkernel :
      kernel sign xExponent yExponent xMantissa yMantissa =
        some result := by
    simpa [NativeSmallWord.withNormalPair?, NativeSmallWord.withNormalPairWord?,
      xBits, yBits, xExponent, yExponent, allOnes, xMantissa,
      yMantissa, sign, hxZero, hxExceptional, hyZero, hyExceptional] using
      hresult
  have hsign :
      sign = Bool.xor (Model.signBit x) (Model.signBit y) := by
    dsimp only [sign, xBits, yBits]
    rw [NativeSmallWord.signField_eq hwidth x,
      NativeSmallWord.signField_eq hwidth y]
  obtain ⟨hxDecode, hxExponentBounds, hxMantissaBounds⟩ :=
    normalOperand hwidth x hxZero hxExceptional
  obtain ⟨hyDecode, hyExponentBounds, hyMantissaBounds⟩ :=
    normalOperand hwidth y hyZero hyExceptional
  exact ⟨{
    sign
    xExponent
    yExponent
    xMantissa
    yMantissa
    sign_eq := hsign
    xDecode := hxDecode
    yDecode := hyDecode
    xExponentBounds := hxExponentBounds
    yExponentBounds := hyExponentBounds
    xMantissaBounds := hxMantissaBounds
    yMantissaBounds := hyMantissaBounds }, hkernel⟩

/--
A normal-pair kernel that rounds like `FiniteProductRound.round` refines `FiniteKernel.mul?`.

Because the shared view handles the native decoding, `kernel_refines` only covers the product and
its rounding.
-/
theorem mul_refines
    {fmt : FloatFormat}
    (hieee : fmt.isIEEE = true)
    (hwidth : fmt.bitWidth ≤ 64)
    (kernel :
      Bool → UInt64 → UInt64 → UInt64 → UInt64 →
        Option (Model fmt))
    (kernel_refines :
      ∀ (sign : Bool)
        (xExponent yExponent xMantissa yMantissa : UInt64)
        (result : Model fmt),
        (0 < xExponent.toNat ∧
          xExponent.toNat < 2 ^ fmt.expWidth) →
        (0 < yExponent.toNat ∧
          yExponent.toNat < 2 ^ fmt.expWidth) →
        (2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧
          xMantissa.toNat < 2 ^ (fmt.fracWidth + 1)) →
        (2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧
          yMantissa.toNat < 2 ^ (fmt.fracWidth + 1)) →
        kernel sign xExponent yExponent xMantissa yMantissa =
          some result →
        result =
          FiniteProductRound.round fmt sign
            (xMantissa.toNat * yMantissa.toNat)
            ((xExponent.toNat - 1) + (yExponent.toNat - 1)))
    (x y result : Model fmt)
    (hresult : NativeSmallWord.withNormalPair? x y kernel = some result) :
    FiniteKernel.mul? x y = some result := by
  rcases view_of_success hwidth x y kernel result hresult with
    ⟨view, hkernel⟩
  have hrefines :=
    kernel_refines view.sign view.xExponent view.yExponent
      view.xMantissa view.yMantissa result
      view.xExponentBounds view.yExponentBounds
      view.xMantissaBounds view.yMantissaBounds hkernel
  unfold FiniteKernel.mul?
  rw [view.xDecode, view.yDecode]
  simp only
  rw [ite_eq_right (by simp [view.xMantissa_toNat_ne_zero, view.yMantissa_toNat_ne_zero])]
  rw [ite_eq_left hieee]
  apply congrArg some
  simp only [FiniteKernel.scale, beq_iff_eq,
    view.xExponentBounds.1.ne', view.yExponentBounds.1.ne', ite_false]
  rw [← view.sign_eq]
  exact hrefines.symm

end Model.NativeNormalPair
end FloatLib.Floats.Formats.BinaryInterchange
