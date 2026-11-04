/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Core.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Division.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Quotient.Proof
public import FloatLib.Floats.ExecFloat.Backends.Generic.QuotientRound.Proof
import FloatLib.Floats.ExecFloat.Backends.Word.Small.Core.Proof
import FloatLib.Floats.ExecFloat.Backends.Word.Small.Div.Proof

/-!
# Verified native normal-result division for binary64

Quotient bits on the native path come from a restoring `UInt64` loop. Every accepted result equals
the generic finite kernel's result, and `divFinite_eq_divFiniteComponents` extends this agreement to
the whole optional finite operation, declined inputs included. Zeros and quotients outside the
normal-result path use the generic finite kernel, and non-finite operands are handled by the outer
arithmetic dispatcher.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord.RestoringQuotient
open FloatLib.Numerics.FixedWord

/-! ## The one-word normal quotient rounder at binary64 -/

/-- At binary64, one-word storage of a word is the native binary64 wrapper. -/
private theorem ofWord_eq_ofUInt64 (bits : UInt64) :
    NativeSmallWord.ofWord (fmt := FloatFormat.binary64) bits = ofUInt64 bits := by
  unfold NativeSmallWord.ofWord ofUInt64
  apply congrArg Model.ofBits
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNatLT, NativeSmallWord.and_storageMask_toNat]
  exact Nat.mod_eq_of_lt bits.toNat_lt

/-- At binary64, one-word field packing is the native binary64 packing. -/
private theorem packFields_eq_packFieldsWord (sign : Bool) (exponent fraction : UInt64) :
    NativeSmallWord.packFields FloatFormat.binary64 sign exponent fraction =
      packFieldsWord sign exponent fraction := by
  have hexponent : NativeSmallWord.exponentMask FloatFormat.binary64 = 0x7ff := by decide
  have hfraction :
      NativeSmallWord.fractionMask FloatFormat.binary64 = 0x000fffffffffffff := by decide
  unfold NativeSmallWord.packFields packFieldsWord
  rw [hexponent, hfraction]
  rfl

private theorem binary64_biasInt : NativeSmallWord.biasInt FloatFormat.binary64 = 1023 := by
  decide

private theorem binary64_carryBit :
    NativeSmallWord.carryBit FloatFormat.binary64 = 0x0020000000000000 := by
  decide

private theorem binary64_hiddenBit :
    NativeSmallWord.hiddenBit FloatFormat.binary64 = 0x0010000000000000 := by
  decide

/--
The binary64 normal quotient rounder is the one-word rounder `roundNormalNative?` at binary64,
so its agreement with `normalSpec?` is the one-word theorem.
-/
private theorem roundNormalNative_eq_spec
    (sign : Bool) (num den : UInt64) (exponent : Int)
    (hnum : num ≠ 0) (hden : den ≠ 0)
    (hnumFit : num.toNat < 2 ^ 53)
    (hdenFit : den.toNat < 2 ^ 53) :
    (let rationalExponent :=
        floorLog2RatWord num den
      let totalExponent := rationalExponent + exponent
      if totalExponent < -1022 || 1023 < totalExponent then
        (none : Option Value)
      else
        let shift := Int.toNat (52 - rationalExponent)
        let roundedMantissa :=
          roundScaledQuotient num den shift
        let carry := roundedMantissa == 0x0020000000000000
        let normalizedExponent :=
          if carry then totalExponent + 1 else totalExponent
        if 1023 < normalizedExponent then
          none
        else
          let normalizedMantissa :=
            if carry then 0x0010000000000000 else roundedMantissa
          let encodedExponent :=
            UInt64.ofNat (Int.toNat (normalizedExponent + 1023))
          let fraction := normalizedMantissa - 0x0010000000000000
          some <| ofUInt64 <|
            packFieldsWord sign encodedExponent fraction) =
      FiniteQuotientRound.normalSpec? FloatFormat.binary64
        sign num.toNat den.toNat exponent := by
  rw [← NativeSmallWordDiv.roundNormalNative_eq_spec FloatFormat.binary64 (by decide)
    sign num den exponent hnum hden hnumFit hdenFit]
  unfold NativeSmallWordDiv.roundNormalNative?
  simp only [binary64_biasInt, binary64_carryBit, binary64_hiddenBit, ofWord_eq_ofUInt64,
    packFields_eq_packFieldsWord, binary64_fracWidth]
  rfl

private theorem divNormal_refines
    (x y result : Value)
    (hresult : divNormal? x y = some result) :
    NativeBinary64.divFiniteComponents? x y = some result := by
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  let xFraction := fracField xBits
  let yFraction := fracField yBits
  let xMantissa := finiteMantissa xExponent xFraction
  let yMantissa := finiteMantissa yExponent yFraction
  by_cases hxExceptional : xExponent = 0x7ff
  · simp [divNormal?, divNormalWord?, xBits, xExponent, hxExceptional] at hresult
  by_cases hyExceptional : yExponent = 0x7ff
  · simp [divNormal?, divNormalWord?, yBits, yExponent, hyExceptional] at hresult
  by_cases hxZero : xMantissa = 0
  · simp [divNormal?, divNormalWord?, xBits, yBits, xExponent, yExponent,
      xFraction, xMantissa,
      hxExceptional, hyExceptional, hxZero] at hresult
  by_cases hyZero : yMantissa = 0
  · simp [divNormal?, divNormalWord?, xBits, yBits, xExponent, yExponent,
      yFraction, yMantissa, hxExceptional, hyExceptional,
      hyZero] at hresult
  have hxFractionBound : xFraction.toNat < 2 ^ 52 := by
    simpa only [xFraction, xBits] using fracField_lt x
  have hyFractionBound : yFraction.toNat < 2 ^ 52 := by
    simpa only [yFraction, yBits] using fracField_lt y
  have hxMantissaFit : xMantissa.toNat < 2 ^ 53 := by
    simpa only [xMantissa] using
      finiteMantissa_lt xExponent xFraction hxFractionBound
  have hyMantissaFit : yMantissa.toNat < 2 ^ 53 := by
    simpa only [yMantissa] using
      finiteMantissa_lt yExponent yFraction hyFractionBound
  let exponent :=
    Int.ofNat (finiteScale xExponent).toNat -
      Int.ofNat (finiteScale yExponent).toNat
  let rationalExponent :=
    floorLog2RatWord xMantissa yMantissa
  have hspec :
      FiniteQuotientRound.normalSpec? FloatFormat.binary64
          (Bool.xor (signBit xBits) (signBit yBits))
          xMantissa.toNat yMantissa.toNat exponent =
        some result := by
    rw [← roundNormalNative_eq_spec
      (Bool.xor (signBit xBits) (signBit yBits))
      xMantissa yMantissa exponent hxZero hyZero
      hxMantissaFit hyMantissaFit]
    simpa [divNormal?, divNormalWord?, apply_ite (Option.map ofUInt64), xBits, yBits,
      xExponent, yExponent, xFraction, yFraction, xMantissa, yMantissa, exponent,
      rationalExponent, hxExceptional, hyExceptional, hxZero, hyZero,
      beq_iff_eq] using hresult
  have hrounded :=
    NativeWordQuotient.roundRatScaled_eq_of_normalSpec FloatFormat.binary64 (by decide)
      (Bool.xor (signBit xBits) (signBit yBits)) xMantissa yMantissa exponent hyZero
      hxMantissaFit result hspec
  unfold NativeBinary64.divFiniteComponents? NativeBinary64.decode?
  simp only [xBits, yBits, xExponent, yExponent, hxExceptional,
    hyExceptional, beq_iff_eq, ite_false, Option.some.injEq]
  change
    FiniteKernel.divComponents FloatFormat.binary64
        { sign := signBit xBits
          exponent := xExponent.toNat
          mantissa := xMantissa.toNat }
        { sign := signBit yBits
          exponent := yExponent.toNat
          mantissa := yMantissa.toNat } =
      result
  unfold FiniteKernel.divComponents
  have hxZeroNat : xMantissa.toNat ≠ 0 :=
    (uint64_toNat_eq_zero xMantissa).not.mpr hxZero
  have hyZeroNat : yMantissa.toNat ≠ 0 :=
    (uint64_toNat_eq_zero yMantissa).not.mpr hyZero
  simp only [hxZeroNat, hyZeroNat, beq_iff_eq, ite_false]
  rw [← FiniteKernel.finiteScale_toNat_eq_scale, ← FiniteKernel.finiteScale_toNat_eq_scale]
  simpa only [exponent] using hrounded.symm

/-- Native finite division with its fallback equals the generic component kernel. -/
theorem divFinite_eq_divFiniteComponents (x y : Value) :
    divFinite? x y = NativeBinary64.divFiniteComponents? x y := by
  cases hfast : divNormal? x y with
  | none => simp [divFinite?, hfast]
  | some result =>
      simp [divFinite?, hfast, divNormal_refines x y result hfast]

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
