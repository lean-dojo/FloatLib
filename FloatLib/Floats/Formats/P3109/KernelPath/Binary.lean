/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.KernelPath.Encoding
public import FloatLib.Floats.Formats.P3109.KernelPath.Flat
public import FloatLib.Floats.Formats.P3109.Arithmetic.External.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.ToRat

/-!
# The kernel P3109 conversion from a binary interchange value

P3109 Interim Report v4.1 (14 September 2026), §§4.8.1 and 4.9.1, an unapproved draft. A value
of a binary interchange format enters P3109 arithmetic through its exact value: the sign of a
zero and the payload of a NaN are dropped, and an infinity keeps its sign. On the encoding of
the value, with shifts and masks:

* `binaryClass`, `binarySign`, `binaryNumerator`, `binaryDenominator`: the class, the sign bit
  and the ratio of natural numbers of the closed value of a binary word;
* `decode_closed`: `Arithmetic.Mixed.decode` of a binary value is that closed value, for every
  format descriptor and every value;
* `convertBinary_eq`: `Arithmetic.Mixed.Convert` of a binary value into a P3109 format stores
  `convertBinary` of the encoding, for every source descriptor, every destination descriptor,
  every rounding mode with every random word and every saturation mode;
* `Flat.convertBinary`: the same function with the stages of the projection unfolded, which the
  kernel rule of `P3109.KernelPath.Rules` evaluates.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.KernelPath

open FloatLib.Numerics FloatLib.Numerics.Kernel
open FloatLib.Floats.Formats.P3109
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)

/-! ## The closed value of a binary word -/

/-- The class of the closed value of the word `a` of the binary format `fmt`: zero for a finite
word, one and two for the positive and the negative infinity, three for a NaN. -/
def binaryClass (fmt : FloatFormat) (a : Nat) : Nat :=
  (fun s u =>
    Bool.casesOn (motive := fun _ => Nat)
      (Nat.beq (BinaryInterchange.KernelPath.nonFinite fmt s u) 0)
      (Bool.casesOn (motive := fun _ => Nat)
        (Nat.beq (BinaryInterchange.KernelPath.infFlag fmt u) 0) (Nat.succ s) 3)
      0)
    (Nat.shiftRight a (BinaryInterchange.KernelPath.signPos fmt))
    (Nat.land a (BinaryInterchange.KernelPath.magnitudeMask fmt))

/-- The sign bit of the word `a` of the binary format `fmt`, as zero or one. -/
def binarySign (fmt : FloatFormat) (a : Nat) : Nat :=
  Nat.shiftRight a (BinaryInterchange.KernelPath.signPos fmt)

/-- The numerator of the magnitude of the finite word `a`: its significand with the implicit
bit, shifted left by its exponent field less one. -/
def binaryNumerator (fmt : FloatFormat) (a : Nat) : Nat :=
  (fun u =>
    (fun h => Nat.shiftLeft (Nat.sub u (Nat.shiftLeft h fmt.fracWidth)) h)
      (Nat.sub (Nat.shiftRight u fmt.fracWidth) 1))
    (Nat.land a (BinaryInterchange.KernelPath.magnitudeMask fmt))

/-- The denominator of the magnitude of a finite word of `fmt`:
`2 ^ (exponentBias + fracWidth - 1)`. -/
def binaryDenominator (fmt : FloatFormat) : Nat :=
  Nat.shiftLeft 1 (Nat.sub (Nat.add fmt.exponentBias fmt.fracWidth) 1)

/-- The code of the value of the binary word `a` in a P3109 format (§4.9.1), projected once. -/
def convertBinary (fmt : FloatFormat) (K P sg ex mi N R si a : Nat) : Nat :=
  project K P sg ex mi N R si (binaryClass fmt a) (binarySign fmt a) (binaryNumerator fmt a)
    (binaryDenominator fmt)

/-- The sign of a binary word is a bit. -/
theorem binarySign_le {fmt : FloatFormat} (x : Model fmt) : binarySign fmt x.toNatBits ≤ 1 := by
  unfold binarySign
  rw [Nat.shiftRight_eq', BinaryInterchange.KernelPath.sign_toNatBits]
  split <;> omega

/-- The denominator of a binary word is not zero. -/
theorem binaryDenominator_ne_zero (fmt : FloatFormat) : binaryDenominator fmt ≠ 0 := by
  unfold binaryDenominator
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul]
  exact (Nat.two_pow_pos _).ne'

/-- A signed ratio of natural numbers as the fraction that the kernel builds. -/
theorem signed_div_eq_mkRat (s n d : Nat) :
    (if s = 0 then (n : Rat) else -(n : Rat)) / (d : Rat) =
      mkRat (Bool.casesOn (motive := fun _ => Int) (Nat.beq s 0) (Int.negOfNat n) (Int.ofNat n))
        d := by
  rw [Rat.mkRat_eq_div]
  cases s with
  | zero => simp
  | succ k => simp [show Nat.beq (k + 1) 0 = false from rfl, Int.negOfNat_eq]

/-- The class of a binary word: zero for a finite value, one or two for an infinity by its
sign, and three for a NaN, for every format descriptor. -/
theorem binaryClass_eq {fmt : FloatFormat} (x : Model fmt) :
    binaryClass fmt x.toNatBits =
      if Model.isFinite x = true then 0
      else if Model.isInfinite x = true then (if Model.signBit x = true then 2 else 1)
      else 3 := by
  unfold binaryClass
  simp only [Nat.shiftRight_eq', Nat.land_eq, BinaryInterchange.KernelPath.sign_toNatBits,
    BinaryInterchange.KernelPath.magnitude_toNatBits]
  kernel_notation
  by_cases hfinite : Model.isFinite x = true
  · rw [ite_eq_left ((BinaryInterchange.KernelPath.nonFinite_eq_zero_iff x).mpr hfinite),
      ite_eq_left hfinite]
  · rw [ite_eq_right (fun h => hfinite ((BinaryInterchange.KernelPath.nonFinite_eq_zero_iff x).mp
      h)), ite_eq_right hfinite, BinaryInterchange.KernelPath.infFlag_eq]
    cases Model.isInfinite x <;> cases Model.signBit x <;> rfl

/--
P3109 interim report v4.1, §4.8.1: the value that mixed arithmetic reads from a binary
interchange value is the closed value of its encoding, for every format descriptor: the exact
value of a finite word, with the sign of a zero dropped, an infinity with its sign, and the one
NaN for every NaN.
-/
theorem decode_closed {fmt : FloatFormat} (x : Model fmt) :
    Arithmetic.Mixed.decode x =
      closed (binaryClass fmt x.toNatBits) (binarySign fmt x.toNatBits)
        (binaryNumerator fmt x.toNatBits) (binaryDenominator fmt) := by
  rw [Arithmetic.External.mixed_decode_eq_decode, binaryClass_eq]
  unfold Arithmetic.External.decode
  by_cases hfinite : Model.isFinite x = true
  · obtain ⟨d, hd⟩ := Model.exists_toDyadic?_of_isFinite hfinite
    have hratio : closed 0 (binarySign fmt x.toNatBits) (binaryNumerator fmt x.toNatBits)
        (binaryDenominator fmt) =
          .finite (BinaryInterchange.KernelPath.ratValue fmt x.toNatBits) := by
      unfold closed
      rw [ite_eq_left rfl, signed_div_eq_mkRat]
      rfl
    rw [ite_eq_left hfinite, hratio, BinaryInterchange.KernelPath.ratValue_eq x d hd]
    simp only [Model.exactNumericalSystem, hd, Arithmetic.toRat]
  · have hfalse : Model.isFinite x = false := by simpa using hfinite
    have hnone := BinaryInterchange.KernelPath.toDyadic?_eq_none_of_isFinite_eq_false x hfalse
    rw [ite_eq_right hfinite]
    simp only [Model.exactNumericalSystem, hnone]
    cases Model.isInfinite x
    · simp [closed, Arithmetic.toRat, Arithmetic.nan]
    · cases Model.signBit x <;> simp [closed, Arithmetic.toRat]

/--
P3109 interim report v4.1, §4.9.1: the conversion of a binary interchange value into a P3109
format stores `convertBinary` of its encoding, for every source descriptor, every destination
descriptor, every rounding mode with every random word and every saturation mode.
-/
theorem convertBinary_eq {fmt : FloatFormat} (x : Model fmt) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Arithmetic.Mixed.Convert (Arithmetic.Destination.p3109 target) x mode saturation =
      ExecFloat.P3109.ofNatBits
        (convertBinary fmt target.bitWidth target.precision (sgOf target) (exOf target)
          (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation)
          x.toNatBits) := by
  change ExecFloat.P3109.projectRat (Arithmetic.Mixed.decode x) mode saturation = _
  rw [decode_closed, projectRat_eq _ _ _ _ _ _ _ (binarySign_le x)
    (fun _ _ => binaryDenominator_ne_zero fmt)]
  rfl

/-! ## The flat form -/

/-- `convertBinary` with the stages of the projection unfolded, on the fields of the word. -/
noncomputable def Flat.convertBinary (fmt : FloatFormat) (K P sg ex mi N R si a : Nat) : Nat :=
  kernel_inline% [KernelPath.binaryClass, KernelPath.binarySign, KernelPath.binaryNumerator,
      KernelPath.binaryDenominator]
    (Flat.project K P sg ex mi N R si (KernelPath.binaryClass fmt a)
      (KernelPath.binarySign fmt a) (KernelPath.binaryNumerator fmt a)
      (KernelPath.binaryDenominator fmt))

/-- `Flat.convertBinary` is `convertBinary`, by unfolding. -/
theorem Flat.convertBinary_eq (fmt : FloatFormat) (K P sg ex mi N R si a : Nat) :
    Flat.convertBinary fmt K P sg ex mi N R si a =
      KernelPath.convertBinary fmt K P sg ex mi N R si a :=
  kernel_refl%

end FloatLib.Floats.Formats.P3109.KernelPath
