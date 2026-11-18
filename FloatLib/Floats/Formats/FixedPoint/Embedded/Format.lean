/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Affine
public import FloatLib.Numerics.Quantization.Integer.Proof

/-!
# N1169 binary fixed-point representations

WG14 N1169, labelled ISO/IEC TR 18037:2006(E), §§4.1.1–4.1.3 and §4.2's
proposed C clause 6.2.6.3, specifies signed and unsigned binary coefficient grids.
The common affine quantizer supplies their stored interval; `IntegerFormat` supplies
their word range. `_Fract` has no integral bits, while `_Accum` leaves that count free.

The family includes every precision, including small extensions below C's minima.
It models value bits, without object padding, alignment, or a C language frontend.
Saturating and primary formats share a representation, as N1169 requires.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics FloatLib.Numerics.Quantization
open FloatLib.Numerics.Representations

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.1: binary value layout, independent of C rank and
    object padding. -/
structure Format where
  /-- Whether the coefficient uses a two's-complement sign bit. -/
  signed : Bool
  /-- Number of integral value bits, excluding a sign bit. -/
  integralBits : Nat
  /-- Number of fractional value bits. -/
  fractionalBits : Nat
  /-- Whether the type itself requests saturation, independently of pragmas. -/
  saturating : Bool := false
  deriving DecidableEq, Repr

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.1: the whole `_Fract` family has zero integral bits. -/
def _Fract (signed : Bool) (fractionalBits : Nat) : Format :=
  ⟨signed, 0, fractionalBits, false⟩

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.1: the whole `_Accum` family has independent integral
    and fractional bits. -/
def _Accum (signed : Bool) (integralBits fractionalBits : Nat) : Format :=
  ⟨signed, integralBits, fractionalBits, false⟩

/-- WG14 N1169 (2006 TR 18037 draft), §§4.1.1–4.1.3: `_Sat` changes overflow behavior and
    preserves representation. -/
def _Sat (format : Format) : Format :=
  { format with saturating := true }

/-- WG14 N1169 (2006 TR 18037 draft), §4.2, C 6.2.6.3: precision counts integral and fractional
    value bits. -/
def Format.precision (format : Format) : Nat :=
  format.integralBits + format.fractionalBits

/-- WG14 N1169 (2006 TR 18037 draft), §4.2, C 6.2.6.3: width also counts the sign bit, but
    excludes padding. -/
def Format.width (format : Format) : Nat :=
  format.precision + format.signed.toNat

/-- The shared signed/unsigned integer format of the coefficient. -/
def Format.integerFormat (format : Format) : IntegerFormat :=
  if format.signed then .signed format.width else .unsigned format.width

/-- N1169's coefficient grid, as the existing affine quantizer with zero point zero.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.1.
-/
def Format.quantizer (format : Format) : AffineQuantizer where
  scale := 1 / (2 : ℚ) ^ format.fractionalBits
  zeroPoint := 0
  qmin := format.integerFormat.minValue
  qmax := format.integerFormat.maxValue
  scale_pos := div_pos (by decide) (pow_pos (by decide) _)
  code_range := (IntegerFormat.zero_inRange format.integerFormat).1.trans
    (IntegerFormat.zero_inRange format.integerFormat).2

/-- A coefficient in the shared affine interval, with its range proof erased at execution. -/
abbrev Format.Code (format : Format) :=
  format.quantizer.storedCode

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.7.4, C 7.18a.6.5: the stored signed or unsigned
    integer coefficient. -/
@[inline] def bitsfx {format : Format} (value : format.Code) : Int :=
  value.1

/-- Exact rational denotation of a binary fixed-point code. -/
@[inline] def Format.decode {format : Format} (value : format.Code) : ℚ :=
  format.quantizer.dequantize value.1

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.7.5, C 7.18a.6.6: an exactly representable integer
    coefficient.
An out-of-range argument has no exact code and is reported as `none`. -/
@[inline] def fxbits (format : Format) (coefficient : Int) : Option format.Code :=
  if h : format.integerFormat.InRange coefficient then some ⟨coefficient, h⟩ else none

/-- The coefficient denotation is division by the fixed binary scale. -/
theorem decode_eq {format : Format} (value : format.Code) :
    Format.decode value = (bitsfx value : ℚ) / (2 : ℚ) ^ format.fractionalBits := by
  simp [Format.decode, Format.quantizer, AffineQuantizer.dequantize, bitsfx, div_eq_mul_inv,
    mul_comm]

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.5: coefficient extraction multiplies the
    value by `2^F`. -/
theorem bitsfx_eq_scaled {format : Format} (value : format.Code) :
    (bitsfx value : ℚ) = Format.decode value * (2 : ℚ) ^ format.fractionalBits := by
  rw [decode_eq, div_mul_cancel₀]
  exact pow_ne_zero _ (by decide)

/-- Integer-to-fixed conversion succeeds exactly for its stated coefficient and valid range. -/
theorem fxbits_eq_some_iff (format : Format) (coefficient : Int) (value : format.Code) :
    fxbits format coefficient = some value ↔ bitsfx value = coefficient := by
  unfold fxbits bitsfx
  split
  · simp only [Option.some.injEq, Subtype.ext_iff]
    exact eq_comm
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro he
    exact h (he ▸ value.2)

/-- Every stored coefficient survives the standard bitwise conversion round trip. -/
@[simp] theorem fxbits_bitsfx {format : Format} (value : format.Code) :
    fxbits format (bitsfx value) = some value :=
  (fxbits_eq_some_iff _ _ _).2 rfl

/-- Complete nonpadding word, with two's-complement encoding for signed values. -/
@[inline] def Format.toBits {format : Format} (value : format.Code) :
    BitVec format.width :=
  if format.signed then BitVec.ofInt format.width value.1
  else BitVec.ofNat format.width value.1.toNat

/-- Decode every nonpadding word into its signed or unsigned coefficient interval. -/
@[inline] def Format.ofBits (format : Format) (bits : BitVec format.width) : format.Code :=
  if hs : format.signed then
    ⟨bits.toInt, by
      change format.integerFormat.InRange bits.toInt
      simp only [integerFormat, hs, ↓reduceIte, IntegerFormat.InRange, IntegerFormat.range,
        IntegerRange.Contains, IntegerFormat.minValue, IntegerFormat.maxValue]
      exact ⟨BitVec.toInt_intMin_le bits, by
        simpa [FixedInt.maxValue_eq] using (BitVec.toInt_le (x := bits))⟩⟩
  else
    ⟨bits.toNat, by
      change format.integerFormat.InRange (bits.toNat : Int)
      simpa [integerFormat, hs] using IntegerFormat.toNat_inRange bits⟩

/-- Word decoding agrees with the corresponding signed or unsigned integer interpretation. -/
theorem bitsfx_ofBits (format : Format) (bits : BitVec format.width) :
    bitsfx (format.ofBits bits) =
      if format.signed then bits.toInt else (bits.toNat : Int) := by
  by_cases hs : format.signed <;> simp [Format.ofBits, bitsfx, hs]

/-- Every coefficient survives word packing and decoding, at every width. -/
@[simp] theorem ofBits_toBits {format : Format} (value : format.Code) :
    format.ofBits (Format.toBits value) = value := by
  apply Subtype.ext
  change bitsfx _ = bitsfx value
  rw [bitsfx_ofBits]
  have hr : format.integerFormat.InRange value.1 := value.2
  by_cases hs : format.signed
  · simp only [hs, ↓reduceIte, Format.toBits]
    rw [Format.integerFormat, ite_eq_left hs] at hr
    exact FixedInt.toInt_ofInt_eq_self
      (by
        simpa only [IntegerFormat.InRange, IntegerFormat.range, IntegerRange.Contains,
          IntegerFormat.minValue, IntegerFormat.maxValue, FixedInt.InRange] using hr)
  · simp only [hs, Format.toBits]
    rw [Format.integerFormat, ite_eq_right hs] at hr
    exact IntegerFormat.toNat_ofNat_of_inRange hr

/-- Every complete word survives decoding and packing; padding is outside this representation. -/
@[simp] theorem toBits_ofBits (format : Format) (bits : BitVec format.width) :
    Format.toBits (format.ofBits bits) = bits := by
  by_cases hs : format.signed <;> simp [Format.toBits, Format.ofBits, hs]

end FloatLib.Floats.Formats.FixedPoint.Embedded
