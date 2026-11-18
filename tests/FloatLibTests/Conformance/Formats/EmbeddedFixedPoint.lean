/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Roundoff
public import FloatLib.Tactic.Roundoff

/-! N1169 representation, rounded overflow, rounding and usual-conversion regressions.

WG14 N1169 (2006 TR 18037 draft), §§4.1.1–4.1.7. -/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.EmbeddedFixedPoint

open FloatLib.Numerics
open FloatLib.Floats.Formats.FixedPoint.Embedded

private def signed : Format := _Fract true 3
private def word (bits : Nat) : signed.Code :=
  signed.ofBits (BitVec.ofNat signed.width bits)
private def even : Rounding := NearestRounding.even.toRounding

-- These clients use the universal representation and path certificates.
example (format : Format) (value : format.Code) :
    format.ofBits (Format.toBits value) = value :=
  ofBits_toBits value

example (format : Format) (bits : BitVec format.width) :
    Format.toBits (format.ofBits bits) = bits :=
  toBits_ofBits format bits

example (format : Format) (rounding : Rounding) (overflow : Overflow)
    (value : format.Code) :
    (compiled_reference% convert using
      { name := "fixed-point reference", kind := .generic, steadyCost := 1 }).run
      format rounding overflow (Format.decode value) = some value := by
  rw [(compiled_reference% convert using
    { name := "fixed-point reference", kind := .generic, steadyCost := 1 }).run_eq_spec]
  exact convert_decode format rounding overflow value

example (format : Format) (rounding : Rounding) (overflow : Overflow) (x : ℚ)
    (hs : ¬ format.Saturates overflow)
    (hx : ¬ format.integerFormat.InRange (rounding.run (x / format.quantizer.scale))) :
    convert format rounding overflow x = none :=
  (convert_eq_none_iff format rounding overflow x).mpr ⟨hs, hx⟩

example (format : Format) (rounding : Rounding) (overflow : Overflow) (x : ℚ)
    (hs : format.Saturates overflow)
    (hx : x / format.quantizer.scale ≤ (format.quantizer.qmin : ℚ)) :
    (convert format rounding overflow x).map bitsfx =
      some (bitsfx (format.clamp format.quantizer.qmin)) := by
  rw [convert_below format rounding overflow x hs hx]
  rfl

example (format : Format) (rounding : Rounding) (overflow : Overflow) (x : ℚ)
    (hs : format.Saturates overflow)
    (hx : (format.quantizer.qmax : ℚ) ≤ x / format.quantizer.scale) :
    (convert format rounding overflow x).map bitsfx =
      some (bitsfx (format.clamp format.quantizer.qmax)) := by
  rw [convert_above format rounding overflow x hs hx]
  rfl

example : Layout.example.Valid := Layout.example_valid
example : Layout.example.Recommended := Layout.example_recommended

example (format : Format) (rounding : Rounding) (overflow : Overflow)
    (x : ℚ) (result : format.Code) (hx : format.SourceInRange x)
    (hr : convert format rounding overflow x = some result) :
    bitsfx result = (x / format.quantizer.scale).floor ∨
      bitsfx result = (x / format.quantizer.scale).ceil :=
  convert_adjacent format rounding overflow x result hx hr

example {format : Format} (value : format.Code) (hnonzero : bitsfx value ≠ 0)
    (count : Nat) (h : format.integerFormat.InRange (bitsfx value * (2 : Int) ^ count)) :
    count ≤ countlsfx value :=
  le_countlsfx value hnonzero count h

example {format : Format} (value : format.Code) :
    format.integerFormat.InRange (bitsfx value * (2 : Int) ^ countlsfx value) :=
  countlsfx_in_range value

example {format : Format} (value : format.Code) :
    countlsfxCompiled.run value = countlsfx value := by
  rw [countlsfxCompiled.run_eq_spec]

-- The shared logarithm theorem applies to non-word intervals as well.
example (range : IntegerRange) (hzero : range.Contains 0) (coefficient : Int)
    (hmem : range.Contains coefficient) (hne : coefficient ≠ 0) (count : Nat) :
    count ≤ range.countLeftShifts coefficient ↔
      range.Contains (coefficient * (2 : Int) ^ count) :=
  range.le_countLeftShifts_iff hzero coefficient hmem hne count

example (rounding : NearestRounding) (fractionalBits : Nat) (coefficient count index : Int) :
    |(roundCoefficient rounding fractionalBits coefficient count : ℚ) - (coefficient : ℚ)| ≤
      |((index * (2 : Int) ^ (fractionalBits - count.toNat) : Int) : ℚ) -
        (coefficient : ℚ)| :=
  roundCoefficient_nearest rounding fractionalBits coefficient count index

example (rounding : NearestRounding) (fractionalBits : Nat) (coefficient count : Int) :
    |(roundCoefficient rounding fractionalBits coefficient count : ℚ) - (coefficient : ℚ)| ≤
      (2 : ℚ) ^ (fractionalBits - count.toNat) / 2 :=
  roundCoefficient_error_le_half rounding fractionalBits coefficient count

example {format : Format} (rounding : NearestRounding) (value result : format.Code)
    (count : Int) (hvalid : 0 ≤ count ∧ count < (format.fractionalBits : Int))
    (hrange : format.integerFormat.InRange
      (roundCoefficient rounding format.fractionalBits (bitsfx value) count))
    (hresult : roundfx rounding value count = some result) :
    ∃ k : Int, bitsfx result = 2 ^ (format.fractionalBits - count.toNat) * k :=
  roundfx_low_bits rounding value result count hvalid hrange hresult

example {format : Format} (value : format.Code) :
    0 ≤ bitsfx (absfx value) := by
  rw [absfx_eq_clamp]
  exact le_max_of_le_right (le_min
    (IntegerFormat.zero_inRange format.integerFormat).2 (abs_nonneg _))

example (destination : IntegerFormat) (x : ℚ) (result : Int)
    (hresult : toInteger destination x = some result) : destination.InRange result :=
  ((toInteger_eq_some_iff destination x result).mp hresult).2

example (format : Format) (rounding : Rounding) (overflow : Overflow) (x : ℚ)
    (result : format.Code) (hx : format.SourceInRange x)
    (hresult : convert format rounding overflow x = some result) :
    |Format.decode result - x| ≤ format.quantizer.scale := by
  simpa only [format.clippingError_eq_zero x hx, add_zero, mul_one] using
    convert_error_le_one format rounding overflow x result hresult

-- A proved local conversion contract composes through ordinary real arithmetic.
example (format : Format) (rounding : Rounding) (overflow : Overflow) (x : ℚ)
    (result : format.Code) (hresult : convert format rounding overflow x = some result) :
    MixedError (-(Format.decode result : ℝ)) (-(x : ℝ)) 0
      ((format.quantizer.scale * (1 + format.clippingError x) : ℚ) : ℝ) := by
  have h := convert_mixedError format rounding overflow x result hresult
  roundoff

example {format : Format} (value : format.Code) :
    (bitsfx value : ℚ) = Format.decode value * (2 : ℚ) ^ format.fractionalBits :=
  bitsfx_eq_scaled value

-- Annex G item 2: rounding precedes overflow; the result depends on the chosen rounder.
example : (convert signed even .DEFAULT (29 / 32)).map bitsfx = some 7 := by decide +kernel
example : (convert signed Rounding.floor .DEFAULT (29 / 32)).map bitsfx = some 7 := by
  decide +kernel
example : convert signed Rounding.ceil .DEFAULT (29 / 32) = none := by decide +kernel
example : (convert signed even .DEFAULT (-33 / 32)).map bitsfx = some (-8) := by
  decide +kernel
example : convert signed Rounding.floor .DEFAULT (-33 / 32) = none := by decide +kernel
example : convert signed even .DEFAULT (15 / 16) = none := by decide +kernel
example : (convert signed even .SAT (15 / 16)).map bitsfx = some 7 := by decide +kernel
example : (convert (_Sat signed) even .DEFAULT (15 / 16)).map bitsfx = some 7 := by
  decide +kernel
example : (convert signed even .SAT (-17 / 16)).map bitsfx = some (-8) := by decide +kernel

example : (convert signed Rounding.floor .DEFAULT (-1 / 16)).map bitsfx = some (-1) := by
  decide +kernel
example : (convert signed Rounding.ceil .DEFAULT (-1 / 16)).map bitsfx = some 0 := by
  decide +kernel
example : (convert signed even .DEFAULT (-1 / 16)).map bitsfx = some 0 := by decide +kernel

example : bitsfx (absfx (word 8)) = 7 := by decide +kernel
example : (roundfx NearestRounding.even (word 7) 1).map bitsfx = some 7 := by decide +kernel
example : (roundfx NearestRounding.even (word 5) 1).map bitsfx = some 4 := by decide +kernel
example : (roundfx NearestRounding.even (word 2) 1).map bitsfx = some 0 := by decide +kernel
example : (roundfx NearestRounding.even (word 6) 1).map bitsfx = some 7 := by decide +kernel
example : roundfx NearestRounding.even (word 2) (-1) = none := by decide +kernel
example : roundfx NearestRounding.even (word 2) 3 = none := by decide +kernel

example : countlsfx (word 0) = 3 := by decide +kernel
example : countlsfx (word 8) = 0 := by decide +kernel
example : countlsfx (word 12) = 1 := by decide +kernel
example : countlsfx (word 1) = 2 := by decide +kernel
example : countlsfx (word 15) = 3 := by decide +kernel
example : (shift false Rounding.floor .DEFAULT (word 15) 1).map bitsfx = some (-1) := by
  decide +kernel
example : (shift false Rounding.ceil .DEFAULT (word 15) 1).map bitsfx = some 0 := by
  decide +kernel
example : shift true even .SAT (word 1) 4 = none := by decide +kernel
example : shift true even .SAT (word 1) (-1) = none := by decide +kernel
example : (Prefix.«--» even .SAT (word 1)).map bitsfx = some (-7) := by decide +kernel
example : (Postfix.«++» even .SAT (word 1)).map
    (fun result ↦ (bitsfx result.1, bitsfx result.2)) = some (1, 7) := by decide +kernel
example : (Assignment.«<<=» even .SAT (word 1) 2).map bitsfx = some 4 := by decide +kernel
example : (Assignment.«>>=» even .SAT (word 12) 1).map bitsfx = some (-2) := by decide +kernel
example : (IntegerLeft.«/» even .SAT 1 (word 4)).map bitsfx = some 7 := by decide +kernel
example : (IntegerRight.«/» even .SAT (word 4) 2).map bitsfx = some 2 := by decide +kernel

example : toInteger (.signed 8) (-7 / 2) = some (-3) := by decide +kernel
example : toInteger (.unsigned 8) (-7 / 2) = none := by decide +kernel
example : fxdivi signed even 1 0 = none := by decide +kernel
example : (fxdivi signed even 9 1).map bitsfx = some 7 := by decide +kernel
example : Arithmetic.div.apply signed even .SAT 1 0 = none := by decide +kernel
example : (_Accum true 8 7).width = 16 := by decide +kernel

-- Small extensions make all type-conversion branches cheap to check in the kernel.
private def layout : Layout :=
  ⟨fun s _ _ ↦ if s then 2 else 3, fun _ _ ↦ 2⟩
private def environment : Environment :=
  ⟨fun _ ↦ even, .DEFAULT, .DEFAULT, .exact .OFF⟩
private def unsignedType : CType := ⟨.fract, .short, false, false⟩
private def accumType : CType := ⟨.accum, .long, true, false⟩
private def unsignedValue : (layout.format unsignedType).Code :=
  (layout.format unsignedType).ofBits (BitVec.ofNat _ 7)
private def accumZero : (layout.format accumType).Code :=
  (layout.format accumType).ofBits (BitVec.ofNat _ 0)

-- Widening the result cannot rescue undefined preliminary unsigned-to-signed conversion.
example : Binary.«+» layout environment unsignedType accumType unsignedValue accumZero = none := by
  decide +kernel

example : Compare.«>» unsignedValue accumZero = true := by decide +kernel
example : unsignedType.common accumType = ⟨.accum, .long, true, false⟩ := by decide +kernel
example : (unsignedType.common accumType).rank = max unsignedType.rank accumType.rank :=
  CType.common_rank _ _

-- Named stdfix variants specialize the same arbitrary-layout definitions.
example : bitshr layout ((layout.format ⟨.fract, .short, true, false⟩).ofBits 7) = -1 := by
  decide +kernel
example : (rdivi layout even 1 2).map bitsfx = some 2 := by decide +kernel
example : (rdivi layout even 2 1).map bitsfx = some 3 := by decide +kernel
example : (Assignment.«+=» layout environment unsignedType unsignedType unsignedValue
    ((layout.format unsignedType).ofBits 0)).map bitsfx = some 7 := by decide +kernel

example (layout : Layout) (environment : Environment) (operation : Arithmetic)
    (left right : CType) (x : (layout.format left).Code) (y : (layout.format right).Code)
    (result : (layout.format (left.common right)).Code)
    (h : layout.evaluate environment operation left right x y = some result) :
    ∃ x' y', layout.preconvert environment left right x = some x' ∧
      layout.preconvert environment right left y = some y' ∧
      operation.Allowed environment.arithmetic.FX_FULL_PRECISION
        (layout.format (left.common right)) (environment.rounding (left.common right))
        (environment.overflow (left.common right)) x' y' result := by
  obtain ⟨x', y', hx, hy, hr⟩ :=
    (layout.evaluate_eq_some_iff environment operation left right x y result).mp h
  exact ⟨x', y', hx, hy, operation.applyWith_allowed _ _ _ _ _ _ _ hr⟩

example (operation : Arithmetic) (precision : Precision) (format : Format)
    (rounding : Rounding) (overflow : Overflow) (x y : ℚ) :
    operation.applyWith (.exact precision) format rounding overflow x y =
      operation.apply format rounding overflow x y :=
  operation.applyWith_exact precision format rounding overflow x y

example (format : Format) (positive : Bool) :
    if positive then
      bitsfx (format.unitProduct positive) < (2 : Int) ^ format.fractionalBits ∧
        ∀ value : format.Code, bitsfx value < (2 : Int) ^ format.fractionalBits →
          bitsfx value ≤ bitsfx (format.unitProduct positive)
    else
      -(2 : Int) ^ format.fractionalBits < bitsfx (format.unitProduct positive) ∧
        ∀ value : format.Code, -(2 : Int) ^ format.fractionalBits < bitsfx value →
          bitsfx (format.unitProduct positive) ≤ bitsfx value :=
  format.unitProduct_closest positive

example : (Arithmetic.mul.applyWith (.neighbor false) signed even .SAT (1/2) (1/2)).map
    bitsfx = some 1 := by decide +kernel
example : (Arithmetic.mul.applyWith (.neighbor true) signed even .SAT (1/2) (1/2)).map
    bitsfx = some 3 := by decide +kernel
example : (Arithmetic.add.applyWith (.neighbor true) signed even .SAT (1/4) (1/4)).map
    bitsfx = some 4 := by decide +kernel
example : Arithmetic.div.applyWith (.neighbor true) signed even .SAT 1 0 = none := by
  decide +kernel
example : Arithmetic.mul.applyWith (.exact .ON) signed even .DEFAULT (-1) (-1) = none := by
  decide +kernel
example : (Arithmetic.mul.applyWith ((ArithmeticPolicy.exact .ON).withUnitProducts)
    signed even .DEFAULT
    (-1) (-1)).map bitsfx = some 7 := by decide +kernel
example : (Arithmetic.mul.applyWith ((ArithmeticPolicy.exact .ON).withUnitProducts)
    (_Accum true 2 3)
    even .DEFAULT 1 1).map bitsfx = some 7 := by decide +kernel
example : (Arithmetic.mul.applyWith ((ArithmeticPolicy.neighbor false).withUnitProducts)
    (_Accum true 2 3)
    even .DEFAULT (-1) 1).map bitsfx = some (-7) := by decide +kernel

example (operation : Arithmetic) (policy : ArithmeticPolicy) (format : Format)
    (rounding : Rounding) (overflow : Overflow) (x y exact : ℚ) (result : format.Code)
    (hexact : operation.exact x y = some exact)
    (hresult : operation.applyWith policy format rounding overflow x y = some result) :
    MixedError (-(Format.decode result : ℝ)) (-(exact : ℝ)) 0
      ((format.quantizer.scale * (2 + format.clippingError exact) : ℚ) : ℝ) := by
  have h := operation.applyWith_mixedError policy format rounding overflow
    x y exact result hexact hresult
  roundoff

example (operation : Arithmetic) (policy : ArithmeticPolicy) (integerFormat : IntegerFormat)
    (format : Format) (rounding : Rounding) (overflow : Overflow) (integer : Int)
    (value : format.Code) (result : Int) :
    operation.assignInteger policy integerFormat rounding overflow integer value = some result ↔
      ∃ intermediate : format.Code,
        operation.applyWith policy format rounding overflow integer (Format.decode value) =
          some intermediate ∧ toInteger integerFormat (Format.decode intermediate) = some result :=
  operation.assignInteger_eq_some_iff policy integerFormat rounding overflow integer value result

-- The fixed intermediate is .875, so assignment to int produces zero, not one.
example : Assignment.IntegerLeft.«+=» (.signed 8) even .SAT 1 (word 0) = some 0 := by
  decide +kernel
example : Assignment.IntegerLeft.«+=» (.signed 8) even .DEFAULT 1 (word 0) = none := by
  decide +kernel
example : Assignment.IntegerLeft.«/=» (.signed 8) even .SAT 1 (word 0) = none := by
  decide +kernel
example : (Assignment.IntegerRight.«*=» even .SAT (word 4) 1).map bitsfx = some 4 := by
  decide +kernel
example : IntegerLeft.«>» 1 (word 7) = true := by decide +kernel
example : IntegerRight.«<» (word 15) 0 = true := by decide +kernel

example (format : Format) (value : format.Code) :
    Format.decode format.minimum ≤ Format.decode value ∧
      Format.decode value ≤ Format.decode format.maximum :=
  ⟨format.minimum_le value, format.le_maximum value⟩

example (format : Format) (h : 0 < format.precision) (value : format.Code)
    (positive : 0 < Format.decode value) :
    Format.decode (format.epsilon h) ≤ Format.decode value :=
  (format.epsilon_le h).2 value positive

example (format : Format) (extra : Nat) (value : format.Code) :
    (format.bitsInteger extra).InRange (bitsfx value) :=
  format.bitsInteger_inRange extra value

example :
    [SFRACT_FBIT, FRACT_FBIT, LFRACT_FBIT, USFRACT_FBIT, UFRACT_FBIT, ULFRACT_FBIT,
      SACCUM_FBIT, ACCUM_FBIT, LACCUM_FBIT, USACCUM_FBIT, UACCUM_FBIT, ULACCUM_FBIT].map
        (fun query ↦ query Layout.example) = [7, 15, 31, 8, 16, 32, 7, 15, 31, 8, 16, 32] := by
  decide +kernel
example :
    [SACCUM_IBIT, ACCUM_IBIT, LACCUM_IBIT, USACCUM_IBIT, UACCUM_IBIT, ULACCUM_IBIT].map
        (fun query ↦ query Layout.example) = [8, 8, 8, 8, 8, 8] := by
  decide +kernel
example : Format.decode (SFRACT_EPSILON Layout.example Layout.example_valid) = 1 / 128 := by
  decide +kernel
example : Format.decode (SFRACT_MIN Layout.example) = -1 := by decide +kernel
example : Format.decode (SFRACT_MAX Layout.example) = 127 / 128 := by decide +kernel
example : Format.decode (USACCUM_MAX Layout.example) = 65535 / 256 := by decide +kernel
example : int_hr_t Layout.example 0 = .signed 8 := by decide +kernel
example : uint_uhr_t Layout.example 7 = .unsigned 15 := by decide +kernel

end FloatLibTests.Conformance.Formats.EmbeddedFixedPoint
