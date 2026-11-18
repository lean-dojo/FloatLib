/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Layout
import Mathlib.Algebra.Order.Ring.Int

/-!
# N1169 fixed-point limits and coefficient integer types

WG14 N1169 (2006 TR 18037 draft), C clauses 7.18a.2–3. Endpoint and epsilon values
are stored coefficients, not host approximations. A conforming layout supplies
the positive precision needed for epsilon. The integer typedef family permits
any extra width and proves that every associated coefficient fits.

These are value-level counterparts of the C macros and typedefs. C preprocessing,
integer type availability and object padding are outside the value model.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: the minimum stored fixed-point value. -/
def Format.minimum (format : Format) : format.Code :=
  ⟨format.quantizer.qmin, le_rfl, format.quantizer.code_range⟩

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: the maximum stored fixed-point value. -/
def Format.maximum (format : Format) : format.Code :=
  ⟨format.quantizer.qmax, format.quantizer.code_range, le_rfl⟩

/-- Fixed-point value order is exactly coefficient order at every binary scale. -/
theorem Format.decode_le_decode_iff {format : Format} (left right : format.Code) :
    Format.decode left ≤ Format.decode right ↔ bitsfx left ≤ bitsfx right := by
  rw [decode_eq, decode_eq, div_le_div_iff_of_pos_right (pow_pos (by decide) _)]
  constructor <;> intro h <;> exact_mod_cast h

/-- Every stored value lies above the declared minimum. -/
theorem Format.minimum_le (format : Format) (value : format.Code) :
    Format.decode format.minimum ≤ Format.decode value :=
  (Format.decode_le_decode_iff _ _).2 value.2.1

/-- Every stored value lies below the declared maximum. -/
theorem Format.le_maximum (format : Format) (value : format.Code) :
    Format.decode value ≤ Format.decode format.maximum :=
  (Format.decode_le_decode_iff _ _).2 value.2.2

/-- Coefficient one fits exactly when there is at least one value bit. -/
theorem Format.one_inRange (format : Format) (h : 0 < format.precision) :
    format.integerFormat.InRange 1 := by
  have hzero := IntegerFormat.zero_inRange format.integerFormat
  change format.integerFormat.minValue ≤ 0 ∧ 0 ≤ format.integerFormat.maxValue at hzero
  change format.integerFormat.minValue ≤ 1 ∧ 1 ≤ format.integerFormat.maxValue
  have hpow : (2 : Int) ≤ 2 ^ format.precision := by
    simpa using (pow_le_pow_right₀ (show (1 : Int) ≤ 2 by decide) h)
  rw [format.maxValue_eq]
  omega

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: the least positive stored value, at any
    positive precision. -/
def Format.epsilon (format : Format) (h : 0 < format.precision) : format.Code :=
  ⟨1, format.one_inRange h⟩

/-- Epsilon decodes to the exact binary grid spacing. -/
theorem Format.decode_epsilon (format : Format) (h : 0 < format.precision) :
    Format.decode (format.epsilon h) = format.quantizer.scale := by
  simp [Format.decode, Format.epsilon, Quantization.AffineQuantizer.dequantize,
    Format.quantizer]

/-- Epsilon is positive and no positive stored value is smaller. -/
theorem Format.epsilon_le (format : Format) (h : 0 < format.precision) :
    0 < Format.decode (format.epsilon h) ∧
      ∀ value : format.Code, 0 < Format.decode value →
        Format.decode (format.epsilon h) ≤ Format.decode value := by
  constructor
  · rw [format.decode_epsilon h]
    exact format.quantizer.scale_pos
  · intro value hvalue
    change 0 < format.quantizer.scale * ((bitsfx value - 0 : Int) : ℚ) at hvalue
    rw [Int.sub_zero] at hvalue
    have hcast := (mul_pos_iff_of_pos_left format.quantizer.scale_pos).mp hvalue
    have hc : 0 < bitsfx value := by exact_mod_cast hcast
    apply (Format.decode_le_decode_iff _ _).2
    exact Int.add_one_le_iff.mpr hc

/-- Every conforming layout has positive value precision in all its fixed-point types. -/
theorem Layout.precision_pos (layout : Layout) (h : layout.Valid) (type : CType) :
    0 < (layout.format type).precision := by
  have hmin := h.fractional_min type.signed type.kind type.length
  have hpos : 0 < type.length.minFractionalBits := by cases type.length <;> decide
  change 0 < _ + layout.fractionalBits type.signed type.kind type.length
  omega

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.2: associated integer range with any
    nonnegative extra value width. -/
def Format.bitsInteger (format : Format) (extra : Nat) : IntegerFormat :=
  { format with integralBits := format.integralBits + extra }.integerFormat

/-- Every associated integer width contains every coefficient of the original format. -/
theorem Format.bitsInteger_inRange (format : Format) (extra : Nat) (value : format.Code) :
    (format.bitsInteger extra).InRange (bitsfx value) := by
  let wider : Format := { format with integralBits := format.integralBits + extra }
  have hn : format.precision ≤ wider.precision := by dsimp [Format.precision, wider]; omega
  have hp : (2 : Int) ^ format.precision ≤ 2 ^ wider.precision :=
    pow_le_pow_right₀ (by decide) hn
  have hv := value.2
  change format.integerFormat.minValue ≤ bitsfx value ∧
    bitsfx value ≤ format.integerFormat.maxValue at hv
  change wider.integerFormat.minValue ≤ bitsfx value ∧
    bitsfx value ≤ wider.integerFormat.maxValue
  rw [format.minValue_eq, format.maxValue_eq] at hv
  rw [wider.minValue_eq, wider.maxValue_eq]
  change (if format.signed then -(2 : Int) ^ wider.precision else 0) ≤ bitsfx value ∧ _
  by_cases hs : format.signed <;> simp [hs] at hv ⊢ <;> omega

end FloatLib.Floats.Formats.FixedPoint.Embedded
