/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Cast.Integer.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Proof
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof
public import FloatLib.Numerics.Representations.FixedInt.Semantics.Basic

/-!
# Exact semantics of posit integer conversions

The integer sentinel has only its most significant bit set. Finite posit values first undergo
exact nearest-even integer rounding; the signed range is checked on that rounded integer.
Within range, decoding the output recovers the rounded integer, with error at most one half.
At an exact halfway numerator/denominator remainder, that integer is even.

The sentinel characterization includes an in-range result equal to the signed minimum,
whose encoding coincides with the overflow and NaR sentinel.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

open FloatLib.Numerics
open FloatLib.Numerics.Representations

variable {format : Format} {width : Nat}

/-- The integer conversion sentinel has precisely its most significant bit set. -/
theorem integerSentinel_toNatBits (hwidth : 0 < width) :
    (FixedInt.minCode width).toNatBits = 2 ^ (width - 1) :=
  BitVec.toNat_intMin_of_pos hwidth

/-- The reserved integer word converts to NaR, independently of the posit format. -/
@[simp] theorem ofFixedInt_minCode (format : Format) (hwidth : 0 < width) :
    ofFixedInt format (FixedInt.minCode width) hwidth = nar format := by
  simp [ofFixedInt]

/-- Every non-sentinel integer undergoes one rounding of its exact signed value. -/
theorem ofFixedInt_eq_roundRat (value : FixedInt width) (hwidth : 0 < width)
    (hvalue : value ≠ FixedInt.minCode width) :
    ofFixedInt format value hwidth = roundRat format (value.toInt : Rat) := by
  simp [ofFixedInt, hvalue]

/-- NaR converts to the reserved integer word at every positive width. -/
@[simp] theorem toFixedInt_nar (format : Format) (hwidth : 0 < width) :
    toFixedInt width (nar format) hwidth = FixedInt.minCode width := by
  simp [toFixedInt]

/-- A finite posit whose rounded integer fits is encoded without wraparound. -/
theorem toFixedInt_eq_of_inRange (value : Model format) (hwidth : 0 < width) {q : Rat}
    (hvalue : value.toRat? = some q) (hrange : FixedInt.InRange width (roundRatEven q)) :
    toFixedInt width value hwidth = FixedInt.ofInt (roundRatEven q) := by
  simp [toFixedInt, hvalue, hrange]

/-- A finite posit whose rounded integer is out of range produces the sentinel. -/
theorem toFixedInt_eq_minCode_of_not_inRange (value : Model format) (hwidth : 0 < width)
    {q : Rat} (hvalue : value.toRat? = some q)
    (hrange : ¬ FixedInt.InRange width (roundRatEven q)) :
    toFixedInt width value hwidth = FixedInt.minCode width := by
  simp [toFixedInt, hvalue, hrange]

/-- Decoding an in-range conversion gives the exact nearest-even integer. -/
theorem toInt_toFixedInt_of_inRange (value : Model format) (hwidth : 0 < width) {q : Rat}
    (hvalue : value.toRat? = some q) (hrange : FixedInt.InRange width (roundRatEven q)) :
    (toFixedInt width value hwidth).toInt = roundRatEven q := by
  rw [toFixedInt_eq_of_inRange value hwidth hvalue hrange]
  exact FixedInt.toInt_ofInt_eq_self hwidth hrange

/--
For a finite posit, sentinel output means either overflow after rounding or a rounded result
equal to the signed minimum. The latter is an in-range integer with the same reserved bits.
-/
theorem toFixedInt_eq_minCode_iff (value : Model format) (hwidth : 0 < width) {q : Rat}
    (hvalue : value.toRat? = some q) :
    toFixedInt width value hwidth = FixedInt.minCode width ↔
      ¬ FixedInt.InRange width (roundRatEven q) ∨
        roundRatEven q = FixedInt.minValue width := by
  by_cases hrange : FixedInt.InRange width (roundRatEven q)
  · rw [toFixedInt_eq_of_inRange value hwidth hvalue hrange]
    simp only [hrange, not_true_eq_false, false_or]
    constructor
    · intro h
      have := congrArg FixedInt.toInt h
      simpa only [FixedInt.toInt_ofInt_eq_self hwidth hrange, FixedInt.toInt_minCode] using this
    · intro h
      rw [h]
      exact FixedInt.ofInt_toInt (FixedInt.minCode width)
  · simp [toFixedInt_eq_minCode_of_not_inRange value hwidth hvalue hrange, hrange]

/-- A finite conversion without rounded overflow has absolute error at most one half. -/
theorem toFixedInt_error_le_half (value : Model format) (hwidth : 0 < width) {q : Rat}
    (hvalue : value.toRat? = some q) (hrange : FixedInt.InRange width (roundRatEven q)) :
    |((toFixedInt width value hwidth).toInt : Rat) - q| ≤ (1 : Rat) / 2 := by
  rw [toInt_toFixedInt_of_inRange value hwidth hvalue hrange]
  exact roundRatEven_error_le_half q

/--
At an exact half-integer, the converted integer is even, provided it is in range.
The remainder condition expresses a fractional magnitude of exactly one half, for either sign.
-/
theorem toFixedInt_even_of_half (value : Model format) (hwidth : 0 < width) {q : Rat}
    (hvalue : value.toRat? = some q) (hrange : FixedInt.InRange width (roundRatEven q))
    (hhalf : 2 * (q.num.natAbs % q.den) = q.den) :
    (toFixedInt width value hwidth).toInt % 2 = 0 := by
  rw [toInt_toFixedInt_of_inRange value hwidth hvalue hrange]
  exact roundRatEven_even_of_quotient_tie q hhalf

/-- A finite posit that denotes an in-range integer converts to that integer exactly. -/
theorem toFixedInt_eq_of_int (value : Model format) (hwidth : 0 < width) {integer : Int}
    (hvalue : value.toRat? = some (integer : Rat)) (hrange : FixedInt.InRange width integer) :
    toFixedInt width value hwidth = FixedInt.ofInt integer := by
  simpa only [roundRatEven_intCast] using
    toFixedInt_eq_of_inRange value hwidth hvalue (by simpa only [roundRatEven_intCast])

/--
An integer round trip is exact when its Section 4.1 posit rounding still denotes that integer
and its input word is not the sentinel. Representability is essential here.
-/
theorem toFixedInt_ofFixedInt (value : FixedInt width) (hwidth : 0 < width)
    (hvalue : value ≠ FixedInt.minCode width)
    (hexact : (roundRat format (value.toInt : Rat)).toRat? = some (value.toInt : Rat)) :
    toFixedInt width (ofFixedInt format value hwidth) hwidth = value := by
  have hrange : FixedInt.InRange width value.toInt := by
    constructor
    · rw [FixedInt.minValue_eq hwidth]
      exact BitVec.le_toInt value.bits
    · rw [FixedInt.maxValue_eq]
      exact BitVec.toInt_le
  rw [ofFixedInt_eq_roundRat value hwidth hvalue,
    toFixedInt_eq_of_int _ hwidth hexact hrange, FixedInt.ofInt_toInt]

end FloatLib.Floats.Formats.Posit.Model
