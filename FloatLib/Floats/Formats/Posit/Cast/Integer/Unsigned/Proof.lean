/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.Posit.Cast.Integer.Unsigned.Runtime
public import FloatLib.Floats.Formats.Posit.Cast.Integer.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.RoundTrip
public import FloatLib.Numerics.Quantization.Integer.Proof

/-!
# Unsigned posit integer conversion guarantees

Accepted outputs denote the nearest-even integer exactly and have at most
one-half unit of error. The range test applies to this rounded integer,
including small negative inputs that round to zero.

The sentinel characterization includes the in-range integer `2^(width-1)`;
its unsigned encoding is indistinguishable from the NaR or out-of-range result.
Input conversion reserves that word before numerical rounding. Representable
non-sentinel integers have exact round trips.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

open FloatLib.Numerics FloatLib.Numerics.Representations

variable {format : Format} {width : Nat}

/-- The reserved unsigned word has just its most significant bit set. -/
theorem unsignedSentinel_toNat (hwidth : 0 < width) :
    (BitVec.intMin width).toNat = 2 ^ (width - 1) :=
  BitVec.toNat_intMin_of_pos hwidth

@[simp] theorem ofUnsigned_intMin (format : Format) (hwidth : 0 < width) :
    ofUnsigned format (BitVec.intMin width) hwidth = nar format := by
  simp [ofUnsigned]

/-- Non-sentinel unsigned inputs use their natural-number value, even when their MSB is set. -/
theorem ofUnsigned_eq_roundRat (value : BitVec width) (hwidth : 0 < width)
    (hvalue : value ≠ BitVec.intMin width) :
    ofUnsigned format value hwidth = roundRat format (value.toNat : Rat) := by
  simp [ofUnsigned, hvalue]

/-- If a finite posit denotes the unsigned integer exactly, conversion recovers that posit. -/
theorem ofUnsigned_eq_of_toRat? (value : BitVec width) (hwidth : 0 < width)
    (hvalue : value ≠ BitVec.intMin width) (result : Model format)
    (hexact : result.toRat? = some (value.toNat : Rat)) :
    ofUnsigned format value hwidth = result := by
  rw [ofUnsigned_eq_roundRat value hwidth hvalue]
  exact roundRat_toRat? result _ hexact

@[simp] theorem toUnsigned_nar (format : Format) (hwidth : 0 < width) :
    toUnsigned width (nar format) hwidth = BitVec.intMin width := by
  simp [toUnsigned]

theorem toUnsigned_eq_intMin_of_none (value : Model format) (hwidth : 0 < width)
    (hvalue : value.toRat? = none) :
    toUnsigned width value hwidth = BitVec.intMin width := by
  simp [toUnsigned, hvalue]

/-- A rounded integer in the full unsigned range is packed without wraparound. -/
theorem toUnsigned_eq_of_inRange (value : Model format) (hwidth : 0 < width) {q : Rat}
    (hvalue : value.toRat? = some q)
    (hrange : (IntegerFormat.unsigned width).InRange (roundRatEven q)) :
    toUnsigned width value hwidth = BitVec.ofNat width (roundRatEven q).toNat := by
  simp [toUnsigned, hvalue, IntegerRange.round?, hrange]

theorem toUnsigned_eq_intMin_of_not_inRange (value : Model format) (hwidth : 0 < width)
    {q : Rat} (hvalue : value.toRat? = some q)
    (hrange : ¬ (IntegerFormat.unsigned width).InRange (roundRatEven q)) :
    toUnsigned width value hwidth = BitVec.intMin width := by
  simp [toUnsigned, hvalue, IntegerRange.round?, hrange]

/-- The output's unsigned numerical interpretation equals the rounded integer. -/
theorem toNat_toUnsigned_of_inRange (value : Model format) (hwidth : 0 < width) {q : Rat}
    (hvalue : value.toRat? = some q)
    (hrange : (IntegerFormat.unsigned width).InRange (roundRatEven q)) :
    ((toUnsigned width value hwidth).toNat : Int) = roundRatEven q := by
  rw [toUnsigned_eq_of_inRange value hwidth hvalue hrange]
  exact IntegerFormat.toNat_ofNat_of_inRange hrange

/-- Sentinel output also occurs for the valid unsigned integer sharing those bits. -/
theorem toUnsigned_eq_intMin_iff (value : Model format) (hwidth : 0 < width) {q : Rat}
    (hvalue : value.toRat? = some q) :
    toUnsigned width value hwidth = BitVec.intMin width ↔
      ¬ (IntegerFormat.unsigned width).InRange (roundRatEven q) ∨
        roundRatEven q = (2 : Int) ^ (width - 1) := by
  by_cases hrange : (IntegerFormat.unsigned width).InRange (roundRatEven q)
  · simp only [hrange, not_true_eq_false, false_or]
    constructor
    · intro h
      have he := congrArg (fun word : BitVec width => (word.toNat : Int)) h
      simpa only [toNat_toUnsigned_of_inRange value hwidth hvalue hrange,
        unsignedSentinel_toNat hwidth, Nat.cast_pow, Nat.cast_ofNat] using he
    · intro h
      apply BitVec.eq_of_toNat_eq
      apply Int.ofNat_inj.mp
      rw [toNat_toUnsigned_of_inRange value hwidth hvalue hrange, h,
        unsignedSentinel_toNat hwidth, Nat.cast_pow, Nat.cast_ofNat]
  · simp [toUnsigned_eq_intMin_of_not_inRange value hwidth hvalue hrange, hrange]

/-- A successful conversion has the nearest-integer error bound. -/
theorem toUnsigned_error_le_half (value : Model format) (hwidth : 0 < width) {q : Rat}
    (hvalue : value.toRat? = some q)
    (hrange : (IntegerFormat.unsigned width).InRange (roundRatEven q)) :
    |((toUnsigned width value hwidth).toNat : Rat) - q| ≤ (1 : Rat) / 2 := by
  have he := congrArg (fun z : Int => (z : Rat))
    (toNat_toUnsigned_of_inRange value hwidth hvalue hrange)
  simp only [Int.cast_natCast] at he
  rw [he]
  exact roundRatEven_error_le_half q

/-- Half-integer ties choose an even output, by the shared exact integer rounder. -/
theorem toUnsigned_even_of_half (value : Model format) (hwidth : 0 < width) {q : Rat}
    (hvalue : value.toRat? = some q)
    (hrange : (IntegerFormat.unsigned width).InRange (roundRatEven q))
    (hhalf : 2 * (q.num.natAbs % q.den) = q.den) :
    (toUnsigned width value hwidth).toNat % 2 = 0 := by
  have hu : ((toUnsigned width value hwidth).toNat : Int) % 2 = 0 := by
    rw [toNat_toUnsigned_of_inRange value hwidth hvalue hrange]
    exact roundRatEven_even_of_quotient_tie q hhalf
  exact_mod_cast hu

/-- An unsigned integer that is exactly represented by the posit is returned unchanged. -/
theorem toUnsigned_eq_of_nat (value : Model format) (hwidth : 0 < width) {integer : Nat}
    (hvalue : value.toRat? = some (integer : Rat)) (hrange : integer < 2 ^ width) :
    toUnsigned width value hwidth = BitVec.ofNat width integer := by
  have hr : (IntegerFormat.unsigned width).InRange (integer : Int) := by
    have hb : (integer : Int) < (2 : Int) ^ width := by exact_mod_cast hrange
    change 0 ≤ (integer : Int) ∧ (integer : Int) ≤ (2 : Int) ^ width - 1
    omega
  have he : roundRatEven (integer : Rat) = (integer : Int) :=
    roundRatEven_intCast (integer : Int)
  rw [toUnsigned_eq_of_inRange value hwidth hvalue (by rwa [he]), he, Int.toNat_natCast]

/-- Exact posit representability and a non-sentinel input suffice for an unsigned round trip. -/
theorem toUnsigned_ofUnsigned (value : BitVec width) (hwidth : 0 < width)
    (hvalue : value ≠ BitVec.intMin width)
    (hexact : (roundRat format (value.toNat : Rat)).toRat? = some (value.toNat : Rat)) :
    toUnsigned width (ofUnsigned format value hwidth) hwidth = value := by
  rw [ofUnsigned_eq_roundRat value hwidth hvalue,
    toUnsigned_eq_of_nat _ hwidth hexact value.isLt, BitVec.ofNat_toNat]
  simp

end FloatLib.Floats.Formats.Posit.Model
