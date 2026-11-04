/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Quantization.Integer.Runtime
public import FloatLib.Numerics.Representations.FixedInt.Semantics.Basic

/-!
# Checked integer quantization

Acceptance is equivalent to the rounded integer being representable, which is a different condition
from the rational input being representable. In a signed 8-bit range with nearest rounding, 127.4 is
accepted because it rounds to 127, and 127.6 is rejected because it rounds to 128. This
characterization covers arbitrary inclusive intervals and both signed and unsigned words.
-/

@[expose] public section

namespace FloatLib.Numerics

open Representations

/-- Acceptance preserves the chosen rounded integer and certifies its range.
The rational input itself need not lie in the destination interval. -/
theorem IntegerRange.round?_eq_some_iff (range : IntegerRange) (round : ℚ → Int)
    (value : ℚ) (integer : Int) :
    range.round? round value = some integer ↔
      round value = integer ∧ range.Contains integer := by
  by_cases h : range.Contains (round value) <;> simp [IntegerRange.round?, h]
  all_goals
    rintro rfl
    exact h

/-- Rejection depends only on the rounded integer lying outside the inclusive range.
An empty range therefore rejects every input, independently of the rounding rule. -/
theorem IntegerRange.round?_eq_none_iff (range : IntegerRange) (round : ℚ → Int)
    (value : ℚ) :
    range.round? round value = none ↔ ¬ range.Contains (round value) := by
  simp [IntegerRange.round?]

/-- An unsigned word's natural-number interpretation lies in its numerical range. -/
theorem IntegerFormat.toNat_inRange {width : Nat} (word : BitVec width) :
    (unsigned width).InRange (word.toNat : Int) := by
  have hb : (word.toNat : Int) < (2 : Int) ^ width := by
    exact_mod_cast word.isLt
  change 0 ≤ (word.toNat : Int) ∧ (word.toNat : Int) ≤ (2 : Int) ^ width - 1
  omega

/-- Checked unsigned packing is exact, including width zero. -/
theorem IntegerFormat.toNat_ofNat_of_inRange {width : Nat} {value : Int}
    (hr : (unsigned width).InRange value) :
    ((BitVec.ofNat width value.toNat).toNat : Int) = value := by
  change 0 ≤ value ∧ value ≤ (2 : Int) ^ width - 1 at hr
  have hn : (value.toNat : Int) = value := Int.toNat_of_nonneg hr.1
  have hb : value.toNat < 2 ^ width := by
    have h : (value.toNat : Int) < (2 : Int) ^ width := by omega
    exact_mod_cast h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, hn]

/-- One additional signed bit contains the whole unsigned numerical range. -/
theorem IntegerFormat.signed_succ_inRange_of_unsigned {width : Nat} {value : Int}
    (hr : (unsigned width).InRange value) : (signed (width + 1)).InRange value := by
  change 0 ≤ value ∧ value ≤ (2 : Int) ^ width - 1 at hr
  simp only [InRange, range, IntegerRange.Contains, minValue, maxValue,
    FixedInt.minValue_eq (Nat.succ_pos width), FixedInt.maxValue_eq, Nat.succ_sub_one]
  have hp : (0 : Int) < 2 ^ width := Int.pow_pos (by decide)
  omega

/--
Zero is representable in every signed or unsigned word format, including width zero: it is the
value of the zero word, and a signed format holds the unsigned range of one bit fewer.
-/
theorem IntegerFormat.zero_inRange (destination : IntegerFormat) : destination.InRange 0 := by
  cases destination with
  | signed width =>
      cases width with
      | zero => decide
      | succ n => exact signed_succ_inRange_of_unsigned (by simpa using toNat_inRange 0#n)
  | unsigned width => simpa using toNat_inRange 0#width

end FloatLib.Numerics
