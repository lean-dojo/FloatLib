/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.NativeCarrier

/-!
# Native binary16 and bfloat16

`Half` and `BFloat16` specialize the common native carrier to their IEEE-style layouts.
Their widening laws are checked for every 16-bit word.
-/

@[expose] public section

namespace FloatLib.Floats.Native

/-- Binary16's layout, quiet NaN and binary32 widening. -/
def halfFormat : Format where
  exponent := 5
  fraction := 10
  nan := 0x7E00
  exponent_ge_two := by decide
  exponent_le_eight := by decide
  fraction_pos := by decide
  precision_le := by decide
  width_eq := by decide
  nan_isNaN := by decide
  widen := Word.widenHalfWord
  widen_eq := Word.widenHalfWord_eq_cast

/-- Bfloat16's layout, quiet NaN and widening by placing its word in binary32's high half. -/
def bfloat16Format : Format where
  exponent := 8
  fraction := 7
  nan := 0x7FC0
  exponent_ge_two := by decide
  exponent_le_eight := by decide
  fraction_pos := by decide
  precision_le := by decide
  width_eq := by decide
  nan_isNaN := by decide
  widen := fun bits => bits.toUInt32 <<< 16
  widen_eq := Word.shiftLeft_eq_cast

native_carrier Half := halfFormat
native_carrier BFloat16 := bfloat16Format

end FloatLib.Floats.Native
