/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.ErrorBound

/-!
# Error bounds through integer casts

An `int8_t` cast preserves the observed integer when its error enclosure fits the range.
-/

public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open FloatLib.Numerics

/-- C's `int8_t` cast keeps an integer whose mixed enclosure is below `2 ^ 7` in magnitude. -/
theorem mixedError_int8_toInt_ofInt {n : ℤ} {reference relative absolute : ℝ}
    (hn : MixedError (n : ℝ) reference relative absolute)
    (hrange : (1 + relative) * |reference| + absolute < 2 ^ 7) :
    MixedError (((Int8.ofInt n).toInt : ℤ) : ℝ) reference relative absolute := by
  have habs : |n| < 2 ^ 7 := by exact_mod_cast lt_of_le_of_lt hn.abs_le hrange
  rw [Int8.toInt_ofInt_of_le (by linarith [neg_abs_le n]) (by linarith [le_abs_self n])]
  exact hn

/-- C's `int8_t` cast keeps an integer within `error` of a reference when the reference's
magnitude plus `error` is below `2 ^ 7`. -/
theorem abs_int8_toInt_ofInt_sub_le {n : ℤ} {reference error : ℝ}
    (hn : |(n : ℝ) - reference| ≤ error) (hrange : |reference| + error < 2 ^ 7) :
    |(((Int8.ofInt n).toInt : ℤ) : ℝ) - reference| ≤ error := by
  have hle : |(n : ℝ)| ≤ |reference| + error := by
    simpa only [sub_zero] using Numerics.compose_error hn (le_refl |reference - 0|)
  have habs : |n| < 2 ^ 7 := by exact_mod_cast lt_of_le_of_lt hle hrange
  rw [Int8.toInt_ofInt_of_le (by linarith [neg_abs_le n]) (by linarith [le_abs_self n])]
  exact hn

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
