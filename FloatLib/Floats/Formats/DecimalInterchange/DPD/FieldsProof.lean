/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.DPD.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Codec.BitsProof
public import Mathlib.Tactic.SplitIfs

/-!
# The DPD combination field and exponent continuation

The DPD combination field packs a leading digit below 10 and a high exponent below 3, and its
accessors recover both. Bounded exponent continuation and trailing fields pack below the
combinations reserved for infinity and NaN.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.DPD

theorem combination_lt (leading high : Nat) (hl : leading < 10) (hh : high < 3) :
    combination leading high < 30 := by
  unfold combination
  split_ifs <;> omega

theorem leadingDigit_lt (field : Nat) : leadingDigit field < 10 := by
  unfold leadingDigit
  split_ifs <;> omega

theorem highExponent_lt (field : Nat) (h : field < 30) : highExponent field < 3 := by
  unfold highExponent
  split_ifs <;> omega

@[simp] theorem leadingDigit_combination (leading high : Nat)
    (hl : leading < 10) (hh : high < 3) :
    leadingDigit (combination leading high) = leading := by
  unfold leadingDigit combination
  split_ifs <;> omega

@[simp] theorem highExponent_combination (leading high : Nat)
    (hl : leading < 10) (hh : high < 3) :
    highExponent (combination leading high) = high := by
  unfold highExponent combination
  split_ifs <;> omega

/-- Assembling the DPD fields never collides with an infinity or NaN combination. -/
theorem encodeFields_lt (f : Format) (leading e trailing : Nat)
    (hl : leading < 10) (he : e < f.exponentBound) (ht : trailing < f.trailingBase) :
    encodeFields f leading e trailing < 30 * (f.exponentBase * f.trailingBase) := by
  have hh : e / f.exponentBase < 3 := by
    exact (Nat.div_lt_iff_lt_mul f.exponentBase_pos).mpr he
  have hc := combination_lt leading _ hl hh
  have ht' := Bits.mul_add_lt_mul (Nat.mod_lt e f.exponentBase_pos) ht
  simpa only [encodeFields, Nat.add_assoc] using Bits.mul_add_lt_mul hc ht'

/-- The three stored fields can be recovered independently. -/
theorem encodeFields_extract (f : Format) (leading e trailing : Nat)
    (ht : trailing < f.trailingBase) :
    let n := encodeFields f leading e trailing
    n / (f.exponentBase * f.trailingBase) = combination leading (e / f.exponentBase) ∧
      n / f.trailingBase % f.exponentBase = e % f.exponentBase ∧
      n % f.trailingBase = trailing := by
  have hn : encodeFields f leading e trailing =
      (combination leading (e / f.exponentBase) * f.exponentBase + e % f.exponentBase) *
        f.trailingBase + trailing := by
    simp only [encodeFields, Nat.add_mul, Nat.mul_assoc]
  have hdiv : encodeFields f leading e trailing / f.trailingBase =
      combination leading (e / f.exponentBase) * f.exponentBase + e % f.exponentBase := by
    rw [hn, Nat.add_comm, Nat.add_mul_div_right _ _ f.trailingBase_pos,
      Nat.div_eq_of_lt ht, Nat.zero_add]
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.mul_comm f.exponentBase f.trailingBase, ← Nat.div_div_eq_div_mul, hdiv,
      Nat.add_comm, Nat.add_mul_div_right _ _ f.exponentBase_pos,
      Nat.div_eq_of_lt (Nat.mod_lt e f.exponentBase_pos), Nat.zero_add]
  · rw [hdiv, Nat.mul_add_mod_self_right, Nat.mod_mod]
  · rw [hn, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt ht]

end FloatLib.Floats.Formats.DecimalInterchange.DPD
