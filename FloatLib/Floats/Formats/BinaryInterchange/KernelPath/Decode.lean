/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Round
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Proof

/-!
# Fields of a natural-number encoding

The kernel operations read the sign, the biased exponent and the significand of an operand from
its natural-number encoding with shifts, masks and truncated subtraction. This module states what
those expressions compute for the encoding `x.toNatBits` of a `Model fmt` value, in terms of
`Model.signBit`, `Model.expField` and `Model.fracField`, for every format descriptor:

* the sign is `word >>> signPos fmt` and the exponent and fraction fields are
  `word &&& magnitudeMask fmt` (`sign_toNatBits`, `magnitude_toNatBits`);
* with `h = exponent field - 1` (truncated), the significand with its implicit bit is
  `magnitude - h * 2 ^ fracWidth`, and `h` is the exponent of that significand above the least
  subnormal (`toDyadic?_of_isFinite`);
* `nonFinite` is zero only for finite values (`isFinite_of_nonFinite_eq_zero`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/-- One when the negative-zero word is the format's NaN (the unsigned-zero encoding). -/
def negZeroNaN (fmt : FloatFormat) : Nat :=
  match fmt.encoding with
  | .finiteUnsignedZero => 1
  | .ieee | .finiteMaxNaN | .finite => 0

kernel_constant negZeroNaN

/--
Zero when a word with sign `sign` and exponent-and-fraction fields `magnitude` is finite: the
fields are at most `maxFinite`, and the word is not the negative zero of an unsigned-zero format.
-/
def nonFinite (fmt : FloatFormat) (sign magnitude : Nat) : Nat :=
  Nat.add (Nat.sub magnitude (maxFinite fmt)) (Nat.mul (negZeroNaN fmt) (Nat.sub sign magnitude))

kernel_constant nonFinite

/-- The encoding of a value is its sign bit above its exponent and fraction fields. -/
theorem toNatBits_eq_fields {fmt : FloatFormat} (x : Model fmt) :
    x.toNatBits =
      (if Model.signBit x then 2 ^ signPos fmt else 0) +
        (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) := by
  conv_lhs => rw [← Model.ofFields_signBit_expField_fracField x]
  exact toNatBits_ofFields fmt _ _ _ (Model.expField_lt_pow2 x) (Model.fracField_lt_pow2 x)

/-- The exponent and fraction fields together lie below the sign bit. -/
theorem fields_lt_two_pow_signPos {fmt : FloatFormat} (x : Model fmt) :
    Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x < 2 ^ signPos fmt := by
  have he := Model.expField_lt_pow2 x
  have hf := Model.fracField_lt_pow2 x
  unfold signPos
  rw [Nat.pow_add]
  calc Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x
      < Model.expField x * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by omega
    _ = (Model.expField x + 1) * 2 ^ fmt.fracWidth := by ring
    _ ≤ 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth := Nat.mul_le_mul_right _ he

/-- The sign of an encoding, as zero or one. -/
theorem sign_toNatBits {fmt : FloatFormat} (x : Model fmt) :
    x.toNatBits >>> signPos fmt = if Model.signBit x then 1 else 0 := by
  rw [toNatBits_eq_fields, Nat.shiftRight_eq_div_pow]
  have hlt := fields_lt_two_pow_signPos x
  have hpos : 0 < 2 ^ signPos fmt := Nat.two_pow_pos _
  cases Model.signBit x
  · simp [Nat.div_eq_of_lt hlt]
  · simp only [ite_true]
    rw [Nat.add_div_left _ hpos, Nat.div_eq_of_lt hlt]

/-- The exponent and fraction fields of an encoding. -/
theorem magnitude_toNatBits {fmt : FloatFormat} (x : Model fmt) :
    x.toNatBits &&& magnitudeMask fmt =
      Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x := by
  have hlt := fields_lt_two_pow_signPos x
  unfold magnitudeMask
  change _ &&& 2 ^ signPos fmt - 1 = _
  rw [Nat.and_two_pow_sub_one_eq_mod, toNatBits_eq_fields]
  cases Model.signBit x
  · simp [Nat.mod_eq_of_lt hlt]
  · simp only [ite_true]
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

/-- The exponent field of the packed fields. -/
theorem fields_shiftRight (exponent fraction width : Nat) (hfraction : fraction < 2 ^ width) :
    (exponent * 2 ^ width + fraction) >>> width = exponent := by
  rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hfraction, Nat.add_zero]

/--
The significand with its implicit bit: removing `exponent - 1` copies of `2 ^ width` from the
packed fields leaves the fraction of a subnormal and `2 ^ width + fraction` otherwise.
-/
theorem fields_sub_shiftLeft (exponent fraction width : Nat) :
    exponent * 2 ^ width + fraction - (exponent - 1) <<< width =
      if exponent = 0 then fraction else 2 ^ width + fraction := by
  rw [Nat.shiftLeft_eq]
  generalize 2 ^ width = F
  rcases exponent with _ | k
  · simp
  · have hexpand : (k + 1) * F = k * F + F := by ring
    simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]
    omega

/-- A word whose `nonFinite` flag is zero is finite. -/
theorem isFinite_of_nonFinite_eq_zero {fmt : FloatFormat} (x : Model fmt)
    (hflag : nonFinite fmt (if Model.signBit x then 1 else 0)
      (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) = 0) :
    Model.isFinite x = true := by
  have he := Model.expField_lt_pow2 x
  have hf := Model.fracField_lt_pow2 x
  have hiff := le_maxFinite_iff fmt (Model.expField x) (Model.fracField x) hf
  rw [← Model.ofFields_signBit_expField_fracField x,
    Model.isFinite_ofFields fmt _ _ _ he hf]
  unfold nonFinite at hflag
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq] at hflag
  obtain ⟨_, hnegZero⟩ := Nat.eq_zero_of_add_eq_zero hflag
  have hle : Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x ≤ maxFinite fmt := by
    omega
  have hfields := hiff.1 hle
  have hfour := fmt.four_le_two_pow_expWidth
  have htwo : 2 ≤ 2 ^ fmt.fracWidth := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ fmt.fracWidth := Nat.pow_le_pow_right (by decide) fmt.fracWidth_pos
  generalize Model.expField x = e at he hfields hnegZero ⊢
  generalize Model.fracField x = f at hf hfields hnegZero ⊢
  cases hencoding : fmt.encoding
  · have hMFE : fmt.maxFiniteExpField = 2 ^ fmt.expWidth - 2 := by
      simp [FloatFormat.maxFiniteExpField, FloatFormat.Encoding.maxFiniteExponent, hencoding]
    rw [hMFE] at hfields
    simp only [bne_iff_ne, ne_eq, FloatFormat.expAllOnesNat]
    omega
  · have hMFE : fmt.maxFiniteExpField = 2 ^ fmt.expWidth - 1 := by
      simp [FloatFormat.maxFiniteExpField, FloatFormat.Encoding.maxFiniteExponent, hencoding]
    have hMFF : fmt.maxFiniteFracField = 2 ^ fmt.fracWidth - 1 - 1 := by
      simp [FloatFormat.maxFiniteFracField, FloatFormat.fracMaskNat, hencoding]
    rw [hMFE, hMFF] at hfields
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      FloatFormat.expAllOnesNat, FloatFormat.fracMaskNat]
    omega
  · have hflagOne : negZeroNaN fmt = 1 := by simp [negZeroNaN, hencoding]
    rw [hflagOne, Nat.one_mul] at hnegZero
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    cases hsign : Model.signBit x
    · simp
    · simp only [hsign, ite_true] at hnegZero
      have hne : e * 2 ^ fmt.fracWidth + f ≠ 0 := by omega
      by_cases hexp : e = 0
      · right
        intro hfrac
        exact hne (by simp [hexp, hfrac])
      · exact Or.inl (Or.inr hexp)
  · rfl

/--
The exact value of a finite word, in the fields the kernel operations use: the sign bit, the
significand with its implicit bit, and for a nonzero significand the exponent
`(exponent field - 1) + minSubnormalExponent`.
-/
theorem toDyadic?_of_isFinite {fmt : FloatFormat} (x : Model fmt)
    (hfinite : Model.isFinite x = true) :
    ∃ d : Numerics.Dyadic, Model.toDyadic? x = some d ∧
      d.negative = Model.signBit x ∧
      d.significand =
        (if Model.expField x = 0 then Model.fracField x
          else 2 ^ fmt.fracWidth + Model.fracField x) ∧
      (d.significand ≠ 0 →
        d.exponent = ((Model.expField x - 1 : Nat) : Int) + fmt.minSubnormalExponent) := by
  have he := Model.expField_lt_pow2 x
  have hf := Model.fracField_lt_pow2 x
  have hdecode := Model.toDyadic?_ofFields_of_isFinite fmt (Model.signBit x)
    (Model.expField x) (Model.fracField x) he hf
    (by rw [Model.ofFields_signBit_expField_fracField]; exact hfinite)
  rw [Model.ofFields_signBit_expField_fracField] at hdecode
  by_cases hexp : Model.expField x = 0
  · by_cases hfrac : Model.fracField x = 0
    · refine ⟨_, by rw [hdecode, ite_eq_left hexp, ite_eq_left hfrac], rfl, ?_, ?_⟩
      · simp [hexp, hfrac]
      · intro h; exact absurd rfl h
    · refine ⟨_, by rw [hdecode, ite_eq_left hexp, ite_eq_right hfrac], rfl, ?_, ?_⟩
      · simp [hexp]
      · intro _
        simp [hexp]
  · refine ⟨_, by rw [hdecode, ite_eq_right hexp], rfl, ?_, ?_⟩
    · simp [hexp, Model.pow2_eq_two_pow]
    · intro _
      simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast]
      omega

/-- The significand of a decoded word is below `2 ^ (fracWidth + 1)`. -/
theorem decoded_significand_lt {fmt : FloatFormat} (x : Model fmt) :
    (if Model.expField x = 0 then Model.fracField x
      else 2 ^ fmt.fracWidth + Model.fracField x) < 2 ^ (fmt.fracWidth + 1) := by
  have hf := Model.fracField_lt_pow2 x
  split <;> omega

/-- The xor of two sign bits, as zero or one. -/
theorem xor_sign (p q : Bool) :
    (if p then 1 else 0 : Nat) ^^^ (if q then 1 else 0) = if Bool.xor p q then 1 else 0 := by
  cases p <;> cases q <;> rfl

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
