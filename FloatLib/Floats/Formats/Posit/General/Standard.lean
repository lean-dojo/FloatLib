/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.General.Comparison
public import FloatLib.Floats.Formats.Posit.General.Integer
public import FloatLib.Floats.Formats.Posit.General.SquareRoot
public import FloatLib.Floats.Formats.Posit.KernelPath.Standard

/-!
# The formats of the Posit Standard as the instance `es = 2`

The Posit Standard (2022) fixes two exponent bits. `Posit.General` proves the values, the order,
the rounding and every operation of `Posit.KernelPath.Core` for every number `es` of exponent
bits, as a FloatLib extension: `General.Spec` states the result of an operation on values
(`General.toRat?`, `General.IsRounded`, `General.IsRoundedTo`), and `General.Arithmetic`,
`General.Quotient`, `General.SquareRoot`, `General.Comparison` and `General.Integer` prove that
the sum, the difference, the product, the fused multiply-add, the quotient, the rounding of a
ratio, the square root, the conversion between formats, the conversions to integers, the
negation, the absolute value, the comparisons and the neighbours return what it names, for all
operands. This module identifies the instance
`es = 2` with the standard's model:

* `toRat?_eq_value`: the rational value of a word that is neither zero nor NaR (Posit Standard
  (2022), §3.2.2) is, up to its sign, `General.value` of its magnitude at `es = 2`, for every
  standard width. `toRat?_toNatBits`: `General.toRat?` at `es = 2` on the encoding of a word is
  the value of the word, for every word.
* `roundRat_isRoundedTo`: the standard's rounding `Model.roundRat` of a rational (§4.1) satisfies
  `General.IsRoundedTo` at `es = 2`. So at `es = 2` the general specification is the
  specification of `Model.Spec`, and its uniqueness (`General.IsRoundedTo.unique`) makes each
  general theorem the corresponding theorem of `Posit.KernelPath.Standard`.
* `KernelPath.round_eq` is the rounding instance: the standard's rounding of a nonzero dyadic
  number (§4.1) is `KernelPath.encode` at `es = 2`.
* `other_exponent_sizes`: the kernel operations evaluated by Lean's kernel in the 8-bit
  formats with zero, one and three exponent bits.

The quire (`KernelPath.Quire`) and the elementary functions are those of the standard's formats
and have no form for another number of exponent bits.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.General

open FloatLib.Floats.Formats.Posit.KernelPath FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/--
Posit Standard (2022), §3.2.2: the rational value of a word that is neither zero nor NaR is, up
to its sign, the general value of its magnitude with two exponent bits, for every standard width.
-/
theorem toRat?_eq_value (x : Model format) (hnar : x ≠ Model.nar format)
    (hzero : x ≠ Model.zero format) :
    x.toRat? =
      some ((if x.signBit then -1 else 1) * value format.payloadBits 2 x.magnitudeBits) := by
  have hv := value_eq_fields (es := 2) format.payloadBits_pos
    (Nat.pos_of_ne_zero (magnitudeBits_ne_zero_of_ne_zero x hzero))
    (magnitudeBits_lt_signMask_of_ne_nar x hnar)
  rw [toRat?_eq_toDyadic?_map, toDyadic?_eq x hnar hzero, Option.map_some, hv]
  congr 1
  unfold FloatLib.Numerics.Dyadic.toRat FloatLib.Numerics.Dyadic.signedSignificand fields
  cases x.signBit <;> simp

/--
`General.toRat?` at two exponent bits is the value of the Posit Standard: on the encoding of a
word it returns the rational value of the word, and none for NaR, for every standard width.
-/
theorem toRat?_toNatBits (x : Model format) :
    toRat? format.payloadBits 2 x.toNatBits = x.toRat? := by
  have hsm : format.signMaskNat = 2 ^ format.payloadBits := rfl
  have hlt := toNatBits_lt_modulus x
  rw [modulus_eq] at hlt
  have : 2 ^ (format.payloadBits + 1) = 2 * 2 ^ format.payloadBits := by
    rw [pow_succ, Nat.mul_comm]
  by_cases hnar : x = Model.nar format
  · subst hnar
    rw [nar_toNatBits, hsm, toRat?_nar, Model.toRat?_nar]
  by_cases hzero : x = Model.zero format
  · subst hzero
    rw [zero_toNatBits, toRat?_zero, Model.toRat?_zero]
  have hbits0 : x.toNatBits ≠ 0 := mt (toNatBits_eq_zero_iff x).1 hzero
  have hbitsn : x.toNatBits ≠ 2 ^ format.payloadBits := by
    rw [← hsm]
    exact mt (toNatBits_eq_signMaskNat_iff x).1 hnar
  rw [toRat?_eq_value x hnar hzero, magnitudeBits_eq_ite, signBit_eq_decide, hsm, modulus_eq]
  rcases Nat.lt_or_gt_of_ne hbitsn with hl | hg
  · rw [toRat?_of_lt hbits0 hl, decide_eq_false (Nat.not_le.mpr hl),
      ite_eq_right (Nat.not_le.mpr hl)]
    simp
  · rw [toRat?_of_gt hg, decide_eq_true hg.le, ite_eq_left hg.le]
    simp

/--
Posit Standard (2022), §4.1: the standard's rounding of a rational satisfies the general
rounding rule at two exponent bits, for every standard width and every rational. With
`IsRoundedTo.unique`, the general specification at `es = 2` is the standard's.
-/
theorem roundRat_isRoundedTo (format : Format) (q : ℚ) :
    IsRoundedTo format.payloadBits 2 q (roundRat format q).toNatBits := by
  have hp := format.payloadBits_pos
  have h := ofRatio_isRoundedTo (es := 2) (num := q.num.natAbs)
    (if decide (q < 0) then 1 else 0) hp q.den_nz
  have hround := ofRatio_eq format (decide (q < 0)) q.num.natAbs q.den q.den_nz
  have hq := Rat.num_div_den q
  have hval : (if decide (q < 0) = true then -((q.num.natAbs : ℕ) : ℚ)
      else ((q.num.natAbs : ℕ) : ℚ)) / (q.den : ℚ) = q ∧
      signFactor (if decide (q < 0) = true then 1 else 0) *
        (((q.num.natAbs : ℕ) : ℚ) / (q.den : ℚ)) = q := by
    unfold signFactor
    by_cases hneg : q < 0
    · have hnum : ((q.num.natAbs : ℕ) : ℚ) = -(q.num : ℚ) := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonpos (Rat.num_nonpos.mpr hneg.le),
          Int.cast_neg]
      have hd : decide (q < 0) = true := decide_eq_true hneg
      simp only [hd, ↓reduceIte, Nat.one_ne_zero, hnum]
      exact ⟨by rw [neg_neg, hq], by rw [neg_div, neg_one_mul, neg_neg, hq]⟩
    · have hnum : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by
        rw [← Int.cast_natCast, Int.natCast_natAbs,
          abs_of_nonneg (Rat.num_nonneg.mpr (not_lt.mp hneg))]
      have hd : decide (q < 0) = false := decide_eq_false hneg
      simp only [hd, Bool.false_eq_true, ↓reduceIte, hnum, one_mul]
      exact ⟨hq, hq⟩
  rw [hval.1] at hround
  rw [hval.2] at h
  rw [← hround, toNatBits_ofNatBits_of_lt _ (by rw [modulus_eq]; exact h.lt)]
  exact h

/--
The kernel operations with zero, one and three exponent bits, in the formats with seven payload
bits: `1 + 1 = 2`, `2 * 2 = 4` and `4 / 2 = 2` on the encodings of each format, where one is
`0x40` and two is `0x60`, `0x50` and `0x44`.
-/
theorem other_exponent_sizes :
    [add 7 0 0x40 0x40, mul 7 0 0x60 0x60, div 7 0 0x70 0x60] = [0x60, 0x70, 0x60] ∧
      [add 7 1 0x40 0x40, mul 7 1 0x50 0x50, div 7 1 0x60 0x50] = [0x50, 0x60, 0x50] ∧
      [add 7 3 0x40 0x40, mul 7 3 0x44 0x44, div 7 3 0x48 0x44] = [0x44, 0x48, 0x44] := by
  decide +kernel

end FloatLib.Floats.Formats.Posit.General
