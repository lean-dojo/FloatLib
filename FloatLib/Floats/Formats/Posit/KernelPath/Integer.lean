/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Cast.Integer.Unsigned.Proof
public import FloatLib.Floats.Formats.Posit.KernelPath.Standard
public import FloatLib.Numerics.Representations.FixedInt.Semantics.Basic

/-!
# Posit conversions to integers on encodings

Posit Standard (2022), §6.4. `KernelPath.toSigned` and `KernelPath.toUnsigned` compute the word
of the conversion of a posit to a signed and to an unsigned integer from its encoding: the
decoded significand and exponent give the nearest integer, ties to even (`nearestNat`), and two
comparisons check the range. This module proves them equal to the conversions as they are
defined, for every standard posit format, every positive integer width and every word:

* `nearestNat_eq`: `nearestNat M E B` is the nearest-even rounding of `M * 2 ^ (E - B)`;
* `roundRatEven_fields`: the rounded value of a word that is neither zero nor NaR is that
  natural number with the sign of the word;
* `toFixedInt_toNatBits`: the word of `Model.toFixedInt` is `toSigned` on the encoding;
* `toUnsigned_toNat`: the word of `Model.toUnsigned` is `toUnsigned` on the encoding.

Reference: Standard for Posit Arithmetic (2022), §6.4.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.KernelPath

open FloatLib.Floats.Formats.Posit.Model
open FloatLib.Numerics FloatLib.Numerics.Representations

variable {format : Format}

/-- `nearestNat M E B` is the nearest-even rounding of `M * 2 ^ (E - B)`. -/
theorem nearestNat_eq (M E B : Nat) :
    roundRatEven ((M : ℚ) * (2 : ℚ) ^ ((E : Int) - (B : Int))) = (nearestNat M E B : Int) := by
  unfold nearestNat
  cases hble : Nat.ble B E
  · -- below the bias: a quotient by a power of two
    have hden : (2 : Nat) ^ (B - E) ≠ 0 := (Nat.two_pow_pos _).ne'
    have hlt : E < B := Nat.lt_of_not_le fun h => by
      rw [Nat.ble_eq_true_of_le h] at hble
      cases hble
    have hvalue : (M : ℚ) * (2 : ℚ) ^ ((E : Int) - (B : Int)) =
        (M : ℚ) / ((2 ^ (B - E) : Nat) : ℚ) := by
      have hexp : (E : Int) - (B : Int) = -((B - E : Nat) : Int) := by omega
      rw [hexp, zpow_neg, zpow_natCast, div_eq_mul_inv]
      push_cast
      rfl
    rw [hvalue, roundRatEven_natCast_div M hden]
    change ((roundQuotientEven M (2 ^ (B - E)) : Nat) : Int) =
      ((M / (1 <<< (B - E)) +
        Bool.casesOn (motive := fun _ => Nat)
          (Nat.ble (2 * (M % (1 <<< (B - E))) + 1) (1 <<< (B - E)))
          (Bool.casesOn (motive := fun _ => Nat)
            (Nat.beq (2 * (M % (1 <<< (B - E)))) (1 <<< (B - E))) 1
            ((M / (1 <<< (B - E))) % 2))
          0 : Nat) : Int)
    rw [Nat.one_shiftLeft]
    generalize 2 ^ (B - E) = den
    congr 1
    unfold roundQuotientEven
    dsimp only
    cases hlow : Nat.ble (2 * (M % den) + 1) den
    · have hge : ¬ 2 * (M % den) < den := fun h => by
        rw [Nat.ble_eq_true_of_le h] at hlow
        cases hlow
      rw [ite_eq_right hge]
      cases htie : Nat.beq (2 * (M % den)) den
      · have hne : 2 * (M % den) ≠ den := Nat.ne_of_beq_eq_false htie
        rw [ite_eq_left (by omega)]
      · have heq : 2 * (M % den) = den := Nat.eq_of_beq_eq_true htie
        rw [ite_eq_right (by omega)]
        by_cases hpar : M / den % 2 = 0
        · simp [hpar]
        · have hone : M / den % 2 = 1 := by omega
          simp [hone]
    · have hlt' : 2 * (M % den) < den := Nat.le_of_ble_eq_true hlow
      rw [ite_eq_left hlt']
      rfl
  · -- at or above the bias: an integer
    have hle : B ≤ E := Nat.le_of_ble_eq_true hble
    have hvalue : (M : ℚ) * (2 : ℚ) ^ ((E : Int) - (B : Int)) =
        (((M * 2 ^ (E - B) : Nat) : Int) : ℚ) := by
      have hexp : (E : Int) - (B : Int) = ((E - B : Nat) : Int) := by omega
      rw [hexp, zpow_natCast]
      push_cast
      rfl
    rw [hvalue, roundRatEven_intCast]
    change ((M * 2 ^ (E - B) : Nat) : Int) = ((M <<< (E - B) : Nat) : Int)
    rw [Nat.shiftLeft_eq]

/-- The rational value of the kernel fields of a word: the significand at its exponent, with
the sign. -/
theorem toRat_fields (x : Model format) :
    (fields x).toRat =
      (if x.signBit then -1 else 1) *
        (((significand 2 x.magnitudeBits
            (tailLength format.payloadBits x.magnitudeBits) : Nat) : ℚ) *
          (2 : ℚ) ^ (((exponent format.payloadBits 2 x.magnitudeBits
            (tailLength format.payloadBits x.magnitudeBits) : Nat) : Int) -
              ((bias format.payloadBits 2 : Nat) : Int))) := by
  unfold FloatLib.Numerics.Dyadic.toRat FloatLib.Numerics.Dyadic.signedSignificand fields
  dsimp only
  cases x.signBit <;> simp

/-- The nearest-even integer of the value of the kernel fields of a word is `nearestNat` of its
significand and exponent, with the sign of the word. -/
theorem roundRatEven_fields (x : Model format) :
    roundRatEven (fields x).toRat =
      if x.signBit then
        -((nearestNat
          (significand 2 x.magnitudeBits (tailLength format.payloadBits x.magnitudeBits))
          (exponent format.payloadBits 2 x.magnitudeBits
            (tailLength format.payloadBits x.magnitudeBits))
          (bias format.payloadBits 2) : Nat) : Int)
      else
        ((nearestNat
          (significand 2 x.magnitudeBits (tailLength format.payloadBits x.magnitudeBits))
          (exponent format.payloadBits 2 x.magnitudeBits
            (tailLength format.payloadBits x.magnitudeBits))
          (bias format.payloadBits 2) : Nat) : Int) := by
  rw [toRat_fields, ← nearestNat_eq]
  cases x.signBit
  · simp
  · rw [show ((if true = true then -1 else 1 : ℚ)) = -1 from rfl, neg_one_mul, roundRatEven_neg]
    rfl

/-- A word that is neither zero nor NaR has the rational value of its kernel fields. -/
theorem toRat?_eq_fields (x : Model format) (hnar : x ≠ Model.nar format)
    (hzero : x ≠ Model.zero format) : x.toRat? = some (fields x).toRat := by
  rw [toRat?_eq_toDyadic?_map, toDyadic?_eq x hnar hzero]
  rfl

/-- The comparison of an encoding with the NaR encoding reads the sign bit. -/
theorem ble_nar (x : Model format) :
    Nat.ble (nar format.payloadBits) x.toNatBits = x.signBit := by
  rw [signBit_eq_decide, nar_eq]
  cases hd : Nat.ble format.signMaskNat x.toNatBits
  · exact (decide_eq_false
      (Nat.not_le_of_not_ble_eq_true (by rw [hd]; exact Bool.false_ne_true))).symm
  · exact (decide_eq_true (Nat.le_of_ble_eq_true hd)).symm

/-- The word of a fixed-width integer built from an integer is its remainder. -/
theorem toNatBits_ofInt {width : Nat} (i : Int) :
    (FixedInt.ofInt i : FixedInt width).toNatBits = (i % ((2 ^ width : Nat) : Int)).toNat :=
  BitVec.toNat_ofInt i

/-- Nearest-even rounding fixes zero. -/
theorem roundRatEven_zero : roundRatEven (0 : ℚ) = 0 := by
  have h := roundRatEven_intCast 0
  simpa using h

/--
Posit Standard (2022), §6.4: the word of the conversion to a signed integer is `toSigned` on
the encoding, for every posit format, every positive integer width and every word.
-/
theorem toFixedInt_toNatBits (width : Nat) (x : Model format) (hwidth : 0 < width) :
    (Model.toFixedInt width x hwidth).toNatBits =
      toSigned format.payloadBits 2 width x.toNatBits := by
  have hhalf : Nat.shiftLeft 1 (Nat.sub width 1) = 2 ^ (width - 1) := Nat.one_shiftLeft _
  have hfull : Nat.shiftLeft 1 width = 2 ^ width := Nat.one_shiftLeft _
  have hpow : 2 ^ width = 2 * 2 ^ (width - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hpos : 0 < 2 ^ (width - 1) := Nat.two_pow_pos _
  have hmin : FixedInt.minValue width = -((2 ^ (width - 1) : Nat) : Int) := by
    rw [FixedInt.minValue_eq hwidth]
    push_cast
    rfl
  have hmax : FixedInt.maxValue width = ((2 ^ (width - 1) : Nat) : Int) - 1 := by
    rw [FixedInt.maxValue_eq]
    push_cast
    rfl
  unfold toSigned
  rw [hhalf, hfull]
  generalize hh : 2 ^ (width - 1) = half at hpow hpos hmin hmax
  generalize hm : 2 ^ width = modulus at hpow
  cases hb : Nat.beq x.toNatBits (nar format.payloadBits)
  · have hnar : x ≠ Model.nar format := fun h => by
      rw [beq_nar x, decide_eq_true h] at hb
      cases hb
    cases hz : Nat.beq x.toNatBits 0
    · have hzero : x ≠ Model.zero format := fun h => by
        rw [beq_zero x, decide_eq_true h] at hz
        cases hz
      have hrat := toRat?_eq_fields x hnar hzero
      have hround := roundRatEven_fields x
      dsimp only
      rw [magnitude_eq x, ble_nar x]
      generalize nearestNat
        (significand 2 x.magnitudeBits (tailLength format.payloadBits x.magnitudeBits))
        (exponent format.payloadBits 2 x.magnitudeBits
          (tailLength format.payloadBits x.magnitudeBits))
        (bias format.payloadBits 2) = n at hround ⊢
      cases hs : x.signBit
      · -- a positive value
        rw [hs] at hround
        replace hround : roundRatEven (fields x).toRat = (n : Int) := hround
        dsimp only
        cases hfit : Nat.ble (Nat.succ n) half
        · have hout : ¬ FixedInt.InRange width (roundRatEven (fields x).toRat) := by
            rw [hround]
            intro hrange
            have hle := hrange.2
            rw [hmax] at hle
            have : n + 1 ≤ half := by omega
            rw [Nat.ble_eq_true_of_le this] at hfit
            cases hfit
          rw [toFixedInt_eq_minCode_of_not_inRange x hwidth hrat hout,
            integerSentinel_toNatBits hwidth, hh]
        · have hlt : n + 1 ≤ half := Nat.le_of_ble_eq_true hfit
          have hin : FixedInt.InRange width (roundRatEven (fields x).toRat) := by
            rw [hround]
            constructor
            · rw [hmin]
              omega
            · rw [hmax]
              omega
          rw [toFixedInt_eq_of_inRange x hwidth hrat hin, hround, toNatBits_ofInt, hm,
            Int.emod_eq_of_lt (Int.natCast_nonneg n) (by omega)]
          exact Int.toNat_natCast n
      · -- a negative value
        rw [hs] at hround
        replace hround : roundRatEven (fields x).toRat = -(n : Int) := hround
        dsimp only
        cases hfit : Nat.ble n half
        · have hout : ¬ FixedInt.InRange width (roundRatEven (fields x).toRat) := by
            rw [hround]
            intro hrange
            have hle := hrange.1
            rw [hmin] at hle
            have : n ≤ half := by omega
            rw [Nat.ble_eq_true_of_le this] at hfit
            cases hfit
          rw [toFixedInt_eq_minCode_of_not_inRange x hwidth hrat hout,
            integerSentinel_toNatBits hwidth, hh]
        · have hle : n ≤ half := Nat.le_of_ble_eq_true hfit
          have hin : FixedInt.InRange width (roundRatEven (fields x).toRat) := by
            rw [hround]
            constructor
            · rw [hmin]
              omega
            · rw [hmax]
              omega
          rw [toFixedInt_eq_of_inRange x hwidth hrat hin, hround, toNatBits_ofInt, hm]
          change _ = (modulus - n) % modulus
          rcases Nat.eq_zero_or_pos n with hn | hn
          · subst hn
            simp
          · have hemod : (-(n : Int)) % (modulus : Int) = ((modulus - n : Nat) : Int) := by
              rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
              omega
            rw [hemod, Int.toNat_natCast, Nat.mod_eq_of_lt (by omega)]
    · -- zero
      have hzero : x = Model.zero format := by
        have h := beq_zero x
        rw [hz] at h
        exact of_decide_eq_true h.symm
      subst hzero
      have hin : FixedInt.InRange width (roundRatEven (0 : ℚ)) := by
        rw [roundRatEven_zero]
        constructor
        · rw [hmin]
          omega
        · rw [hmax]
          omega
      rw [toFixedInt_eq_of_inRange _ hwidth (Model.toRat?_zero format) hin, toNatBits_ofInt,
        roundRatEven_zero]
      simp
  · -- NaR
    have hnar : x = Model.nar format := by
      have h := beq_nar x
      rw [hb] at h
      exact of_decide_eq_true h.symm
    subst hnar
    rw [toFixedInt_nar, integerSentinel_toNatBits hwidth, hh]

/--
Posit Standard (2022), §6.4: the word of the conversion to an unsigned integer is `toUnsigned`
on the encoding, for every posit format, every positive integer width and every word.
-/
theorem toUnsigned_toNat (width : Nat) (x : Model format) (hwidth : 0 < width) :
    (Model.toUnsigned width x hwidth).toNat =
      KernelPath.toUnsigned format.payloadBits 2 width x.toNatBits := by
  have hhalf : Nat.shiftLeft 1 (Nat.sub width 1) = 2 ^ (width - 1) := Nat.one_shiftLeft _
  have hfull : Nat.shiftLeft 1 width = 2 ^ width := Nat.one_shiftLeft _
  have hrange : ∀ r : Int, (IntegerFormat.unsigned width).InRange r ↔
      0 ≤ r ∧ r ≤ ((2 ^ width : Nat) : Int) - 1 := by
    intro r
    change (0 ≤ r ∧ r ≤ (2 : Int) ^ width - 1) ↔ _
    push_cast
    exact Iff.rfl
  unfold KernelPath.toUnsigned
  rw [hhalf, hfull]
  generalize hm : 2 ^ width = modulus at hrange
  cases hb : Nat.beq x.toNatBits (nar format.payloadBits)
  · have hnar : x ≠ Model.nar format := fun h => by
      rw [beq_nar x, decide_eq_true h] at hb
      cases hb
    cases hz : Nat.beq x.toNatBits 0
    · have hzero : x ≠ Model.zero format := fun h => by
        rw [beq_zero x, decide_eq_true h] at hz
        cases hz
      have hrat := toRat?_eq_fields x hnar hzero
      have hround := roundRatEven_fields x
      dsimp only
      rw [magnitude_eq x, ble_nar x]
      generalize nearestNat
        (significand 2 x.magnitudeBits (tailLength format.payloadBits x.magnitudeBits))
        (exponent format.payloadBits 2 x.magnitudeBits
          (tailLength format.payloadBits x.magnitudeBits))
        (bias format.payloadBits 2) = n at hround ⊢
      cases hs : x.signBit
      · -- a positive value
        rw [hs] at hround
        replace hround : roundRatEven (fields x).toRat = (n : Int) := hround
        dsimp only
        cases hfit : Nat.ble (Nat.succ n) modulus
        · have hout : ¬ (IntegerFormat.unsigned width).InRange
              (roundRatEven (fields x).toRat) := by
            rw [hround, hrange]
            intro hin
            have : n + 1 ≤ modulus := by omega
            rw [Nat.ble_eq_true_of_le this] at hfit
            cases hfit
          rw [toUnsigned_eq_intMin_of_not_inRange x hwidth hrat hout,
            unsignedSentinel_toNat hwidth]
        · have hlt : n + 1 ≤ modulus := Nat.le_of_ble_eq_true hfit
          have hin : (IntegerFormat.unsigned width).InRange
              (roundRatEven (fields x).toRat) := by
            rw [hround, hrange]
            omega
          rw [toUnsigned_eq_of_inRange x hwidth hrat hin, hround, BitVec.toNat_ofNat,
            Int.toNat_natCast, hm, Nat.mod_eq_of_lt (by omega)]
      · -- a negative value
        rw [hs] at hround
        replace hround : roundRatEven (fields x).toRat = -(n : Int) := hround
        dsimp only
        cases hn : Nat.beq n 0
        · have hpos : n ≠ 0 := Nat.ne_of_beq_eq_false hn
          have hout : ¬ (IntegerFormat.unsigned width).InRange
              (roundRatEven (fields x).toRat) := by
            rw [hround, hrange]
            omega
          rw [toUnsigned_eq_intMin_of_not_inRange x hwidth hrat hout,
            unsignedSentinel_toNat hwidth]
        · have hzero' : n = 0 := Nat.eq_of_beq_eq_true hn
          subst hzero'
          have hin : (IntegerFormat.unsigned width).InRange
              (roundRatEven (fields x).toRat) := by
            rw [hround, hrange]
            have := Nat.two_pow_pos width
            omega
          rw [toUnsigned_eq_of_inRange x hwidth hrat hin, hround]
          simp
    · -- zero
      have hzero : x = Model.zero format := by
        have h := beq_zero x
        rw [hz] at h
        exact of_decide_eq_true h.symm
      subst hzero
      have hin : (IntegerFormat.unsigned width).InRange (roundRatEven (0 : ℚ)) := by
        rw [roundRatEven_zero, hrange]
        have := Nat.two_pow_pos width
        omega
      rw [toUnsigned_eq_of_inRange _ hwidth (Model.toRat?_zero format) hin, roundRatEven_zero]
      simp
  · -- NaR
    have hnar : x = Model.nar format := by
      have h := beq_nar x
      rw [hb] at h
      exact of_decide_eq_true h.symm
    subst hnar
    rw [toUnsigned_nar, unsignedSentinel_toNat hwidth]

end FloatLib.Floats.Formats.Posit.KernelPath
