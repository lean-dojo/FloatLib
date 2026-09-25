/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Fields.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Fields.Proof
import Mathlib.Tactic.NormNum

/-!
# Correctness of scalar-field posit decoding

The machine-scalar decoder agrees with its natural-number reference view and the exact posit
field model. Executable definitions live in
`FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Fields.Runtime`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWord

open FloatLib.Numerics

/-! ## Scalar-field decoding for compiled kernels -/

/-- The machine-indexed bit reader is the existing proved native reader at the same index. -/
theorem bitAtWord_eq_bitAt
    (value index : UInt64) :
    FixedWord.bitAtWord value index = bitAt value index.toNat := by
  rw [FixedWord.bitAtWord_eq_testBit, bitAt_eq_testBit]

/-- Machine-width low-bit extraction reuses the existing Posit native-field semantics. -/
theorem lowBitsWord_eq_lowBits
    (value width : UInt64) (hwidth : width ≤ 64) :
    FixedWord.lowBitsWord value width = lowBits value width.toNat := by
  apply UInt64.toNat_inj.mp
  rw [FixedWord.lowBitsWord_toNat value width hwidth,
    lowBits_toNat_of_le value width.toNat]
  exact_mod_cast hwidth

/-- Machine-width right shift agrees with the existing Posit native-field operation. -/
theorem shiftRightWord_eq_shiftRight
    (value shift : UInt64) (hshift : shift < 64) :
    FixedWord.shiftRightWord value shift = shiftRight value shift.toNat := by
  apply UInt64.toNat_inj.mp
  rw [FixedWord.shiftRightWord_toNat value shift hshift,
    shiftRight_toNat value shift.toNat]
  exact_mod_cast hshift

/-- Native minimum commutes with observation as a natural number. -/
private theorem min_toNat (left right : UInt64) :
    (left ⊓ right).toNat = min left.toNat right.toNat := by
  change (if left ≤ right then left else right).toNat =
    min left.toNat right.toNat
  by_cases hle : left ≤ right
  · rw [ite_eq_left hle,
      Nat.min_eq_left (UInt64.le_iff_toNat_le.mp hle)]
  · have hgeNat : right.toNat ≤ left.toNat := by
      have hnotNat : ¬left.toNat ≤ right.toNat :=
        fun hleNat => hle (UInt64.le_iff_toNat_le.mpr hleNat)
      omega
    rw [ite_eq_right hle, Nat.min_eq_right hgeNat]

/-- The machine-width and natural-width regime scans return the same run length. -/
theorem countLeadingRunWord_toNat_eq
    (value width : UInt64) (bit : Bool) (hwidth : width ≤ 64) :
    (FixedWord.countLeadingRunWord value width bit).toNat =
      countLeadingRun value width.toNat bit := by
  have hwidthNat : width.toNat ≤ 64 := by
    exact_mod_cast hwidth
  rw [FixedWord.countLeadingRunWord_toNat value width bit hwidth]
  unfold countLeadingRun
  simp only [ite_eq_left hwidthNat]
  unfold countLeadingZeros
  simp only [FixedWord.log2Word_eq_log2]
  rw [← lowBitsWord_eq_lowBits
    (if bit then ~~~value else value) width hwidth]

/-- A nonnegative word below the signed boundary has the same `Int64` and mathematical value. -/
private theorem toInt_toInt64_of_lt
    (value : UInt64) (hvalue : value.toNat < 2 ^ 63) :
    value.toInt64.toInt = Int.ofNat value.toNat := by
  calc
    value.toInt64.toInt =
        (UInt64.ofNat value.toNat).toInt64.toInt := by
          rw [UInt64.ofNat_toNat]
    _ = (Int64.ofNat value.toNat).toInt := by
      rw [UInt64.toInt64_ofNat']
    _ = Int.ofNat value.toNat :=
      Int64.toInt_ofNat_of_lt hvalue

/-- Reduction modulo the machine modulus fixes every integer of `Int64` magnitude. -/
private theorem bmod_two_pow_eq_self {n : Int} (hlower : -2 ^ 63 ≤ n) (hupper : n < 2 ^ 63) :
    n.bmod (2 ^ 64) = n :=
  Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)

/-- The signed regime and exponent arithmetic is exact for in-range field widths. -/
private theorem toInt_regimeExponent (bit : Bool) (run field fraction : UInt64)
    (hrun : run.toNat ≤ 64) (hfield : field.toNat ≤ 3) (hfraction : fraction.toNat < 64) :
    ((if bit then run.toInt64 - 1 else -run.toInt64) * 4 +
        field.toInt64 - fraction.toInt64).toInt =
      (if bit then Int.ofNat run.toNat - 1 else -Int.ofNat run.toNat) * 4 +
        Int.ofNat field.toNat - Int.ofNat fraction.toNat := by
  have hrun' := toInt_toInt64_of_lt run (by omega)
  have hfield' := toInt_toInt64_of_lt field (by omega)
  have hfraction' := toInt_toInt64_of_lt fraction (by omega)
  have hfour : (4 : Int64).toInt = 4 := rfl
  simp only [Int.ofNat_eq_natCast] at hrun' hfield' hfraction' ⊢
  cases bit <;>
    simp (disch := omega) only [Int64.toInt_sub, Int64.toInt_add, Int64.toInt_mul,
      Int64.toInt_neg, Int64.toInt_one, hrun', hfield', hfraction', hfour, ite_true, ite_false,
      Bool.false_eq_true, bmod_two_pow_eq_self]

/-- Shifting a stored exponent into two positions is exact and stays below four. -/
private theorem exponentField_toNat (stored used : UInt64)
    (hused : used.toNat ≤ 2) (hstored : stored.toNat < 2 ^ used.toNat) :
    (stored <<< (2 - used)).toNat = stored.toNat <<< (2 - used.toNat) ∧
      stored.toNat <<< (2 - used.toNat) ≤ 3 := by
  have hshift : (2 - used).toNat = 2 - used.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hused))]
    rfl
  rw [UInt64.toNat_shiftLeft, hshift, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  obtain h | h | h : used.toNat = 0 ∨ used.toNat = 1 ∨ used.toNat = 2 := by omega
  all_goals
    simp only [h] at hstored ⊢
    norm_num at hstored ⊢
    omega

/-- The trailing-bit count after the regime and its optional terminator is exact. -/
private theorem trailing_toNat (payload run : UInt64) (hrun : run ≤ payload) :
    (payload - run - (if (decide (run < payload)) then 1 else 0)).toNat =
      payload.toNat - run.toNat - (if (decide (run.toNat < payload.toNat)) then 1 else 0) := by
  have hsub := UInt64.toNat_sub_of_le _ _ hrun
  by_cases h : run < payload
  · have h' : run.toNat < payload.toNat := UInt64.lt_iff_toNat_lt.mp h
    rw [ite_eq_left (decide_eq_true h), ite_eq_left (decide_eq_true h'),
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
        rw [hsub, UInt64.toNat_one]
        omega)),
      hsub, UInt64.toNat_one]
  · have h' : ¬ run.toNat < payload.toNat := fun h' => h (UInt64.lt_iff_toNat_lt.mpr h')
    rw [ite_eq_right (fun hc => h (of_decide_eq_true hc)),
      ite_eq_right (fun hc => h' (of_decide_eq_true hc)),
      UInt64.sub_zero, hsub, Nat.sub_zero]

/-- Significand assembly agrees with the reference once the fraction width is known. -/
private theorem significand_eq (code fraction : UInt64) (fractionNat : Nat)
    (hfraction : fraction.toNat = fractionNat) (hlt : fractionNat < 64) :
    FixedWord.lowBitsWord code fraction ||| ((1 : UInt64) <<< fraction) =
      lowBits code fractionNat ||| ((1 : UInt64) <<< UInt64.ofNat fractionNat) := by
  rw [lowBitsWord_eq_lowBits code fraction (UInt64.le_iff_toNat_le.mpr (by
      rw [hfraction]
      exact hlt.le)),
    hfraction, ← hfraction, UInt64.ofNat_toNat]

/--
The fully machine-scalar decoder refines the reference Posit field decoder.

The continuation observes the signed machine exponent through `Int64.toInt`. The width bounds make
every unsigned layout subtraction and every signed exponent operation exact; no modular behavior
is exposed at the semantic boundary.
-/
theorem withNonnegativeMachineFieldsAtPayload_eq_reference {α : Type}
    (payloadBits code : UInt64)
    (hpayloadPositive : 0 < payloadBits) (hpayload : payloadBits ≤ 64)
    (continuation : UInt64 → Int → α) :
      withNonnegativeMachineFieldsAtPayload payloadBits code
        (fun significand exponent =>
          continuation significand exponent.toInt) =
      withNonnegativeReferenceFieldsAtPayload
        payloadBits.toNat code continuation := by
  by_cases hzero : code == 0
  · simp [withNonnegativeMachineFieldsAtPayload,
      withNonnegativeReferenceFieldsAtPayload, hzero]
  · let payloadNat := payloadBits.toNat
    let regimeBitWord := FixedWord.bitAtWord code (payloadBits - 1)
    let regimeRunWord := FixedWord.countLeadingRunWord code payloadBits regimeBitWord
    let trailingWord :=
      payloadBits - regimeRunWord - (if (decide (regimeRunWord < payloadBits)) then 1 else 0)
    let usedExponentWord := min 2 trailingWord
    let fractionWord := trailingWord - usedExponentWord
    let storedExponentWord :=
      FixedWord.lowBitsWord (FixedWord.shiftRightWord code fractionWord) usedExponentWord
    let regimeBitNat := bitAt code (payloadNat - 1)
    let regimeRunNat := countLeadingRun code payloadNat regimeBitNat
    let trailingNat :=
      payloadNat - regimeRunNat - (if (decide (regimeRunNat < payloadNat)) then 1 else 0)
    let usedExponentNat := min 2 trailingNat
    let fractionNat := trailingNat - usedExponentNat
    let storedExponentNat := lowBits (shiftRight code fractionNat) usedExponentNat
    have hpayloadNatPositive : 0 < payloadNat := by
      exact_mod_cast hpayloadPositive
    have hpayloadNat : payloadNat ≤ 64 := by
      exact_mod_cast hpayload
    have hregimeBit : regimeBitWord = regimeBitNat := by
      unfold regimeBitWord regimeBitNat
      rw [bitAtWord_eq_bitAt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
          rw [UInt64.toNat_one]
          exact hpayloadNatPositive)),
        UInt64.toNat_one]
    have hregimeRun : regimeRunWord.toNat = regimeRunNat := by
      unfold regimeRunWord regimeRunNat
      rw [hregimeBit, countLeadingRunWord_toNat_eq code payloadBits regimeBitNat hpayload]
    have hregimeRunLe : regimeRunNat ≤ payloadNat := by
      unfold regimeRunNat
      rw [countLeadingRun_eq_model]
      exact Model.countLeadingRun_le code.toNat payloadNat regimeBitNat
    have hregimeRunPos : 0 < regimeRunNat := by
      unfold regimeRunNat regimeBitNat
      rw [countLeadingRun_eq_model, bitAt_eq_testBit]
      exact Model.countLeadingRun_self_pos code.toNat payloadNat hpayloadNatPositive
    have htrailing : trailingWord.toNat = trailingNat := by
      unfold trailingWord trailingNat
      rw [trailing_toNat payloadBits regimeRunWord
          (UInt64.le_iff_toNat_le.mpr (hregimeRun ▸ hregimeRunLe)),
        hregimeRun]
    have husedExponent : usedExponentWord.toNat = usedExponentNat := by
      unfold usedExponentWord usedExponentNat
      rw [min_toNat, htrailing]
      rfl
    have husedExponentNatLe : usedExponentNat ≤ 2 := Nat.min_le_left _ _
    have hfraction : fractionWord.toNat = fractionNat := by
      unfold fractionWord fractionNat
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
          rw [husedExponent, htrailing]
          exact Nat.min_le_right _ _)),
        htrailing, husedExponent]
    have hfractionLt : fractionNat < 64 := by
      unfold fractionNat trailingNat
      omega
    have hstoredExponent : storedExponentWord = storedExponentNat := by
      unfold storedExponentWord storedExponentNat
      rw [shiftRightWord_eq_shiftRight code fractionWord (UInt64.lt_iff_toNat_lt.mpr (by
          rw [hfraction]
          exact hfractionLt)),
        hfraction,
        lowBitsWord_eq_lowBits _ usedExponentWord (UInt64.le_iff_toNat_le.mpr (by
          rw [husedExponent]
          exact le_trans husedExponentNatLe (by decide))),
        husedExponent]
    have hstoredLt : storedExponentNat.toNat < 2 ^ usedExponentNat := by
      unfold storedExponentNat
      rw [lowBits_toNat_of_le _ _ (by omega)]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    obtain ⟨hexponentField, hexponentFieldLe⟩ :=
      exponentField_toNat storedExponentNat usedExponentWord
        (by rw [husedExponent]; exact husedExponentNatLe) (by rw [husedExponent]; exact hstoredLt)
    simp only [withNonnegativeMachineFieldsAtPayload,
      withNonnegativeReferenceFieldsAtPayload, hzero, Bool.false_eq_true, ite_false]
    change
      continuation (FixedWord.lowBitsWord code fractionWord ||| ((1 : UInt64) <<< fractionWord))
          ((if regimeBitWord then regimeRunWord.toInt64 - 1 else -regimeRunWord.toInt64) * 4 +
            (storedExponentWord <<< (2 - usedExponentWord)).toInt64 - fractionWord.toInt64).toInt =
        continuation (lowBits code fractionNat ||| ((1 : UInt64) <<< UInt64.ofNat fractionNat))
          ((if regimeBitNat then Int.ofNat regimeRunNat - 1 else -Int.ofNat regimeRunNat) * 4 +
            Int.ofNat (storedExponentNat.toNat <<< (2 - usedExponentNat)) - Int.ofNat fractionNat)
    rw [significand_eq code fractionWord fractionNat hfraction hfractionLt,
      toInt_regimeExponent regimeBitWord regimeRunWord _ fractionWord (by omega)
        (by rw [hstoredExponent, hexponentField]; exact hexponentFieldLe) (by omega),
      hregimeBit, hregimeRun, hstoredExponent, hexponentField, husedExponent, hfraction]

/-- The selected word decoder always refines the natural-number reference decoder. -/
theorem withNonnegativeWordFieldsAtPayload_eq_reference {α : Type}
    (payloadBits : Nat) (code : UInt64)
    (continuation : UInt64 → Int → α) :
    withNonnegativeWordFieldsAtPayload payloadBits code continuation =
      withNonnegativeReferenceFieldsAtPayload
        payloadBits code continuation := by
  unfold withNonnegativeWordFieldsAtPayload
  by_cases hpayloadPositive : 0 < payloadBits
  · simp only [hpayloadPositive, dite_true]
    by_cases hpayload : payloadBits ≤ 64
    · simp only [hpayload, dite_true]
      have htoNat :
          (UInt64.ofNat payloadBits).toNat = payloadBits := by
        exact UInt64.toNat_ofNat_of_lt'
          (lt_of_le_of_lt hpayload (by norm_num))
      have hpayloadPositiveWord :
          0 < UInt64.ofNat payloadBits := by
        rw [UInt64.lt_iff_toNat_lt, htoNat]
        exact hpayloadPositive
      have hpayloadWord :
          UInt64.ofNat payloadBits ≤ 64 := by
        rw [UInt64.le_iff_toNat_le, htoNat]
        exact hpayload
      simpa only [htoNat] using
        withNonnegativeMachineFieldsAtPayload_eq_reference
          (UInt64.ofNat payloadBits) code
          hpayloadPositiveWord hpayloadWord continuation
    · simp only [hpayload, dite_false]
  · simp only [hpayloadPositive, dite_false]

/--
Taking the natural value of a native decoder result can be pushed through its continuation.

This reusable map law lets carrier-facing kernels return `UInt64` while their refinement proofs
compare against an existing `Nat` result. It contains the decoder case split once instead of
repeating it in every arithmetic operation.
-/
theorem withNonnegativeWordFieldsAtPayload_toNat
    (payloadBits : Nat) (code : UInt64)
    (continuation : UInt64 → Int → UInt64) :
    (withNonnegativeWordFieldsAtPayload payloadBits code continuation).toNat =
      withNonnegativeWordFieldsAtPayload payloadBits code
        fun significand exponent =>
          (continuation significand exponent).toNat := by
  rw [withNonnegativeWordFieldsAtPayload_eq_reference,
    withNonnegativeWordFieldsAtPayload_eq_reference]
  unfold withNonnegativeReferenceFieldsAtPayload
  by_cases hzero : code == 0
  · simp only [hzero, ite_true]
  · simp only [hzero, Bool.false_eq_true, ite_false]

/--
The exact-field decoder is definitionally the `Nat` view of the native-word decoder.

This small bridge is the reusable refinement boundary for optimized kernels: their proofs may
rewrite to the existing exact semantics without reproving posit field extraction.
-/
theorem withNonnegativeFields_eq_word {α : Type}
    (format : Format) (code : UInt64)
    (continuation : Nat → Int → α) :
    withNonnegativeFields format code continuation =
      withNonnegativeWordFields format code fun significand exponent =>
        continuation significand.toNat exponent :=
  rfl

/-- Scalar nonnegative decoding is exactly record-producing nonnegative decoding. -/
theorem withNonnegativeFields_eq {α : Type}
    (format : Format) (code : UInt64)
    (continuation : Nat → Int → α) :
    withNonnegativeFields format code continuation =
      let value := nonnegativeDyadicAt format code
      continuation value.significand value.exponent := by
  unfold withNonnegativeFields withNonnegativeFieldsAtPayload
    nonnegativeDyadicAt
  rw [withNonnegativeWordFieldsAtPayload_eq_reference]
  unfold withNonnegativeReferenceFieldsAtPayload
  simp only [Format.exponentBits]
  split <;> rfl

end FloatLib.Floats.Formats.Posit.Model.NativeWord
