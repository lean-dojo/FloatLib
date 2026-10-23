/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.BoundedParsing
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.ExponentClamp
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Formatting
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Representation
public import FloatLib.Numerics.Exact.DecimalText.NotationProof
public import FloatLib.Numerics.Exact.HexText.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable

/-! # Exact binary character round trips

The string scanner recovers the exact coefficient and exponent. For conventional IEEE
descriptors, finite hexadecimal output round-trips in every supported rounding mode, and finite
exact decimal output and the shortest display round-trip under nearest-even input. All results
include signed zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

/-- Successfully scanned text passes unchanged to the destination conversion. -/
theorem TextParser.run_of_readText (fmt : FloatFormat) (mode : IEEERoundingMode)
    (text : String) (value : TextValue) (hread : readText text = some value) :
    TextParser.run fmt mode text = convertText fmt mode value := by
  simp [TextParser.run, hread]

/-- The shared binary scanner recognizes every exact decimal spelling. -/
@[simp] theorem readText_decimal_format (value : DecimalText.Decimal) :
    readText value.format = some (.decimal value) := by
  simp [readText, DecimalText.Decimal.format]

/-- The shared binary scanner recognizes every exact hexadecimal spelling. -/
@[simp] theorem readText_hex_format (value : Numerics.Dyadic) :
    readText (HexText.format value) = some (.dyadic value) := by
  have hn : DecimalText.parseCharacters (HexText.format value).toList = none := by
    cases hs : value.negative <;>
      simp [HexText.format, HexText.characters, hs, DecimalText.parseCharacters,
        DecimalText.splitSign, RadixText.parseMagnitude, RadixText.scanDigits,
        DecimalText.digitValue?, DecimalText.parseExponent]
  simp [readText, hn]

/-- Hexadecimal text restores a finite IEEE word in every supported rounding direction. -/
theorem parse_format_hex_of_isFinite {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (mode : IEEERoundingMode) (value : Model fmt) (hfinite : isFinite value = true) :
    parse fmt (format value (style := .hex)) (mode := mode) = .ok value := by
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hf : format value (style := .hex) = HexText.format d := by
    simp [format, Internal.Status.format, Internal.Status.formatFinite, exactValue, hd,
      formatDyadicText]
  rw [hf, parse_eq_run, TextParser.run_of_readText _ _ _ _ (readText_hex_format d)]
  simp [convertText, convertDyadicText, Except.map,
    Internal.Directed.roundDyadic_toDyadic? hfmt mode hd]

/-- The rational operands used by decimal conversion denote the complete decimal value. -/
theorem signedScaledRatToReal_decimal (value : DecimalText.Decimal) :
    let magnitude := (value.significand : Rat) * (10 : Rat) ^ value.exponent
    signedScaledRatToReal value.negative magnitude.num.natAbs magnitude.den 0 =
      (value.toRat : Real) := by
  dsimp only
  let magnitude := (value.significand : Rat) * (10 : Rat) ^ value.exponent
  have hm : 0 ≤ magnitude := mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  have hn := Rat.num_nonneg.mpr hm
  have hc : (magnitude.num.natAbs : Real) = (magnitude.num : Real) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : Int => (z : Real)) (Int.natAbs_of_nonneg hn)
  have hrat : (magnitude.num.natAbs : Real) / magnitude.den = (magnitude : Real) := by
    rw [hc, Rat.cast_def]
  change signedScaledRatToReal value.negative magnitude.num.natAbs magnitude.den 0 = _
  have hmreal : scaledRatToReal magnitude.num.natAbs magnitude.den 0 = (magnitude : Real) := by
    simpa [scaledRatToReal] using hrat
  cases hs : value.negative <;>
    simp only [signedScaledRatToReal, hmreal, Bool.false_eq_true, ite_true, ite_false]
  · simp [magnitude, DecimalText.Decimal.toRat, hs]
  · simp [magnitude, DecimalText.Decimal.toRat, hs]

/-- Decimal conversion rounds the complete exact input once, including inexact text and zero. -/
theorem toReal_convertDecimalText_nearest (fmt : FloatFormat)
    (hfmt : fmt.isIEEE = true) (value : DecimalText.Decimal)
    (hfinite : isFinite (convertDecimalText fmt .nearest value).value = true) :
    toReal (convertDecimalText fmt .nearest value).value =
      roundAt fmt (value.toRat : ℝ) := by
  rw [convertDecimalText_eq_exact] at hfinite ⊢
  change toReal (roundRatScaled fmt value.negative
    _ _ 0) = _
  rw [toReal_roundRatScaled_eq_roundAt_of_isFinite fmt value.negative
    _ _ 0 hfmt (Rat.den_nz _) hfinite, signedScaledRatToReal_decimal]

/-- Successfully parsed decimal text has the nearest-even real value of its exact decimal datum.
The input may be inexact for the destination. Only a nonfinite delivered value is excluded. -/
theorem toReal_parse_decimal_nearest {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (text : String) (value : DecimalText.Decimal) (result : Model fmt)
    (hread : readText text = some (.decimal value))
    (hparse : parse fmt text = .ok result) (hfinite : isFinite result = true) :
    toReal result = roundAt fmt (value.toRat : ℝ) := by
  rw [parse_eq_run, TextParser.run_of_readText _ _ _ _ hread] at hparse
  have hvalue : (convertDecimalText fmt .nearest value).value = result := by
    simpa only [convertText, Except.map, Except.ok.injEq] using hparse
  rw [← hvalue] at hfinite ⊢
  exact toReal_convertDecimalText_nearest fmt hfmt value hfinite

/-- Decimal conversion of an exact finite nonzero value restores its complete IEEE word. -/
theorem convertDecimalText_eq_of_nonzero {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (hfinite : isFinite value = true) (hzero : toReal value ≠ 0)
    (textValue : DecimalText.Decimal) (hexact : (textValue.toRat : Real) = toReal value) :
    (convertDecimalText fmt .nearest textValue).value = value := by
  rw [convertDecimalText_eq_exact]
  let magnitude := (textValue.significand : Rat) * (10 : Rat) ^ textValue.exponent
  have hv : signedScaledRatToReal textValue.negative magnitude.num.natAbs magnitude.den 0 =
      toReal value := (signedScaledRatToReal_decimal textValue).trans hexact
  have hn : magnitude.num.natAbs ≠ 0 := by
    intro hz
    apply hzero
    rw [← hv]
    simp [signedScaledRatToReal, scaledRatToReal, hz]
  have hb : |signedScaledRatToReal textValue.negative magnitude.num.natAbs magnitude.den 0| ≤
      toReal (posMaxFinite fmt) := by
    rw [hv]
    exact abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite value hfmt hfinite
  have hf := isFinite_roundRatScaled_of_abs_le_posMaxFinite fmt textValue.negative
    magnitude.num.natAbs magnitude.den 0 hfmt magnitude.den_nz hb
  have hr := toReal_roundRatScaled_eq_roundAt fmt textValue.negative
    magnitude.num.natAbs magnitude.den 0 hfmt hn magnitude.den_nz hf
  rw [hv, roundAt_toReal_eq value hfinite] at hr
  exact eq_of_toReal_eq_of_nonzero hf hfinite hr (hr.trans_ne hzero)

/-- Exact decimal output restores every nonzero finite IEEE word under nearest-even input. -/
theorem parse_format_exact_of_isFinite_of_nonzero {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) (value : Model fmt) (hfinite : isFinite value = true)
    (hzero : toReal value ≠ 0) :
    parse fmt (format value (style := .exact)) = .ok value := by
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hf : format value (style := .exact) = (DecimalText.ofDyadic d).format := by
    simp [format, Internal.Status.format, Internal.Status.formatFinite, exactValue, hd,
      formatDyadicText, DecimalText.formatDyadic]
  have hv : ((DecimalText.ofDyadic d).toRat : Real) = toReal value := by
    simp [toReal_eq, hd]
  rw [hf, parse_eq_run, TextParser.run_of_readText _ _ _ _ (readText_decimal_format _)]
  simp only [convertText, Except.map]
  exact congrArg Except.ok (convertDecimalText_eq_of_nonzero hfmt value hfinite hzero _ hv)

/-- A zero of an IEEE format, with its sign, is the nearest-even conversion of signed zero text. -/
theorem convertDecimalText_zero {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (d : Numerics.Dyadic)
    (hd : toDyadic? value = some d) (hm : d.significand = 0) :
    toDyadic? value = some ⟨signBit value, 0, 0⟩ ∧
      (convertDecimalText fmt .nearest ⟨signBit value, 0, 0⟩).value = value := by
  have hzero := isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hd hm
  have hdx := toDyadic?_eq_zero_of_isZero_eq_true value hzero
  have hv : zero fmt (signBit value) = value := by
    apply eq_of_toDyadic?_eq_some (d := ⟨signBit value, 0, 0⟩) _ hdx
    simp [toDyadic?_zero, signBit_zero,
      FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt]
  refine ⟨hdx, ?_⟩
  simp [convertDecimalText_eq_exact, convertDecimalTextExact, Internal.Directed.roundRat,
    Internal.Directed.roundRatScaled, hv]

/-- Exact decimal output restores every finite IEEE word, including either signed zero. -/
theorem parse_format_exact_of_isFinite {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (hfinite : isFinite value = true) :
    parse fmt (format value (style := .exact)) = .ok value := by
  by_cases hz : toReal value = 0
  · obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
    have hm : d.significand = 0 := by
      apply (Dyadic.toReal_eq_zero_iff d).mp
      simpa [toReal_eq, hd] using hz
    obtain ⟨hdx, hv⟩ := convertDecimalText_zero hfmt value d hd hm
    have hf :
        format value (style := .exact) = (DecimalText.Decimal.mk (signBit value) 0 0).format := by
      simp [format, Internal.Status.format, Internal.Status.formatFinite, exactValue, hdx,
        formatDyadicText, DecimalText.formatDyadic, DecimalText.ofDyadic]
    rw [hf, parse_eq_run, TextParser.run_of_readText _ _ _ _ (readText_decimal_format _)]
    simp only [convertText, Except.map]
    exact congrArg Except.ok hv
  · exact parse_format_exact_of_isFinite_of_nonzero hfmt value hfinite hz

/-- Decimal conversion depends only on the sign and the value of the decimal record. -/
theorem convertDecimalText_congr (fmt : FloatFormat) (mode : IEEERoundingMode)
    {a b : DecimalText.Decimal} (hneg : a.negative = b.negative) (hval : a.toRat = b.toRat) :
    convertDecimalText fmt mode a = convertDecimalText fmt mode b := by
  have hm : (a.significand : Rat) * (10 : Rat) ^ a.exponent =
      (b.significand : Rat) * (10 : Rat) ^ b.exponent := by
    simp only [DecimalText.Decimal.toRat, hneg] at hval
    cases hb : b.negative <;> simp only [hb, Bool.false_eq_true, ite_true, ite_false] at hval
    · exact hval
    · simpa [neg_mul] using hval
  rw [convertDecimalText_eq_exact, convertDecimalText_eq_exact]
  simp only [convertDecimalTextExact, hm, hneg]

namespace Shortest

/-- The displayed characters read back as a record with the sign and value of the displayed one. -/
theorem readText_characters (count : Nat) (record : DecimalText.Decimal) :
    ∃ scanned, readText (String.ofList (characters count record)) = some (.decimal scanned) ∧
      scanned.negative = record.negative ∧ scanned.toRat = record.toRat := by
  unfold characters
  dsimp only
  split
  · exact ⟨record.fixedRepresentation, by simp [readText], by simp, by simp⟩
  · exact ⟨record, by simp [readText], rfl, rfl⟩

/-- The displayed record of a finite IEEE word converts back to the word in nearest-even. -/
theorem convertDecimalText_decimal {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (hfinite : isFinite value = true) {exact : Numerics.Dyadic}
    (hd : toDyadic? value = some exact) :
    (convertDecimalText fmt .nearest (decimal .nearest value exact)).value = value := by
  have hval : ((DecimalText.ofDyadic exact).compact.toRat : Real) = toReal value := by
    simp [toReal_eq, hd]
  have hverified : toReal value ≠ 0 →
      (convertDecimalText fmt .nearest (verified .nearest value exact)).value = value := by
    intro hz
    unfold verified
    dsimp only
    split
    · rename_i candidate _
      split
      · rename_i restored hconvert
        split
        · rename_i h
          rw [Internal.Value.convertText_eq_map] at hconvert
          simp only [convertText, Except.map, Except.ok.injEq] at hconvert
          rw [hconvert, h]
        · exact convertDecimalText_eq_of_nonzero hfmt value hfinite hz _ hval
      · exact convertDecimalText_eq_of_nonzero hfmt value hfinite hz _ hval
    · exact convertDecimalText_eq_of_nonzero hfmt value hfinite hz _ hval
  unfold decimal
  split
  · rename_i hm
    obtain ⟨hdx, hv⟩ := convertDecimalText_zero hfmt value exact hd hm
    have hex : exact = ⟨signBit value, 0, 0⟩ := Option.some.inj (hd.symm.trans hdx)
    subst hex
    exact hv
  · rename_i hm
    have hz : toReal value ≠ 0 := by
      intro hz
      apply hm
      apply (Dyadic.toReal_eq_zero_iff exact).mp
      simpa [toReal_eq, hd] using hz
    dsimp only
    split
    · split
      · exact convertDecimalText_eq_of_nonzero hfmt value hfinite hz _ hval
      · exact hverified hz
    · exact hverified hz

end Shortest

/-- The display of every finite IEEE word reads back as the same word. -/
theorem parse_format_of_isFinite {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (hfinite : isFinite value = true) :
    parse fmt (format value) = .ok value := by
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hf : format value = String.ofList
      (Shortest.characters (Shortest.digits fmt) (Shortest.decimal .nearest value d)) := by
    simp [format, Internal.Status.format, Internal.Status.formatFinite, exactValue, hd]
  obtain ⟨scanned, hread, hneg, hval⟩ :=
    Shortest.readText_characters (Shortest.digits fmt) (Shortest.decimal .nearest value d)
  rw [hf, parse_eq_run, TextParser.run_of_readText _ _ _ _ hread]
  simp only [convertText, Except.map]
  rw [convertDecimalText_congr fmt .nearest hneg hval]
  exact congrArg Except.ok (Shortest.convertDecimalText_decimal hfmt value hfinite hd)

/-- `toString` of every finite IEEE word reads back as the same word. -/
theorem parse_toString_of_isFinite {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (hfinite : isFinite value = true) :
    parse fmt (toString value) = .ok value :=
  parse_format_of_isFinite hfmt value hfinite

end FloatLib.Floats.Formats.BinaryInterchange.Model
