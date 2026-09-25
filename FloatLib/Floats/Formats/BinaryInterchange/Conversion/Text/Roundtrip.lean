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
public import FloatLib.Numerics.Exact.HexText.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable

/-! # Exact binary character round trips

The string scanner recovers the exact coefficient and exponent. For conventional IEEE
descriptors, finite hexadecimal output round-trips in every supported rounding mode; finite
decimal output round-trips under nearest-even input. Both results include signed zero.
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
theorem parse_formatHex_of_isFinite {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (mode : IEEERoundingMode) (value : Model fmt) (hfinite : isFinite value = true) :
    parse fmt (formatHex value) (rounding := mode) = .ok value := by
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hf : formatHex value = HexText.format d := by
    simp [formatHex, formatWithStatus, exactValue, hd, formatDyadicText]
  rw [hf, parse_eq_run, TextParser.run_of_readText _ _ _ _ (readText_hex_format d)]
  simp [convertText, convertDyadicText, Except.map,
    roundDyadicWithRounding_toDyadic? hfmt mode hd]

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

/-- Decimal conversion of an exact finite nonzero value restores its complete IEEE word. -/
theorem convertDecimalText_eq_of_nonzero {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (hfinite : isFinite value = true) (hzero : toReal value ≠ 0)
    (textValue : DecimalText.Decimal) (hexact : (textValue.toRat : Real) = toReal value) :
    (convertDecimalText fmt .nearestEven textValue).value = value := by
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
theorem parse_formatDecimal_of_isFinite_of_nonzero {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (hfinite : isFinite value = true) (hzero : toReal value ≠ 0) :
    parse fmt (formatDecimal value) = .ok value := by
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hf : formatDecimal value = (DecimalText.ofDyadic d).format := by
    simp [formatDecimal, formatWithStatus, exactValue, hd, formatDyadicText,
      DecimalText.formatDyadic]
  have hv : ((DecimalText.ofDyadic d).toRat : Real) = toReal value := by
    simp [toReal_eq, hd]
  rw [hf, parse_eq_run, TextParser.run_of_readText _ _ _ _ (readText_decimal_format _)]
  simp only [convertText, Except.map]
  exact congrArg Except.ok (convertDecimalText_eq_of_nonzero hfmt value hfinite hzero _ hv)

/-- Exact decimal output restores every finite IEEE word, including either signed zero. -/
theorem parse_formatDecimal_of_isFinite {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (value : Model fmt) (hfinite : isFinite value = true) :
    parse fmt (formatDecimal value) = .ok value := by
  by_cases hz : toReal value = 0
  · obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
    have hm : d.significand = 0 := by
      apply (Dyadic.toReal_eq_zero_iff d).mp
      simpa [toReal_eq, hd] using hz
    have hzero := isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hd hm
    have hdx := toDyadic?_eq_zero_of_isZero_eq_true value hzero
    have hv : zero fmt (signBit value) = value := by
      apply eq_of_toDyadic?_eq_some (d := ⟨signBit value, 0, 0⟩) _ hdx
      simp [toDyadic?_zero, signBit_zero,
        FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt]
    have hf :
        formatDecimal value = (DecimalText.Decimal.mk (signBit value) 0 0).format := by
      simp [formatDecimal, formatWithStatus, exactValue, hdx, formatDyadicText,
        DecimalText.formatDyadic, DecimalText.ofDyadic]
    rw [hf, parse_eq_run, TextParser.run_of_readText _ _ _ _ (readText_decimal_format _)]
    simp [convertText, convertDecimalText_eq_exact, convertDecimalTextExact,
      roundRatWithRounding, roundRatWithRoundingScaled, Except.map, hv]
  · exact parse_formatDecimal_of_isFinite_of_nonzero hfmt value hfinite hz

end FloatLib.Floats.Formats.BinaryInterchange.Model
