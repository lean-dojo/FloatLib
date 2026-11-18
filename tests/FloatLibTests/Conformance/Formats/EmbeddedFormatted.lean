/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Roundoff
public import FloatLib.Tactic.Roundoff
import all Mathlib.Data.Nat.Digits.Defs

/-! WG14 N1169 (2006 TR 18037 draft), C clause 7.19.6.1–2: decimal presentation, item consumption
and conversion outcomes. -/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.EmbeddedFormatted

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat
open FloatLib.Floats.Formats.FixedPoint.Embedded

example (coefficient exponent : Int) (negativeZero : Bool) :
    (DecimalText.Decimal.ofScaledInt coefficient exponent negativeZero).toRat =
      (coefficient : ℚ) * (10 : ℚ) ^ exponent :=
  DecimalText.Decimal.ofScaledInt_toRat coefficient exponent negativeZero

example (rounding : Rounding) (value : ℚ) (places : Nat) :
    DecimalText.parse (Formatted.decimal rounding value places).formatFixed =
      some ((rounding.run (value * (10 : ℚ) ^ places) : ℚ) / (10 : ℚ) ^ places) :=
  Formatted.parse_decimal_fixed rounding value places

example (rounding : NearestRounding) (value : ℚ) (places : Nat) :
    |(Formatted.decimal rounding.toRounding value places).toRat - value| ≤
      (1 / 2) / (10 : ℚ) ^ places :=
  Formatted.decimal_error_le_half rounding value places

example (signed : Bool) (options : Formatted.PrintOptions) (value : DecimalText.Decimal) :
    options.width.natAbs ≤ (Formatted.fieldCharacters signed options value).length :=
  Formatted.fieldCharacters_length signed options value

example (characters : List Char) (h : Formatted.item characters = some ()) :
    ∃ suffix : List Char, (Text.subject (characters ++ suffix)).isSome :=
  Formatted.item_has_completion characters h

example (width : Option ℕ+) (text : String) (length : Nat)
    (hbound : length ≤ (Formatted.input width text).length)
    (hcomplete : ∃ suffix,
      (Text.subject ((Formatted.input width text).take length ++ suffix)).isSome) :
    length ≤ RadixText.prefixLength Formatted.item (Formatted.input width text) :=
  Formatted.le_item_length_of_completion width text length hbound hcomplete

example (format : Format) (rounding : Rounding) (width : Option ℕ+) (text : String) :
    (Formatted.scan format rounding width text).consumed =
      text.toList.length - (Text.subjectInput text).length +
        RadixText.prefixLength Formatted.item (Formatted.input width text) :=
  Formatted.scan_consumed format rounding width text

example (format : Format) (rounding : Rounding) (width : Option ℕ+) (text : String)
    (hpos : RadixText.prefixLength Formatted.item (Formatted.input width text) ≠ 0)
    (hparse : Text.subject ((Formatted.input width text).take
      (RadixText.prefixLength Formatted.item (Formatted.input width text))) = none) :
    (Formatted.scan format rounding width text).status = .matchingFailure ∧
      (Formatted.scan format rounding width text).value = none :=
  Formatted.scan_incomplete format rounding width text hpos hparse

example (format : Format) (rounding : Rounding) (value : ℚ) (result : format.Code) :
    Formatted.scanValue format rounding value = some result ↔
      bitsfx result = rounding.run (value / format.quantizer.scale) :=
  Formatted.scanValue_eq_some_iff format rounding value result

example (format : Format) (rounding : Rounding) (value : ℚ) :
    Formatted.scanValue format rounding value = none ↔
      ¬ format.integerFormat.InRange (rounding.run (value / format.quantizer.scale)) :=
  Formatted.scanValue_eq_none_iff format rounding value

example (format : Format) (rounding : Rounding) (width : Option ℕ+) (text : String)
    (result : format.Code) :
    (Formatted.scan format rounding width text).value = some result ↔
      RadixText.prefixLength Formatted.item (Formatted.input width text) ≠ 0 ∧
        ∃ exact, Text.subject ((Formatted.input width text).take
          (RadixText.prefixLength Formatted.item (Formatted.input width text))) = some exact ∧
            Formatted.scanValue format rounding exact = some result :=
  Formatted.scan_value_eq_some_iff format rounding width text result

example (rounding : Rounding) (value : ℚ) (places : Nat) :
    MixedError (-((Formatted.decimal rounding value places).toRat : ℝ)) (-(value : ℝ)) 0
      ((1 / (10 : ℚ) ^ places : ℚ) : ℝ) := by
  have h := Formatted.decimal_mixedError rounding value places
  roundoff

example (format : Format) (rounding : Rounding) (value : ℚ) (result : format.Code)
    (hprimary : format.saturating = false)
    (hresult : Formatted.scanValue format rounding value = some result) :
    MixedError (Format.decode result : ℝ) (value : ℝ) 0
      ((format.quantizer.scale * (1 + format.clippingError value) : ℚ) : ℝ) :=
  Formatted.scanValue_mixedError format rounding value result hprimary hresult

private def fract : Format := _Fract true 3
private def print (coefficient : Int) (options : Formatted.PrintOptions) : String :=
  Formatted.formatValue NearestRounding.even.toRounding options (fract.clamp coefficient)

local macro "print_decide" : tactic =>
  `(tactic| (apply String.toList_injective
             simp only [print, Formatted.formatValue, String.toList_ofList]
             decide +kernel))

example : print 4 {} = "0.500000" := by print_decide
example : print 1 { precision := some 2 } = "0.12" := by print_decide
example : print (-1) { precision := some 0 } = "-0" := by print_decide
example : print 4 { precision := some 0, alternate := true } = "0." := by print_decide
example : print 4 { precision := some 2, width := 8, zero := true, plus := true } =
    "+0000.50" := by print_decide
example : print 4 {
    precision := some 2, width := 8, zero := true, plus := true
    left := true, space := true } = "+0.50   " := by print_decide
example : print 4 { precision := some 2, width := -8, zero := true } =
    "0.50    " := by print_decide
example : print 4 { precision := some (-1) } = "0.500000" := by print_decide

private def observed (result : Formatted.ScanResult fract) :
    Nat × Formatted.ScanStatus × Option Int :=
  (result.consumed, result.status, result.value.map bitsfx)

example : observed (Formatted.scan fract .floor none "1e+") = (3, .matchingFailure, none) :=
  by decide +kernel
example : observed (Formatted.scan fract .floor none "0x.") = (3, .matchingFailure, none) :=
  by decide +kernel
example : observed (Formatted.scan fract .floor none " \t") = (2, .inputFailure, none) :=
  by decide +kernel
example : observed (Formatted.scan fract .floor none " x") = (1, .matchingFailure, none) :=
  by decide +kernel
example : observed (Formatted.scan fract .floor none "0.9!") = (3, .success, some 7) :=
  by decide +kernel
example : observed (Formatted.scan fract .ceil none "0.9!") = (3, .undefined, none) :=
  by decide +kernel
example : observed (Formatted.scan fract .floor (some 2) ".5e+") = (2, .success, some 4) :=
  by decide +kernel
example : observed (Formatted.scan fract .floor (some 3) ".5e+") = (3, .matchingFailure, none) :=
  by decide +kernel

example : (Formatted.Specifier.R.type .long).signed = false ∧
    (Formatted.Specifier.k.type .short).kind = .accum ∧
    (Formatted.Specifier.K.type .default).signed = false ∧
    (Formatted.Specifier.r.type .short).length = .short := by decide +kernel

example : Backend.Certified (@Formatted.fprintf) :=
  compiled_reference% (@Formatted.fprintf) using
    { name := "fixed-point reference", kind := .generic, steadyCost := 1 }
example : Backend.Certified (@Formatted.fscanf) :=
  compiled_reference% (@Formatted.fscanf) using
    { name := "fixed-point reference", kind := .generic, steadyCost := 1 }
example : Backend.Certified (@Formatted.decimal) :=
  compiled_reference% (@Formatted.decimal) using
    { name := "fixed-point reference", kind := .generic, steadyCost := 1 }
example : Backend.Certified (@Formatted.formatValue) :=
  compiled_reference% (@Formatted.formatValue) using
    { name := "fixed-point reference", kind := .generic, steadyCost := 1 }
example : Backend.Certified (@Formatted.scan) :=
  compiled_reference% (@Formatted.scan) using
    { name := "fixed-point reference", kind := .generic, steadyCost := 1 }
example : Backend.Certified (@Formatted.scanValue) :=
  compiled_reference% (@Formatted.scanValue) using
    { name := "fixed-point reference", kind := .generic, steadyCost := 1 }

end FloatLibTests.Conformance.Formats.EmbeddedFormatted
