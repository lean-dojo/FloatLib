/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Roundoff
public import FloatLib.Tactic.Roundoff

/-! N1169 C-locale subject grammar, maximal consumption and conversion outcomes.

WG14 N1169 (2006 TR 18037 draft), §4.2, C clauses 7.18a.6.8 and 7.19.6.2. -/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.EmbeddedText

open FloatLib.Numerics
open FloatLib.Floats.Formats.FixedPoint.Embedded

example {α : Type} (parse : List Char → Option α) (input : List Char)
    (length : Nat) (value : α) (h : parse (input.take length) = some value)
    (hbound : length ≤ input.length) :
    length ≤ RadixText.prefixLength parse input :=
  RadixText.le_prefixLength parse input length value hbound h

example (text : String) (endptr : Nat) (value : ℚ)
    (h : Text.scan text = some (endptr, value)) :
    ∃ length, length = RadixText.prefixLength Text.subject (Text.subjectInput text) ∧
      Text.subject ((Text.subjectInput text).take length) = some value ∧
      endptr = text.toList.length - (Text.subjectInput text).length + length :=
  (Text.scan_eq_some_iff text endptr value).mp h

example (text : String) (h : Text.scan text = none) :
    ∀ length ≤ (Text.subjectInput text).length,
      Text.subject ((Text.subjectInput text).take length) = none :=
  (Text.scan_eq_none_iff text).mp h

example (format : Format) (rounding : Rounding) (text : String)
    (h : Text.scan text = none) :
    (Text.convert format rounding text).endptr = 0 := by
  rw [Text.convert_of_none format rounding text h]

example (format : Format) (rounding : Rounding) (text : String)
    (endptr : Nat) (value : ℚ) (h : Text.scan text = some (endptr, value)) :
    (Text.convert format rounding text).rangeError = true ↔ ¬ format.SourceInRange value :=
  (Text.convert_outcomes format rounding text endptr value h).2

example (format : Format) (rounding : Rounding) (text : String)
    (endptr : Nat) (value : ℚ) (h : Text.scan text = some (endptr, value)) :
    MixedError (-(Format.decode (Text.convert format rounding text).value : ℝ))
      (-(value : ℝ)) 0
      ((format.quantizer.scale * (1 + format.clippingError value) : ℚ) : ℝ) := by
  have hbound := Text.convert_mixedError format rounding text endptr value h
  roundoff

example : Text.subject [] = none := Text.subject_nil
example : Text.scan " \t-0x1.8p+2tail" = some (11, -6) := by decide +kernel
example : Text.scan "1e+" = some (1, 1) := by decide +kernel
example : Text.scan "0x.p+" = some (1, 0) := by decide +kernel
example : Text.scan "+.5x" = some (3, 1 / 2) := by decide +kernel
example : Text.scan "+." = none := by decide +kernel
example : Text.scan "\t\n-INF" = none := by decide +kernel
example : Text.scan "nan(1)" = none := by decide +kernel
example : Text.scan " \r\t\n\x0b\x0c" = none := by decide +kernel
example : Text.scan "12\x00.5" = some (2, 12) := by decide +kernel
example : Text.scan "0x1.f!" = some (5, 31 / 16) := by decide +kernel

private def observed (result : Text.Result (_Fract true 3)) : Int × Nat × Bool :=
  (bitsfx result.value, result.endptr, result.rangeError)

example : observed (Text.convert (_Fract true 3) Rounding.floor "0.9!") =
    (7, 3, true) := by decide +kernel
example : observed (Text.convert (_Fract true 3) Rounding.ceil "-2") =
    (-8, 2, true) := by decide +kernel
example : observed (Text.convert (_Fract true 3) Rounding.ceil "x") =
    (0, 0, false) := by decide +kernel
example : (strtofxhr Layout.example Rounding.floor "0.5").endptr = 3 := by decide +kernel
example : bitsfx (strtofxulk Layout.example Rounding.floor "2").value =
    8589934592 := by decide +kernel

end FloatLibTests.Conformance.Formats.EmbeddedText
