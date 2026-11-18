/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Conversion
public import FloatLib.Numerics.Exact.HexText.Runtime
public import FloatLib.Numerics.Exact.RadixText.Prefix

/-!
# N1169 numeric text conversion

WG14 N1169 (2006 TR 18037 draft), C clauses 7.18a.6.8. The C-locale grammar reuses
the exact decimal and hexadecimal parsers. A proved greatest-prefix search
implements maximal subject consumption, including fallback before an incomplete
exponent. Hexadecimal subjects may omit their binary exponent.

The result records the stored value, `endptr` offset and `ERANGE` condition.
No subject returns zero and offset zero. A subject is rounded with the selected
implementation's adjacent rounder and saturated; its exact source range sets
the range-error flag. This is a value model, without C memory or errno mutation.
Consumed characters are ASCII; the offset counts those characters and bytes.
Other locale-specific grammars are outside this C-locale instance.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics

namespace Text

/-- The six white-space characters of the C locale. -/
def isSpace (character : Char) : Bool :=
  character == ' ' || character == '\t' || character == '\n' ||
    character == '\r' || character == '\x0b' || character == '\x0c'

/-- Complete N1169 subject grammar, without surrounding whitespace or type suffix.
The inherited hexadecimal parser accepts a binary exponent; appending `p0` admits
precisely its optional-exponent form. Decimal parsing already permits no exponent.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.2, C clause 7.18a.6.8.
-/
def subject (characters : List Char) : Option ℚ :=
  (DecimalText.parseCharacters characters).map DecimalText.Decimal.toRat <|>
    ((HexText.parseCharacters characters <|>
      HexText.parseCharacters (characters ++ ['p', '0'])).map Numerics.Dyadic.toRat)

/-- An empty subject never converts. -/
theorem subject_nil : subject [] = none := rfl

/-- Initial whitespace is excluded from the subject grammar. -/
def subjectInput (text : String) : List Char :=
  text.toList.dropWhile isSpace

/-- Exact rational value and end position of the longest accepted subject. -/
def scan (text : String) : Option (Nat × ℚ) :=
  (RadixText.parsePrefix subject (subjectInput text)).map fun (length, value) ↦
    (text.toList.length - (subjectInput text).length + length, value)

/-- Every successful scan is the longest complete parse after initial whitespace. -/
theorem scan_eq_some_iff (text : String) (endptr : Nat) (value : ℚ) :
    scan text = some (endptr, value) ↔
      ∃ length, length = RadixText.prefixLength subject (subjectInput text) ∧
        subject ((subjectInput text).take length) = some value ∧
        endptr = text.toList.length - (subjectInput text).length + length := by
  simp only [scan, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq,
    RadixText.parsePrefix_eq_some_iff]
  constructor
  · rintro ⟨length, parsed, ⟨hlength, hparse⟩, hend, rfl⟩
    exact ⟨length, hlength, hparse, hend.symm⟩
  · rintro ⟨length, hlength, hparse, rfl⟩
    exact ⟨length, value, ⟨hlength, hparse⟩, rfl, rfl⟩

/-- A failed scan means that every possible subject prefix is rejected. -/
theorem scan_eq_none_iff (text : String) :
    scan text = none ↔ ∀ length ≤ (subjectInput text).length,
      subject ((subjectInput text).take length) = none := by
  simp only [scan, Option.map_eq_none_iff, RadixText.parsePrefix_eq_none_iff]

/-- Stored numeric-conversion result and the observable C end/range outcomes. -/
structure Result (format : Format) where
  /-- Saturated stored value, zero if no subject was converted. -/
  value : format.Code
  /-- Offset to the first unconsumed character, zero when no conversion occurred. -/
  endptr : Nat
  /-- Whether the exact subject value was outside the representable interval. -/
  rangeError : Bool

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.8: rounded, saturated conversion with
    explicit end and range data. -/
def convert (format : Format) (rounding : Rounding) (text : String) : Result format :=
  match scan text with
  | none => ⟨format.clamp 0, 0, false⟩
  | some (endptr, value) =>
    ⟨format.clamp (rounding.run (value / format.quantizer.scale)),
      endptr, decide (¬ format.SourceInRange value)⟩

/-- No accepted subject returns zero and leaves the original end pointer. -/
theorem convert_of_none (format : Format) (rounding : Rounding) (text : String)
    (h : scan text = none) :
    convert format rounding text = ⟨format.clamp 0, 0, false⟩ := by
  simp [convert, h]

/-- Every successful text value is exactly the shared saturated numeric conversion. -/
theorem convert_value_spec (format : Format) (rounding : Rounding) (text : String)
    (endptr : Nat) (value : ℚ) (h : scan text = some (endptr, value)) :
    Embedded.convert format rounding .SAT value = some (convert format rounding text).value := by
  simp [convert, h, Embedded.convert, Format.finish, Format.Saturates]

/-- End position and the exact-source range flag are preserved by numeric conversion. -/
theorem convert_outcomes (format : Format) (rounding : Rounding) (text : String)
    (endptr : Nat) (value : ℚ) (h : scan text = some (endptr, value)) :
    (convert format rounding text).endptr = endptr ∧
      ((convert format rounding text).rangeError = true ↔ ¬ format.SourceInRange value) := by
  simp [convert, h]

end Text

end FloatLib.Floats.Formats.FixedPoint.Embedded
