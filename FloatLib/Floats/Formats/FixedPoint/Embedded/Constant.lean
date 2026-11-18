/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Limits
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Text

/-!
# N1169 fixed-point constants

N1169, ISO/IEC TR 18037:2006(E), §4.1.5 and C 6.4.4.2a, inherits the
translation rules of C99 6.4.4.2 (read in N1256). Decimal translation permits
a nearest value or either immediate neighbor. Hexadecimal translation follows
the supplied adjacent rounding mode. The exact fract constant one denotes the
type's maximum; all other exact source values must be in range.

Parsing covers all twelve case-insensitive suffixes. A sign belongs to a
separate unary expression, and hexadecimal constants require a binary exponent.
This module models a complete constant and its value, not C preprocessing.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics

namespace Constant

/-- Complete numeric constant after its suffix has selected a primary fixed type. -/
structure Literal where
  /-- Original spelling, available to implementation-defined translation choices. -/
  spelling : String
  /-- Type selected by the suffix. -/
  type : CType
  /-- Exact positional value before translation rounding. -/
  value : ℚ
  /-- Hexadecimal and decimal constants have different translation requirements. -/
  hexadecimal : Bool

/-- Remove the optional length letter from a reversed constant body and suffix. -/
def splitLength : List Char → Length × List Char
  | character :: rest =>
      if character.toLower = 'h' then (.short, rest)
      else if character.toLower = 'l' then (.long, rest)
      else (.default, character :: rest)
  | [] => (.default, [])

/-- Remove the optional unsigned marker from the reversed suffix. -/
def splitSigned : List Char → Bool × List Char
  | character :: rest =>
      if character.toLower = 'u' then (false, rest) else (true, character :: rest)
  | [] => (true, [])

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.5: all twelve suffixes, leaving the complete numeric
    body. -/
def splitSuffix (characters : List Char) : Option (CType × List Char) := do
  let qualifier :: rest := characters.reverse | none
  let kind ← if qualifier.toLower = 'r' then some Kind.fract
    else if qualifier.toLower = 'k' then some Kind.accum else none
  let (length, rest) := splitLength rest
  let (signed, rest) := splitSigned rest
  return (⟨kind, length, signed, false⟩, rest.reverse)

/-- Parse one complete C constant; unary signs, suffix-free subjects and partial parses fail. -/
def parse (text : String) : Option Literal := do
  let (type, body) ← splitSuffix text.toList
  if body.head? = some '+' ∨ body.head? = some '-' then none else
    let hexadecimal := match body with
      | '0' :: character :: _ => character.toLower == 'x'
      | _ => false
    let value ← if hexadecimal then
      (HexText.parseCharacters body).map Numerics.Dyadic.toRat
    else (DecimalText.parseCharacters body).map DecimalText.Decimal.toRat
    return ⟨text, type, value, hexadecimal⟩

/-- Translation choices from WG14 N1169 (2006 TR 18037 draft), C clause 6.4.4.2a and inherited
    C99 6.4.4.2 paragraph 3. -/
structure Policy where
  /-- The specified hexadecimal rounding mode, represented by its adjacent integer choice. -/
  hexadecimal : Rounding
  /-- Nearest decimal translation before an optional neighboring-value choice. -/
  nearest : NearestRounding
  /-- A decimal choice may depend on the destination and the whole source constant. -/
  decimalStep : Format → Literal → Int
  /-- Only the nearest value and its immediate neighbors are admitted. -/
  decimalStep_bound (format : Format) (literal : Literal) : |decimalStep format literal| ≤ 1

/-- Nearest-even translation for both bases, with no optional decimal displacement. -/
def Policy.even : Policy where
  hexadecimal := NearestRounding.even.toRounding
  nearest := NearestRounding.even
  decimalStep := fun _ _ ↦ 0
  decimalStep_bound := by intros; decide

/-- A fixed permitted decimal neighbor, retaining the supplied hexadecimal mode. -/
def Policy.neighbor (hexadecimal : Rounding) (nearest : NearestRounding)
    (upper : Bool) : Policy where
  hexadecimal := hexadecimal
  nearest := nearest
  decimalStep := fun _ _ ↦ if upper then 1 else -1
  decimalStep_bound := by intros; cases upper <;> decide

/-- Rounded coefficient, with decimal-only displacement and endpoint clipping. -/
def rounded (layout : Layout) (policy : Policy) (literal : Literal) :
    (layout.format literal.type).Code :=
  let format := layout.format literal.type
  let scaled := literal.value / format.quantizer.scale
  if literal.hexadecimal then format.clamp (policy.hexadecimal.run scaled)
  else Format.move (format.clamp (policy.nearest.run scaled))
    (policy.decimalStep format literal)

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.5: exact range constraint, with the separate
    fract-one exception. -/
def translate (layout : Layout) (policy : Policy) (literal : Literal) :
    Option (layout.format literal.type).Code :=
  if literal.type.kind = .fract ∧ literal.value = 1 then
    some (layout.format literal.type).maximum
  else if (layout.format literal.type).SourceInRange literal.value then
    some (rounded layout policy literal)
  else none

/-- The exact fract-one exception is independent of every translation policy. -/
theorem translate_fract_one (layout : Layout) (policy : Policy) (literal : Literal)
    (hkind : literal.type.kind = .fract) (hvalue : literal.value = 1) :
    translate layout policy literal = some (layout.format literal.type).maximum := by
  simp [translate, hkind, hvalue]

/-- A rejected constant violates both the ordinary range constraint and the fract-one exception. -/
theorem translate_eq_none_iff (layout : Layout) (policy : Policy) (literal : Literal) :
    translate layout policy literal = none ↔
      ¬ (literal.type.kind = .fract ∧ literal.value = 1) ∧
        ¬ (layout.format literal.type).SourceInRange literal.value := by
  by_cases hunit : literal.type.kind = .fract ∧ literal.value = 1
  · simp [translate, hunit]
  · by_cases hrange : (layout.format literal.type).SourceInRange literal.value <;>
      simp [translate, hunit, hrange]

/-- A valid hexadecimal constant has exactly the coefficient selected by its rounding mode. -/
theorem rounded_hexadecimal (layout : Layout) (policy : Policy) (literal : Literal)
    (hhex : literal.hexadecimal = true)
    (hrange : (layout.format literal.type).SourceInRange literal.value) :
    bitsfx (rounded layout policy literal) =
      policy.hexadecimal.run (literal.value / (layout.format literal.type).quantizer.scale) := by
  have h := policy.hexadecimal.in_range (layout.format literal.type).integerFormat.range hrange
  simp only [rounded, hhex, ↓reduceIte, bitsfx, Format.clamp]
  exact (layout.format literal.type).quantizer.clampCode_eq_self h.1 h.2

/-- A valid decimal result is the nearest coefficient or an immediate stored neighbor. -/
theorem rounded_decimal_distance (layout : Layout) (policy : Policy) (literal : Literal)
    (hdecimal : literal.hexadecimal = false)
    (hrange : (layout.format literal.type).SourceInRange literal.value) :
    |bitsfx (rounded layout policy literal) -
      policy.nearest.run (literal.value / (layout.format literal.type).quantizer.scale)| ≤ 1 := by
  let format := layout.format literal.type
  have h := policy.nearest.toRounding.in_range format.integerFormat.range hrange
  have hbase : bitsfx (format.clamp (policy.nearest.run
      (literal.value / format.quantizer.scale))) =
      policy.nearest.run (literal.value / format.quantizer.scale) :=
    format.quantizer.clampCode_eq_self h.1 h.2
  have hmove := Format.move_distance (format.clamp (policy.nearest.run
    (literal.value / format.quantizer.scale))) (policy.decimalStep format literal)
  rw [hbase] at hmove
  simpa only [rounded, hdecimal, Bool.false_eq_true, ↓reduceIte] using
    hmove.trans (policy.decimalStep_bound format literal)

end Constant

end FloatLib.Floats.Formats.FixedPoint.Embedded
