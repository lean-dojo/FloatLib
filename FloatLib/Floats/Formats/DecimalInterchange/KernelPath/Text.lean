/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Formatting.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Conversion
public import FloatLib.Numerics.Kernel.Text

/-!
# Kernel path of the decimal conversions to and from character sequences

IEEE 754-2019 §5.12 `convertToDecimalCharacter` and `convertFromDecimalCharacter` are
`Formatting.formatExact` and `Formatting.parse` on a decimal datum. Both work on strings, which
Lean's kernel evaluates through their UTF-8 bytes.

`characters x` lists the characters of the exact spelling of a datum, with the digits written
by the loop of `Numerics.Kernel.Text`, and `formatExact_eq` states `Formatting.formatExact` as
`String.ofList` of that list. `parseCharacters f mode characters` reads a list of characters
and rounds a finite datum with a moderate exponent by `KernelPath.project`, and `parse_eq`
states `Formatting.parse` as `parseCharacters` on the characters of its string. With the rules
of `Numerics.Kernel.Text` a datum that is written and read back never becomes a string. Both
rules hold for every format, rounding direction, datum and string.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

open FloatLib.Numerics

/--
Characters of the exact spelling of a datum (`characters_eq`): its coefficient and quantum
exponent, an infinity, or a NaN with its payload.
-/
def characters (x : Datum) : List Char :=
  Datum.casesOn (motive := fun _ => List Char) x
    (fun negative coefficient quantum =>
      Kernel.Text.decimalCharacters ⟨negative, coefficient, quantum⟩)
    (fun negative => Kernel.Text.infinityCharacters negative)
    (fun negative signaling payload => Kernel.Text.nanCharacters negative signaling payload)

/--
Kernel form of `Formatting.convert` (`convert_eq`): a finite datum with a moderate exponent is
projected into the format at its own exponent. Every other case is the specification.
-/
def convert (f : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun s c q =>
      Bool.casesOn (motive := fun _ => Outcome) (moderate q)
        (Formatting.convert f mode x) (project f mode s c q))
    (fun _ => Formatting.convert f mode x) (fun _ _ _ => Formatting.convert f mode x)

/--
Parse an unbounded decimal datum (`readCharacters_eq`): the reference
`Formatting.readCharacters` with the digits of the coefficient read off the character codes.
-/
def readCharacters (characters : List Char) : Option Datum :=
  match Kernel.Text.parseDecimal characters with
  | some value => some (.finite value.negative value.significand value.exponent)
  | none =>
      let (negative, rest) := DecimalText.splitSign characters
      Formatting.parseSpecial negative rest

/--
Kernel form of `Formatting.parse` on the characters of its string (`parse_eq`): the characters
are scanned by `readCharacters` and the datum is rounded by `convert`.
-/
def parseCharacters (f : Format) (mode : RoundingMode) (characters : List Char) : Outcome :=
  match readCharacters characters with
  | some value => convert f mode value
  | none => Formatting.invalidText

/-- `characters` lists the characters of the reference spelling. -/
theorem characters_eq (x : Datum) : characters x = Formatting.characters x := by
  rcases x with ⟨negative, coefficient, quantum⟩ | negative | ⟨negative, signaling, payload⟩
  · exact Kernel.Text.decimalCharacters_eq _
  · exact Kernel.Text.infinityCharacters_eq _
  · exact Kernel.Text.nanCharacters_eq _ _ _

/-- `readCharacters` is the scan of the reference. -/
theorem readCharacters_eq (characters : List Char) :
    readCharacters characters = Formatting.readCharacters characters := by
  unfold readCharacters Formatting.readCharacters
  rw [Kernel.Text.parseDecimal_eq]
  rfl

/-- `convert` is `Formatting.convert`, for every format, rounding direction and datum. -/
theorem convert_eq (f : Format) (mode : RoundingMode) (x : Datum) :
    convert f mode x = Formatting.convert f mode x := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> try rfl
  change Bool.casesOn (motive := fun _ => Outcome) (moderate q)
    (Formatting.convert f mode (.finite s c q)) (project f mode s c q) = _
  cases moderate q
  · rfl
  · change project f mode s c q = projectScaled f mode s c q q
    rw [project_eq, projectScaled_eq]

/--
The exact text of a decimal datum is the list of its characters, for every datum.
-/
@[kernel_optimize] theorem formatExact_eq (x : Datum) :
    Formatting.formatExact x = String.ofList (characters x) := by
  rw [characters_eq]
  rfl

/--
Reading a decimal datum from a string is the kernel form on the characters of the string, for
every format, rounding direction and string.
-/
@[kernel_optimize] theorem parse_eq (f : Format) (mode : RoundingMode) (text : String) :
    Formatting.parse f mode text = parseCharacters f mode text.toList := by
  unfold parseCharacters Formatting.parse Formatting.read
  rw [readCharacters_eq]
  cases Formatting.readCharacters text.toList with
  | none => rfl
  | some value => exact (convert_eq f mode value).symm

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath
