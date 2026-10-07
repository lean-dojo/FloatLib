/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Shared oracle input parsing

The SMT and TestFloat runners accept the same hexadecimal digits and whitespace-delimited fields.
-/

@[expose] public section

namespace FloatLibTests.Oracle.Parsing

/-- Value of an ASCII hexadecimal digit. -/
def hexDigit? (character : Char) : Option Nat :=
  let code := character.toNat
  if 48 ≤ code ∧ code ≤ 57 then
    some (code - 48)
  else if 65 ≤ code ∧ code ≤ 70 then
    some (code - 55)
  else if 97 ≤ code ∧ code ≤ 102 then
    some (code - 87)
  else
    none

/-- Read an ASCII hexadecimal field without a prefix. -/
def parseHex? (text : String) : Option Nat :=
  text.toList.foldlM
    (fun value character => do
      let digit ← hexDigit? character
      pure (16 * value + digit))
    0

/-- Split an input row into its nonempty whitespace-delimited fields. -/
def fields (line : String) : List String :=
  (line.trimAscii.copy.splitToList (fun character => character.isWhitespace)).filter
    (fun field => !field.isEmpty)

end FloatLibTests.Oracle.Parsing
