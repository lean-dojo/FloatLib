/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.HexText.Runtime
public import FloatLib.Numerics.Exact.DecimalText.Grammar

/-!
# Character grammar for hexadecimal external sequences

IEEE 754 §5.12.3 requires the `0x` prefix and a binary exponent.
These lemmas expose that syntax independently of the decoded dyadic value.
-/

@[expose] public section

namespace FloatLib.Numerics.HexText

/-- The mandatory binary exponent consists of a `p` or `P` and a signed decimal integer. -/
theorem parseExponent_cons_isSome (c : Char) (rest : List Char) :
    (parseExponent (c :: rest)).isSome ↔
      (c = 'p' ∨ c = 'P') ∧ (DecimalText.parseInteger rest).isSome := by
  by_cases hp : c = 'p'
  · subst c
    simp [parseExponent]
  · by_cases hP : c = 'P'
    · subst c
      simp [parseExponent]
    · simp [parseExponent, hp, hP]

/-- Binary exponent markers cannot be consumed as hexadecimal digits or a radix point. -/
theorem parseExponent_head (characters : List Char)
    (hparse : (parseExponent characters).isSome) :
    ∀ c ∈ characters.head?, digitValue? c = none ∧ c ≠ '.' := by
  cases characters with
  | nil => simp
  | cons c rest =>
      rcases ((parseExponent_cons_isSome c rest).mp hparse).1 with rfl | rfl <;>
        simp [digitValue?, DecimalText.digitValue?]

/-- Hexadecimal acceptance depends on the unsigned magnitude after its sign and `0x` prefix. -/
theorem parseCharacters_isSome (characters : List Char) :
    (parseCharacters characters).isSome =
      match (DecimalText.splitSign characters).2 with
      | '0' :: 'x' :: magnitude | '0' :: 'X' :: magnitude =>
          (RadixText.parseMagnitude magnitude 16 digitValue? parseExponent 4).isSome
      | _ => false := by
  unfold parseCharacters
  cases DecimalText.splitSign characters
  simp only
  split <;> simp [Option.isSome_bind]

end FloatLib.Numerics.HexText
