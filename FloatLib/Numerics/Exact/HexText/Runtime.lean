/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Exact.DecimalText.Runtime
public import FloatLib.Numerics.Exact.RadixText.Precision
public import FloatLib.Numerics.Exact.RadixText.Runtime

/-!
# Exact hexadecimal external character sequences

IEEE 754 §5.12.3 uses a hexadecimal significand and a mandatory decimal binary
exponent: `-0x1.ap+3` denotes `-13`. The positional scanner, signs and exponent
integer parser are shared with decimal input. No host floating point is used.
-/

@[expose] public section

namespace FloatLib.Numerics.HexText

/-- Decode an ASCII hexadecimal digit, accepting either letter case. -/
def digitValue? (character : Char) : Option Nat :=
  match DecimalText.digitValue? character with
  | some digit => some digit
  | none =>
      if 'a' ≤ character ∧ character ≤ 'f' then some (character.toNat - 'a'.toNat + 10)
      else if 'A' ≤ character ∧ character ≤ 'F' then
        some (character.toNat - 'A'.toNat + 10)
      else none

/-- A hexadecimal exponent must have a `p` marker and a signed decimal integer. -/
def parseExponent : List Char → Option Int
  | 'p' :: rest | 'P' :: rest => DecimalText.parseInteger rest
  | _ => none

/-- Decode a hexadecimal significand with a `0x` prefix and `p` exponent to an exact signed dyadic. -/
def parseCharacters (characters : List Char) : Option Dyadic := do
  let (negative, rest) := DecimalText.splitSign characters
  let magnitude ← match rest with
    | '0' :: 'x' :: rest | '0' :: 'X' :: rest => some rest
    | _ => none
  let (significand, exponent) ←
    RadixText.parseMagnitude magnitude 16 digitValue? parseExponent 4
  some { negative, significand, exponent }

/-- Parse a hexadecimal external character sequence without discarding signed zero. -/
def parse (text : String) : Option Dyadic := parseCharacters text.toList

/-- Exact IEEE hexadecimal spelling; the significand is integral and the exponent is binary. -/
def characters (value : Dyadic) : List Char :=
  (if value.negative then ['-'] else []) ++ ['0', 'x'] ++
    RadixText.naturalDigits value.significand 16 ++
    'p' :: DecimalText.integerDigits value.exponent

/-- Exact hexadecimal output preserves all three dyadic fields. -/
def format (value : Dyadic) : String := String.ofList (characters value)

/-- Express the dyadic magnitude as a coefficient times an integral power of sixteen. -/
def radixPair (value : Dyadic) : Nat × Int :=
  (value.significand * 2 ^ (value.exponent % 4).toNat, value.exponent / 4)

/-- Round to a requested hexadecimal digit count using the common radix precision algorithm. -/
def significant (roundMagnitude : Bool → ℚ → Nat) (value : Dyadic) (digits : ℕ+) :
    Dyadic :=
  let original := radixPair value
  let result := RadixText.significant 16 roundMagnitude value.negative
    original.1 original.2 digits
  { negative := value.negative, significand := result.1, exponent := 4 * result.2 }

end FloatLib.Numerics.HexText
