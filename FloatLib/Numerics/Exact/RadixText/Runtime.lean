/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Nat.Digits.Defs

/-!
# Positional character conversion

Printing and scanning share an explicit radix. The scanner accepts a digit decoder and leaves
the first nondigit and its suffix unconsumed. Magnitude parsing adds a radix point and delegates
exponent syntax to its caller; fractional digits each subtract `fractionScale` exponent units.
Decimal and hexadecimal text use the same implementation with different syntax parameters.
-/

@[expose] public section

namespace FloatLib.Numerics.RadixText

/-- Digits in printing order, including one digit for zero. -/
def naturalDigits (value radix : Nat) : List Char :=
  if value = 0 then ['0'] else ((Nat.digits radix value).reverse.map Nat.digitChar)

/-- Read a maximal digit prefix, returning its value, length, and unconsumed suffix. -/
def scanDigits (characters : List Char) (accumulator radix : Nat)
    (readDigit : Char → Option Nat) : Nat × Nat × List Char :=
  match characters with
  | [] => (accumulator, 0, [])
  | character :: rest =>
      match readDigit character with
      | none => (accumulator, 0, character :: rest)
      | some digit =>
          let result := scanDigits rest (accumulator * radix + digit) radix readDigit
          (result.1, result.2.1 + 1, result.2.2)

/-- Parse an unsigned significand and exponent with caller-supplied radix and exponent syntax. -/
def parseMagnitude (characters : List Char) (radix : Nat)
    (readDigit : Char → Option Nat) (readExponent : List Char → Option Int)
    (fractionScale : Int) : Option (Nat × Int) := do
  let (whole, wholeCount, rest) := scanDigits characters 0 radix readDigit
  match rest with
  | '.' :: fraction =>
      let (significand, fractionCount, tail) := scanDigits fraction whole radix readDigit
      if wholeCount + fractionCount = 0 then none
      else
        let exponent ← readExponent tail
        some (significand, exponent - (fractionCount : Int) * fractionScale)
  | tail =>
      if wholeCount = 0 then none
      else
        let exponent ← readExponent tail
        some (whole, exponent)

end FloatLib.Numerics.RadixText
