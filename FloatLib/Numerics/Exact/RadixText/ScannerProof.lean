/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Exact.RadixText.Runtime
import all Init.Data.Repr

/-!
# Positional scanner laws shared by decimal and hexadecimal text

Digit scanning computes the positional value, counts consumed digits, and leaves a nondigit
suffix unchanged. For radix greater than one and a decoder that recognizes the printed digits,
printing then scanning recovers any natural number, including zero.
-/

@[expose] public section

namespace FloatLib.Numerics.RadixText

/-- A radix scanner leaves a nondigit suffix untouched. -/
theorem scanDigits_stop (radix : Nat) (readDigit : Char → Option Nat)
    (tail : List Char) (htail : ∀ c ∈ tail.head?, readDigit c = none) (accumulator : Nat) :
    scanDigits tail accumulator radix readDigit = (accumulator, 0, tail) := by
  cases tail with
  | nil => rfl
  | cons c rest => simp [scanDigits, htail c (by simp)]

/-- Digit scanning computes the positional value, independently of the chosen radix. -/
theorem scanDigits_map_append (radix : Nat) (readDigit : Char → Option Nat)
    (digits : List Nat) (tail : List Char)
    (hdigits : ∀ digit ∈ digits, readDigit (Nat.digitChar digit) = some digit)
    (htail : ∀ c ∈ tail.head?, readDigit c = none) (accumulator : Nat) :
    scanDigits (digits.map Nat.digitChar ++ tail) accumulator radix readDigit =
      (accumulator * radix ^ digits.length + Nat.ofDigits radix digits.reverse,
        digits.length, tail) := by
  induction digits generalizing accumulator with
  | nil => simpa using scanDigits_stop radix readDigit tail htail accumulator
  | cons digit digits ih =>
      simp only [List.map_cons, List.cons_append, scanDigits, hdigits digit (by simp)]
      rw [ih (fun d hd => hdigits d (by simp [hd]))]
      simp only [List.length_cons, List.reverse_cons, Nat.ofDigits_append,
        Nat.ofDigits_singleton, List.length_reverse, pow_succ]
      apply Prod.ext
      · dsimp
        ring
      · rfl

/-- Radix output has at least one digit, including for zero. -/
@[simp] theorem naturalDigits_ne_nil (radix value : Nat) :
    naturalDigits value radix ≠ [] := by
  by_cases hz : value = 0
  · simp [naturalDigits, hz]
  · simp [naturalDigits, hz, Nat.digits_eq_nil_iff_eq_zero]

/-- Printing then scanning recovers an arbitrary natural and leaves the nondigit suffix. -/
theorem scanDigits_naturalDigits (radix : Nat) (hradix : 1 < radix)
    (readDigit : Char → Option Nat)
    (hdigit : ∀ digit < radix, readDigit (Nat.digitChar digit) = some digit)
    (value : Nat) (tail : List Char)
    (htail : ∀ c ∈ tail.head?, readDigit c = none) :
    scanDigits (naturalDigits value radix ++ tail) 0 radix readDigit =
      (value, (naturalDigits value radix).length, tail) := by
  by_cases hz : value = 0
  · subst value
    have hzero : readDigit '0' = some 0 := hdigit 0 (by omega)
    simp [naturalDigits, scanDigits, hzero, scanDigits_stop radix readDigit tail htail]
  · rw [naturalDigits, ite_eq_right hz]
    rw [scanDigits_map_append radix readDigit _ tail
      (fun digit h => hdigit digit (Nat.digits_lt_base hradix (List.mem_reverse.mp h))) htail]
    simp [hz, Nat.ofDigits_digits]

end FloatLib.Numerics.RadixText
