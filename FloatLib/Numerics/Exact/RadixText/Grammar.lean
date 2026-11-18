/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.RadixText.ScannerProof

/-!
# Character grammar of positional magnitudes

The common scanner accepts a nonempty digit significand, with an optional
point, followed by a suffix accepted by its exponent parser. These laws
describe the characters independently of their accumulated numeric value.
The radix, digit decoder, exponent syntax and fractional scale are arbitrary.
-/

@[expose] public section

namespace FloatLib.Numerics.RadixText

/-- Accepting more exponent suffixes preserves every previously accepted magnitude. -/
theorem parseMagnitude_isSome_mono (radix : Nat) (readDigit : Char → Option Nat)
    (readExponent readExponent' : List Char → Option Int) (fractionScale : Int)
    (h : ∀ tail, (readExponent tail).isSome → (readExponent' tail).isSome)
    (characters : List Char)
    (hparse : (parseMagnitude characters radix readDigit readExponent fractionScale).isSome) :
    (parseMagnitude characters radix readDigit readExponent' fractionScale).isSome := by
  unfold parseMagnitude at hparse ⊢
  split at hparse
  simp_all only
  split at hparse
  all_goals split at hparse <;>
    simp_all only [Option.isSome_none, Bool.false_eq_true, ite_false]
  all_goals
    obtain ⟨exponent, hexponent⟩ := Option.isSome_iff_exists.mp
      (h _ (Option.isSome_of_isSome_bind hparse))
    simp [hexponent]

/-- A nonempty digit significand followed by an accepted exponent parses completely. -/
theorem parseMagnitude_digits (radix : Nat) (readDigit : Char → Option Nat)
    (readExponent : List Char → Option Int) (fractionScale : Int)
    (digits tail : List Char) (exponent : Int)
    (hne : digits ≠ [])
    (hdigits : ∀ c ∈ digits, ∃ digit, readDigit c = some digit)
    (htail : ∀ c ∈ tail.head?, readDigit c = none ∧ c ≠ '.')
    (hexponent : readExponent tail = some exponent) :
    parseMagnitude (digits ++ tail) radix readDigit readExponent fractionScale =
      some ((scanDigits digits 0 radix readDigit).1, exponent) := by
  rw [parseMagnitude, scanDigits_digits radix readDigit digits tail hdigits
    (fun c hc => (htail c hc).1)]
  have hcount : digits.length ≠ 0 := by simpa using hne
  cases tail with
  | nil => simp [hcount, hexponent]
  | cons c rest =>
      have hc : c ≠ '.' := (htail c (by simp)).2
      simp [hc, hcount, hexponent]

/-- A point may have no digits on either side separately, but not on both sides. -/
theorem parseMagnitude_point (radix : Nat) (readDigit : Char → Option Nat)
    (readExponent : List Char → Option Int) (fractionScale : Int)
    (whole fraction tail : List Char) (exponent : Int)
    (hdot : readDigit '.' = none)
    (hne : whole ++ fraction ≠ [])
    (hwhole : ∀ c ∈ whole, ∃ digit, readDigit c = some digit)
    (hfraction : ∀ c ∈ fraction, ∃ digit, readDigit c = some digit)
    (htail : ∀ c ∈ tail.head?, readDigit c = none)
    (hexponent : readExponent tail = some exponent) :
    parseMagnitude (whole ++ '.' :: (fraction ++ tail))
        radix readDigit readExponent fractionScale =
      some ((scanDigits (whole ++ fraction) 0 radix readDigit).1,
        exponent - (fraction.length : Int) * fractionScale) := by
  rw [parseMagnitude, scanDigits_digits radix readDigit whole
    ('.' :: (fraction ++ tail)) hwhole (by simpa using hdot)]
  simp only
  rw [scanDigits_digits radix readDigit fraction tail hfraction htail]
  have hcount : whole.length + fraction.length ≠ 0 := by
    simpa using hne
  simp only [hcount, ite_false, hexponent]
  rw [scanDigits_append radix readDigit whole fraction hwhole]
  rfl

/-- Every successful magnitude has digit segments, at most one point and an accepted exponent. -/
theorem parseMagnitude_decomposition (radix : Nat) (readDigit : Char → Option Nat)
    (readExponent : List Char → Option Int) (fractionScale : Int)
    (characters : List Char)
    (hparse : (parseMagnitude characters radix readDigit readExponent fractionScale).isSome) :
    (∃ digits tail exponent,
      characters = digits ++ tail ∧ digits ≠ [] ∧
      (∀ c ∈ digits, ∃ digit, readDigit c = some digit) ∧
      readExponent tail = some exponent) ∨
    (∃ whole fraction tail exponent,
      characters = whole ++ '.' :: (fraction ++ tail) ∧ whole ++ fraction ≠ [] ∧
      (∀ c ∈ whole ++ fraction, ∃ digit, readDigit c = some digit) ∧
      readExponent tail = some exponent) := by
  obtain ⟨whole, rest, value, hcharacters, hwhole, _, hscan⟩ :=
    scanDigits_decomposition radix readDigit characters 0
  rw [parseMagnitude, hscan] at hparse
  cases rest with
  | nil =>
      have hcount : whole.length ≠ 0 := by
        intro h
        simp [h] at hparse
      cases hexponent : readExponent [] with
      | none => simp [hcount, hexponent] at hparse
      | some exponent =>
          exact Or.inl ⟨whole, [], exponent, hcharacters,
            by simpa using hcount, hwhole, hexponent⟩
  | cons c rest =>
      by_cases hc : c = '.'
      · subst c
        obtain ⟨fraction, tail, significand, hrest, hfraction, _, hscanFraction⟩ :=
          scanDigits_decomposition radix readDigit rest value
        simp only [hscanFraction] at hparse
        have hcount : whole.length + fraction.length ≠ 0 := by
          intro h
          simp [h] at hparse
        cases hexponent : readExponent tail with
        | none => simp [hexponent] at hparse
        | some exponent =>
            refine Or.inr ⟨whole, fraction, tail, exponent,
              by simpa [hrest] using hcharacters, ?_, ?_, hexponent⟩
            · simpa using hcount
            · intro d hd
              exact (List.mem_append.mp hd).elim (hwhole d) (hfraction d)
      · have hcount : whole.length ≠ 0 := by
          intro h
          simp [hc, h] at hparse
        cases hexponent : readExponent (c :: rest) with
        | none => simp [hc, hcount, hexponent] at hparse
        | some exponent =>
            exact Or.inl ⟨whole, c :: rest, exponent, hcharacters,
              by simpa using hcount, hwhole, hexponent⟩

end FloatLib.Numerics.RadixText
