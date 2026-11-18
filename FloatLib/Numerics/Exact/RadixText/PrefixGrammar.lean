/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.RadixText.Grammar

/-!
# Completing prefixes of positional magnitudes

When an exponent grammar accepts the empty exponent and every prefix of an
exponent can be completed by at most one zero, the same property holds for
the entire magnitude grammar. The result is independent of the radix,
numeric values and length of the digit strings.
-/

@[expose] public section

namespace FloatLib.Numerics.RadixText

/-- A prefix ends in the first part of a concatenation or contains that part completely. -/
theorem prefix_append_cases {α : Type*} {initial front tail : List α}
    (h : initial <+: front ++ tail) :
    initial <+: front ∨ ∃ rest, initial = front ++ rest ∧ rest <+: tail := by
  rcases List.prefix_or_prefix_of_prefix h (List.prefix_append front tail) with hfront | hfront
  · exact Or.inl hfront
  · obtain ⟨rest, rfl⟩ := hfront
    exact Or.inr ⟨rest, rfl, (List.prefix_append_right_inj front).mp h⟩

/-- Optional exponents with one-zero prefix completion give the same law for whole magnitudes. -/
theorem parseMagnitude_prefix_completion (radix : Nat) (readDigit : Char → Option Nat)
    (readExponent : List Char → Option Int) (fractionScale : Int)
    (hzero : ∃ digit, readDigit '0' = some digit)
    (hdot : readDigit '.' = none)
    (hempty : (readExponent []).isSome)
    (hhead : ∀ tail, (readExponent tail).isSome →
      ∀ c ∈ tail.head?, readDigit c = none ∧ c ≠ '.')
    (hcomplete : ∀ tail, (readExponent tail).isSome →
      ∀ initial, initial <+: tail →
        (readExponent initial).isSome ∨ (readExponent (initial ++ ['0'])).isSome)
    {characters initial : List Char}
    (hparse : (parseMagnitude characters radix readDigit readExponent fractionScale).isSome)
    (hprefix : initial <+: characters) :
    (parseMagnitude initial radix readDigit readExponent fractionScale).isSome ∨
      (parseMagnitude (initial ++ ['0']) radix readDigit readExponent fractionScale).isSome := by
  have digits_parse (digits tail : List Char) (hne : digits ≠ [])
      (hdigits : ∀ c ∈ digits, ∃ digit, readDigit c = some digit)
      (hexp : (readExponent tail).isSome) :
      (parseMagnitude (digits ++ tail) radix readDigit readExponent fractionScale).isSome := by
    obtain ⟨exponent, hexponent⟩ := Option.isSome_iff_exists.mp hexp
    rw [parseMagnitude_digits radix readDigit readExponent fractionScale digits tail exponent
      hne hdigits (hhead tail hexp) hexponent]
    rfl
  have point_parse (whole fraction tail : List Char) (hne : whole ++ fraction ≠ [])
      (hwhole : ∀ c ∈ whole, ∃ digit, readDigit c = some digit)
      (hfraction : ∀ c ∈ fraction, ∃ digit, readDigit c = some digit)
      (hexp : (readExponent tail).isSome) :
      (parseMagnitude (whole ++ '.' :: (fraction ++ tail))
        radix readDigit readExponent fractionScale).isSome := by
    obtain ⟨exponent, hexponent⟩ := Option.isSome_iff_exists.mp hexp
    rw [parseMagnitude_point radix readDigit readExponent fractionScale
      whole fraction tail exponent hdot hne hwhole hfraction
      (fun c hc => (hhead tail hexp c hc).1) hexponent]
    rfl
  have digits_complete (digits : List Char)
      (hdigits : ∀ c ∈ digits, ∃ digit, readDigit c = some digit) :
      (parseMagnitude digits radix readDigit readExponent fractionScale).isSome ∨
        (parseMagnitude (digits ++ ['0']) radix readDigit readExponent fractionScale).isSome := by
    by_cases hne : digits = []
    · subst digits
      exact Or.inr (by simpa using digits_parse ['0'] [] (by simp) (by simpa using hzero) hempty)
    · exact Or.inl (by simpa using digits_parse digits [] hne hdigits hempty)
  rcases parseMagnitude_decomposition radix readDigit readExponent fractionScale
    characters hparse with h | h
  · obtain ⟨digits, tail, exponent, rfl, hne, hdigits, hexponent⟩ := h
    rcases prefix_append_cases hprefix with h | ⟨rest, rfl, hrest⟩
    · exact digits_complete initial (fun c hc => hdigits c (h.sublist.subset hc))
    · rcases hcomplete tail (by simp [hexponent]) rest hrest with h | h
      · exact Or.inl (digits_parse digits rest hne hdigits h)
      · apply Or.inr
        simpa [List.append_assoc] using digits_parse digits (rest ++ ['0']) hne hdigits h
  · obtain ⟨whole, fraction, tail, exponent, rfl, hne, hdigits, hexponent⟩ := h
    have hwhole c hc := hdigits c (List.mem_append_left fraction hc)
    have hfraction c hc := hdigits c (List.mem_append_right whole hc)
    rcases prefix_append_cases hprefix with h | ⟨rest, rfl, hrest⟩
    · exact digits_complete initial (fun c hc => hwhole c (h.sublist.subset hc))
    · rcases List.prefix_cons_iff.mp hrest with rfl | ⟨afterPoint, rfl, hafterPoint⟩
      · simpa using digits_complete whole hwhole
      · rcases prefix_append_cases hafterPoint with h | ⟨afterDigits, rfl, hafterDigits⟩
        · have hrestDigits c hc := hfraction c (h.sublist.subset hc)
          by_cases hzeroDigits : whole ++ afterPoint = []
          · apply Or.inr
            simpa using point_parse whole (afterPoint ++ ['0']) [] (by simp) hwhole (by
              intro c hc
              rcases List.mem_append.mp hc with hc | hc
              · exact hrestDigits c hc
              · have : c = '0' := by simpa using hc
                subst c
                exact hzero) hempty
          · apply Or.inl
            simpa using point_parse whole afterPoint [] hzeroDigits hwhole hrestDigits hempty
        · rcases hcomplete tail (by simp [hexponent]) afterDigits hafterDigits with h | h
          · exact Or.inl (point_parse whole fraction afterDigits hne hwhole hfraction h)
          · apply Or.inr
            simpa [List.append_assoc] using
              point_parse whole fraction (afterDigits ++ ['0']) hne hwhole hfraction h

end FloatLib.Numerics.RadixText
