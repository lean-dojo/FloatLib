/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.DecimalText.Runtime
public import FloatLib.Numerics.Exact.RadixText.PrefixGrammar

/-!
# Prefix grammar for signed decimal text

Signs preserve the prefix relation. Signed integer exponents and decimal
magnitudes have the one-zero completion property for every character list.
The marked-exponent lemma also applies to hexadecimal binary exponents.
-/

@[expose] public section

namespace FloatLib.Numerics.DecimalText

/-- Removing an optional sign preserves prefixes, including the empty prefix. -/
theorem splitSign_prefix {initial characters : List Char} (h : initial <+: characters) :
    (splitSign initial).2 <+: (splitSign characters).2 := by
  cases characters with
  | nil =>
      have : initial = [] := List.prefix_nil.mp h
      subst initial
      exact List.prefix_refl _
  | cons c rest =>
      rcases List.prefix_cons_iff.mp h with rfl | ⟨initial, rfl, hp⟩
      · simp [splitSign]
      · by_cases hm : c = '-'
        · subst c
          simpa [splitSign] using hp
        · by_cases hp : c = '+'
          · subst c
            simpa [splitSign] using h
          · simpa [splitSign, hm, hp] using h

/-- Extending a nonempty input commutes with removing its optional leading sign. -/
theorem splitSign_append (characters tail : List Char) (hne : characters ≠ []) :
    (splitSign (characters ++ tail)).2 = (splitSign characters).2 ++ tail := by
  cases characters with
  | nil => contradiction
  | cons c rest =>
      by_cases hm : c = '-'
      · subst c
        rfl
      · by_cases hp : c = '+'
        · subst c
          rfl
        · simp [splitSign, hm, hp]

/-- Appending a zero commutes with removing one optional leading sign. -/
theorem splitSign_append_zero (characters : List Char) :
    (splitSign (characters ++ ['0'])).2 = (splitSign characters).2 ++ ['0'] := by
  by_cases hne : characters = []
  · subst characters
    rfl
  · exact splitSign_append characters ['0'] hne

/-- A signed integer is exactly a nonempty sequence of decimal digits after its sign. -/
theorem parseInteger_isSome_iff (characters : List Char) :
    (parseInteger characters).isSome ↔
      (splitSign characters).2 ≠ [] ∧
        ∀ c ∈ (splitSign characters).2, ∃ digit, digitValue? c = some digit := by
  cases hsign : splitSign characters with
  | mk negative rest =>
      constructor
      · intro h
        obtain ⟨digits, tail, value, hrest, hdigits, _, hscan⟩ :=
          RadixText.scanDigits_decomposition 10 digitValue? rest 0
        have hvalid : digits.length ≠ 0 ∧ tail = [] := by
          by_cases hc : digits.length = 0 <;> by_cases ht : tail = [] <;>
            simp [parseInteger, hsign, hscan, hc, ht] at h ⊢
        simpa [hrest, hvalid.2] using
          And.intro (show digits ≠ [] by simpa using hvalid.1) hdigits
      · rintro ⟨hne, hdigits⟩
        have hscan := RadixText.scanDigits_digits 10 digitValue? rest [] hdigits (by simp) 0
        simp only [List.append_nil] at hscan
        rw [parseInteger, hsign]
        simp only
        rw [hscan]
        simp [show rest.length ≠ 0 by simpa using hne]

/-- Every prefix of an integer either is an integer or becomes one after appending zero. -/
theorem parseInteger_prefix_completion {characters initial : List Char}
    (hparse : (parseInteger characters).isSome) (hprefix : initial <+: characters) :
    (parseInteger initial).isSome ∨ (parseInteger (initial ++ ['0'])).isSome := by
  obtain ⟨_, hdigits⟩ := (parseInteger_isSome_iff characters).mp hparse
  have hp := splitSign_prefix hprefix
  have hprefixDigits c hc := hdigits c (hp.sublist.subset hc)
  by_cases hne : (splitSign initial).2 = []
  · apply Or.inr
    rw [parseInteger_isSome_iff, splitSign_append_zero, hne]
    exact ⟨by simp, by simp [digitValue?]⟩
  · exact Or.inl ((parseInteger_isSome_iff initial).mpr ⟨hne, hprefixDigits⟩)

/-- Any optional exponent marker followed by a signed integer has one-zero prefix completion. -/
theorem parseMarkedExponent_prefix_completion (readExponent : List Char → Option Int)
    (marker : Char → Prop) (hempty : (readExponent []).isSome)
    (hcons : ∀ c rest, (readExponent (c :: rest)).isSome ↔
      marker c ∧ (parseInteger rest).isSome)
    {characters initial : List Char} (hparse : (readExponent characters).isSome)
    (hprefix : initial <+: characters) :
    (readExponent initial).isSome ∨ (readExponent (initial ++ ['0'])).isSome := by
  cases characters with
  | nil =>
      have : initial = [] := List.prefix_nil.mp hprefix
      subst initial
      exact Or.inl hempty
  | cons c rest =>
      obtain ⟨hc, hrest⟩ := (hcons c rest).mp hparse
      rcases List.prefix_cons_iff.mp hprefix with rfl | ⟨initial, rfl, hp⟩
      · exact Or.inl hempty
      · rcases parseInteger_prefix_completion hrest hp with h | h
        · exact Or.inl ((hcons c initial).mpr ⟨hc, h⟩)
        · exact Or.inr ((hcons c (initial ++ ['0'])).mpr ⟨hc, h⟩)

/-- A nonempty decimal exponent begins with one of its two case-equivalent markers. -/
theorem parseExponent_cons_isSome (c : Char) (rest : List Char) :
    (parseExponent (c :: rest)).isSome ↔
      (c = 'e' ∨ c = 'E') ∧ (parseInteger rest).isSome := by
  by_cases he : c = 'e'
  · subst c
    simp [parseExponent]
  · by_cases hE : c = 'E'
    · subst c
      simp [parseExponent]
    · simp [parseExponent, he, hE]

/-- Decimal exponent prefixes need at most one added zero. -/
theorem parseExponent_prefix_completion {characters initial : List Char}
    (hparse : (parseExponent characters).isSome) (hprefix : initial <+: characters) :
    (parseExponent initial).isSome ∨ (parseExponent (initial ++ ['0'])).isSome :=
  parseMarkedExponent_prefix_completion parseExponent (fun c => c = 'e' ∨ c = 'E')
    (by decide) parseExponent_cons_isSome hparse hprefix

/-- Decimal exponent markers cannot be consumed as significand digits or a radix point. -/
theorem parseExponent_head (characters : List Char)
    (hparse : (parseExponent characters).isSome) :
    ∀ c ∈ characters.head?, digitValue? c = none ∧ c ≠ '.' := by
  cases characters with
  | nil => simp
  | cons c rest =>
      rcases ((parseExponent_cons_isSome c rest).mp hparse).1 with rfl | rfl <;>
        simp [digitValue?]

/-- Decimal character acceptance depends only on its unsigned magnitude after sign removal. -/
theorem parseCharacters_isSome (characters : List Char) :
    (parseCharacters characters).isSome =
      (RadixText.parseMagnitude (splitSign characters).2 10 digitValue? parseExponent 1).isSome
        := by
  unfold parseCharacters
  cases splitSign characters
  simp [Option.isSome_bind]

/-- Every prefix of a complete decimal is complete or becomes complete after one added zero. -/
theorem parseCharacters_prefix_completion {characters initial : List Char}
    (hparse : (parseCharacters characters).isSome) (hprefix : initial <+: characters) :
    (parseCharacters initial).isSome ∨ (parseCharacters (initial ++ ['0'])).isSome := by
  simp only [parseCharacters_isSome, splitSign_append_zero] at hparse ⊢
  exact RadixText.parseMagnitude_prefix_completion 10 digitValue? parseExponent 1
    ⟨0, by decide⟩ (by decide) (by decide) parseExponent_head
    (fun _ h _ hp => parseExponent_prefix_completion h hp) hparse (splitSign_prefix hprefix)

end FloatLib.Numerics.DecimalText
