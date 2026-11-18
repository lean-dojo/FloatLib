/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Text
public import FloatLib.Numerics.Exact.HexText.Grammar

/-!
# Completeness of fixed-point numeric subject prefixes

WG14 N1169 (2006 TR 18037 draft), C clause 7.19.6.2 inherits the C99 input-item rule: an item is
    a complete
numeric subject or an initial subsequence of one. For the decimal and
optional-exponent hexadecimal grammar used here, every such prefix either
parses already or parses after one appended zero. This holds for arbitrary
character-list lengths and is independent of the destination fixed format.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded.Text

open FloatLib.Numerics

/-- Subject acceptance is decimal, IEEE hexadecimal, or hexadecimal completed with `p0`. -/
theorem subject_isSome_iff (characters : List Char) :
    (subject characters).isSome ↔
      (DecimalText.parseCharacters characters).isSome ∨
      (HexText.parseCharacters characters).isSome ∨
      (HexText.parseCharacters (characters ++ ['p', '0'])).isSome := by
  cases hd : DecimalText.parseCharacters characters <;>
    cases hh : HexText.parseCharacters characters <;>
    cases hp : HexText.parseCharacters (characters ++ ['p', '0']) <;>
    simp [subject, hd, hh, hp]

private def optionalHexExponent : List Char → Option Int
  | [] => some 0
  | characters => HexText.parseExponent characters

private theorem optionalHexExponent_cons (c : Char) (rest : List Char) :
    (optionalHexExponent (c :: rest)).isSome ↔
      (c = 'p' ∨ c = 'P') ∧ (DecimalText.parseInteger rest).isSome :=
  HexText.parseExponent_cons_isSome c rest

private theorem optionalHexExponent_head (characters : List Char)
    (hparse : (optionalHexExponent characters).isSome) :
    ∀ c ∈ characters.head?, HexText.digitValue? c = none ∧ c ≠ '.' := by
  cases characters with
  | nil => simp
  | cons c rest => exact HexText.parseExponent_head (c :: rest) hparse

private theorem optionalHexExponent_complete {characters initial : List Char}
    (hparse : (optionalHexExponent characters).isSome) (hprefix : initial <+: characters) :
    (optionalHexExponent initial).isSome ∨
      (optionalHexExponent (initial ++ ['0'])).isSome :=
  DecimalText.parseMarkedExponent_prefix_completion optionalHexExponent
    (fun c => c = 'p' ∨ c = 'P') (by decide) optionalHexExponent_cons hparse hprefix

private theorem optionalHexMagnitude_strict (characters : List Char)
    (hparse : (RadixText.parseMagnitude characters 16 HexText.digitValue?
      optionalHexExponent 4).isSome) :
    (RadixText.parseMagnitude characters 16 HexText.digitValue? HexText.parseExponent 4).isSome ∨
    (RadixText.parseMagnitude (characters ++ ['p', '0']) 16 HexText.digitValue?
      HexText.parseExponent 4).isSome := by
  have padding : HexText.parseExponent ['p', '0'] = some 0 := by decide
  have paddingHead : ∀ c ∈ (['p', '0'] : List Char).head?,
      HexText.digitValue? c = none ∧ c ≠ '.' :=
    HexText.parseExponent_head _ (by simp [padding])
  rcases RadixText.parseMagnitude_decomposition 16 HexText.digitValue?
    optionalHexExponent 4 characters hparse with h | h
  · obtain ⟨digits, tail, exponent, rfl, hne, hdigits, hexponent⟩ := h
    cases tail with
    | nil =>
        apply Or.inr
        simp only [List.append_nil]
        rw [RadixText.parseMagnitude_digits 16 HexText.digitValue? HexText.parseExponent 4
          digits ['p', '0'] 0 hne hdigits paddingHead padding]
        rfl
    | cons c rest =>
        have hexponent' : HexText.parseExponent (c :: rest) = some exponent := by
          simpa only [optionalHexExponent] using hexponent
        apply Or.inl
        rw [RadixText.parseMagnitude_digits 16 HexText.digitValue? HexText.parseExponent 4
          digits (c :: rest) exponent hne hdigits
          (HexText.parseExponent_head _ (by simp [hexponent'])) hexponent']
        rfl
  · obtain ⟨whole, fraction, tail, exponent, rfl, hne, hdigits, hexponent⟩ := h
    have hwhole c hc := hdigits c (List.mem_append_left fraction hc)
    have hfraction c hc := hdigits c (List.mem_append_right whole hc)
    cases tail with
    | nil =>
        apply Or.inr
        simp only [List.append_nil, List.append_assoc, List.cons_append]
        rw [RadixText.parseMagnitude_point 16 HexText.digitValue? HexText.parseExponent 4
          whole fraction ['p', '0'] 0 (by decide) hne hwhole hfraction
          (fun c hc => (paddingHead c hc).1) padding]
        rfl
    | cons c rest =>
        have hexponent' : HexText.parseExponent (c :: rest) = some exponent := by
          simpa only [optionalHexExponent] using hexponent
        apply Or.inl
        rw [RadixText.parseMagnitude_point 16 HexText.digitValue? HexText.parseExponent 4
          whole fraction (c :: rest) exponent (by decide) hne hwhole hfraction
          (fun c hc => (HexText.parseExponent_head _ (by simp [hexponent']) c hc).1) hexponent']
        rfl

private theorem subject_hexadecimal (characters magnitude : List Char) (marker : Char)
    (hmarker : marker = 'x' ∨ marker = 'X')
    (hcharacters : (DecimalText.splitSign characters).2 = '0' :: marker :: magnitude)
    (hparse : (RadixText.parseMagnitude magnitude 16 HexText.digitValue?
      HexText.parseExponent 4).isSome) :
    (subject characters).isSome := by
  apply (subject_isSome_iff characters).mpr
  apply Or.inr ∘ Or.inl
  rw [HexText.parseCharacters_isSome, hcharacters]
  rcases hmarker with rfl | rfl <;> exact hparse

private theorem subject_optionalHexMagnitude (characters magnitude : List Char) (marker : Char)
    (hmarker : marker = 'x' ∨ marker = 'X')
    (hcharacters : (DecimalText.splitSign characters).2 = '0' :: marker :: magnitude)
    (hparse : (RadixText.parseMagnitude magnitude 16 HexText.digitValue?
      optionalHexExponent 4).isSome) :
    (subject characters).isSome := by
  rcases optionalHexMagnitude_strict magnitude hparse with h | h
  · exact subject_hexadecimal characters magnitude marker hmarker hcharacters h
  · apply (subject_isSome_iff characters).mpr
    apply Or.inr ∘ Or.inr
    rw [HexText.parseCharacters_isSome, DecimalText.splitSign_append characters _ (by
      rintro rfl
      simp [DecimalText.splitSign] at hcharacters), hcharacters]
    rcases hmarker with rfl | rfl <;> exact h

private theorem subject_hexadecimal_prefix {characters initial : List Char}
    (hparse : (HexText.parseCharacters characters).isSome) (hprefix : initial <+: characters) :
    (subject initial).isSome ∨ (subject (initial ++ ['0'])).isSome := by
  obtain ⟨marker, magnitude, hmarker, hcharacters, hmagnitude⟩ :
      ∃ marker magnitude, (marker = 'x' ∨ marker = 'X') ∧
        (DecimalText.splitSign characters).2 = '0' :: marker :: magnitude ∧
        (RadixText.parseMagnitude magnitude 16 HexText.digitValue?
          HexText.parseExponent 4).isSome := by
    rw [HexText.parseCharacters_isSome] at hparse
    split at hparse
    · exact ⟨'x', _, Or.inl rfl, ‹_›, hparse⟩
    · exact ⟨'X', _, Or.inr rfl, ‹_›, hparse⟩
    · contradiction
  have hp := DecimalText.splitSign_prefix hprefix
  rw [hcharacters] at hp
  have decimal_zero (input : List Char) (hinput : (DecimalText.splitSign input).2 = ['0']) :
      (subject input).isSome := by
    apply (subject_isSome_iff input).mpr
    apply Or.inl
    rw [DecimalText.parseCharacters_isSome, hinput]
    decide
  rcases List.prefix_cons_iff.mp hp with hempty | ⟨afterZero, hrest, hAfterZero⟩
  · exact Or.inr (decimal_zero _ (by rw [DecimalText.splitSign_append_zero, hempty]; rfl))
  · rcases List.prefix_cons_iff.mp hAfterZero with rfl | ⟨rest, rfl, hAfterMarker⟩
    · exact Or.inl (decimal_zero initial hrest)
    · have hmagnitude' := RadixText.parseMagnitude_isSome_mono 16 HexText.digitValue?
        HexText.parseExponent optionalHexExponent 4 (by
          intro tail h
          cases tail with
          | nil => decide
          | cons c rest => exact h) magnitude hmagnitude
      rcases RadixText.parseMagnitude_prefix_completion 16 HexText.digitValue?
        optionalHexExponent 4 ⟨0, by decide⟩ (by decide) (by decide)
        optionalHexExponent_head (fun _ h _ hp => optionalHexExponent_complete h hp)
        hmagnitude' hAfterMarker with h | h
      · exact Or.inl (subject_optionalHexMagnitude initial rest marker hmarker hrest h)
      · exact Or.inr (subject_optionalHexMagnitude (initial ++ ['0']) (rest ++ ['0'])
          marker hmarker (by rw [DecimalText.splitSign_append_zero, hrest]; rfl) h)

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.19.6.2: every numeric-subject prefix needs at
    most one zero to become complete. -/
theorem subject_prefix_completion {characters initial : List Char}
    (hparse : (subject characters).isSome) (hprefix : initial <+: characters) :
    (subject initial).isSome ∨ (subject (initial ++ ['0'])).isSome := by
  rcases (subject_isSome_iff characters).mp hparse with h | h | h
  · rcases DecimalText.parseCharacters_prefix_completion h hprefix with h | h
    · exact Or.inl ((subject_isSome_iff initial).mpr (Or.inl h))
    · exact Or.inr ((subject_isSome_iff (initial ++ ['0'])).mpr (Or.inl h))
  · exact subject_hexadecimal_prefix h hprefix
  · exact subject_hexadecimal_prefix h (hprefix.trans (List.prefix_append _ _))

/-- An arbitrary continuation exists exactly when the subject or its one-zero completion parses. -/
theorem subject_has_completion_iff (characters : List Char) :
    (∃ suffix, (subject (characters ++ suffix)).isSome) ↔
      (subject characters).isSome ∨ (subject (characters ++ ['0'])).isSome := by
  constructor
  · rintro ⟨suffix, h⟩
    exact subject_prefix_completion h (List.prefix_append characters suffix)
  · rintro (h | h)
    · exact ⟨[], by simpa using h⟩
    · exact ⟨['0'], h⟩

end FloatLib.Floats.Formats.FixedPoint.Embedded.Text
