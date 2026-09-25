/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Formatting.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Cohort
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Saturation
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Direction
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Minimal
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Zero
public import FloatLib.Numerics.Exact.DecimalText.Proof

/-!
# Decimal text roundtrips

The character scanner recovers the full datum. Destination rounding then fixes
every valid datum: preferred-cohort optimality recovers the printed quantum,
and numerical exactness recovers its coefficient. This preserves more than a
rational value: signed zeros, trailing coefficient zeros, and NaN diagnostics
survive a format/parse roundtrip.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Formatting

open FloatLib.Numerics.DecimalText

/-- Projection with a representable input's own quantum preserves its full representation. -/
theorem projectMagnitude_same_quantum (f : Format) (mode : RoundingMode)
    (negative : Bool) (coefficient : Nat) (quantum : Int)
    (hvalid : (Datum.finite negative coefficient quantum).Valid f) :
    (projectMagnitude f mode negative
      ((coefficient : ℚ) * (10 : ℚ) ^ quantum) quantum).value =
        .finite negative coefficient quantum := by
  have hq := (roundedPair_quantum_le_of_valid f mode negative coefficient quantum hvalid).trans
    ((Datum.valid_quantum_iff ..).mp hvalid).2.2
  have hv := roundedPair_exact_value f mode negative coefficient quantum hvalid
  obtain ⟨d, r, hout⟩ : ∃ d r,
      (projectMagnitude f mode negative ((coefficient : ℚ) * (10 : ℚ) ^ quantum)
        quantum).value = .finite negative d r := by
    simp only [projectMagnitude_eq, ite_eq_right (not_lt.mpr hq), hv, ne_eq, not_true_eq_false,
      decide_false, Bool.false_eq_true, ite_false]
    exact ⟨_, _, rfl⟩
  have hclosest := projectMagnitude_quantum_closest f mode negative coefficient quantum quantum
    hvalid d r hout coefficient quantum hvalid rfl
  have hr : quantum = r := by
    simpa only [sub_self, abs_zero, abs_nonpos_iff, sub_eq_zero] using hclosest
  subst r
  have he := projectMagnitude_exact f mode negative coefficient quantum quantum hvalid
  rw [hout] at he
  simp only [Datum.toRat?_eq, Option.some.injEq] at he
  have hc : d = coefficient := by
    have hten : (10 : ℚ) ^ quantum ≠ 0 := zpow_ne_zero _ (by norm_num)
    cases negative <;> simpa [hten] using he
  simpa [hc] using hout

/-- Valid decoded datums are fixed, with no flags, in every rounding mode. -/
theorem convert_of_valid (f : Format) (mode : RoundingMode) (value : Datum)
    (hvalid : value.Valid f) :
    convert f mode value = { value := value } := by
  cases value with
  | finite negative coefficient quantum =>
      have hv := projectMagnitude_same_quantum f mode negative coefficient quantum hvalid
      have hs := projectMagnitude_exact_status f mode negative coefficient quantum quantum hvalid
      change projectScaled f mode negative coefficient quantum quantum = _
      rw [projectScaled_eq]
      cases h : projectMagnitude f mode negative
          ((coefficient : ℚ) * (10 : ℚ) ^ quantum) quantum
      simp_all
  | infinity negative => rfl
  | nan negative signaling payload =>
      exact ite_eq_left hvalid

/-- Decoding the exact character spelling recovers every field, without a format restriction. -/
@[simp] theorem readCharacters_characters (value : Datum) :
    readCharacters (characters value) = some value := by
  cases value with
  | finite negative coefficient quantum =>
      simp only [characters, readCharacters, parseCharacters_characters]
  | infinity negative =>
      cases negative <;>
        simp [characters, Numerics.SpecialText.infinityCharacters,
          readCharacters, parseCharacters, splitSign,
          Numerics.RadixText.parseMagnitude, Numerics.RadixText.scanDigits, digitValue?,
          parseSpecial, FloatLib.Numerics.SpecialText.parseSpecial,
          FloatLib.Numerics.SpecialText.consumeKeyword, Char.toLower] <;> decide
  | nan negative signaling payload =>
      cases negative <;> cases signaling <;>
        simp [characters, Numerics.SpecialText.nanCharacters,
          readCharacters, parseCharacters, splitSign,
          Numerics.RadixText.parseMagnitude, Numerics.RadixText.scanDigits, digitValue?,
          parseSpecial, FloatLib.Numerics.SpecialText.parseSpecial,
          FloatLib.Numerics.SpecialText.consumeKeyword, Char.toLower,
          FloatLib.Numerics.SpecialText.parsePayload] <;>
        simp [show (⟨110, by decide⟩ : Char) = 'n' from rfl]

/-- Exact output and unbounded parsing are inverses, including all NaNs and signed zeros. -/
@[simp] theorem read_formatExact (value : Datum) :
    read (formatExact value) = some value := by
  simp [read, formatExact]

/-- Full destination-format representation roundtrip, in every rounding mode and with no flags. -/
theorem parse_formatExact (f : Format) (mode : RoundingMode) (value : Datum)
    (hvalid : value.Valid f) :
    parse f mode (formatExact value) = { value := value } := by
  simp only [parse, read_formatExact]
  exact convert_of_valid f mode value hvalid

/-- Distinct datums, including members of the same cohort, have distinct exact spellings. -/
theorem formatExact_injective : Function.Injective formatExact := by
  intro a b h
  have he := congrArg read h
  simpa using he

/-- Every parser result is representable in its destination format, even on invalid input. -/
theorem convert_valid (f : Format) (mode : RoundingMode) (value : Datum) :
    (convert f mode value).value.Valid f := by
  cases value with
  | finite negative coefficient quantum =>
      change (projectScaled f mode negative coefficient quantum quantum).value.Valid f
      rw [projectScaled_eq]
      exact projectMagnitude_valid f mode negative
        (mul_nonneg (Nat.cast_nonneg coefficient) (zpow_pos (by norm_num) quantum).le) quantum
  | infinity negative => trivial
  | nan negative signaling payload =>
      by_cases h : payload < f.payloadBound
      · simp [convert, h, Datum.Valid]
      · simpa [convert, h, invalidText, Datum.Valid] using f.payloadBound_pos

/-- Character conversion always returns a valid destination datum, including on invalid input. -/
theorem parse_valid (f : Format) (mode : RoundingMode) (text : String) :
    (parse f mode text).value.Valid f := by
  cases h : read text with
  | none => simpa [parse, h, invalidText, Datum.Valid] using f.payloadBound_pos
  | some value => simpa [parse, h] using convert_valid f mode value

/-- The finite parser performs exactly one destination rounding, using the written quantum. -/
theorem parse_of_decimal (f : Format) (mode : RoundingMode) (text : String) (value : Decimal)
    (hread : parseCharacters text.toList = some value) :
    parse f mode text =
      projectMagnitude f mode value.negative
        ((value.significand : ℚ) * (10 : ℚ) ^ value.exponent) value.exponent := by
  simp [parse, read, readCharacters, hread, convert, projectScaled_eq]

/-- Zero keeps its sign and uses the written quantum clamped to the destination range. -/
theorem parse_zero (f : Format) (mode : RoundingMode) (text : String)
    (negative : Bool) (quantum : Int)
    (hread : parseCharacters text.toList = some ⟨negative, 0, quantum⟩) :
    parse f mode text =
      { value := .finite negative 0 (max f.minQuantum (min quantum f.maxQuantum)) } := by
  rw [parse_of_decimal f mode text _ hread]
  simpa using projectMagnitude_zero f mode negative quantum

private theorem decimal_magnitude_nonneg (value : Decimal) :
    0 ≤ (value.significand : ℚ) * (10 : ℚ) ^ value.exponent :=
  mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le

private theorem decimal_signed_magnitude (value : Decimal) :
    (if value.negative then -((value.significand : ℚ) * (10 : ℚ) ^ value.exponent)
      else (value.significand : ℚ) * (10 : ℚ) ^ value.exponent) = value.toRat := by
  cases h : value.negative <;> simp [Decimal.toRat, h]

private theorem parse_quantum_le (f : Format) (mode : RoundingMode)
    (text : String) (value : Decimal)
    (hread : parseCharacters text.toList = some value)
    (hfinite : (parse f mode text).status.overflow = false) :
    (roundedPair f mode value.negative
      ((value.significand : ℚ) * (10 : ℚ) ^ value.exponent)).2 ≤ f.maxQuantum := by
  rw [parse_of_decimal f mode text value hread] at hfinite
  apply le_of_not_gt
  intro h
  have ht := (projectMagnitude_overflow_iff f mode value.negative _ value.exponent).mpr h
  simp [hfinite] at ht

/-- Nearest decimal parsing has half-grid error unless the destination overflows. -/
theorem parse_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (text : String) (value : Decimal)
    (hread : parseCharacters text.toList = some value)
    (hfinite : (parse f mode text).status.overflow = false) :
    ∃ result, (parse f mode text).value.toRat? = some result ∧
      |result - value.toRat| ≤
        (10 : ℚ) ^ roundingQuantum f
          ((value.significand : ℚ) * (10 : ℚ) ^ value.exponent) / 2 := by
  have hq := parse_quantum_le f mode text value hread hfinite
  rw [parse_of_decimal f mode text value hread]
  simpa only [decimal_signed_magnitude] using
    projectMagnitude_error_le_half f mode hm value.negative
      (decimal_magnitude_nonneg value) value.exponent hq

/-- A finite parser result is inexact precisely when its numerical value changed. -/
theorem parse_inexact_iff (f : Format) (mode : RoundingMode)
    (text : String) (value : Decimal) (result : ℚ)
    (hread : parseCharacters text.toList = some value)
    (hfinite : (parse f mode text).status.overflow = false)
    (hvalue : (parse f mode text).value.toRat? = some result) :
    (parse f mode text).status.inexact = true ↔ result ≠ value.toRat := by
  have hq := parse_quantum_le f mode text value hread hfinite
  rw [parse_of_decimal f mode text value hread] at hvalue ⊢
  simpa only [decimal_signed_magnitude] using
    projectMagnitude_inexact_iff f mode value.negative _ result value.exponent hq hvalue

/-- Upward parsing returns an upper bound on the exact decimal input. -/
theorem le_parse_towardPositive (f : Format) (text : String) (value : Decimal)
    (hread : parseCharacters text.toList = some value)
    (hfinite : (parse f .towardPositive text).status.overflow = false) :
    ∃ result, (parse f .towardPositive text).value.toRat? = some result ∧
      value.toRat ≤ result := by
  have hq := parse_quantum_le f .towardPositive text value hread hfinite
  rw [parse_of_decimal f .towardPositive text value hread]
  simpa only [decimal_signed_magnitude] using
    projectMagnitude_towardPositive_le f value.negative
      (decimal_magnitude_nonneg value) value.exponent hq

/-- Downward parsing returns a lower bound on the exact decimal input. -/
theorem parse_towardNegative_le (f : Format) (text : String) (value : Decimal)
    (hread : parseCharacters text.toList = some value)
    (hfinite : (parse f .towardNegative text).status.overflow = false) :
    ∃ result, (parse f .towardNegative text).value.toRat? = some result ∧
      result ≤ value.toRat := by
  have hq := parse_quantum_le f .towardNegative text value hread hfinite
  rw [parse_of_decimal f .towardNegative text value hread]
  simpa only [decimal_signed_magnitude] using
    projectMagnitude_towardNegative_le f value.negative
      (decimal_magnitude_nonneg value) value.exponent hq

/-- Exact input selects the valid cohort member closest to the written quantum.
The written coefficient and quantum need not themselves fit the destination. -/
theorem parse_exact_cohort_closest (f : Format) (mode : RoundingMode)
    (text : String) (value : Decimal)
    (hread : parseCharacters text.toList = some value)
    (coefficient : Nat) (quantum : Int)
    (hvalid : (Datum.finite value.negative coefficient quantum).Valid f)
    (hexact : (value.significand : ℚ) * (10 : ℚ) ^ value.exponent =
      (coefficient : ℚ) * (10 : ℚ) ^ quantum)
    (d : Nat) (r : Int)
    (hout : (parse f mode text).value = .finite value.negative d r)
    (e : Nat) (t : Int) (he : (Datum.finite value.negative e t).Valid f)
    (hvalue : (coefficient : ℚ) * (10 : ℚ) ^ quantum = (e : ℚ) * (10 : ℚ) ^ t) :
    |value.exponent - r| ≤ |value.exponent - t| := by
  rw [parse_of_decimal f mode text value hread, hexact] at hout
  exact projectMagnitude_quantum_closest f mode value.negative coefficient quantum
    value.exponent hvalid d r hout e t he hvalue

/-- Inexact parsing uses the least quantum in the result's cohort, including directed overflow. -/
theorem parse_inexact_quantum_minimal (f : Format) (mode : RoundingMode)
    (text : String) (value : Decimal)
    (hread : parseCharacters text.toList = some value)
    (hinexact : (parse f mode text).status.inexact = true)
    (c : Nat) (q : Int) (hout : (parse f mode text).value = .finite value.negative c q)
    (d : Nat) (r : Int) (hvalid : (Datum.finite value.negative d r).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) :
    q ≤ r := by
  rw [parse_of_decimal f mode text value hread] at hinexact hout
  exact projectMagnitude_inexact_quantum_minimal f mode value.negative
    (decimal_magnitude_nonneg value) value.exponent hinexact c q hout d r hvalid hvalue

end FloatLib.Floats.Formats.DecimalInterchange.Formatting
