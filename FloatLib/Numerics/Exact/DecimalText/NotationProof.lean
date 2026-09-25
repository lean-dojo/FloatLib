/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Exact.DecimalText.Notation
public import FloatLib.Numerics.Exact.DecimalText.Proof

/-!
# Preservation laws for fixed and scientific decimal notation

Point insertion preserves the positional coefficient. Leading fractional padding does not
change that coefficient, and the scanner counts the padding when recovering the decimal scale.
-/

@[expose] public section

namespace FloatLib.Numerics.DecimalText

private theorem scanDigits_append (front suffix : List Char)
    (hdigits : ∀ c ∈ front, ∃ digit, digitValue? c = some digit) (accumulator : Nat) :
    RadixText.scanDigits (front ++ suffix) accumulator 10 digitValue? =
      let result := RadixText.scanDigits suffix
        (RadixText.scanDigits front accumulator 10 digitValue?).1 10 digitValue?
      (result.1, front.length + result.2.1, result.2.2) := by
  induction front generalizing accumulator with
  | nil => simp [RadixText.scanDigits]
  | cons c front ih =>
      obtain ⟨digit, hdigit⟩ := hdigits c (by simp)
      simp only [List.cons_append, RadixText.scanDigits, hdigit]
      rw [ih (fun c hc => hdigits c (by simp [hc]))]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem scanDigits_digits (digits tail : List Char)
    (hdigits : ∀ c ∈ digits, ∃ digit, digitValue? c = some digit)
    (htail : ∀ c ∈ tail.head?, digitValue? c = none) (accumulator : Nat) :
    RadixText.scanDigits (digits ++ tail) accumulator 10 digitValue? =
      ((RadixText.scanDigits digits accumulator 10 digitValue?).1, digits.length, tail) := by
  rw [scanDigits_append digits tail hdigits,
    RadixText.scanDigits_stop 10 digitValue? tail htail]
  simp

private theorem naturalDigits_are_digits (coefficient : Nat) :
    ∀ c ∈ RadixText.naturalDigits coefficient 10, ∃ digit, digitValue? c = some digit := by
  intro c hc
  obtain ⟨digit, _, hdigit⟩ := digitValue?_mem_naturalDigits hc
  exact ⟨digit, hdigit⟩

/-- Inserting a point preserves the coefficient and subtracts the fractional digit count.
The suffix may be empty or an exponent accepted by the existing decimal scanner. -/
theorem parseMagnitude_pointCharacters (whole fraction tail : List Char) (exponent : Int)
    (hwhole : whole ≠ [])
    (hdigits : ∀ c ∈ whole ++ fraction, ∃ digit, digitValue? c = some digit)
    (htail : ∀ c ∈ tail.head?, digitValue? c = none)
    (hexponent : parseExponent tail = some exponent) :
    RadixText.parseMagnitude (pointCharacters whole fraction ++ tail)
      10 digitValue? parseExponent 1 =
      some ((RadixText.scanDigits (whole ++ fraction) 0 10 digitValue?).1,
        exponent - (fraction.length : Int)) := by
  have hw : ∀ c ∈ whole, ∃ digit, digitValue? c = some digit :=
    fun c hc => hdigits c (List.mem_append_left _ hc)
  have hf : ∀ c ∈ fraction, ∃ digit, digitValue? c = some digit :=
    fun c hc => hdigits c (List.mem_append_right _ hc)
  have hcount : whole.length ≠ 0 := by simpa using hwhole
  by_cases hnil : fraction = []
  · subst fraction
    simp only [pointCharacters, ite_true, List.append_nil, List.length_nil,
      Nat.cast_zero, sub_zero]
    rw [RadixText.parseMagnitude, scanDigits_digits whole tail hw htail]
    cases tail with
    | nil => simp_all
    | cons c rest =>
        have hc : c ≠ '.' := by
          rintro rfl
          simp [parseExponent] at hexponent
        simp [hc, hcount, hexponent]
  · simp only [pointCharacters, ite_eq_right hnil, List.append_assoc, List.cons_append]
    rw [RadixText.parseMagnitude,
      scanDigits_digits whole ('.' :: (fraction ++ tail)) hw (by simp [digitValue?])]
    simp only
    rw [scanDigits_digits fraction tail hf htail]
    have htotal : whole.length + fraction.length ≠ 0 := by omega
    simp only [htotal, ite_false, hexponent, mul_one]
    rw [scanDigits_append whole fraction hw]
    rfl

private theorem splitSign_digits (whole rest : List Char) (hwhole : whole ≠ [])
    (hdigits : ∀ c ∈ whole, ∃ digit, digitValue? c = some digit) :
    splitSign (whole ++ rest) = (false, whole ++ rest) := by
  cases whole with
  | nil => contradiction
  | cons c whole =>
      obtain ⟨digit, hdigit⟩ := hdigits c (by simp)
      simp only [List.cons_append, splitSign]
      split <;> simp_all [digitValue?]

private theorem parseCharacters_signed (negative : Bool) (characters : List Char)
    (coefficient : Nat) (exponent : Int)
    (hsign : splitSign characters = (false, characters))
    (hmagnitude : RadixText.parseMagnitude characters 10 digitValue? parseExponent 1 =
      some (coefficient, exponent)) :
    parseCharacters ((if negative then ['-'] else []) ++ characters) =
      some ⟨negative, coefficient, exponent⟩ := by
  cases negative with
  | false => simp [parseCharacters, hsign, hmagnitude]
  | true => simp [parseCharacters, splitSign, hmagnitude]

private theorem splitSign_pointCharacters (whole fraction tail : List Char)
    (hwhole : whole ≠ [])
    (hdigits : ∀ c ∈ whole, ∃ digit, digitValue? c = some digit) :
    splitSign (pointCharacters whole fraction ++ tail) =
      (false, pointCharacters whole fraction ++ tail) := by
  simpa only [pointCharacters, List.append_assoc] using
    splitSign_digits whole ((if fraction = [] then [] else '.' :: fraction) ++ tail)
      hwhole hdigits

private theorem scanDigits_zeroes_naturalDigits (zeros coefficient : Nat) :
    RadixText.scanDigits
      (List.replicate zeros '0' ++ RadixText.naturalDigits coefficient 10) 0 10 digitValue? =
      (coefficient, zeros + (RadixText.naturalDigits coefficient 10).length, []) := by
  induction zeros with
  | zero => simp
  | succ zeros ih =>
      simp [List.replicate_succ, RadixText.scanDigits, digitValue?, ih,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem fractionalCharacters_parts (coefficient places : Nat) :
    ∃ whole fraction : List Char,
      fractionalCharacters coefficient places = pointCharacters whole fraction ∧
      whole ≠ [] ∧
      (∀ c ∈ whole ++ fraction, ∃ digit, digitValue? c = some digit) ∧
      (RadixText.scanDigits (whole ++ fraction) 0 10 digitValue?).1 = coefficient ∧
      fraction.length = places := by
  let digits := RadixText.naturalDigits coefficient 10
  have hdigits := naturalDigits_are_digits coefficient
  have hlength : digits.length ≠ 0 := by simp [digits]
  by_cases hplaces : places < digits.length
  · refine ⟨digits.take (digits.length - places), digits.drop (digits.length - places),
      by simp [fractionalCharacters, digits, hplaces], ?_, ?_, ?_, ?_⟩
    · intro hnil
      have h := congrArg List.length hnil
      simp only [List.length_take, List.length_nil] at h
      omega
    · simpa using hdigits
    · simp [digits]
    · simp only [List.length_drop]
      omega
  · refine ⟨['0'], List.replicate (places - digits.length) '0' ++ digits,
      by simp [fractionalCharacters, digits, hplaces], by simp, ?_, ?_, ?_⟩
    · intro c hc
      simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at hc
      rcases hc with rfl | ⟨_, rfl⟩ | hc
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
      · exact hdigits c hc
    · simpa only [List.replicate_succ, List.cons_append, List.nil_append] using
        congrArg Prod.fst (scanDigits_zeroes_naturalDigits
          (places - digits.length + 1) coefficient)
    · simp only [List.length_append, List.length_replicate]
      omega

/-- Fixed fractional digits recover the exact coefficient and the requested decimal scale. -/
theorem parseMagnitude_fractionalCharacters (coefficient places : Nat) (tail : List Char)
    (exponent : Int) (htail : ∀ c ∈ tail.head?, digitValue? c = none)
    (hexponent : parseExponent tail = some exponent) :
    RadixText.parseMagnitude (fractionalCharacters coefficient places ++ tail)
      10 digitValue? parseExponent 1 = some (coefficient, exponent - (places : Int)) := by
  obtain ⟨whole, fraction, htext, hwhole, hdigits, hvalue, hlength⟩ :=
    fractionalCharacters_parts coefficient places
  rw [htext, parseMagnitude_pointCharacters whole fraction tail exponent
    hwhole hdigits htail hexponent, hvalue, hlength]

private theorem splitSign_fractionalCharacters (coefficient places : Nat) (tail : List Char) :
    splitSign (fractionalCharacters coefficient places ++ tail) =
      (false, fractionalCharacters coefficient places ++ tail) := by
  obtain ⟨whole, fraction, htext, hwhole, hdigits, _, _⟩ :=
    fractionalCharacters_parts coefficient places
  rw [htext]
  exact splitSign_pointCharacters whole fraction tail hwhole
    (fun c hc => hdigits c (List.mem_append_left _ hc))

/-- Signed fixed fractional text, optionally followed by an exponent, preserves its coefficient. -/
theorem parseCharacters_fractionalCharacters (negative : Bool) (coefficient places : Nat)
    (tail : List Char) (exponent : Int)
    (htail : ∀ c ∈ tail.head?, digitValue? c = none)
    (hexponent : parseExponent tail = some exponent) :
    parseCharacters ((if negative then ['-'] else []) ++
      (fractionalCharacters coefficient places ++ tail)) =
      some ⟨negative, coefficient, exponent - (places : Int)⟩ :=
  parseCharacters_signed negative _ coefficient _
    (splitSign_fractionalCharacters coefficient places tail)
    (parseMagnitude_fractionalCharacters coefficient places tail exponent htail hexponent)

/-- Fixed notation recovers the coefficient after absorbing any positive exponent. -/
@[simp] theorem parseCharacters_fixedCharacters (value : Decimal) :
    parseCharacters value.fixedCharacters = some value.fixedRepresentation := by
  rcases value with ⟨negative, coefficient, exponent⟩
  cases exponent with
  | ofNat exponent =>
      exact parseCharacters_signed negative _ _ 0
        (splitSign_naturalDigits_nil _)
        (by simpa using parseMagnitude_decimal (coefficient * 10 ^ exponent) 0)
  | negSucc exponent =>
      simpa [Decimal.fixedCharacters, Decimal.fixedRepresentation, Int.negSucc_eq] using
        parseCharacters_fractionalCharacters negative coefficient (exponent + 1) [] 0
          (by simp) rfl

/-- Fixed notation retains the complete record when its exponent specifies fractional places. -/
theorem Decimal.fixedRepresentation_eq_self (value : Decimal) (hexponent : value.exponent ≤ 0) :
    value.fixedRepresentation = value := by
  rcases value with ⟨negative, coefficient, exponent⟩
  cases exponent with
  | ofNat exponent =>
      have hzero : exponent = 0 := by simpa using hexponent
      subst exponent
      simp [fixedRepresentation]
  | negSucc exponent => rfl

/-- In particular, printing a decimal rounded to exponent `-places` preserves the exact record. -/
theorem parseCharacters_fixedCharacters_of_nonpos (value : Decimal)
    (hexponent : value.exponent ≤ 0) :
    parseCharacters value.fixedCharacters = some value := by
  rw [parseCharacters_fixedCharacters, value.fixedRepresentation_eq_self hexponent]

/-- Absorbing a positive exponent into the coefficient preserves the exact rational value. -/
@[simp] theorem Decimal.fixedRepresentation_toRat (value : Decimal) :
    value.fixedRepresentation.toRat = value.toRat := by
  rcases value with ⟨negative, coefficient, exponent⟩
  cases exponent with
  | ofNat exponent => cases negative <;> simp [fixedRepresentation, toRat]
  | negSucc exponent => rfl

/-- Fixed presentation preserves the sign, including the sign of zero. -/
@[simp] theorem Decimal.fixedRepresentation_negative (value : Decimal) :
    value.fixedRepresentation.negative = value.negative := by
  unfold fixedRepresentation
  split <;> rfl

/-- Fixed formatting followed by parsing preserves the exact rational denoted by the input. -/
@[simp] theorem parse_formatFixed (value : Decimal) :
    parse value.formatFixed = some value.toRat := by
  simp [parse, Decimal.formatFixed]

/-- Scientific notation recovers the entire decimal record, including zero sign and precision. -/
@[simp] theorem parseCharacters_scientificCharacters (value : Decimal) :
    parseCharacters value.scientificCharacters = some value := by
  rcases value with ⟨negative, coefficient, exponent⟩
  dsimp only [Decimal.scientificCharacters]
  by_cases hzero : coefficient = 0 ∧ exponent ≤ 0
  · rw [ite_eq_left hzero]
    have hscale : -(exponent.natAbs : Int) = exponent := by
      rw [Int.natCast_natAbs, abs_of_nonpos hzero.2, neg_neg]
    simpa only [hzero.1, zero_sub, hscale] using
      parseCharacters_fractionalCharacters negative 0 exponent.natAbs ['e', '0'] 0
        (by simp [digitValue?]) rfl
  · rw [ite_eq_right hzero]
    let digits := RadixText.naturalDigits coefficient 10
    have hwhole : digits.take 1 ≠ [] := by
      intro hnil
      have h := congrArg List.length hnil
      have hlength : digits.length ≠ 0 := by simp [digits]
      simp only [List.length_take, List.length_nil] at h
      omega
    have hdigits : ∀ c ∈ digits.take 1 ++ digits.drop 1,
        ∃ digit, digitValue? c = some digit := by
      simpa only [List.take_append_drop] using naturalDigits_are_digits coefficient
    apply parseCharacters_signed negative _ coefficient exponent
    · exact splitSign_pointCharacters _ _ _ hwhole
        (fun c hc => hdigits c (List.mem_append_left _ hc))
    · rw [parseMagnitude_pointCharacters _ _ _
        (exponent + ((digits.drop 1).length : Int)) hwhole hdigits
          (by simp [digitValue?]) (by simp [parseExponent, digits])]
      rw [List.take_append_drop]
      simp [digits]

/-- Scientific formatting followed by parsing preserves the exact rational denoted by the input. -/
@[simp] theorem parse_formatScientific (value : Decimal) :
    parse value.formatScientific = some value.toRat := by
  simp [parse, Decimal.formatScientific]

/-- Removing trailing zeros with any amount of fuel preserves the exact rational value. -/
theorem Decimal.trimTrailingZerosLoop_toRat (fuel : Nat) (value : Decimal) :
    (Decimal.trimTrailingZerosLoop fuel value).toRat = value.toRat := by
  induction fuel generalizing value with
  | zero => rfl
  | succ fuel ih =>
      unfold Decimal.trimTrailingZerosLoop
      split
      · rename_i h
        rw [ih]
        obtain ⟨-, hmod⟩ := h
        obtain ⟨q, hq⟩ : ∃ q, value.significand = 10 * q := ⟨value.significand / 10, by omega⟩
        have hdiv : value.significand / 10 = q := by omega
        rcases value with ⟨negative, significand, exponent⟩
        simp only at hq hdiv ⊢
        subst hq
        rw [hdiv]
        have hpow : (10 : Rat) ^ (exponent + 1) = (10 : Rat) ^ exponent * 10 := by
          rw [zpow_add_one₀ (by norm_num)]
        cases negative <;> simp [Decimal.toRat, hpow] <;> ring
      · rfl

/-- Removing trailing zeros preserves the exact rational value. -/
@[simp] theorem Decimal.trimTrailingZeros_toRat (value : Decimal) :
    value.trimTrailingZeros.toRat = value.toRat :=
  Decimal.trimTrailingZerosLoop_toRat _ value

/-- Compact dyadic text parses back to exactly the dyadic's rational value. -/
@[simp] theorem parse_formatDyadicCompact (value : Dyadic) :
    parse (formatDyadicCompact value) = some value.toRat := by
  simp only [formatDyadicCompact]
  split <;> simp

end FloatLib.Numerics.DecimalText
