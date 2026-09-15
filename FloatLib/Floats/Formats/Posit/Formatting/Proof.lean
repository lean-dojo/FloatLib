/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Formatting
public import FloatLib.Numerics.Exact.DecimalText.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.RoundTrip

/-!
# Value-preserving Posit decimal conversion

The decimal string denotes exactly the decoded dyadic rational. Rounding that rational recovers
the original posit word. This proves the decimal preservation guarantee of
Posit Standard (2022), §6.3 for every descriptor width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

open FloatLib.Numerics

variable {format : Format}

/-- Decimal parsing uses the standard exact-rational rounder once. -/
theorem parse_eq_roundRat (input : String) (value : Rat)
    (hinput : DecimalText.parse input = some value) :
    parse format input = .ok (roundRat format value) := by
  have hnar : input ≠ "NaR" := by
    intro h
    subst input
    simp [DecimalText.parse, DecimalText.parseCharacters, DecimalText.splitSign,
      RadixText.parseMagnitude, RadixText.scanDigits, DecimalText.digitValue?] at hinput
  simp [parse, hnar, hinput]

/-- An ordinary finite word's decimal display has exactly its decoded rational value. -/
theorem decimalParse_display (value : Model format) (exact : FloatLib.Numerics.Dyadic)
    (hexact : value.toDyadic? = some exact) :
    DecimalText.parse value.display = some exact.toRat := by
  simp [display, hexact]

/-- Decimal display and parsing preserve every posit word, including zero and NaR. -/
@[simp] theorem parse_display (value : Model format) :
    parse format value.display = .ok value := by
  cases hexact : value.toDyadic? with
  | none =>
      have hrat : value.toRat? = none := by
        rw [toRat?_eq_toDyadic?_map, hexact]
        rfl
      have hnar := (toRat?_eq_none_iff value).mp hrat
      have hvalue := (isNaR_eq_true_iff value).mp hnar
      subst value
      simp [display, parse]
  | some exact =>
      rw [parse_eq_roundRat value.display exact.toRat (decimalParse_display value exact hexact)]
      congr 1
      apply roundRat_toRat? value exact.toRat
      simp [toRat?_eq_toDyadic?_map, hexact]

/-- Exact decimal parsing inverts `ToString`. -/
@[simp] theorem parse_toString (value : Model format) :
    parse format (toString value) = .ok value :=
  parse_display value

end FloatLib.Floats.Formats.Posit.Model
