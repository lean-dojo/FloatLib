/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Parsing

/-!
# Binary character input with explicit resource limits

The byte limit is checked before scanning, including before trimming ASCII whitespace.
The exponent limit applies to the parsed exponent after fractional digits adjust its scale.
Both checks precede exact numerical conversion. Accepted values are never clamped or approximated
to satisfy a limit: their value and exception status agree with `TextParser.run`.

Infinity and NaN spellings have exponent magnitude zero. Their text, including every NaN payload
digit, remains subject to the byte limit.

`Model.parse` is the caller-facing entrypoint. Resource limits are opt-in with `limits := true`;
`status := true` includes all IEEE exception flags. The `TextParser` namespace contains
implementation helpers used by this entrypoint and its correctness proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- Caller-selected limits on input bytes and the magnitude of the adjusted parsed exponent. -/
structure ParseLimits where
  /-- Maximum UTF-8 byte length of the original input, including edge whitespace. -/
  maxBytes : Nat := 4096
  /-- Maximum absolute decimal or binary exponent after accounting for fractional digits. -/
  maxExponent : Nat := 10000
  deriving DecidableEq, Repr, Inhabited

/-- Magnitude of the adjusted decimal or binary exponent; special values have no exponent. -/
def TextValue.exponentMagnitude : TextValue → Nat
  | .decimal value => value.exponent.natAbs
  | .dyadic value => value.exponent.natAbs
  | .infinity _ | .nan _ _ _ => 0

/-- Scan with the same ASCII trimming and syntax errors as `TextParser.run`, without rounding. -/
def readTextInput (input : String) : Except ParseError TextValue :=
  match readText input with
  | some value => .ok value
  | none =>
      let trimmed := input.trimAscii.toString
      if trimmed.isEmpty then .error .emptyInput
      else match readText trimmed with
        | some value => .ok value
        | none => .error (.invalidSyntax input)

/-- The existing parser is exactly this scan followed by its original numerical conversion. -/
theorem TextParser.run_eq_bind_readTextInput (fmt : FloatFormat) (mode : IEEERoundingMode)
    (input : String) :
    run fmt mode input = (readTextInput input).bind (convertText fmt mode) := by
  unfold run readTextInput
  cases readText input with
  | some value => rfl
  | none =>
      dsimp
      split
      · rfl
      · cases readText input.trimAscii.toString <;> rfl

/--
Check the original byte length before scanning, then check the adjusted exponent before conversion.
The successful result is the scanned value itself, so conversion does not scan the input again.
-/
def readTextWithLimits (limits : ParseLimits) (input : String) : Except ParseError TextValue :=
  if input.utf8ByteSize ≤ limits.maxBytes then
    (readTextInput input).bind fun value =>
      if value.exponentMagnitude ≤ limits.maxExponent then
        .ok value
      else
        .error (.exponentTooLarge value.exponentMagnitude limits.maxExponent)
  else
    .error (.inputTooLong input.utf8ByteSize limits.maxBytes)

/-- Implementation core with explicit resource limits, retaining the complete IEEE status. -/
def TextParser.runBounded (fmt : FloatFormat) (mode : IEEERoundingMode)
    (limits : ParseLimits) (input : String) : Except ParseError (IEEEOutcome fmt) :=
  (readTextWithLimits limits input).bind (convertText fmt mode)

/-- A successful bounded scan is exactly an original scan satisfying both resource limits. -/
theorem readTextWithLimits_eq_ok_iff (limits : ParseLimits) (input : String) (value : TextValue) :
    readTextWithLimits limits input = .ok value ↔
      input.utf8ByteSize ≤ limits.maxBytes ∧
      readTextInput input = .ok value ∧ value.exponentMagnitude ≤ limits.maxExponent := by
  by_cases hbytes : input.utf8ByteSize ≤ limits.maxBytes
  · cases hread : readTextInput input with
    | error error =>
        simp [readTextWithLimits, hbytes, hread, Except.bind]
    | ok scanned =>
        by_cases hexponent : scanned.exponentMagnitude ≤ limits.maxExponent
        · simp [readTextWithLimits, hbytes, hread, Except.bind, hexponent]
          rintro rfl
          exact hexponent
        · simp [readTextWithLimits, hbytes, hread, Except.bind, hexponent]
          rintro rfl
          exact Nat.lt_of_not_ge hexponent
  · simp [readTextWithLimits, hbytes]

/-- The byte bound holds for the original input, before any edge whitespace is removed. -/
theorem readTextWithLimits_byte_bound {limits : ParseLimits} {input : String} {value : TextValue}
    (hread : readTextWithLimits limits input = .ok value) :
    input.utf8ByteSize ≤ limits.maxBytes :=
  ((readTextWithLimits_eq_ok_iff limits input value).mp hread).1

/-- Every successful scan respects the bound on its actual adjusted exponent. -/
theorem readTextWithLimits_exponent_bound
    {limits : ParseLimits} {input : String} {value : TextValue}
    (hread : readTextWithLimits limits input = .ok value) :
    value.exponentMagnitude ≤ limits.maxExponent :=
  ((readTextWithLimits_eq_ok_iff limits input value).mp hread).2.2

/-- When the original input meets the limits, bounded scanning preserves syntax errors as well. -/
theorem readTextWithLimits_eq_readTextInput (limits : ParseLimits) (input : String)
    (hbytes : input.utf8ByteSize ≤ limits.maxBytes)
    (hexponent : ∀ value, readTextInput input = .ok value →
      value.exponentMagnitude ≤ limits.maxExponent) :
    readTextWithLimits limits input = readTextInput input := by
  cases hread : readTextInput input with
  | error error =>
      simp [readTextWithLimits, hbytes, hread, Except.bind]
  | ok value =>
      simp [readTextWithLimits, hbytes, hread, Except.bind, hexponent value hread]

/-- Within the declared limits, bounded and original parsing agree on every value, flag, and error. -/
theorem TextParser.runBounded_eq_run (fmt : FloatFormat) (mode : IEEERoundingMode)
    (limits : ParseLimits) (input : String)
    (hbytes : input.utf8ByteSize ≤ limits.maxBytes)
    (hexponent : ∀ value, readTextInput input = .ok value →
      value.exponentMagnitude ≤ limits.maxExponent) :
    runBounded fmt mode limits input = run fmt mode input := by
  rw [runBounded, readTextWithLimits_eq_readTextInput limits input hbytes hexponent,
    run_eq_bind_readTextInput]

/--
Successful bounded conversion comes from an original scanned value within the exponent limit.
The original input satisfies the byte bound, and conversion preserves the full outcome.
-/
theorem TextParser.runBounded_eq_ok_iff (fmt : FloatFormat) (mode : IEEERoundingMode)
    (limits : ParseLimits) (input : String) (outcome : IEEEOutcome fmt) :
    runBounded fmt mode limits input = .ok outcome ↔
      input.utf8ByteSize ≤ limits.maxBytes ∧
      ∃ value, readTextInput input = .ok value ∧
        value.exponentMagnitude ≤ limits.maxExponent ∧
        convertText fmt mode value = .ok outcome := by
  constructor
  · intro hparse
    cases hread : readTextWithLimits limits input with
    | error error =>
        simp [runBounded, hread, Except.bind] at hparse
    | ok value =>
        obtain ⟨hbytes, horiginal, hexponent⟩ :=
          (readTextWithLimits_eq_ok_iff limits input value).mp hread
        exact ⟨hbytes, value, horiginal, hexponent,
          by simpa [runBounded, hread, Except.bind] using hparse⟩
  · rintro ⟨hbytes, value, hread, hexponent, hconvert⟩
    have hbounded := (readTextWithLimits_eq_ok_iff limits input value).mpr
      ⟨hbytes, hread, hexponent⟩
    simpa [runBounded, hbounded, Except.bind] using hconvert

/-- A bounded success is exactly the original parser's outcome, including all exception flags. -/
theorem TextParser.run_eq_of_runBounded_eq_ok
    {fmt : FloatFormat} {mode : IEEERoundingMode} {limits : ParseLimits} {input : String}
    {outcome : IEEEOutcome fmt} (hparse : runBounded fmt mode limits input = .ok outcome) :
    run fmt mode input = .ok outcome := by
  obtain ⟨_, value, hread, _, hconvert⟩ :=
    (runBounded_eq_ok_iff fmt mode limits input outcome).mp hparse
  simpa [run_eq_bind_readTextInput, hread, Except.bind] using hconvert

/--
Parse text with optional rounding, resource limits, and IEEE exception status.

By default, conversion uses nearest-even rounding without resource limits and returns the value.
With `limits := true`, `maxBytes` bounds the original UTF-8 input before scanning and
`maxExponent` bounds the adjusted decimal or binary exponent before numerical conversion.
With `status := true`, the result also carries all five IEEE exception flags.
-/
def parse (fmt : FloatFormat) (input : String) (rounding : IEEERoundingMode := .nearestEven)
    (limits : Bool := false) (maxBytes : Nat := 4096) (maxExponent : Nat := 10000)
    (status : Bool := false) :
    Except ParseError (match status with
      | true => IEEEOutcome fmt
      | false => Model fmt) :=
  let result := if limits then
      TextParser.runBounded fmt rounding { maxBytes, maxExponent } input
    else
      TextParser.run fmt rounding input
  match status with
  | true => result
  | false => result.map (·.value)

/-- With limits and status disabled, parsing returns the exact core's value. -/
@[simp] theorem parse_eq_run (fmt : FloatFormat) (input : String) (rounding : IEEERoundingMode) :
    parse fmt input (rounding := rounding) =
      (TextParser.run fmt rounding input).map (·.value) := rfl

/-- Status-enabled parsing without limits returns the complete exact core outcome. -/
@[simp] theorem parse_status_eq_run (fmt : FloatFormat) (input : String)
    (rounding : IEEERoundingMode) (maxBytes maxExponent : Nat) :
    parse fmt input (rounding := rounding) (maxBytes := maxBytes) (maxExponent := maxExponent)
        (status := true) =
      TextParser.run fmt rounding input := rfl

/-- With limits enabled and status disabled, parsing returns the bounded core's value. -/
@[simp] theorem parse_limits_eq_runBounded_map (fmt : FloatFormat) (input : String)
    (rounding : IEEERoundingMode) (maxBytes maxExponent : Nat) :
    parse fmt input (rounding := rounding) (limits := true) (maxBytes := maxBytes)
        (maxExponent := maxExponent) =
      (TextParser.runBounded fmt rounding { maxBytes, maxExponent } input).map (·.value) := rfl

/-- With limits and status enabled, parsing returns the complete bounded core outcome. -/
@[simp] theorem parse_limits_status_eq_runBounded (fmt : FloatFormat) (input : String)
    (rounding : IEEERoundingMode) (maxBytes maxExponent : Nat) :
    parse fmt input (rounding := rounding) (limits := true) (maxBytes := maxBytes)
        (maxExponent := maxExponent) (status := true) =
      TextParser.runBounded fmt rounding { maxBytes, maxExponent } input := rfl

/-- A successful bounded parse returns exactly the value produced by unlimited parsing. -/
theorem parse_eq_of_parse_limits_eq_ok
    {fmt : FloatFormat} {input : String} {rounding : IEEERoundingMode}
    {maxBytes maxExponent : Nat} {value : Model fmt}
    (hparse : parse fmt input (rounding := rounding) (limits := true) (maxBytes := maxBytes)
      (maxExponent := maxExponent) = .ok value) :
    parse fmt input (rounding := rounding) = .ok value := by
  rw [parse_limits_eq_runBounded_map] at hparse
  rw [parse_eq_run]
  cases hrun : TextParser.runBounded fmt rounding { maxBytes, maxExponent } input with
  | error error =>
      simp [hrun, Except.map] at hparse
  | ok outcome =>
      rw [TextParser.run_eq_of_runBounded_eq_ok hrun]
      simpa [hrun, Except.map] using hparse

/-- A bounded parse with status preserves the unlimited parser's value and every exception flag. -/
theorem parse_status_eq_of_parse_limits_status_eq_ok
    {fmt : FloatFormat} {input : String} {rounding : IEEERoundingMode}
    {maxBytes maxExponent : Nat} {outcome : IEEEOutcome fmt}
    (hparse : parse fmt input (rounding := rounding) (limits := true) (maxBytes := maxBytes)
      (maxExponent := maxExponent) (status := true) = .ok outcome) :
    parse fmt input (rounding := rounding) (status := true) = .ok outcome := by
  rw [parse_limits_status_eq_runBounded] at hparse
  rw [parse_status_eq_run]
  exact TextParser.run_eq_of_runBounded_eq_ok hparse

end FloatLib.Floats.Formats.BinaryInterchange.Model
