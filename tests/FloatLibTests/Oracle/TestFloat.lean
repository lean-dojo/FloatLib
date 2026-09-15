/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# Berkeley TestFloat stream checker

This executable consumes function-mode output from Berkeley TestFloat's `testfloat_gen`.
One generic implementation checks binary16, binary32, binary64, and binary128. Arithmetic
results are compared bit-for-bit. NaN payload and sign differences are ignored, because IEEE 754
does not prescribe one payload-propagation encoding, but quiet and signaling NaNs remain distinct.

The checker also compares all five IEEE exception flags. It expects TestFloat to use tininess
after rounding, matching `Model.*WithStatus`.

The checker calls logical `Model` operations directly. It does not execute configured `ExecFloat`
backends or the explicit `NativeFPU.Unchecked` host API.
-/

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Oracle.TestFloat

private inductive Operation where
  | add
  | sub
  | mul
  | div
  | mulAdd
  | sqrt
  | rem
  | roundToInt
  | eq
  | le
  | lt
  | eqSignaling
  | leQuiet
  | ltQuiet
  | minNum
  | maxNum
  | maxNumMag
  | copy
  | neg
  | abs
  | isSNaN
  | isSubnormal
  | isNormal
  | isInf
  | isFinite
  | isNaN
  | isZero
  | signBit
  | cast (destination : FloatFormat)
  deriving Repr

private def Operation.parse? : String → Option Operation
  | "add" => some .add
  | "sub" => some .sub
  | "mul" => some .mul
  | "div" => some .div
  | "mulAdd" => some .mulAdd
  | "sqrt" => some .sqrt
  | "rem" => some .rem
  | "roundToInt" => some .roundToInt
  | "eq" => some .eq
  | "le" => some .le
  | "lt" => some .lt
  | "eq_signaling" => some .eqSignaling
  | "le_quiet" => some .leQuiet
  | "lt_quiet" => some .ltQuiet
  | "minNum" => some .minNum
  | "maxNum" => some .maxNum
  | "maxNumMag" => some .maxNumMag
  | "copy" => some .copy
  | "neg" => some .neg
  | "abs" => some .abs
  | "isSNaN" => some .isSNaN
  | "isSubnormal" => some .isSubnormal
  | "isNormal" => some .isNormal
  | "isInf" => some .isInf
  | "isFinite" => some .isFinite
  | "isNaN" => some .isNaN
  | "isZero" => some .isZero
  | "signBit" => some .signBit
  | "to_bf16" => some (.cast .bfloat16)
  | "to_f16" => some (.cast .binary16)
  | "to_f32" => some (.cast .binary32)
  | "to_f64" => some (.cast .binary64)
  | "to_f128" => some (.cast .binary128)
  | _ => none

private def parseRoundingMode? : String → Option Model.IEEERoundingMode
  | "near_even" => some .nearestEven
  | "minMag" => some .towardZero
  | "min" => some .towardNegativeInfinity
  | "max" => some .towardPositiveInfinity
  | _ => none

private def formatName? : String → Option FloatFormat
  | "bf16" => some .bfloat16
  | "f16" => some .binary16
  | "f32" => some .binary32
  | "f64" => some .binary64
  | "f128" => some .binary128
  | _ => none

private def hexDigit? (character : Char) : Option Nat :=
  let code := character.toNat
  if 48 ≤ code ∧ code ≤ 57 then
    some (code - 48)
  else if 65 ≤ code ∧ code ≤ 70 then
    some (code - 55)
  else if 97 ≤ code ∧ code ≤ 102 then
    some (code - 87)
  else
    none

private def parseHex? (text : String) : Option Nat :=
  text.toList.foldlM
    (fun value character => do
      let digit ← hexDigit? character
      pure (16 * value + digit))
    0

private def fields (line : String) : List String :=
  (line.trimAscii.copy.splitToList (fun character => character.isWhitespace)).filter
    (fun field => !field.isEmpty)

private def statusBits (status : Model.IEEEStatus) : Nat :=
  (if status.inexact then 1 else 0) +
  (if status.underflow then 2 else 0) +
  (if status.overflow then 4 else 0) +
  (if status.divideByZero then 8 else 0) +
  (if status.invalid then 16 else 0)

private def sameResult {format : FloatFormat}
    (actual : Model format) (expectedBits : Nat) : Bool :=
  let expected := Model.ofNatBits (fmt := format) expectedBits
  if Model.isNaN actual && Model.isNaN expected then
    Model.isSNaN actual == Model.isSNaN expected
  else
    actual.toNatBits == expected.toNatBits

private structure Check where
  valueMatches : Bool
  flagsMatch : Bool
  actualValue : Nat
  expectedValue : Nat
  actualFlags : Nat
  expectedFlags : Nat

private def checkOutcome {format : FloatFormat}
    (outcome : Model.IEEEOutcome format)
    (expectedValue expectedFlags : Nat) : Check :=
  let actualFlags := statusBits outcome.status
  { valueMatches := sameResult outcome.value expectedValue
    flagsMatch := actualFlags == expectedFlags
    actualValue := outcome.value.toNatBits
    expectedValue
    actualFlags
    expectedFlags }

private def checkBoolean (actual : Bool) (expectedValue expectedFlags : Nat) : Check :=
  let actualValue := if actual then 1 else 0
  { valueMatches := actualValue == expectedValue
    flagsMatch := expectedFlags == 0
    actualValue
    expectedValue
    actualFlags := 0
    expectedFlags }

private def maxNumMag {format : FloatFormat}
    (left right : Model format) : Model format :=
  if Model.isSNaN left then
    Model.quietNaN left
  else if Model.isSNaN right then
    Model.quietNaN right
  else if Model.isNaN left then
    if Model.isNaN right then Model.quietNaN left else right
  else if Model.isNaN right then
    left
  else
    let leftMagnitude := (Model.abs left).toNatBits
    let rightMagnitude := (Model.abs right).toNatBits
    if rightMagnitude < leftMagnitude then
      left
    else if leftMagnitude < rightMagnitude then
      right
    else
      Model.maximum left right

private def unaryOutcome {format : FloatFormat}
    (value input : Model format) : Model.IEEEOutcome format :=
  Model.outcomeWithInvalid value (Model.isSNaN input)

private def selectionOutcome {format : FloatFormat}
    (value left right : Model format) : Model.IEEEOutcome format :=
  Model.outcomeWithInvalid value (Model.isSNaN left || Model.isSNaN right)

private def comparisonStatus {format : FloatFormat}
    (operation : Operation) (left right : Model format) : Model.IEEEStatus :=
  let invalid :=
    match operation with
    | .eq | .leQuiet | .ltQuiet =>
        Model.isSNaN left || Model.isSNaN right
    | .le | .lt | .eqSignaling =>
        Model.isNaN left || Model.isNaN right
    | _ => false
  { invalid }

private def comparisonResult {format : FloatFormat}
    (operation : Operation) (left right : Model format) : Bool :=
  match operation, Model.compare left right with
  | .eq, some .eq
  | .eqSignaling, some .eq => true
  | .le, some .lt
  | .le, some .eq
  | .leQuiet, some .lt
  | .leQuiet, some .eq => true
  | .lt, some .lt
  | .ltQuiet, some .lt => true
  | _, _ => false

private def parseBits (name : String) (width : Nat) (text : String) : Except String Nat := do
  let some bits := parseHex? text
    | throw s!"invalid hexadecimal {name}: {text}"
  if bits < 2 ^ width then
    pure bits
  else
    throw s!"{name} exceeds its {width}-bit format: {text}"

private def parseFloat (format : FloatFormat) (text : String) : Except String (Model format) := do
  let bits ← parseBits "floating-point field" format.bitWidth text
  pure (Model.ofNatBits (fmt := format) bits)

private def parseExpectedFloat (format : FloatFormat) (text : String) : Except String Nat :=
  parseBits "floating-point result" format.bitWidth text

private def parseExpected (name text : String) : Except String Nat := do
  let some value := parseHex? text
    | throw s!"invalid hexadecimal {name}: {text}"
  pure value

private def applyBinary? {format : FloatFormat}
    (operation : Operation) (rounding : Model.IEEERoundingMode)
    (left right : Model format) : Option (Model.IEEEOutcome format) :=
  match operation with
  | .add => some (Model.addWithStatus left right rounding)
  | .sub => some (Model.subWithStatus left right rounding)
  | .mul => some (Model.mulWithStatus left right rounding)
  | .div => some (Model.divWithStatus left right rounding)
  | .rem => some (Model.remainderWithStatus left right)
  | _ => none

private def checkLine (format : FloatFormat) (operation : Operation)
    (rounding : Model.IEEERoundingMode) (line : String) : Except String Check := do
  match operation, fields line with
  | .cast destination, [inputText, expectedText, flagsText] =>
      let input ← parseFloat format inputText
      let expected ← parseExpectedFloat destination expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkOutcome
        (Model.castWithStatus format destination input rounding) expected flags)
  | .sqrt, [inputText, expectedText, flagsText] =>
      let input ← parseFloat format inputText
      let expected ← parseExpectedFloat format expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkOutcome (Model.sqrtWithStatus input rounding) expected flags)
  | .roundToInt, [inputText, expectedText, flagsText] =>
      let input ← parseFloat format inputText
      let expected ← parseExpectedFloat format expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkOutcome (Model.roundToIntegralExactWithStatus input rounding) expected flags)
  | .copy, [inputText, expectedText, flagsText] =>
      let input ← parseFloat format inputText
      let expected ← parseExpectedFloat format expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkOutcome (unaryOutcome input input) expected flags)
  | .neg, [inputText, expectedText, flagsText] =>
      let input ← parseFloat format inputText
      let expected ← parseExpectedFloat format expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkOutcome (unaryOutcome (Model.neg input) input) expected flags)
  | .abs, [inputText, expectedText, flagsText] =>
      let input ← parseFloat format inputText
      let expected ← parseExpectedFloat format expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkOutcome (unaryOutcome (Model.abs input) input) expected flags)
  | .isSNaN, [inputText, expectedText, flagsText] =>
      let input ← parseFloat format inputText
      let expected ← parseExpected "Boolean result" expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkBoolean (Model.isSNaN input) expected flags)
  | .isSubnormal, [inputText, expectedText, flagsText] =>
      let input ← parseFloat format inputText
      let expected ← parseExpected "Boolean result" expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkBoolean (Model.isSubnormal input) expected flags)
  | .isNormal, [inputText, expectedText, flagsText] =>
      let input ← parseFloat format inputText
      let expected ← parseExpected "Boolean result" expectedText
      let flags ← parseExpected "flags" flagsText
      let actual := Model.isFinite input && !Model.isZero input && !Model.isSubnormal input
      pure (checkBoolean actual expected flags)
  | .isInf, [inputText, expectedText, flagsText] =>
      let input ← parseFloat format inputText
      let expected ← parseExpected "Boolean result" expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkBoolean (Model.isInf input) expected flags)
  | .isFinite, [inputText, expectedText, flagsText] =>
      let input ← parseFloat format inputText
      let expected ← parseExpected "Boolean result" expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkBoolean (Model.isFinite input) expected flags)
  | .isNaN, [inputText, expectedText, flagsText] =>
      let input ← parseFloat format inputText
      let expected ← parseExpected "Boolean result" expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkBoolean (Model.isNaN input) expected flags)
  | .isZero, [inputText, expectedText, flagsText] =>
      let input ← parseFloat format inputText
      let expected ← parseExpected "Boolean result" expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkBoolean (Model.isZero input) expected flags)
  | .signBit, [inputText, expectedText, flagsText] =>
      let input ← parseFloat format inputText
      let expected ← parseExpected "Boolean result" expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkBoolean (Model.signBit input) expected flags)
  | .mulAdd, [leftText, rightText, addendText, expectedText, flagsText] =>
      let left ← parseFloat format leftText
      let right ← parseFloat format rightText
      let addend ← parseFloat format addendText
      let expected ← parseExpectedFloat format expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkOutcome (Model.fmaWithStatus left right addend rounding) expected flags)
  | .add, [leftText, rightText, expectedText, flagsText]
  | .sub, [leftText, rightText, expectedText, flagsText]
  | .mul, [leftText, rightText, expectedText, flagsText]
  | .div, [leftText, rightText, expectedText, flagsText]
  | .rem, [leftText, rightText, expectedText, flagsText] =>
      let left ← parseFloat format leftText
      let right ← parseFloat format rightText
      let expected ← parseExpectedFloat format expectedText
      let flags ← parseExpected "flags" flagsText
      let some outcome := applyBinary? operation rounding left right
        | throw s!"internal operation/arity mismatch: {repr operation}"
      pure (checkOutcome outcome expected flags)
  | .minNum, [leftText, rightText, expectedText, flagsText] =>
      let left ← parseFloat format leftText
      let right ← parseFloat format rightText
      let expected ← parseExpectedFloat format expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkOutcome
        (selectionOutcome (Model.minNum left right) left right) expected flags)
  | .maxNum, [leftText, rightText, expectedText, flagsText] =>
      let left ← parseFloat format leftText
      let right ← parseFloat format rightText
      let expected ← parseExpectedFloat format expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkOutcome
        (selectionOutcome (Model.maxNum left right) left right) expected flags)
  | .maxNumMag, [leftText, rightText, expectedText, flagsText] =>
      let left ← parseFloat format leftText
      let right ← parseFloat format rightText
      let expected ← parseExpectedFloat format expectedText
      let flags ← parseExpected "flags" flagsText
      pure (checkOutcome
        (selectionOutcome (maxNumMag left right) left right) expected flags)
  | .eq, [leftText, rightText, expectedText, flagsText]
  | .le, [leftText, rightText, expectedText, flagsText]
  | .lt, [leftText, rightText, expectedText, flagsText]
  | .eqSignaling, [leftText, rightText, expectedText, flagsText]
  | .leQuiet, [leftText, rightText, expectedText, flagsText]
  | .ltQuiet, [leftText, rightText, expectedText, flagsText] =>
      let left ← parseFloat format leftText
      let right ← parseFloat format rightText
      let expected ← parseExpected "Boolean result" expectedText
      let flags ← parseExpected "flags" flagsText
      let actual := if comparisonResult operation left right then 1 else 0
      let actualFlags := statusBits (comparisonStatus operation left right)
      pure
        { valueMatches := actual == expected
          flagsMatch := actualFlags == flags
          actualValue := actual
          expectedValue := expected
          actualFlags
          expectedFlags := flags }
  | _, input =>
      throw s!"wrong field count for {repr operation}: {input.length}"

private structure Statistics where
  cases : Nat := 0
  valueMismatches : Nat := 0
  flagMismatches : Nat := 0
  parseErrors : Nat := 0

private def Statistics.failed (statistics : Statistics) : Bool :=
  statistics.cases == 0 ||
  statistics.valueMismatches != 0 ||
  statistics.flagMismatches != 0 ||
  statistics.parseErrors != 0

private def hexText (value : Nat) : String :=
  String.ofList (Nat.toDigits 16 value)

private def reportMismatch (caseNumber : Nat) (line : String) (check : Check) : IO Unit := do
  IO.eprintln s!"case {caseNumber}: {line.trimAscii.copy}"
  if !check.valueMatches then
    IO.eprintln
      s!"  result: actual={hexText check.actualValue} expected={hexText check.expectedValue}"
  if !check.flagsMatch then
    IO.eprintln
      s!"  flags: actual={hexText check.actualFlags} expected={hexText check.expectedFlags}"

private partial def checkStream (format : FloatFormat) (operation : Operation)
    (rounding : Model.IEEERoundingMode) (maximumReports : Nat) :
    IO Statistics := do
  let stdin ← IO.getStdin
  let rec loop (statistics : Statistics) (reports : Nat) : IO Statistics := do
    let line ← stdin.getLine
    if line.isEmpty then
      pure statistics
    else
      let caseNumber := statistics.cases + 1
      match checkLine format operation rounding line with
      | .ok check =>
          let mismatch := !check.valueMatches || !check.flagsMatch
          if mismatch && reports < maximumReports then
            reportMismatch caseNumber line check
          loop
            { cases := caseNumber
              valueMismatches :=
                statistics.valueMismatches + (if check.valueMatches then 0 else 1)
              flagMismatches :=
                statistics.flagMismatches + (if check.flagsMatch then 0 else 1)
              parseErrors := statistics.parseErrors }
            (reports + if mismatch then 1 else 0)
      | .error message =>
          if reports < maximumReports then
            IO.eprintln s!"case {caseNumber}: {message}\n  input: {line.trimAscii.copy}"
          loop
            { statistics with
              cases := caseNumber
              parseErrors := statistics.parseErrors + 1 }
            (reports + 1)
  loop {} 0

private def usage : String :=
  "usage: oracle testfloat {bf16|f16|f32|f64|f128} " ++
  "{add|sub|mul|div|mulAdd|sqrt|rem|roundToInt|eq|le|lt|" ++
  "eq_signaling|le_quiet|lt_quiet|minNum|maxNum|maxNumMag|copy|neg|abs|" ++
  "isSNaN|isSubnormal|isNormal|isInf|isFinite|isNaN|isZero|signBit|" ++
  "to_bf16|to_f16|to_f32|to_f64|to_f128} " ++
  "{near_even|minMag|min|max} [MAX_REPORTS]"

private def parseMaximumReports (text : String) : IO Nat :=
  match text.toNat? with
  | some value => pure value
  | none => throw <| IO.userError s!"invalid maximum report count: {text}"

/-- Check TestFloat vectors from standard input. -/
public def run (args : List String) : IO UInt32 := do
  let (formatText, operationText, roundingText, maximumReports) ←
    match args with
    | [format, operation, rounding] => pure (format, operation, rounding, 10)
    | [format, operation, rounding, maximum] =>
        pure (format, operation, rounding, ← parseMaximumReports maximum)
    | _ => throw <| IO.userError usage
  let format ←
    match formatName? formatText with
    | some value => pure value
    | none => throw <| IO.userError s!"unknown format: {formatText}\n{usage}"
  let operation ←
    match Operation.parse? operationText with
    | some value => pure value
    | none => throw <| IO.userError s!"unknown operation: {operationText}\n{usage}"
  let rounding ←
    match parseRoundingMode? roundingText with
    | some value => pure value
    | none => throw <| IO.userError s!"unknown rounding mode: {roundingText}\n{usage}"
  let statistics ← checkStream format operation rounding maximumReports
  IO.println <|
    s!"RESULT format={formatText} operation={operationText} rounding={roundingText} " ++
    s!"cases={statistics.cases} value_mismatches={statistics.valueMismatches} " ++
    s!"flag_mismatches={statistics.flagMismatches} parse_errors={statistics.parseErrors}"
  pure <| if statistics.failed then 1 else 0

end FloatLibTests.Oracle.TestFloat
