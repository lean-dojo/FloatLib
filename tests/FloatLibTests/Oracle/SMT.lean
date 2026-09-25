/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.ExecFloat.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Instances
import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeDispatch
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Instances
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Runtime

/-!
# SMT-LIB floating-point differential runner

This standalone runner reads deterministic cases produced by `tests/oracles/smt_fp.py` and emits
the exact interchange word returned by configured `ExecFloat.Binary` execution.

Nearest-even arithmetic uses the ordinary certified dispatch selected for each format. The other
three IEEE directions use the explicit configured rounding API. Cross-format cases use the public
`ExecFloat.castWith` conversion with an explicit IEEE rounding context. Keeping this runner separate
from the shared oracle executable lets the SMT adapter remain independently runnable without
changing its command surface.

Input and output are tab-separated. The Python adapter owns comparison, aggregate counts, and
machine-readable reports; this module only parses cases and executes FloatLib.
-/

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Oracle.SMT

private abbrev Binary16 := ExecFloat.Binary 5 10
private abbrev Binary32 := ExecFloat.Binary 8 23
private abbrev Binary64 := ExecFloat.Binary 11 52

private inductive Operation where
  | add
  | sub
  | mul
  | div
  | sqrt
  | fma
  | cast

private def Operation.parse? : String → Option Operation
  | "add" => some .add
  | "sub" => some .sub
  | "mul" => some .mul
  | "div" => some .div
  | "sqrt" => some .sqrt
  | "fma" => some .fma
  | "cast" => some .cast
  | _ => none

private inductive Format where
  | f16
  | f32
  | f64
  deriving BEq

private def Format.parse? : String → Option Format
  | "f16" => some .f16
  | "f32" => some .f32
  | "f64" => some .f64
  | _ => none

private def Format.hexDigits : Format → Nat
  | .f16 => 4
  | .f32 => 8
  | .f64 => 16

private def parseRounding? : String → Option Model.IEEERoundingMode
  | "rne" => some .nearestEven
  | "rtz" => some .towardZero
  | "rtp" => some .towardPositiveInfinity
  | "rtn" => some .towardNegativeInfinity
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

private structure ArithmeticOps (Value : Type) where
  ofBits : Nat → Value
  toBits : Value → Nat
  add : Value → Value → Model.IEEERoundingMode → Value
  sub : Value → Value → Model.IEEERoundingMode → Value
  mul : Value → Value → Model.IEEERoundingMode → Value
  div : Value → Value → Model.IEEERoundingMode → Value
  sqrt : Value → Model.IEEERoundingMode → Value
  fma : Value → Value → Value → Model.IEEERoundingMode → Value

/--
Use the selected certified kernel for nearest-even and the explicit configured implementation for
directed rounding. This distinction exercises the ordinary execution path without pretending that
the nearest-even-only dispatcher chooses a process-global rounding mode.
-/
private def chooseBinary {Value : Type}
    (nearest : Value → Value → Value)
    (directed : Value → Value → Model.IEEERoundingMode → Value) :
    Value → Value → Model.IEEERoundingMode → Value :=
  fun left right rounding =>
    match rounding with
    | .nearestEven => nearest left right
    | _ => directed left right rounding

private def chooseUnary {Value : Type}
    (nearest : Value → Value)
    (directed : Value → Model.IEEERoundingMode → Value) :
    Value → Model.IEEERoundingMode → Value :=
  fun value rounding =>
    match rounding with
    | .nearestEven => nearest value
    | _ => directed value rounding

private def chooseTernary {Value : Type}
    (nearest : Value → Value → Value → Value)
    (directed : Value → Value → Value → Model.IEEERoundingMode → Value) :
    Value → Value → Value → Model.IEEERoundingMode → Value :=
  fun left right addend rounding =>
    match rounding with
    | .nearestEven => nearest left right addend
    | _ => directed left right addend rounding

private def binary16Ops : ArithmeticOps Binary16 where
  ofBits := fun bits => (ExecFloat.Binary.ofNatBits bits : Binary16)
  toBits := ExecFloat.Binary.toNatBits
  add := chooseBinary ExecFloat.add ExecFloat.Binary.addWithRounding
  sub := chooseBinary ExecFloat.sub ExecFloat.Binary.subWithRounding
  mul := chooseBinary ExecFloat.mul ExecFloat.Binary.mulWithRounding
  div := chooseBinary ExecFloat.div ExecFloat.Binary.divWithRounding
  sqrt := chooseUnary ExecFloat.sqrt ExecFloat.Binary.sqrtWithRounding
  fma := chooseTernary ExecFloat.fma ExecFloat.Binary.fmaWithRounding

private def binary32Ops : ArithmeticOps Binary32 where
  ofBits := fun bits => (ExecFloat.Binary.ofNatBits bits : Binary32)
  toBits := ExecFloat.Binary.toNatBits
  add := chooseBinary ExecFloat.add ExecFloat.Binary.addWithRounding
  sub := chooseBinary ExecFloat.sub ExecFloat.Binary.subWithRounding
  mul := chooseBinary ExecFloat.mul ExecFloat.Binary.mulWithRounding
  div := chooseBinary ExecFloat.div ExecFloat.Binary.divWithRounding
  sqrt := chooseUnary ExecFloat.sqrt ExecFloat.Binary.sqrtWithRounding
  fma := chooseTernary ExecFloat.fma ExecFloat.Binary.fmaWithRounding

private def binary64Ops : ArithmeticOps Binary64 where
  ofBits := fun bits => (ExecFloat.Binary.ofNatBits bits : Binary64)
  toBits := ExecFloat.Binary.toNatBits
  add := chooseBinary ExecFloat.add ExecFloat.Binary.addWithRounding
  sub := chooseBinary ExecFloat.sub ExecFloat.Binary.subWithRounding
  mul := chooseBinary ExecFloat.mul ExecFloat.Binary.mulWithRounding
  div := chooseBinary ExecFloat.div ExecFloat.Binary.divWithRounding
  sqrt := chooseUnary ExecFloat.sqrt ExecFloat.Binary.sqrtWithRounding
  fma := chooseTernary ExecFloat.fma ExecFloat.Binary.fmaWithRounding

private def ArithmeticOps.evaluate {Value : Type} (operations : ArithmeticOps Value)
    (operation : Operation) (rounding : Model.IEEERoundingMode)
    (operands : List Nat) : Except String Nat := do
  match operation, operands with
  | .add, [left, right] =>
      pure <| operations.toBits <|
        operations.add (operations.ofBits left) (operations.ofBits right) rounding
  | .sub, [left, right] =>
      pure <| operations.toBits <|
        operations.sub (operations.ofBits left) (operations.ofBits right) rounding
  | .mul, [left, right] =>
      pure <| operations.toBits <|
        operations.mul (operations.ofBits left) (operations.ofBits right) rounding
  | .div, [left, right] =>
      pure <| operations.toBits <|
        operations.div (operations.ofBits left) (operations.ofBits right) rounding
  | .sqrt, [value] =>
      pure <| operations.toBits <| operations.sqrt (operations.ofBits value) rounding
  | .fma, [left, right, addend] =>
      pure <| operations.toBits <|
        operations.fma
          (operations.ofBits left) (operations.ofBits right) (operations.ofBits addend) rounding
  | .cast, _ =>
      throw "internal error: cast reached same-format arithmetic"
  | _, values =>
      throw s!"wrong operand count: received {values.length}"

private def evaluateArithmetic (format : Format) (operation : Operation)
    (rounding : Model.IEEERoundingMode) (operands : List Nat) : Except String Nat :=
  match format with
  | .f16 => binary16Ops.evaluate operation rounding operands
  | .f32 => binary32Ops.evaluate operation rounding operands
  | .f64 => binary64Ops.evaluate operation rounding operands

private def castOutcomeBits {Value : Type}
    (toBits : Value → Nat) :
    ExecFloat.ConversionOutcome Value → Except String Nat
  | .success value _ => pure (toBits value)
  | .failure reason => throw s!"conversion failed: {repr reason}"

private def evaluateCast (source destination : Format)
    (rounding : Model.IEEERoundingMode) (operands : List Nat) : Except String Nat := do
  let bits ←
    match operands with
    | [value] => pure value
    | values => throw s!"wrong cast operand count: received {values.length}"
  let context :=
    ExecFloat.Binary.Conversion.Context.withRounding rounding.toRoundingMode
  match source, destination with
  | .f16, .f32 =>
      castOutcomeBits ExecFloat.Binary.toNatBits <|
        (ExecFloat.Binary.ofNatBits bits : Binary16).castWith
          (target := Binary32) context
  | .f16, .f64 =>
      castOutcomeBits ExecFloat.Binary.toNatBits <|
        (ExecFloat.Binary.ofNatBits bits : Binary16).castWith
          (target := Binary64) context
  | .f32, .f16 =>
      castOutcomeBits ExecFloat.Binary.toNatBits <|
        (ExecFloat.Binary.ofNatBits bits : Binary32).castWith
          (target := Binary16) context
  | .f32, .f64 =>
      castOutcomeBits ExecFloat.Binary.toNatBits <|
        (ExecFloat.Binary.ofNatBits bits : Binary32).castWith
          (target := Binary64) context
  | .f64, .f16 =>
      castOutcomeBits ExecFloat.Binary.toNatBits <|
        (ExecFloat.Binary.ofNatBits bits : Binary64).castWith
          (target := Binary16) context
  | .f64, .f32 =>
      castOutcomeBits ExecFloat.Binary.toNatBits <|
        (ExecFloat.Binary.ofNatBits bits : Binary64).castWith
          (target := Binary32) context
  | _, _ =>
      throw "cast source and destination formats must differ"

private def parseOperand (text : String) : Except String Nat :=
  match parseHex? text with
  | some value => pure value
  | none => throw s!"invalid hexadecimal operand: {text}"

private def evaluateLine (line : String) : Except String (String × Format × Nat) := do
  match fields line with
  | caseId :: operationText :: sourceText :: destinationText :: roundingText :: operandTexts =>
      let operation ←
        match Operation.parse? operationText with
        | some value => pure value
        | none => throw s!"unknown operation: {operationText}"
      let source ←
        match Format.parse? sourceText with
        | some value => pure value
        | none => throw s!"unknown source format: {sourceText}"
      let destination ←
        match Format.parse? destinationText with
        | some value => pure value
        | none => throw s!"unknown destination format: {destinationText}"
      let rounding ←
        match parseRounding? roundingText with
        | some value => pure value
        | none => throw s!"unknown rounding mode: {roundingText}"
      let operands ← operandTexts.mapM parseOperand
      let result ←
        match operation with
        | .cast => evaluateCast source destination rounding operands
        | _ =>
            if source != destination then
              throw "same-format arithmetic has different source and destination formats"
            else
              evaluateArithmetic source operation rounding operands
      pure (caseId, destination, result)
  | _ => throw "expected id, operation, source, destination, rounding, and operands"

private def hexText (digits value : Nat) : String :=
  let raw :=
    if value == 0 then "0" else String.ofList (Nat.toDigits 16 value)
  String.ofList (List.replicate (digits - raw.length) '0') ++ raw

private def fallbackId (line : String) : String :=
  (fields line).head?.getD "?"

private structure Statistics where
  cases : Nat := 0
  errorCount : Nat := 0

private partial def checkStream : IO Statistics := do
  let stdin ← IO.getStdin
  let rec loop (statistics : Statistics) : IO Statistics := do
    let line ← stdin.getLine
    if line.isEmpty then
      pure statistics
    else
      let trimmed := line.trimAscii.copy
      if trimmed.isEmpty || trimmed.startsWith "#" then
        loop statistics
      else
        match evaluateLine trimmed with
        | .ok (caseId, destination, bits) =>
            IO.println s!"{caseId}\tok\t{hexText destination.hexDigits bits}"
            loop { statistics with cases := statistics.cases + 1 }
        | .error message =>
            let caseId := fallbackId trimmed
            IO.println s!"{caseId}\terror"
            IO.eprintln s!"{caseId}: {message}\n  input: {trimmed}"
            loop {
              cases := statistics.cases + 1
              errorCount := statistics.errorCount + 1
            }
  loop {}

/-- Execute cases from standard input and return failure when any protocol row is invalid. -/
def run : IO UInt32 := do
  let statistics ← checkStream
  IO.eprintln s!"RESULT cases={statistics.cases} errors={statistics.errorCount}"
  pure <| if statistics.cases == 0 || statistics.errorCount != 0 then 1 else 0

end FloatLibTests.Oracle.SMT

public def main : IO UInt32 :=
  FloatLibTests.Oracle.SMT.run
