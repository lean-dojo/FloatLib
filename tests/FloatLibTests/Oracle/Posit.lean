/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.Posit

/-!
# SoftPosit stream checker

This checker consumes the compact binary protocol emitted by `tests/oracles/softposit_emitter.c`.
The versioned header binds the stream to its generation mode, complete source case space, shard,
seed, expected record count, and exact SoftPosit Git revision. Records must then carry precisely
the case identifiers implied by that metadata. A missing, duplicated, reordered, or extra record
is a protocol failure rather than an accidentally smaller test.

The C oracle and Lean checker remain separate processes: SoftPosit computes reference words in C,
while this module reconstructs public `ExecFloat.Posit n` values and calls the statically selected
Lean backend for that width.

SoftPosit's generic pX2 carrier stores an `n`-bit posit left-aligned in a 32-bit word. The emitter
validates that every result has canonical zero padding and sends only the compact `n`-bit word.
The checker never observes FloatLib's internal byte, word, pair, or limb carrier.
-/

namespace FloatLibTests.Oracle.Posit

open FloatLib.Floats

private inductive Operation where
  | add
  | sub
  | mul
  | div
  | fma
  | sqrt
  | rint
  | eq
  | le
  | lt
  deriving BEq, Repr

private def Operation.ofId? : UInt8 → Option Operation
  | 1 => some .add
  | 2 => some .sub
  | 3 => some .mul
  | 4 => some .div
  | 5 => some .fma
  | 6 => some .sqrt
  | 7 => some .rint
  | 8 => some .eq
  | 9 => some .le
  | 10 => some .lt
  | _ => none

private def Operation.name : Operation → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"
  | .fma => "fma"
  | .sqrt => "sqrt"
  | .rint => "rint"
  | .eq => "eq"
  | .le => "le"
  | .lt => "lt"

private def Operation.arity : Operation → Nat
  | .sqrt | .rint => 1
  | .add | .sub | .mul | .div | .eq | .le | .lt => 2
  | .fma => 3

private def Operation.isComparison : Operation → Bool
  | .eq | .le | .lt => true
  | _ => false

private inductive Family where
  | px2
  | p32
  deriving BEq

private def Family.ofId? : UInt8 → Option Family
  | 0 => some .px2
  | 1 => some .p32
  | _ => none

private def Family.name : Family → String
  | .px2 => "px2"
  | .p32 => "p32"

private inductive GenerationMode where
  | exhaustive
  | sampled
  deriving BEq

private def GenerationMode.ofId? : UInt8 → Option GenerationMode
  | 0 => some .exhaustive
  | 1 => some .sampled
  | _ => none

private def GenerationMode.name : GenerationMode → String
  | .exhaustive => "exhaustive"
  | .sampled => "sampled"

private structure Header where
  bits : Nat
  operation : Operation
  family : Family
  mode : GenerationMode
  sourceCases : Nat
  expectedCases : Nat
  firstCaseId : Nat
  caseStride : Nat
  seed : Nat
  sourceRevision : String

private structure Statistics where
  cases : Nat := 0
  mismatches : Nat := 0
  protocolErrors : Nat := 0

private def Statistics.failed (statistics : Statistics) : Bool :=
  statistics.cases == 0 || statistics.mismatches != 0 || statistics.protocolErrors != 0

private structure Check where
  caseId : Nat
  expected : Nat
  actual : Nat
  operands : Array Nat

private def byte (bytes : ByteArray) (offset : Nat) : Nat :=
  (bytes.get! offset).toNat

private def uint32LE (bytes : ByteArray) (offset : Nat) : Nat :=
  byte bytes offset +
    (byte bytes (offset + 1) <<< 8) +
    (byte bytes (offset + 2) <<< 16) +
    (byte bytes (offset + 3) <<< 24)

private def uint64LE (bytes : ByteArray) (offset : Nat) : Nat :=
  uint32LE bytes offset + (uint32LE bytes (offset + 4) <<< 32)

private def hexText (value : Nat) : String :=
  String.ofList (Nat.toDigits 16 value)

private def byteHexText (value : Nat) : String :=
  if value < 16 then "0" ++ hexText value else hexText value

private def revisionText (bytes : ByteArray) : String :=
  String.intercalate "" <|
    (List.range 20).map fun index => byteHexText (byte bytes (56 + index))

private def protocolHeaderSize : Nat :=
  80

private def expectedCaseCount (sourceCases firstCaseId caseStride : Nat) : Nat :=
  if firstCaseId < sourceCases then
    1 + (sourceCases - 1 - firstCaseId) / caseStride
  else
    0

private def decodeHeader (bytes : ByteArray) : Except String Header := do
  if bytes.size < protocolHeaderSize then
    throw s!"truncated protocol header: received {bytes.size} of {protocolHeaderSize} bytes"
  if byte bytes 0 != 0x53 || byte bytes 1 != 0x50 ||
      byte bytes 2 != 0x58 || byte bytes 3 != 0x32 then
    throw "invalid protocol magic (expected SPX2)"
  if byte bytes 4 != 2 then
    throw s!"unsupported protocol version: {byte bytes 4}"
  if byte bytes 5 != protocolHeaderSize then
    throw s!"invalid protocol header size: {byte bytes 5}"
  let bits := byte bytes 6
  if bits < 2 || 32 < bits then
    throw s!"invalid posit width in protocol header: {bits}"
  let some operation := Operation.ofId? (bytes.get! 7)
    | throw s!"unknown operation id: {byte bytes 7}"
  let some family := Family.ofId? (bytes.get! 8)
    | throw s!"unknown SoftPosit family id: {byte bytes 8}"
  if family == .p32 && bits != 32 then
    throw "the named p32 family is valid only at width 32"
  if byte bytes 9 != operation.arity then
    throw s!"header arity {byte bytes 9} does not match {operation.name}"
  let some mode := GenerationMode.ofId? (bytes.get! 10)
    | throw s!"unknown generation mode id: {byte bytes 10}"
  for offset in [11:16] do
    if byte bytes offset != 0 then
      throw s!"nonzero reserved header byte at offset {offset}"
  let expectedCases := uint64LE bytes 16
  let firstCaseId := uint64LE bytes 24
  let caseStride := uint64LE bytes 32
  let sourceCases := uint64LE bytes 40
  let seed := uint64LE bytes 48
  if caseStride = 0 then
    throw "case stride must be positive"
  if caseStride ≤ firstCaseId then
    throw s!"invalid shard metadata: first case {firstCaseId} is not below stride {caseStride}"
  if sourceCases = 0 then
    throw "source case count must be positive"
  if sourceCases ≤ firstCaseId then
    throw s!"selected shard starts at {firstCaseId}, outside {sourceCases} source cases"
  match mode with
  | .exhaustive =>
      let indexBits := bits * operation.arity
      if 64 ≤ indexBits then
        throw s!"exhaustive index width {indexBits} does not fit the protocol's 64-bit case id"
      let completeSpace := 2 ^ indexBits
      if sourceCases != completeSpace then
        throw s!"exhaustive source count {sourceCases} does not match 2^{indexBits}"
  | .sampled =>
      pure ()
  let derivedCases := expectedCaseCount sourceCases firstCaseId caseStride
  if expectedCases != derivedCases then
    throw <|
      s!"header expects {expectedCases} records, but its source and shard metadata imply " ++
        s!"{derivedCases}"
  if expectedCases = 0 then
    throw "the selected shard contains no cases"
  let mut revisionNonzero := false
  for offset in [56:76] do
    if byte bytes offset != 0 then
      revisionNonzero := true
  if !revisionNonzero then
    throw "SoftPosit source revision is the all-zero object id"
  for offset in [76:80] do
    if byte bytes offset != 0 then
      throw s!"nonzero reserved header byte at offset {offset}"
  pure {
    bits
    operation
    family
    mode
    sourceCases
    expectedCases
    firstCaseId
    caseStride
    seed
    sourceRevision := revisionText bytes
  }

@[inline] private def evaluate {bits : Nat} (bits_ge_two : 2 ≤ bits)
    (operation : Operation) (operands : Array Nat) : Except String Nat := do
  let value (index : Nat) : ExecFloat.Posit bits bits_ge_two :=
    ExecFloat.Posit.ofNatBits (operands[index]!)
  match operation with
  | .add => pure <| ExecFloat.Posit.toNatBits (ExecFloat.add (value 0) (value 1))
  | .sub => pure <| ExecFloat.Posit.toNatBits (ExecFloat.sub (value 0) (value 1))
  | .mul => pure <| ExecFloat.Posit.toNatBits (ExecFloat.mul (value 0) (value 1))
  | .div => pure <| ExecFloat.Posit.toNatBits (ExecFloat.div (value 0) (value 1))
  | .fma =>
      pure <| ExecFloat.Posit.toNatBits (ExecFloat.fma (value 0) (value 1) (value 2))
  | .sqrt => pure <| ExecFloat.Posit.toNatBits (ExecFloat.sqrt (value 0))
  | .rint => pure <| ExecFloat.Posit.toNatBits (ExecFloat.Posit.nearestInt (value 0))
  | .eq => pure <| if ExecFloat.compareEqual (value 0) (value 1) then 1 else 0
  | .le => pure <| if ExecFloat.compareLessEqual (value 0) (value 1) then 1 else 0
  | .lt => pure <| if ExecFloat.compareLess (value 0) (value 1) then 1 else 0

private def recordSize (operation : Operation) : Nat :=
  8 + 4 * (operation.arity + 1)

private def decodeOperands (operation : Operation) (record : ByteArray) : Array Nat :=
  Array.ofFn fun index : Fin operation.arity =>
    uint32LE record (8 + 4 * index)

private def reportMismatch (header : Header) (caseId expected actual : Nat)
    (operands : Array Nat) : IO Unit := do
  let rendered := String.intercalate " " <|
    operands.toList.map fun operand => s!"0x{hexText operand}"
  IO.eprintln <|
    s!"case {caseId}: family={header.family.name} bits={header.bits} " ++
      s!"operation={header.operation.name} operands=[{rendered}]"
  IO.eprintln s!"  result: actual=0x{hexText actual} expected=0x{hexText expected}"

private def checkRecord {bits : Nat} (bits_ge_two : 2 ≤ bits)
    (header : Header) (expectedCaseId : Nat) (record : ByteArray) : Except String Check := do
  let caseId := uint64LE record 0
  if caseId != expectedCaseId then
    throw s!"case id {caseId} does not match the required id {expectedCaseId}"
  if header.sourceCases ≤ caseId then
    throw s!"case id {caseId} lies outside the source case space {header.sourceCases}"
  let operands := decodeOperands header.operation record
  let expected := uint32LE record (8 + 4 * header.operation.arity)
  let limit := 2 ^ bits
  for operand in operands do
    if limit ≤ operand then
      throw s!"case {caseId}: non-compact operand 0x{hexText operand} for {bits} bits"
  if header.operation.isComparison && expected > 1 then
    throw s!"case {caseId}: comparison result is not Boolean: 0x{hexText expected}"
  if !header.operation.isComparison && limit ≤ expected then
    throw s!"case {caseId}: non-compact result 0x{hexText expected} for {bits} bits"
  let actual ← evaluate bits_ge_two header.operation operands
  pure { caseId, expected, actual, operands }

private partial def checkBuffered {bits : Nat} (bits_ge_two : 2 ≤ bits)
    (stdin : IO.FS.Stream) (header : Header) (maximumReports : Nat)
    (buffer : ByteArray) (cursor reports : Nat) (statistics : Statistics) :
    IO Statistics := do
  let size := recordSize header.operation
  if cursor + size ≤ buffer.size then
    let record := buffer.extract cursor (cursor + size)
    let expectedCaseId := header.firstCaseId + statistics.cases * header.caseStride
    match checkRecord bits_ge_two header expectedCaseId record with
    | .ok check =>
        let mismatch := check.actual != check.expected
        if mismatch && reports < maximumReports then
          reportMismatch header check.caseId check.expected check.actual check.operands
        checkBuffered bits_ge_two stdin header maximumReports buffer (cursor + size)
          (reports + if mismatch then 1 else 0)
          { statistics with
            cases := statistics.cases + 1
            mismatches := statistics.mismatches + if mismatch then 1 else 0 }
    | .error message =>
        if reports < maximumReports then
          IO.eprintln s!"record {statistics.cases + 1}: {message}"
        checkBuffered bits_ge_two stdin header maximumReports buffer (cursor + size)
          (reports + 1)
          { statistics with
            cases := statistics.cases + 1
            protocolErrors := statistics.protocolErrors + 1 }
  else
    let remainder := buffer.extract cursor buffer.size
    let chunk ← stdin.read (1024 * 1024)
    if chunk.isEmpty then
      let completed ←
        if remainder.isEmpty then
          pure statistics
        else
          IO.eprintln s!"truncated final record: received {remainder.size} of {size} bytes"
          pure { statistics with protocolErrors := statistics.protocolErrors + 1 }
      if completed.cases == header.expectedCases then
        pure completed
      else
        IO.eprintln <|
          s!"final case count {completed.cases} does not match authenticated expectation " ++
            s!"{header.expectedCases}"
        pure { completed with protocolErrors := completed.protocolErrors + 1 }
    else
      checkBuffered bits_ge_two stdin header maximumReports (remainder.append chunk) 0 reports
        statistics

private def checkWidth {bits : Nat} (bits_ge_two : 2 ≤ bits)
    (stdin : IO.FS.Stream) (header : Header) (maximumReports : Nat)
    (buffer : ByteArray) : IO Statistics :=
  checkBuffered bits_ge_two stdin header maximumReports buffer protocolHeaderSize 0 {}

private def dispatchWidth (stdin : IO.FS.Stream) (header : Header) (maximumReports : Nat)
    (buffer : ByteArray) : IO Statistics :=
  match header.bits with
  | 2 => checkWidth (bits := 2) (by decide) stdin header maximumReports buffer
  | 3 => checkWidth (bits := 3) (by decide) stdin header maximumReports buffer
  | 4 => checkWidth (bits := 4) (by decide) stdin header maximumReports buffer
  | 5 => checkWidth (bits := 5) (by decide) stdin header maximumReports buffer
  | 6 => checkWidth (bits := 6) (by decide) stdin header maximumReports buffer
  | 7 => checkWidth (bits := 7) (by decide) stdin header maximumReports buffer
  | 8 => checkWidth (bits := 8) (by decide) stdin header maximumReports buffer
  | 9 => checkWidth (bits := 9) (by decide) stdin header maximumReports buffer
  | 10 => checkWidth (bits := 10) (by decide) stdin header maximumReports buffer
  | 11 => checkWidth (bits := 11) (by decide) stdin header maximumReports buffer
  | 12 => checkWidth (bits := 12) (by decide) stdin header maximumReports buffer
  | 13 => checkWidth (bits := 13) (by decide) stdin header maximumReports buffer
  | 14 => checkWidth (bits := 14) (by decide) stdin header maximumReports buffer
  | 15 => checkWidth (bits := 15) (by decide) stdin header maximumReports buffer
  | 16 => checkWidth (bits := 16) (by decide) stdin header maximumReports buffer
  | 17 => checkWidth (bits := 17) (by decide) stdin header maximumReports buffer
  | 18 => checkWidth (bits := 18) (by decide) stdin header maximumReports buffer
  | 19 => checkWidth (bits := 19) (by decide) stdin header maximumReports buffer
  | 20 => checkWidth (bits := 20) (by decide) stdin header maximumReports buffer
  | 21 => checkWidth (bits := 21) (by decide) stdin header maximumReports buffer
  | 22 => checkWidth (bits := 22) (by decide) stdin header maximumReports buffer
  | 23 => checkWidth (bits := 23) (by decide) stdin header maximumReports buffer
  | 24 => checkWidth (bits := 24) (by decide) stdin header maximumReports buffer
  | 25 => checkWidth (bits := 25) (by decide) stdin header maximumReports buffer
  | 26 => checkWidth (bits := 26) (by decide) stdin header maximumReports buffer
  | 27 => checkWidth (bits := 27) (by decide) stdin header maximumReports buffer
  | 28 => checkWidth (bits := 28) (by decide) stdin header maximumReports buffer
  | 29 => checkWidth (bits := 29) (by decide) stdin header maximumReports buffer
  | 30 => checkWidth (bits := 30) (by decide) stdin header maximumReports buffer
  | 31 => checkWidth (bits := 31) (by decide) stdin header maximumReports buffer
  | 32 => checkWidth (bits := 32) (by decide) stdin header maximumReports buffer
  | _ => throw <| IO.userError s!"unsupported posit width: {header.bits}"

private partial def readInitialBuffer (stdin : IO.FS.Stream) : IO ByteArray := do
  let rec loop (buffer : ByteArray) : IO ByteArray := do
    if protocolHeaderSize ≤ buffer.size then
      pure buffer
    else
      let chunk ← stdin.read (1024 * 1024)
      if chunk.isEmpty then
        throw <| IO.userError <|
          s!"truncated protocol header: received {buffer.size} of {protocolHeaderSize} bytes"
      loop (buffer.append chunk)
  loop ByteArray.empty

private def usage : String :=
  "usage: oracle posit [MAX_REPORTS]"

private def parseMaximumReports (text : String) : IO Nat :=
  match text.toNat? with
  | some value => pure value
  | none => throw <| IO.userError s!"invalid maximum report count: {text}"

/-- Compare a SoftPosit pX2 or named-p32 stream against public configured posit operations. -/
public def run (args : List String) : IO UInt32 := do
  let maximumReports ←
    match args with
    | [] => pure 10
    | [text] => parseMaximumReports text
    | _ => throw <| IO.userError usage
  let stdin ← IO.getStdin
  if ← stdin.isTty then
    throw <| IO.userError "refusing to read a binary SoftPosit stream from a terminal"
  let buffer ← readInitialBuffer stdin
  let header ←
    match decodeHeader buffer with
    | .ok value => pure value
    | .error message => throw <| IO.userError message
  let statistics ← dispatchWidth stdin header maximumReports buffer
  IO.println <|
    s!"RESULT oracle=softposit family={header.family.name} bits={header.bits} " ++
      s!"operation={header.operation.name} mode={header.mode.name} " ++
      s!"source_cases={header.sourceCases} expected_cases={header.expectedCases} " ++
      s!"first_case={header.firstCaseId} stride={header.caseStride} seed={header.seed} " ++
      s!"revision={header.sourceRevision} cases={statistics.cases} " ++
      s!"mismatches={statistics.mismatches} protocol_errors={statistics.protocolErrors}"
  pure <| if statistics.failed then 1 else 0

end FloatLibTests.Oracle.Posit
