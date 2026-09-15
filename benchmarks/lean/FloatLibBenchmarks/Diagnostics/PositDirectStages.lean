/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Support.ExactWorkload
import FloatLibBenchmarks.Support.Sink
import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Direct.Runtime
import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Direct.Runtime
import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Runtime

/-!
# Direct Posit kernel diagnostics

This executable audits the width-generic square-root prefix kernel against the independent exact
squared-boundary implementation and times the two direct irrational-result pipelines:

* normalized quotient prefix and complete quotient rounding;
* integer-root prefix and complete square-root rounding.

The diagnostic contains no candidate, certificate, correction interval, or fallback-search
stage. Every measured operation is an actual stage of the current executable kernels.
-/

open FloatLib.Floats
open FloatLibBenchmarks.Support.ExactWorkload
open FloatLib.Floats.Formats.Posit
open FloatLib.Numerics

namespace FloatLibBenchmarks.Diagnostics.PositDirectStages

private instance : Inhabited FloatLib.Numerics.Dyadic where
  default := FloatLib.Numerics.Dyadic.zero

private structure AuditCounts where
  exact : Nat := 0
  belowByOne : Nat := 0
  aboveByOne : Nat := 0
  other : Nat := 0

private def AuditCounts.record
    (counts : AuditCounts) (actual reference : Nat) : AuditCounts :=
  if actual = reference then
    { counts with exact := counts.exact + 1 }
  else if actual + 1 = reference then
    { counts with belowByOne := counts.belowByOne + 1 }
  else if reference + 1 = actual then
    { counts with aboveByOne := counts.aboveByOne + 1 }
  else
    { counts with other := counts.other + 1 }

private def AuditCounts.mismatches (counts : AuditCounts) : Nat :=
  counts.belowByOne + counts.aboveByOne + counts.other

private def pushFiniteCode
    (format : Format) (codes : Array Nat) (code : Nat) : Array Nat :=
  if 0 < code && code < format.signMaskNat then
    codes.push code
  else
    codes

/-- Codes around finite endpoints, one, and every encoded power-of-two boundary. -/
private def boundaryCodes (format : Format) : Array Nat := Id.run do
  let mut codes := #[]
  for offset in [1:9] do
    codes := pushFiniteCode format codes offset
    codes := pushFiniteCode format codes (format.signMaskNat - offset)
    codes := pushFiniteCode format codes (format.oneCodeNat - offset)
    codes := pushFiniteCode format codes (format.oneCodeNat + offset)
  for bit in [0:format.payloadBits] do
    let boundary := 1 <<< bit
    codes := pushFiniteCode format codes boundary
    codes := pushFiniteCode format codes (boundary - 1)
    codes := pushFiniteCode format codes (boundary + 1)
    codes := pushFiniteCode format codes (format.signMaskNat - boundary)
    codes := pushFiniteCode format codes (format.signMaskNat - boundary - 1)
    codes := pushFiniteCode format codes (format.signMaskNat - boundary + 1)
  return codes

private def allPositiveCodes (format : Format) : Array Nat :=
  (Array.range (format.signMaskNat - 1)).map fun offset => offset + 1

private def publicSquareRootCodes (format : Format) : Array Nat :=
  (sqrtXs.map (Model.roundRat format)).foldl
    (fun codes value => pushFiniteCode format codes value.toNatBits) #[]

private def auditSquareRoot
    (format : Format) (codes : Array Nat) : AuditCounts :=
  Id.run do
    let mut counts : AuditCounts := {}
    for code in codes do
      let radicand :=
        Model.DyadicRounding.nonnegativeDyadicAt format code
      let actual :=
        Model.DirectDyadicSquareRoot.roundCode format radicand
      let reference :=
        Model.DyadicSquareRoot.roundCode format radicand
      counts := counts.record actual reference
    return counts

private def printAuditHeader : IO Unit :=
  IO.println <|
    "suite,totalBits,samples,exact,mismatches,belowByOne,aboveByOne,other"

private def reportAudit
    (suite : String) (format : Format) (codes : Array Nat) : IO Unit := do
  let counts := auditSquareRoot format codes
  IO.println <|
    s!"{suite},{format.bits},{codes.size},{counts.exact},{counts.mismatches}," ++
      s!"{counts.belowByOne},{counts.aboveByOne},{counts.other}"

@[noinline] private def quotientPrefixLoop
    (format : Format) :
    Nat → Array FloatLib.Numerics.Dyadic →
      Array FloatLib.Numerics.Dyadic → UInt64 → UInt64
  | 0, _, _, sink => sink
  | count + 1, numerators, denominators, sink =>
      let index := count &&& 15
      let quotientPrefix :=
        Model.DirectDyadicQuotient.quotientPrefix format
          numerators[index]! denominators[index]!
      quotientPrefixLoop format count numerators denominators
        (Support.Sink.mixNat
          (Support.Sink.mixNat sink quotientPrefix.significand)
          quotientPrefix.exponent.natAbs)

@[noinline] private def quotientRoundLoop
    (format : Format) :
    Nat → Array FloatLib.Numerics.Dyadic →
      Array FloatLib.Numerics.Dyadic → UInt64 → UInt64
  | 0, _, _, sink => sink
  | count + 1, numerators, denominators, sink =>
      let index := count &&& 15
      let code :=
        Model.DirectDyadicQuotient.roundPositiveCode format
          numerators[index]! denominators[index]!
      quotientRoundLoop format count numerators denominators
        (Support.Sink.mixNat sink code)

@[noinline] private def squareRootPrefixLoop
    (format : Format) :
    Nat → Array FloatLib.Numerics.Dyadic → UInt64 → UInt64
  | 0, _, sink => sink
  | count + 1, radicands, sink =>
      let index := count &&& 15
      let rootPrefix :=
        Model.DirectDyadicSquareRoot.rootPrefix
          format radicands[index]!
      squareRootPrefixLoop format count radicands
        (Support.Sink.mixNat
          (Support.Sink.mixNat sink rootPrefix.significand)
          rootPrefix.exponent.natAbs)

@[noinline] private def squareRootRoundLoop
    (format : Format) :
    Nat → Array FloatLib.Numerics.Dyadic → UInt64 → UInt64
  | 0, _, sink => sink
  | count + 1, radicands, sink =>
      let index := count &&& 15
      let code :=
        Model.DirectDyadicSquareRoot.roundCode
          format radicands[index]!
      squareRootRoundLoop format count radicands
        (Support.Sink.mixNat sink code)

private def iterationCount (width : Nat) : Nat :=
  if width ≤ 128 then 4096
  else if width ≤ 256 then 2048
  else if width ≤ 512 then 1024
  else if width ≤ 1024 then 512
  else if width ≤ 2048 then 256
  else 128

private def measure (format : Format) (operation stage : String)
    (iterations : Nat) (run : Nat → UInt64) : IO Unit := do
  let resultRef ← IO.mkRef 0
  resultRef.set (run (min iterations 17))
  let start ← IO.monoNanosNow
  resultRef.set (run iterations)
  let stop ← IO.monoNanosNow
  let sink ← resultRef.get
  let elapsed := stop - start
  IO.println <|
    s!"{format.bits},{operation},{stage},{iterations},{elapsed}," ++
      s!"{elapsed / iterations},{sink.toNat}"

private def printTimingHeader : IO Unit :=
  IO.println "totalBits,operation,stage,iterations,totalNanos,nanosPerOperation,sink"

private def benchmarkWidth (format : Format) : IO Unit := do
  let numerators :=
    (xs.map (Model.roundRat format)).map fun value =>
      Model.DyadicRounding.magnitude value.toDyadic?.get!
  let denominators :=
    (ys.map (Model.roundRat format)).map fun value =>
      Model.DyadicRounding.magnitude value.toDyadic?.get!
  let radicands :=
    (sqrtXs.map (Model.roundRat format)).map fun value =>
      value.toDyadic?.get!
  let iterations := iterationCount format.bits
  measure format "div" "quotient-prefix" iterations fun count =>
    quotientPrefixLoop format count numerators denominators 0
  measure format "div" "complete-round" iterations fun count =>
    quotientRoundLoop format count numerators denominators 0
  measure format "sqrt" "root-prefix" iterations fun count =>
    squareRootPrefixLoop format count radicands 0
  measure format "sqrt" "complete-round" iterations fun count =>
    squareRootRoundLoop format count radicands 0

private def parseNat (label text : String) : IO Nat :=
  match text.toNat? with
  | some value => pure value
  | none => throw <| IO.userError s!"invalid {label}: {text}"

private def formatOfWidth (width : Nat) : IO Format := do
  if hwidth : 2 ≤ width then
    pure (Format.ofBits width hwidth)
  else
    throw <| IO.userError s!"Posit width must be at least 2: {width}"

private def auditSmallWidth (width : Nat) : IO Unit := do
  unless width ≤ 16 do
    throw <| IO.userError s!"exhaustive audit width must be at most 16: {width}"
  let format ← formatOfWidth width
  printAuditHeader
  reportAudit "exhaustive" format (allPositiveCodes format)

private def auditWideWidth (width : Nat) : IO Unit := do
  let format ← formatOfWidth width
  printAuditHeader
  reportAudit "boundary" format
    (boundaryCodes format ++ publicSquareRootCodes format)

private def wideFormats : Array Format :=
  #[Format.ofBits 32, Format.ofBits 64, Format.ofBits 128,
    Format.ofBits 256, Format.ofBits 512, Format.ofBits 1024,
    Format.ofBits 2048, Format.ofBits 4096]

private def smallFormats : Array Format :=
  #[Format.ofBits 2, Format.ofBits 3, Format.ofBits 4, Format.ofBits 5,
    Format.ofBits 6, Format.ofBits 7, Format.ofBits 8, Format.ofBits 9,
    Format.ofBits 10, Format.ofBits 11, Format.ofBits 12, Format.ofBits 13,
    Format.ofBits 14, Format.ofBits 15, Format.ofBits 16]

def run : IO Unit := do
  printAuditHeader
  for format in smallFormats do
    reportAudit "exhaustive" format (allPositiveCodes format)
  for format in wideFormats do
    reportAudit "boundary" format
      (boundaryCodes format ++ publicSquareRootCodes format)
  IO.println ""
  printTimingHeader
  for format in wideFormats do
    benchmarkWidth format

def runArgs : List String → IO Unit
  | [] | ["all"] =>
      run
  | ["audit-small", widthText] => do
      auditSmallWidth (← parseNat "width" widthText)
  | ["audit-wide", widthText] => do
      auditWideWidth (← parseNat "width" widthText)
  | ["timing", widthText] => do
      let format ← formatOfWidth (← parseNat "width" widthText)
      printTimingHeader
      benchmarkWidth format
  | _ =>
      throw <| IO.userError <|
        "usage: execFloatPositDirectStages " ++
          "[all | audit-small WIDTH | audit-wide WIDTH | timing WIDTH]"

end FloatLibBenchmarks.Diagnostics.PositDirectStages

public def main (args : List String) : IO Unit :=
  FloatLibBenchmarks.Diagnostics.PositDirectStages.runArgs args
