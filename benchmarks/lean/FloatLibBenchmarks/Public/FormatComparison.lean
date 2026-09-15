/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.Sweep
import FloatLibBenchmarks.Support.ExactWorkload
import FloatLibBenchmarks.Support.Posit
public meta import Lean.Elab.Command

/-!
# Fair same-workload posit and binary-format comparison

We wanted one comparison where every implementation consumes the same exact inputs and follows
the same dependency chain. This executable compares current-standard posits with binary encodings
at equal total storage widths wherever both families exist. Posits begin at their two-bit minimum;
configured binary formats begin at four bits. For widths four through eight, the binary exponent field is
`width / 2` and the fraction field consumes the remaining non-sign bits. This single rule reaches
the existing E4M3 layout at eight bits without inventing per-width formats. Widths 16, 32, 64, and
128 use the corresponding IEEE 754 binary interchange layouts. Widths 96 and 112 keep the
binary128 exponent field with 80- and 96-bit fractions, so the two-word kernel is measured at three
storage widths. Widths 24 and 48 probe the machine-word tier between the IEEE widths with
documented custom layouts (8 exponent bits with 15 fraction bits, and 11 exponent bits with 36
fraction bits). Wider rows deliberately use a
documented custom binary layout with 19 exponent bits and all remaining non-sign bits as fraction
bits; they are never labelled IEEE formats. Every lane begins from the exact rational vectors in
`Benchmarks.Support.ExactWorkload`; each format rounds those mathematical inputs once, before
timing. The comparison therefore does not assume that unlike encodings represent the same set.

This executable emits only `proved-software` rows. Public binary32 and binary64 dispatch already
selects the proved fixed-word kernels; their specialized rows pin those same kernels directly so
the benchmark label does not depend on planner metadata. The cross-implementation runner
compiles its binary32/64 hardware ceiling as a separate C executable and validates every measured
result against MPFR before timing. Keeping that external lane out of this module prevents a
Lean-native diagnostic from being mistaken for the independent C baseline.

Every timed loop is latency-oriented: an observed result selects the next member of the fixed,
ordinary-input vector. We adapted the dependency-chain part directly from Abel and Reineke's
uops.info methodology (https://doi.org/10.1145/3297858.3304062), then used a finite fixture set so
multiply, divide, and square root do not collapse into overflow, underflow, or a fixed point. The
CSV calls this `result-dependent-fixture-chain`; the comparison plot rejects raw runs that mix
this method with the earlier counter-indexed loop.

The 8-bit binary row is explicitly the library's E4M3 binary encoding, not a generic “IEEE
binary8”: IEEE 754 does not define a binary8 interchange format, and practical E4M3/E5M2
encodings have distinct exceptional-value policies. Specialized FP8 variants remain in the
dedicated FP8 comparison.
-/

open FloatLib.Floats
open FloatLib.Numerics
open FloatLibBenchmarks.Support
open FloatLibBenchmarks.Support.Environment
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.Posit

open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput

namespace FloatLibBenchmarks.Public.FormatComparison

namespace Exact

def xs : Array Rat :=
  FloatLibBenchmarks.Support.ExactWorkload.xs

def ys : Array Rat :=
  FloatLibBenchmarks.Support.ExactWorkload.ys

def sqrtXs : Array Rat :=
  FloatLibBenchmarks.Support.ExactWorkload.sqrtXs

end Exact

namespace PositSupport

def inputsX
    (F : Type) [EncodedFormat F]
    [BenchmarkCarrier F
      FloatLib.Floats.Formats.Posit.Format FloatLib.Floats.Formats.Posit.Model] :
    Array (ExecFloat F) :=
  FloatLibBenchmarks.Support.Posit.inputsX F

def inputsY
    (F : Type) [EncodedFormat F]
    [BenchmarkCarrier F
      FloatLib.Floats.Formats.Posit.Format FloatLib.Floats.Formats.Posit.Model] :
    Array (ExecFloat F) :=
  FloatLibBenchmarks.Support.Posit.inputsY F

def inputsSqrt
    (F : Type) [EncodedFormat F]
    [BenchmarkCarrier F
      FloatLib.Floats.Formats.Posit.Format FloatLib.Floats.Formats.Posit.Model] :
    Array (ExecFloat F) :=
  FloatLibBenchmarks.Support.Posit.inputsSqrt F

@[inline] def resultBits
    {F : Type} [EncodedFormat F]
    [BenchmarkCarrier F
      FloatLib.Floats.Formats.Posit.Format FloatLib.Floats.Formats.Posit.Model]
    (value : ExecFloat F) : UInt64 :=
  FloatLibBenchmarks.Support.Posit.resultBits value

end PositSupport

namespace BinarySupport

private def exponentMix : UInt64 :=
  0x9e3779b97f4a7c15

private def signMix : UInt64 :=
  0x8000000000000000

private def zeroTag : UInt64 :=
  0x2d358dccaa6c78a5

private def infinityTag : UInt64 :=
  0x8bb84b93962eacc9

private def nanTag : UInt64 :=
  0x4f1bbcdc6764c1ab

@[inline] private def signedTag (tag : UInt64) (negative : Bool) : UInt64 :=
  tag ^^^ if negative then signMix else 0

@[inline] private def finiteFingerprint
    (negative : Bool) (exponent : Int) (significand : UInt64) : UInt64 :=
  significand ^^^ (UInt64.ofInt exponent * exponentMix) ^^^
    if negative then signMix else 0

/--
Return the shared dependency token for an IEEE-style binary result.

For formats that fit in one machine word, the token records the normalized
sign, exponent, and significand. This is the same calculation used by the C,
MPFR, SoftFloat, and CPython adapters. Above 64 bits, the normalized
significand's low word is already the encoding's low fraction word, so we use
that directly instead of putting an arbitrary-precision decode in the timed
loop. The runner checks FloatLib and MPFR sinks and fixture traces before it
accepts a campaign.
-/
@[inline] def resultBits
    {F : Type} [EncodedFormat F]
    [carrier : BenchmarkCarrier F FloatFormat
      FloatLib.Floats.Formats.BinaryInterchange.Model]
    (value : ExecFloat F) : UInt64 :=
  let format := carrier.format
  let bits := carrier.lowBits value
  if format.bitWidth > 64 then
    bits
  else
    let fractionMask := (1 <<< UInt64.ofNat format.fracWidth) - 1
    let exponentMask := (1 <<< UInt64.ofNat format.expWidth) - 1
    let fraction := bits &&& fractionMask
    let exponentField :=
      (bits >>> UInt64.ofNat format.fracWidth) &&& exponentMask
    let negative :=
      ((bits >>> UInt64.ofNat (format.fracWidth + format.expWidth)) &&& 1) != 0
    if exponentField == exponentMask then
      if fraction == 0 then signedTag infinityTag negative else nanTag
    else if exponentField == 0 then
      if fraction == 0 then
        signedTag zeroTag negative
      else
        let leading := fraction.toNat.log2
        let shift := format.fracWidth - leading
        finiteFingerprint negative
          (2 - Int.ofNat format.exponentBias - Int.ofNat shift)
          (fraction <<< UInt64.ofNat shift)
    else
      finiteFingerprint negative
        (Int.ofNat exponentField.toNat - Int.ofNat format.exponentBias + 1)
        ((1 <<< UInt64.ofNat format.fracWidth) ||| fraction)

end BinarySupport

private instance binaryInhabited
    (F : Type) [EncodedFormat F]
    [carrier : BenchmarkCarrier F FloatFormat
      FloatLib.Floats.Formats.BinaryInterchange.Model] :
    Inhabited (ExecFloat F) where
  default := carrier.ofModel default

/-- Round the first shared exact vector into one configured binary format. -/
def binaryInputsX
    (F : Type) [EncodedFormat F]
    [carrier : BenchmarkCarrier F FloatFormat
      FloatLib.Floats.Formats.BinaryInterchange.Model] :
    Array (ExecFloat F) :=
  Exact.xs.map fun value =>
    carrier.ofModel <| Model.roundRatQ carrier.format value

/-- Round the second shared exact vector into one configured binary format. -/
def binaryInputsY
    (F : Type) [EncodedFormat F]
    [carrier : BenchmarkCarrier F FloatFormat
      FloatLib.Floats.Formats.BinaryInterchange.Model] :
    Array (ExecFloat F) :=
  Exact.ys.map fun value =>
    carrier.ofModel <| Model.roundRatQ carrier.format value

/-- Round the nonnegative shared exact vector into one configured binary format. -/
def binaryInputsSqrt
    (F : Type) [EncodedFormat F]
    [carrier : BenchmarkCarrier F FloatFormat
      FloatLib.Floats.Formats.BinaryInterchange.Model] :
    Array (ExecFloat F) :=
  Exact.sqrtXs.map fun value =>
    carrier.ofModel <| Model.roundRatQ carrier.format value

syntax "comparison_binary_workload " ident " : " term " using " term " observing " term : command
syntax "comparison_unary_workload " ident " : " term " using " term " observing " term : command
syntax "comparison_ternary_workload " ident " : " term " using " term " observing " term : command

/-!
We retain the fixture trace separately from the result sink because the old counter-indexed loop
could still produce a convincing-looking checksum. The shell runner now rejects that old sequence.
-/
private structure Measurement where
  sink : UInt64
  fixtureTrace : UInt64

private def Measurement.initial : Measurement :=
  { sink := Support.Sink.initial, fixtureTrace := Support.Sink.initial }

private def Measurement.empty : Measurement :=
  { sink := 0, fixtureTrace := 0 }

macro_rules
  | `(comparison_binary_workload $name:ident : $type:term using $operation:term
        observing $observe:term) =>
      `(@[noinline] def $name :
          Nat → Array $type → Array $type → Measurement → Measurement
        | 0, _, _, measurement => measurement
        | count + 1, xs, ys, measurement =>
            let index := Support.Sink.dependentIndex measurement.sink
            let result := $operation xs[index]! ys[index]!
            $name count xs ys {
              sink := Support.Sink.mix measurement.sink ($observe result)
              fixtureTrace := Support.Sink.mixNat measurement.fixtureTrace index
            })
  | `(comparison_unary_workload $name:ident : $type:term using $operation:term
        observing $observe:term) =>
      `(@[noinline] def $name :
          Nat → Array $type → Measurement → Measurement
        | 0, _, measurement => measurement
        | count + 1, xs, measurement =>
            let index := Support.Sink.dependentIndex measurement.sink
            let result := $operation xs[index]!
            $name count xs {
              sink := Support.Sink.mix measurement.sink ($observe result)
              fixtureTrace := Support.Sink.mixNat measurement.fixtureTrace index
            })
  | `(comparison_ternary_workload $name:ident : $type:term using $operation:term
        observing $observe:term) =>
      `(@[noinline] def $name :
          Nat → Array $type → Array $type → Array $type → Measurement → Measurement
        | 0, _, _, _, measurement => measurement
        | count + 1, xs, ys, zs, measurement =>
            let index := Support.Sink.dependentIndex measurement.sink
            let result := $operation xs[index]! ys[index]! zs[index]!
            $name count xs ys zs {
              sink := Support.Sink.mix measurement.sink ($observe result)
              fixtureTrace := Support.Sink.mixNat measurement.fixtureTrace index
            })

private structure Filters where
  width? : Option Nat
  operation? : Option String
  family? : Option String
  executionClass? : Option String
  iterations? : Option Nat
  warmupIterations : Nat
  agreementIterations : Nat

private def readFilters : IO Filters := do
  let width? ← positiveNat? "FORMAT_COMPARE_WIDTH"
  let operation? ← IO.getEnv "FORMAT_COMPARE_OPERATION"
  if let some operation := operation? then
    unless operation ∈ ["add", "sub", "mul", "div", "sqrt", "fma"] do
      throw <| IO.userError s!"invalid FORMAT_COMPARE_OPERATION: {operation}"
  let family? ← IO.getEnv "FORMAT_COMPARE_FAMILY"
  if let some family := family? then
    unless family ∈ ["posit", "binary-interchange"] do
      throw <| IO.userError s!"invalid FORMAT_COMPARE_FAMILY: {family}"
  let executionClass? ← IO.getEnv "FORMAT_COMPARE_EXECUTION_CLASS"
  if let some executionClass := executionClass? then
    unless executionClass = "proved-software" do
      throw <| IO.userError
        s!"invalid FORMAT_COMPARE_EXECUTION_CLASS: {executionClass}"
  let iterations? ← positiveNat? "FORMAT_COMPARE_ITERATIONS"
  let warmupIterations :=
    (← positiveNat? "FORMAT_COMPARE_WARMUP_ITERATIONS").getD 64
  let agreementIterations :=
    (← positiveNat? "FORMAT_COMPARE_AGREEMENT_ITERATIONS").getD 256
  pure {
    width?,
    operation?,
    family?,
    executionClass?,
    iterations?,
    warmupIterations,
    agreementIterations
  }

private def Filters.accepts (filters : Filters)
    (family : String) (width : Nat) (operation executionClass : String) : Bool :=
  filters.width?.all (· == width) &&
    filters.operation?.all (· == operation) &&
    filters.family?.all (· == family) &&
    filters.executionClass?.all (· == executionClass)

private def defaultIterations (width : Nat) : Nat :=
  if width ≤ 16 then 100000
  else if width ≤ 32 then 50000
  else if width ≤ 64 then 25000
  else if width ≤ 128 then 5000
  else if width ≤ 256 then 500
  else if width ≤ 512 then 100
  else if width ≤ 1024 then 25
  else if width ≤ 2048 then 10
  else 5

private def timeRow (filters : Filters)
    (family formatName : String) (width : Nat) (operation executionClass backend : String)
    (checkAgreement : Bool)
    (run : Nat → Measurement) : IO Unit := do
  unless filters.accepts family width operation executionClass do
    return
  let iterations := filters.iterations?.getD (defaultIterations width)
  let warmupSink ← IO.mkRef 0
  warmupSink.set (run filters.warmupIterations).sink
  let agreement :=
    if checkAgreement then run filters.agreementIterations else Measurement.empty
  let resultRef ← IO.mkRef Measurement.initial
  let start ← IO.monoNanosNow
  resultRef.set (run iterations)
  let stop ← IO.monoNanosNow
  let result ← resultRef.get
  IO.println <|
    s!"ExecFloat,{family},{formatName},{width},{operation},{executionClass}," ++
      s!"{backend},result-dependent-fixture-chain,{iterations},{stop - start}," ++
        s!"{result.sink.toNat},{result.fixtureTrace.toNat}," ++
        s!"{if checkAgreement then filters.agreementIterations else 0}," ++
        s!"{agreement.sink.toNat},{agreement.fixtureTrace.toNat}"

private def runPositBinary
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F
      FloatLib.Floats.Formats.Posit.Format FloatLib.Floats.Formats.Posit.Model]
    (filters : Filters) (formatName : String) (width : Nat) (operation : String)
    (candidate : ExecFloat.Backend.Candidate)
    (workload :
      Nat → Array (ExecFloat F) → Array (ExecFloat F) → Measurement → Measurement) :
    IO Unit := do
  unless filters.accepts "posit" width operation "proved-software" do
    return
  let xs := PositSupport.inputsX F
  let ys := PositSupport.inputsY F
  timeRow filters "posit" formatName width operation "proved-software" candidate.name false
      fun count =>
    workload count xs ys Measurement.initial

private def runPositUnary
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F
      FloatLib.Floats.Formats.Posit.Format FloatLib.Floats.Formats.Posit.Model]
    (filters : Filters) (formatName : String) (width : Nat)
    (candidate : ExecFloat.Backend.Candidate)
    (workload : Nat → Array (ExecFloat F) → Measurement → Measurement) :
    IO Unit := do
  unless filters.accepts "posit" width "sqrt" "proved-software" do
    return
  let xs := PositSupport.inputsSqrt F
  timeRow filters "posit" formatName width "sqrt" "proved-software" candidate.name false
      fun count =>
    workload count xs Measurement.initial

private def runPositTernary
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F
      FloatLib.Floats.Formats.Posit.Format FloatLib.Floats.Formats.Posit.Model]
    (filters : Filters) (formatName : String) (width : Nat)
    (candidate : ExecFloat.Backend.Candidate)
    (workload :
      Nat → Array (ExecFloat F) → Array (ExecFloat F) →
        Array (ExecFloat F) → Measurement → Measurement) :
    IO Unit := do
  unless filters.accepts "posit" width "fma" "proved-software" do
    return
  let xs := PositSupport.inputsX F
  let ys := PositSupport.inputsY F
  let zs := xs.reverse
  timeRow filters "posit" formatName width "fma" "proved-software" candidate.name false
      fun count =>
    workload count xs ys zs Measurement.initial

private def runBinaryBinary
    {F : Type} [EncodedFormat F]
    [BenchmarkCarrier F FloatFormat
      FloatLib.Floats.Formats.BinaryInterchange.Model]
    (filters : Filters) (formatName : String) (width : Nat)
    (operation executionClass backend : String)
    (workload :
      Nat → Array (ExecFloat F) → Array (ExecFloat F) → Measurement → Measurement) :
    IO Unit := do
  unless filters.accepts "binary-interchange" width operation executionClass do
    return
  let xs := binaryInputsX F
  let ys := binaryInputsY F
  timeRow filters "binary-interchange" formatName width operation executionClass backend true
      fun count =>
    workload count xs ys Measurement.initial

private def runBinaryUnary
    {F : Type} [EncodedFormat F]
    [BenchmarkCarrier F FloatFormat
      FloatLib.Floats.Formats.BinaryInterchange.Model]
    (filters : Filters) (formatName : String) (width : Nat)
    (executionClass backend : String)
    (workload : Nat → Array (ExecFloat F) → Measurement → Measurement) :
    IO Unit := do
  unless filters.accepts "binary-interchange" width "sqrt" executionClass do
    return
  let xs := binaryInputsSqrt F
  timeRow filters "binary-interchange" formatName width "sqrt" executionClass backend true
      fun count =>
    workload count xs Measurement.initial

private def runBinaryTernary
    {F : Type} [EncodedFormat F]
    [BenchmarkCarrier F FloatFormat
      FloatLib.Floats.Formats.BinaryInterchange.Model]
    (filters : Filters) (formatName : String) (width : Nat)
    (executionClass backend : String)
    (workload :
      Nat → Array (ExecFloat F) → Array (ExecFloat F) →
        Array (ExecFloat F) → Measurement → Measurement) :
    IO Unit := do
  unless filters.accepts "binary-interchange" width "fma" executionClass do
    return
  let xs := binaryInputsX F
  let ys := binaryInputsY F
  let zs := xs.reverse
  timeRow filters "binary-interchange" formatName width "fma" executionClass backend true
      fun count =>
    workload count xs ys zs Measurement.initial

/-
Each declaration below expands at compile time to six concrete, monomorphic hot loops and one
runner. This keeps the source format-generic without introducing higher-order calls into the timed
path. Distinct generated names also keep the compiler from merging workloads whose code generation
we want to inspect independently.
-/

open Lean Elab Command in
elab "posit_comparison_format " stem:ident " with " runner:ident " at " width:num :
    command => do
      let base := stem.getId.getString!
      let addName := mkIdent <| Name.mkSimple (base ++ "Add")
      let subName := mkIdent <| Name.mkSimple (base ++ "Sub")
      let mulName := mkIdent <| Name.mkSimple (base ++ "Mul")
      let divName := mkIdent <| Name.mkSimple (base ++ "Div")
      let sqrtName := mkIdent <| Name.mkSimple (base ++ "Sqrt")
      let fmaName := mkIdent <| Name.mkSimple (base ++ "Fma")
      elabCommand <| ← `(command|
        comparison_binary_workload $addName : ExecFloat.Posit $width using ExecFloat.add
          observing PositSupport.resultBits)
      elabCommand <| ← `(command|
        comparison_binary_workload $subName : ExecFloat.Posit $width using ExecFloat.sub
          observing PositSupport.resultBits)
      elabCommand <| ← `(command|
        comparison_binary_workload $mulName : ExecFloat.Posit $width using ExecFloat.mul
          observing PositSupport.resultBits)
      elabCommand <| ← `(command|
        comparison_binary_workload $divName : ExecFloat.Posit $width using ExecFloat.div
          observing PositSupport.resultBits)
      elabCommand <| ← `(command|
        comparison_unary_workload $sqrtName : ExecFloat.Posit $width using ExecFloat.sqrt
          observing PositSupport.resultBits)
      elabCommand <| ← `(command|
        comparison_ternary_workload $fmaName : ExecFloat.Posit $width using ExecFloat.fma
          observing PositSupport.resultBits)
      elabCommand <| ← `(command|
        @[noinline] private def $runner (filters : Filters) : IO Unit := do
          let formatName := s!"posit{$width}"
          runPositBinary filters formatName $width "add"
            (ExecFloat.Add.selectedCandidate
              (F := ExecFloat.Posit.Family $width)) $addName
          runPositBinary filters formatName $width "sub"
            (ExecFloat.Sub.selectedCandidate
              (F := ExecFloat.Posit.Family $width)) $subName
          runPositBinary filters formatName $width "mul"
            (ExecFloat.Mul.selectedCandidate
              (F := ExecFloat.Posit.Family $width)) $mulName
          runPositBinary filters formatName $width "div"
            (ExecFloat.Div.selectedCandidate
              (F := ExecFloat.Posit.Family $width)) $divName
          runPositUnary filters formatName $width
            (ExecFloat.Sqrt.selectedCandidate
              (F := ExecFloat.Posit.Family $width)) $sqrtName
          runPositTernary filters formatName $width
            (ExecFloat.Fma.selectedCandidate
              (F := ExecFloat.Posit.Family $width)) $fmaName)

open Lean Elab Command in
elab "binary_comparison_format " stem:ident " with " runner:ident " named "
    formatName:term " at " width:num " layout " exponentBits:num fractionBits:num :
    command => do
      let base := stem.getId.getString!
      let addName := mkIdent <| Name.mkSimple (base ++ "Add")
      let subName := mkIdent <| Name.mkSimple (base ++ "Sub")
      let mulName := mkIdent <| Name.mkSimple (base ++ "Mul")
      let divName := mkIdent <| Name.mkSimple (base ++ "Div")
      let sqrtName := mkIdent <| Name.mkSimple (base ++ "Sqrt")
      let fmaName := mkIdent <| Name.mkSimple (base ++ "Fma")
      let type ← `(term|
        ExecFloat.Binary (exponentBits := $exponentBits) (fractionBits := $fractionBits))
      elabCommand <| ← `(command|
        comparison_binary_workload $addName : $type using ExecFloat.add
          observing BinarySupport.resultBits)
      elabCommand <| ← `(command|
        comparison_binary_workload $subName : $type using ExecFloat.sub
          observing BinarySupport.resultBits)
      elabCommand <| ← `(command|
        comparison_binary_workload $mulName : $type using ExecFloat.mul
          observing BinarySupport.resultBits)
      elabCommand <| ← `(command|
        comparison_binary_workload $divName : $type using ExecFloat.div
          observing BinarySupport.resultBits)
      elabCommand <| ← `(command|
        comparison_unary_workload $sqrtName : $type using ExecFloat.sqrt
          observing BinarySupport.resultBits)
      elabCommand <| ← `(command|
        comparison_ternary_workload $fmaName : $type using ExecFloat.fma
          observing BinarySupport.resultBits)
      elabCommand <| ← `(command|
        @[noinline] private def $runner (filters : Filters) : IO Unit := do
          runBinaryBinary filters $formatName $width "add" "proved-software"
            (ExecFloat.Add.selectedCandidate
              (F := ExecFloat.Binary.Family $exponentBits $fractionBits)).name $addName
          runBinaryBinary filters $formatName $width "sub" "proved-software"
            (ExecFloat.Sub.selectedCandidate
              (F := ExecFloat.Binary.Family $exponentBits $fractionBits)).name $subName
          runBinaryBinary filters $formatName $width "mul" "proved-software"
            (ExecFloat.Mul.selectedCandidate
              (F := ExecFloat.Binary.Family $exponentBits $fractionBits)).name $mulName
          runBinaryBinary filters $formatName $width "div" "proved-software"
            (ExecFloat.Div.selectedCandidate
              (F := ExecFloat.Binary.Family $exponentBits $fractionBits)).name $divName
          runBinaryUnary filters $formatName $width "proved-software"
            (ExecFloat.Sqrt.selectedCandidate
              (F := ExecFloat.Binary.Family $exponentBits $fractionBits)).name $sqrtName
          runBinaryTernary filters $formatName $width "proved-software"
            (ExecFloat.Fma.selectedCandidate
              (F := ExecFloat.Binary.Family $exponentBits $fractionBits)).name $fmaName)

/-
Generate binary workloads that intentionally exercise the proved fixed-word kernels instead of the
generic benchmark declaration. Public dispatch selects the same kernels. Only binary32 and
binary64 use this specialized declaration.
-/
open Lean Elab Command in
elab "binary_word_comparison_format " stem:ident " with " runner:ident " named "
    formatName:term " at " width:num " layout " exponentBits:num fractionBits:num :
    command => do
      let base := stem.getId.getString!
      let addName := mkIdent <| Name.mkSimple (base ++ "Add")
      let subName := mkIdent <| Name.mkSimple (base ++ "Sub")
      let mulName := mkIdent <| Name.mkSimple (base ++ "Mul")
      let divName := mkIdent <| Name.mkSimple (base ++ "Div")
      let sqrtName := mkIdent <| Name.mkSimple (base ++ "Sqrt")
      let fmaName := mkIdent <| Name.mkSimple (base ++ "Fma")
      let type ← `(term|
        ExecFloat.Binary (exponentBits := $exponentBits) (fractionBits := $fractionBits))
      elabCommand <| ← `(command|
        comparison_binary_workload $addName : $type using Configured.Backend.wordAdd
          observing BinarySupport.resultBits)
      elabCommand <| ← `(command|
        comparison_binary_workload $subName : $type using Configured.Backend.wordSub
          observing BinarySupport.resultBits)
      elabCommand <| ← `(command|
        comparison_binary_workload $mulName : $type using Configured.Backend.wordMul
          observing BinarySupport.resultBits)
      elabCommand <| ← `(command|
        comparison_binary_workload $divName : $type using Configured.Backend.wordDiv
          observing BinarySupport.resultBits)
      elabCommand <| ← `(command|
        comparison_unary_workload $sqrtName : $type using Configured.Backend.wordSqrt
          observing BinarySupport.resultBits)
      elabCommand <| ← `(command|
        comparison_ternary_workload $fmaName : $type using Configured.Backend.wordFma
          observing BinarySupport.resultBits)
      elabCommand <| ← `(command|
        @[noinline] private def $runner (filters : Filters) : IO Unit := do
          let backend := "configured proved word kernel"
          runBinaryBinary filters $formatName $width "add" "proved-software"
            backend $addName
          runBinaryBinary filters $formatName $width "sub" "proved-software"
            backend $subName
          runBinaryBinary filters $formatName $width "mul" "proved-software"
            backend $mulName
          runBinaryBinary filters $formatName $width "div" "proved-software"
            backend $divName
          runBinaryUnary filters $formatName $width "proved-software"
            backend $sqrtName
          runBinaryTernary filters $formatName $width "proved-software"
            backend $fmaName)

/-!
## Compiled comparison matrix

The rows are data: each one chooses a storage width and, for binary formats, a documented layout.
The declarations above generate all operation-specific code uniformly.
-/

posit_comparison_format posit2 with runPosit2 at 2
posit_comparison_format posit3 with runPosit3 at 3
posit_comparison_format posit4 with runPosit4 at 4
posit_comparison_format posit5 with runPosit5 at 5
posit_comparison_format posit6 with runPosit6 at 6
posit_comparison_format posit7 with runPosit7 at 7
posit_comparison_format posit8 with runPosit8 at 8
posit_comparison_format posit16 with runPosit16 at 16
posit_comparison_format posit32 with runPosit32 at 32
posit_comparison_format posit64 with runPosit64 at 64
posit_comparison_format posit128 with runPosit128 at 128
posit_comparison_format posit256 with runPosit256 at 256
posit_comparison_format posit512 with runPosit512 at 512
posit_comparison_format posit1024 with runPosit1024 at 1024
posit_comparison_format posit2048 with runPosit2048 at 2048
posit_comparison_format posit4096 with runPosit4096 at 4096

binary_comparison_format binary4Software with runBinary4
  named "binary4-e2m1" at 4 layout 2 1
binary_comparison_format binary5Software with runBinary5
  named "binary5-e2m2" at 5 layout 2 2
binary_comparison_format binary6Software with runBinary6
  named "binary6-e3m2" at 6 layout 3 2
binary_comparison_format binary7Software with runBinary7
  named "binary7-e3m3" at 7 layout 3 3
binary_comparison_format binary8Software with runBinary8
  named "binary8-e4m3" at 8 layout 4 3
binary_comparison_format binary16Software with runBinary16
  named "binary16" at 16 layout 5 10
binary_comparison_format binary24Software with runBinary24
  named "binary24-custom-e8m15" at 24 layout 8 15
binary_word_comparison_format binary32Software with runBinary32Software
  named "binary32" at 32 layout 8 23
binary_comparison_format binary48Software with runBinary48
  named "binary48-custom-e11m36" at 48 layout 11 36
binary_word_comparison_format binary64Software with runBinary64Software
  named "binary64" at 64 layout 11 52
binary_comparison_format binary96Software with runBinary96
  named "binary96-custom-e15m80" at 96 layout 15 80
binary_comparison_format binary112Software with runBinary112
  named "binary112-custom-e15m96" at 112 layout 15 96
binary_comparison_format binary128Software with runBinary128
  named "binary128" at 128 layout 15 112
binary_comparison_format binary256Software with runBinary256
  named "binary256-custom-e19m236" at 256 layout 19 236
binary_comparison_format binary512Software with runBinary512
  named "binary512-custom-e19m492" at 512 layout 19 492
binary_comparison_format binary1024Software with runBinary1024
  named "binary1024-custom-e19m1004" at 1024 layout 19 1004
binary_comparison_format binary2048Software with runBinary2048
  named "binary2048-custom-e19m2028" at 2048 layout 19 2028
binary_comparison_format binary4096Software with runBinary4096
  named "binary4096-custom-e19m4076" at 4096 layout 19 4076

/-- Ordered rows emitted by the comparison executable. -/
private def benchmarkRows : List (Filters → IO Unit) :=
  [ runPosit2
  , runPosit3
  , runPosit4
  , runBinary4
  , runPosit5
  , runBinary5
  , runPosit6
  , runBinary6
  , runPosit7
  , runBinary7
  , runPosit8
  , runBinary8
  , runPosit16
  , runBinary16
  , runBinary24
  , runPosit32
  , runBinary32Software
  , runBinary48
  , runPosit64
  , runBinary64Software
  , runBinary96
  , runBinary112
  , runPosit128
  , runBinary128
  , runPosit256
  , runBinary256
  , runPosit512
  , runBinary512
  , runPosit1024
  , runBinary1024
  , runPosit2048
  , runBinary2048
  , runPosit4096
  , runBinary4096
  ]

def run : IO Unit := do
  let filters ← readFilters
  IO.println <|
    "implementation,family,format,totalBits,operation,executionClass,backend," ++
      "measurementMethod,iterations,totalNanos,sink,fixtureTraceDigest," ++
      "agreementIterations,agreementSink,agreementFixtureTraceDigest"
  for runRow in benchmarkRows do
    runRow filters

end FloatLibBenchmarks.Public.FormatComparison

public def main : IO Unit :=
  FloatLibBenchmarks.Public.FormatComparison.run
