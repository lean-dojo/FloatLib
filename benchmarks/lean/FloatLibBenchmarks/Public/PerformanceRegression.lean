/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.Sweep
import FloatLibBenchmarks.Support.Posit

/-!
# Public arithmetic performance regressions

The runtime half of `benchmarks/scripts/performance-regression.sh` covers all six core operations
on a fixed catalog of binary and posit carriers. Ordinary inputs cover every format; a smaller
set also exercises zeros, subnormals, cancellation, exponent gaps, and exact rounding ties.
The manifest in the script is deliberately independent: missing or unexpected rows fail closed.

Each hot loop is monomorphic, visits sixteen prepared inputs, and observes every result. Format,
operation, class, backend selection, and input construction are outside the timed interval.
Changing this workload requires a schema bump in both this executable and its parser.
-/

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics
open FloatLibBenchmarks.Support
open FloatLibBenchmarks.Support.Environment

namespace FloatLibBenchmarks.Public.PerformanceRegression

abbrev Binary16 := FloatLibBenchmarks.Public.Sweep.P11
abbrev Binary32 := FloatLibBenchmarks.Public.Sweep.P24
abbrev Binary64 := FloatLibBenchmarks.Public.Sweep.P53
abbrev Binary128 := FloatLibBenchmarks.Public.Sweep.P113
abbrev Binary256 := FloatLibBenchmarks.Public.Sweep.P237
abbrev Descriptor24 := ExecFloat (Descriptor (FloatFormat.ieee 7 16))
abbrev Descriptor48 := ExecFloat (Descriptor (FloatFormat.ieee 7 40))
abbrev Descriptor64 := ExecFloat (Descriptor (FloatFormat.ieee 2 61))
abbrev Posit16 := ExecFloat.Posit 16
abbrev Posit32 := ExecFloat.Posit 32
abbrev Posit65 := ExecFloat.Posit 65

private def formats : List String :=
  ["binary16", "binary32", "binary64", "binary128", "binary256", "descriptor24",
    "descriptor48", "descriptor64", "posit16", "posit32", "posit65"]

private def operations : List String := ["add", "sub", "mul", "div", "sqrt", "fma"]

private def inputClasses : List String :=
  ["ordinary", "zero", "subnormal", "cancel", "gap", "tie"]

/-- A curated boundary set keeps the default gate smaller than the Cartesian product. -/
private def classesFor (format operation : String) : List String := Id.run do
  let binary := format ∈ ["binary32", "binary256", "descriptor24"]
  let posit := format ∈ ["posit32", "posit65"]
  let mut classes := ["ordinary"]
  if binary || posit then
    classes := classes ++ ["zero"]
    if binary then
      classes := classes ++ ["subnormal"]
    if operation ∈ ["add", "sub", "fma"] then
      classes := classes ++ ["cancel", "gap"]
    if binary && operation != "sqrt" then
      classes := classes ++ ["tie"]
  return classes

private structure Filters where
  format? : Option String
  operation? : Option String
  inputClass? : Option String
  iterations? : Option Nat
  warmupIterations : Nat
  reverse : Bool

private def readChoice (name : String) (choices : List String) : IO (Option String) := do
  let value? ← IO.getEnv name
  if let some value := value? then
    unless value ∈ choices do
      throw <| IO.userError s!"invalid {name}: {value}"
  return value?

private def Filters.accepts (filters : Filters) (format operation inputClass : String) : Bool :=
  filters.format?.all (· == format) && filters.operation?.all (· == operation) &&
    filters.inputClass?.all (· == inputClass)

private def readFilters : IO Filters := do
  let filters : Filters := {
    format? := ← readChoice "PERF_FORMAT" formats
    operation? := ← readChoice "PERF_OPERATION" operations
    inputClass? := ← readChoice "PERF_INPUT_CLASS" inputClasses
    iterations? := ← positiveNat? "PERF_ITERATIONS"
    warmupIterations := (← positiveNat? "PERF_WARMUP_ITERATIONS").getD 256
    reverse := ← Environment.bool "PERF_REVERSE"
  }
  unless formats.any (fun format => operations.any fun operation =>
      (classesFor format operation).any (filters.accepts format operation)) do
    throw <| IO.userError "performance filters select no rows"
  return filters

private def defaultIterations (format : String) : Nat :=
  if format ∈ ["binary16", "binary32", "binary64"] then 100000
  else if format ∈ ["posit16", "posit32"] then 20000
  else if format == "binary128" then 10000
  else 5000

private structure Inputs (α : Type) where
  xs : Array α
  ys : Array α
  zs : Array α

private abbrev Workload (α : Type) :=
  Nat → Array α → Array α → Array α → UInt64 → UInt64

syntax "regression_binary_workload " ident " : " term " using " term
  " observing " term : command
syntax "regression_unary_workload " ident " : " term " using " term
  " observing " term : command
syntax "regression_ternary_workload " ident " : " term " using " term
  " observing " term : command

macro_rules
  | `(regression_binary_workload $name:ident : $type:term using $operation:term
      observing $observe:term) =>
      `(@[noinline] def $name :
          Nat → Array $type → Array $type → Array $type → UInt64 → UInt64
        | 0, _, _, _, sink => sink
        | count + 1, xs, ys, zs, sink =>
            let index := count &&& 15
            let result := $operation xs[index]! ys[index]!
            $name count xs ys zs (Sink.mix sink ($observe result)))
  | `(regression_unary_workload $name:ident : $type:term using $operation:term
      observing $observe:term) =>
      `(@[noinline] def $name :
          Nat → Array $type → Array $type → Array $type → UInt64 → UInt64
        | 0, _, _, _, sink => sink
        | count + 1, xs, ys, zs, sink =>
            let index := count &&& 15
            let result := $operation xs[index]!
            $name count xs ys zs (Sink.mix sink ($observe result)))
  | `(regression_ternary_workload $name:ident : $type:term using $operation:term
      observing $observe:term) =>
      `(@[noinline] def $name :
          Nat → Array $type → Array $type → Array $type → UInt64 → UInt64
        | 0, _, _, _, sink => sink
        | count + 1, xs, ys, zs, sink =>
            let index := count &&& 15
            let result := $operation xs[index]! ys[index]! zs[index]!
            $name count xs ys zs (Sink.mix sink ($observe result)))

regression_binary_workload binary16Add : Binary16
  using ExecFloat.add
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary16Sub : Binary16
  using ExecFloat.sub
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary16Mul : Binary16
  using ExecFloat.mul
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary16Div : Binary16
  using ExecFloat.div
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_unary_workload binary16Sqrt : Binary16
  using ExecFloat.sqrt
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_ternary_workload binary16Fma : Binary16
  using ExecFloat.fma
  observing FloatLibBenchmarks.Public.Sweep.resultBits

regression_binary_workload binary32Add : Binary32
  using ExecFloat.add
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary32Sub : Binary32
  using ExecFloat.sub
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary32Mul : Binary32
  using ExecFloat.mul
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary32Div : Binary32
  using ExecFloat.div
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_unary_workload binary32Sqrt : Binary32
  using ExecFloat.sqrt
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_ternary_workload binary32Fma : Binary32
  using ExecFloat.fma
  observing FloatLibBenchmarks.Public.Sweep.resultBits

regression_binary_workload binary64Add : Binary64
  using ExecFloat.add
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary64Sub : Binary64
  using ExecFloat.sub
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary64Mul : Binary64
  using ExecFloat.mul
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary64Div : Binary64
  using ExecFloat.div
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_unary_workload binary64Sqrt : Binary64
  using ExecFloat.sqrt
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_ternary_workload binary64Fma : Binary64
  using ExecFloat.fma
  observing FloatLibBenchmarks.Public.Sweep.resultBits

regression_binary_workload binary128Add : Binary128
  using ExecFloat.add
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary128Sub : Binary128
  using ExecFloat.sub
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary128Mul : Binary128
  using ExecFloat.mul
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary128Div : Binary128
  using ExecFloat.div
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_unary_workload binary128Sqrt : Binary128
  using ExecFloat.sqrt
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_ternary_workload binary128Fma : Binary128
  using ExecFloat.fma
  observing FloatLibBenchmarks.Public.Sweep.resultBits

regression_binary_workload binary256Add : Binary256
  using ExecFloat.add
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary256Sub : Binary256
  using ExecFloat.sub
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary256Mul : Binary256
  using ExecFloat.mul
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload binary256Div : Binary256
  using ExecFloat.div
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_unary_workload binary256Sqrt : Binary256
  using ExecFloat.sqrt
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_ternary_workload binary256Fma : Binary256
  using ExecFloat.fma
  observing FloatLibBenchmarks.Public.Sweep.resultBits

regression_binary_workload descriptor24Add : Descriptor24
  using ExecFloat.add
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload descriptor24Sub : Descriptor24
  using ExecFloat.sub
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload descriptor24Mul : Descriptor24
  using ExecFloat.mul
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload descriptor24Div : Descriptor24
  using ExecFloat.div
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_unary_workload descriptor24Sqrt : Descriptor24
  using ExecFloat.sqrt
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_ternary_workload descriptor24Fma : Descriptor24
  using ExecFloat.fma
  observing FloatLibBenchmarks.Public.Sweep.resultBits

regression_binary_workload descriptor48Add : Descriptor48
  using ExecFloat.add
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload descriptor48Sub : Descriptor48
  using ExecFloat.sub
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload descriptor48Mul : Descriptor48
  using ExecFloat.mul
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload descriptor48Div : Descriptor48
  using ExecFloat.div
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_unary_workload descriptor48Sqrt : Descriptor48
  using ExecFloat.sqrt
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_ternary_workload descriptor48Fma : Descriptor48
  using ExecFloat.fma
  observing FloatLibBenchmarks.Public.Sweep.resultBits

regression_binary_workload descriptor64Add : Descriptor64
  using ExecFloat.add
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload descriptor64Sub : Descriptor64
  using ExecFloat.sub
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload descriptor64Mul : Descriptor64
  using ExecFloat.mul
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_binary_workload descriptor64Div : Descriptor64
  using ExecFloat.div
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_unary_workload descriptor64Sqrt : Descriptor64
  using ExecFloat.sqrt
  observing FloatLibBenchmarks.Public.Sweep.resultBits
regression_ternary_workload descriptor64Fma : Descriptor64
  using ExecFloat.fma
  observing FloatLibBenchmarks.Public.Sweep.resultBits

regression_binary_workload posit16Add : Posit16
  using ExecFloat.add
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_binary_workload posit16Sub : Posit16
  using ExecFloat.sub
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_binary_workload posit16Mul : Posit16
  using ExecFloat.mul
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_binary_workload posit16Div : Posit16
  using ExecFloat.div
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_unary_workload posit16Sqrt : Posit16
  using ExecFloat.sqrt
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_ternary_workload posit16Fma : Posit16
  using ExecFloat.fma
  observing FloatLibBenchmarks.Support.Posit.resultBits

regression_binary_workload posit32Add : Posit32
  using ExecFloat.add
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_binary_workload posit32Sub : Posit32
  using ExecFloat.sub
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_binary_workload posit32Mul : Posit32
  using ExecFloat.mul
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_binary_workload posit32Div : Posit32
  using ExecFloat.div
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_unary_workload posit32Sqrt : Posit32
  using ExecFloat.sqrt
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_ternary_workload posit32Fma : Posit32
  using ExecFloat.fma
  observing FloatLibBenchmarks.Support.Posit.resultBits

regression_binary_workload posit65Add : Posit65
  using ExecFloat.add
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_binary_workload posit65Sub : Posit65
  using ExecFloat.sub
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_binary_workload posit65Mul : Posit65
  using ExecFloat.mul
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_binary_workload posit65Div : Posit65
  using ExecFloat.div
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_unary_workload posit65Sqrt : Posit65
  using ExecFloat.sqrt
  observing FloatLibBenchmarks.Support.Posit.resultBits
regression_ternary_workload posit65Fma : Posit65
  using ExecFloat.fma
  observing FloatLibBenchmarks.Support.Posit.resultBits

/-- Build encoded binary boundary operands without expanding extreme exponents to rationals. -/
private def binaryInputs
    (F : Type) [EncodedFormat F] [carrier : BenchmarkCarrier F FloatFormat Model]
    (operation inputClass : String) : Inputs (ExecFloat F) := Id.run do
  if inputClass == "ordinary" then
    return {
      xs := if operation == "sqrt" then FloatLibBenchmarks.Public.Sweep.inputsSqrt F
        else FloatLibBenchmarks.Public.Sweep.inputsX F
      ys := FloatLibBenchmarks.Public.Sweep.inputsY F
      zs := (FloatLibBenchmarks.Public.Sweep.inputsX F).reverse
    }
  let fmt := carrier.format
  let unit := 2 ^ fmt.fracWidth
  let one := fmt.exponentBias * unit
  let two := one + unit
  let halfUlp := (fmt.exponentBias - fmt.fracWidth - 1) * unit
  let sign := 2 ^ (fmt.expWidth + fmt.fracWidth)
  let signed := fun i bits => if i % 2 == 0 then bits else bits + sign
  let triples := (Array.range 16).map fun (i : Nat) =>
    let x := one + i
    match inputClass with
    | "zero" => (signed i 0, x, signed i (one + 15 - i))
    | "subnormal" =>
        let tiny := if i < 8 then i + 1 else unit - (16 - i)
        -- Both ends of the subnormal range; no zero divisor or negative square root.
        let y := if operation ∈ ["add", "sub"] then unit + i
          else if operation == "div" then two else one + unit / 2
        (tiny, y, sign + unit + i)
    | "cancel" =>
        let nearby := x - i % 2
        if operation == "fma" then (x, two, sign + nearby + unit)
        else (x, if operation == "add" then sign + nearby else nearby, 0)
    | "gap" =>
        let tiny := signed i ((fmt.exponentBias - fmt.fracWidth - 4 - i) * unit)
        if operation == "fma" then (x, two, tiny) else (x, tiny, 0)
    | "tie" =>
        -- Half-ulp sums; odd significands times 3/2; odd subnormals divided by two.
        -- Varying the low bit exercises both directions of nearest-even rounding.
        if operation == "mul" then (signed i (one + 2 * i + 1), one + unit / 2, 0)
        else if operation == "div" then (signed i (2 * i + 1), two, 0)
        else if operation == "fma" then (signed i x, one, signed i halfUlp)
        else (signed i (x + if operation == "sub" then 1 else 0), signed i halfUlp, 0)
    | _ => (x, one, 0)
  let encode := fun bits => carrier.ofModel (Model.ofNatBits bits)
  return {
    xs := triples.map fun (x, _, _) => encode x
    ys := triples.map fun (_, y, _) => encode y
    zs := triples.map fun (_, _, z) => encode z
  }

private def positInputs
    (F : Type) [EncodedFormat F]
    [carrier : BenchmarkCarrier F FloatLib.Floats.Formats.Posit.Format
      FloatLib.Floats.Formats.Posit.Model]
    (operation inputClass : String) : Inputs (ExecFloat F) := Id.run do
  if inputClass == "ordinary" then
    return {
      xs := if operation == "sqrt" then FloatLibBenchmarks.Support.Posit.inputsSqrt F
        else FloatLibBenchmarks.Support.Posit.inputsX F
      ys := FloatLibBenchmarks.Support.Posit.inputsY F
      zs := (FloatLibBenchmarks.Support.Posit.inputsX F).reverse
    }
  let triples := (Array.range 16).map fun (i : Nat) =>
    let x : Rat := 1 + (i : Rat) / 32
    let parity : Nat := i % 2
    let delta : Rat := (parity : Rat) / (2 ^ (carrier.format.bits - 8) : Nat)
    match inputClass with
    | "zero" => (0, x, x + 1)
    | "cancel" =>
        if operation == "fma" then (x, 2, -2 * x + delta)
        else (x, if operation == "add" then -x + delta else x - delta, 0)
    | "gap" =>
        let tiny : Rat := 1 / (2 ^ (carrier.format.bits + 4 + i) : Nat)
        let tiny := if i % 2 == 0 then tiny else -tiny
        if operation == "fma" then (x, 2, tiny) else (x, tiny, 0)
    | _ => (x, 1, 0)
  let encode := fun value =>
    carrier.ofModel (FloatLib.Floats.Formats.Posit.Model.roundRat carrier.format value)
  return {
    xs := triples.map fun (x, _, _) => encode x
    ys := triples.map fun (_, y, _) => encode y
    zs := triples.map fun (_, _, z) => encode z
  }

private def timeRow {α : Type} (filters : Filters)
    (format operation inputClass backend : String) (totalBits : Nat)
    (inputs : Inputs α) (workload : Workload α) : IO Unit := do
  unless inputs.xs.size == 16 && inputs.ys.size == 16 && inputs.zs.size == 16 do
    throw <| IO.userError "performance inputs must contain sixteen operands per vector"
  let iterations := filters.iterations?.getD (defaultIterations format)
  let warmup ← IO.mkRef 0
  warmup.set (workload filters.warmupIterations inputs.xs inputs.ys inputs.zs Sink.initial)
  -- The observed warmup result seeds the timed sink, so even equal counts do distinct work.
  let seed ← warmup.get
  let result ← IO.mkRef 0
  let start ← IO.monoNanosNow
  result.set (workload iterations inputs.xs inputs.ys inputs.zs seed)
  let stop ← IO.monoNanosNow
  IO.println <|
    s!"2,{format},{totalBits},{operation},{inputClass},{backend},{iterations}," ++
      s!"{filters.warmupIterations},{stop - start},{(← result.get).toNat}"

private def runFormat
    {F : Type} [EncodedFormat F] [ExecFloat.Backend.PolicyFor F]
    [ExecFloat.Add F] [ExecFloat.Sub F] [ExecFloat.Mul F]
    [ExecFloat.Div F] [ExecFloat.Sqrt F] [ExecFloat.Fma F]
    (filters : Filters) (format : String) (totalBits : Nat)
    (prepare : String → String → Inputs (ExecFloat F))
    (workloads : Array (Workload (ExecFloat F))) : IO Unit := do
  unless filters.format?.all (· == format) do
    return
  let backends := #[
    (ExecFloat.Add.selectedCandidate (F := F)).name,
    (ExecFloat.Sub.selectedCandidate (F := F)).name,
    (ExecFloat.Mul.selectedCandidate (F := F)).name,
    (ExecFloat.Div.selectedCandidate (F := F)).name,
    (ExecFloat.Sqrt.selectedCandidate (F := F)).name,
    (ExecFloat.Fma.selectedCandidate (F := F)).name]
  let indices := if filters.reverse then (List.range 6).reverse else List.range 6
  for index in indices do
    let operation := operations[index]!
    let classes := classesFor format operation
    for inputClass in (if filters.reverse then classes.reverse else classes) do
      if filters.accepts format operation inputClass then
        timeRow filters format operation inputClass backends[index]! totalBits
          (prepare operation inputClass) workloads[index]!

def run : IO Unit := do
  let filters ← readFilters
  IO.println <|
    "schema,format,totalBits,operation,inputClass,backend,iterations," ++
      "warmupIterations,totalNanos,sink"
  let runners : Array (IO Unit) := #[
    runFormat filters "binary16" 16 (binaryInputs _)
      #[binary16Add, binary16Sub, binary16Mul, binary16Div, binary16Sqrt, binary16Fma],
    runFormat filters "binary32" 32 (binaryInputs _)
      #[binary32Add, binary32Sub, binary32Mul, binary32Div, binary32Sqrt, binary32Fma],
    runFormat filters "binary64" 64 (binaryInputs _)
      #[binary64Add, binary64Sub, binary64Mul, binary64Div, binary64Sqrt, binary64Fma],
    runFormat filters "binary128" 128 (binaryInputs _)
      #[binary128Add, binary128Sub, binary128Mul, binary128Div, binary128Sqrt, binary128Fma],
    runFormat filters "binary256" 256 (binaryInputs _)
      #[binary256Add, binary256Sub, binary256Mul, binary256Div, binary256Sqrt, binary256Fma],
    runFormat filters "descriptor24" 24 (binaryInputs _)
      #[descriptor24Add, descriptor24Sub, descriptor24Mul, descriptor24Div,
        descriptor24Sqrt, descriptor24Fma],
    runFormat filters "descriptor48" 48 (binaryInputs _)
      #[descriptor48Add, descriptor48Sub, descriptor48Mul, descriptor48Div,
        descriptor48Sqrt, descriptor48Fma],
    runFormat filters "descriptor64" 64 (binaryInputs _)
      #[descriptor64Add, descriptor64Sub, descriptor64Mul, descriptor64Div,
        descriptor64Sqrt, descriptor64Fma],
    runFormat filters "posit16" 16 (positInputs _)
      #[posit16Add, posit16Sub, posit16Mul, posit16Div, posit16Sqrt, posit16Fma],
    runFormat filters "posit32" 32 (positInputs _)
      #[posit32Add, posit32Sub, posit32Mul, posit32Div, posit32Sqrt, posit32Fma],
    runFormat filters "posit65" 65 (positInputs _)
      #[posit65Add, posit65Sub, posit65Mul, posit65Div, posit65Sqrt, posit65Fma]]
  for runner in (if filters.reverse then runners.reverse else runners) do
    runner

end FloatLibBenchmarks.Public.PerformanceRegression

public def main : IO Unit :=
  FloatLibBenchmarks.Public.PerformanceRegression.run
