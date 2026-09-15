/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Support.Carrier
public import FloatLibBenchmarks.Support.ExactWorkload
public import FloatLibBenchmarks.Support.Environment
public import FloatLibBenchmarks.Support.Sink
public import FloatLib.Floats.ExecFloat.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeDispatch
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Backends
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Conversion

/-!
# Shared `ExecFloat` precision-sweep driver

We keep formats, exact inputs, timing, and CSV output here so every precision-sweep operation uses
the same driver. The sweep measures the user-facing `ExecFloat.Binary` carrier selected from each
complete encoding width, not the reference descriptor proof model. Inputs come from
`Support.ExactWorkload`, shared with posit, MPFR, Flocq, and the independent-library comparisons.
Each format rounds those mathematical rationals once before timing.

`BenchmarkCarrier` keeps input generation independent of representation. Both the configured
public carrier and the descriptor carrier implement the same exact model bridge. We still make
every timed loop monomorphic: no runtime format or carrier switch is hidden in the measurement.
-/

@[expose] public section

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics
open FloatLibBenchmarks.Support
open FloatLibBenchmarks.Support.ExactWorkload

namespace FloatLibBenchmarks.Public.Sweep

instance descriptorBenchmarkCarrier (format : FloatFormat) :
    BenchmarkCarrier (Descriptor format) FloatFormat Model where
  format := format
  toModel := Descriptor.unpack
  ofModel := Descriptor.pack
  lowBits := fun value => UInt64.ofNat (Descriptor.unpack value).toNatBits

instance configuredBenchmarkCarrier
    (format : FloatFormat) (plan : Configured.StoragePlan format)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) (Configured.Code plan)] :
    BenchmarkCarrier
      (Configured.Family format (Configured.Code plan) plan) FloatFormat Model where
  format := format
  toModel := Configured.Family.toModel
  ofModel := Configured.Family.ofModel
  lowBits :=
    match plan with
    | .byte _ => fun value => UInt64.ofNat value.raw.1.toNat
    | .word16 _ => fun value => UInt64.ofNat value.raw.1.toNat
    | .word32 _ => fun value => UInt64.ofNat value.raw.1.toNat
    | .word64 _ => fun value => value.raw.1
    | .wide => fun value => UInt64.ofNat value.raw.toNatBits
    | .limbs _ => fun value =>
        (value.raw.1.limb 0).toUInt64 ||| ((value.raw.1.limb 1).toUInt64 <<< 32)

/--
Benchmark-local default for any carrier that can round the exact zero model.

This instance supports bounds-checked array access in benchmark clients. We keep it in the
benchmark driver rather than the numerical API: importing `Public.Sweep` opts into it explicitly.
-/
instance benchmarkExecFloatInhabited
    (F : Type) [EncodedFormat F] [carrier : BenchmarkCarrier F FloatFormat Model] :
    Inhabited (ExecFloat F) where
  default := carrier.ofModel default

abbrev P2 := ExecFloat.Binary (exponentBits := 2) (fractionBits := 1)
abbrev P3 := ExecFloat.Binary (exponentBits := 2) (fractionBits := 2)
abbrev P4 := ExecFloat.Binary (exponentBits := 2) (fractionBits := 3)
abbrev P5 := ExecFloat.Binary (exponentBits := 3) (fractionBits := 4)
abbrev P6 := ExecFloat.Binary (exponentBits := 4) (fractionBits := 5)
abbrev P7 := ExecFloat.Binary (exponentBits := 4) (fractionBits := 6)
abbrev P8 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 7)
abbrev P11 := ExecFloat.Binary (exponentBits := 5) (fractionBits := 10)
abbrev P24 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)
abbrev P53 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)
abbrev P113 := ExecFloat.Binary (exponentBits := 15) (fractionBits := 112)
abbrev P161 := ExecFloat.Binary (exponentBits := 19) (fractionBits := 160)
abbrev P237 := ExecFloat.Binary (exponentBits := 19) (fractionBits := 236)
abbrev P493 := ExecFloat.Binary (exponentBits := 19) (fractionBits := 492)
abbrev P1024 := ExecFloat.Binary (exponentBits := 19) (fractionBits := 1023)
abbrev P2048 := ExecFloat.Binary (exponentBits := 19) (fractionBits := 2047)
abbrev P4096 := ExecFloat.Binary (exponentBits := 19) (fractionBits := 4095)

@[inline] def resultBits
    {F : Type} [EncodedFormat F] [carrier : BenchmarkCarrier F FloatFormat Model]
    (value : ExecFloat F) : UInt64 :=
  carrier.lowBits value

syntax "binary_sweep_workload " ident " : " term " using " term : command
syntax "ternary_sweep_workload " ident " : " term " using " term : command
syntax "unary_sweep_workload " ident " : " term " using " term : command

macro_rules
  | `(binary_sweep_workload $name:ident : $type:term using $operation:term) =>
      `(@[noinline] def $name :
          Nat → Array $type → Array $type → UInt64 → UInt64
        | 0, _, _, sink => sink
        | n + 1, xs, ys, sink =>
            let i := n &&& 15
            let result := $operation xs[i]! ys[i]!
            $name n xs ys (Support.Sink.mix sink (resultBits result)))
  | `(ternary_sweep_workload $name:ident : $type:term using $operation:term) =>
      `(@[noinline] def $name :
          Nat → Array $type → Array $type → Array $type → UInt64 → UInt64
        | 0, _, _, _, sink => sink
        | n + 1, xs, ys, zs, sink =>
            let i := n &&& 15
            let result := $operation xs[i]! ys[i]! zs[i]!
            $name n xs ys zs (Support.Sink.mix sink (resultBits result)))
  | `(unary_sweep_workload $name:ident : $type:term using $operation:term) =>
      `(@[noinline] def $name :
          Nat → Array $type → UInt64 → UInt64
        | 0, _, sink => sink
        | n + 1, xs, sink =>
            let i := n &&& 15
            let result := $operation xs[i]!
            $name n xs (Support.Sink.mix sink (resultBits result)))

def inputsX
    (F : Type) [EncodedFormat F] [carrier : BenchmarkCarrier F FloatFormat Model] :
    Array (ExecFloat F) :=
  xs.map fun value =>
    carrier.ofModel <| Model.roundRatQ carrier.format value

def inputsY
    (F : Type) [EncodedFormat F] [carrier : BenchmarkCarrier F FloatFormat Model] :
    Array (ExecFloat F) :=
  ys.map fun value =>
    carrier.ofModel <| Model.roundRatQ carrier.format value

/-- Nonnegative shared exact vector used by square root. -/
def inputsSqrt
    (F : Type) [EncodedFormat F] [carrier : BenchmarkCarrier F FloatFormat Model] :
    Array (ExecFloat F) :=
  sqrtXs.map fun value =>
    carrier.ofModel <| Model.roundRatQ carrier.format value

def defaultIterations (precision : Nat) : Nat :=
  if precision ≤ 64 then
    250000
  else if precision ≤ 256 then
    100000
  else if precision ≤ 512 then
    50000
  else if precision ≤ 1024 then
    20000
  else if precision ≤ 2048 then
    10000
  else
    5000

def iterationsFor (precision : Nat) : IO Nat := do
  FloatLibBenchmarks.Support.Environment.positiveNat
    "BENCH_ITERATIONS" (defaultIterations precision)

def printHeader : IO Unit :=
  IO.println <|
    "implementation,operation,precision,backend,policy,expectedCalls," ++
      "iterations,totalNanos,sink"

def timeRow (operation backend policyProfile : String)
    (expectedCalls precision iterations : Nat)
    (run : Unit → UInt64) : IO Unit := do
  let sink ← IO.mkRef 0
  let start ← IO.monoNanosNow
  sink.set (run ())
  let stop ← IO.monoNanosNow
  let result ← sink.get
  IO.println <|
    s!"ExecFloat,{operation},{precision},{backend},{policyProfile},{expectedCalls}," ++
      s!"{iterations},{stop - start},{result.toNat}"

private def runBinary
    {F : Type} [EncodedFormat F] [BenchmarkCarrier F FloatFormat Model]
    (operation backend policyProfile : String) (expectedCalls precision : Nat)
    (workload : Nat → Array (ExecFloat F) →
      Array (ExecFloat F) → UInt64 → UInt64) :
    IO Unit := do
  let xs := inputsX F
  let ys := inputsY F
  let warmup ← IO.mkRef 0
  warmup.set (workload 32 xs ys 0)
  let iterations ← iterationsFor precision
  timeRow operation backend policyProfile expectedCalls precision iterations fun _ =>
    workload iterations xs ys 0

private def runTernary
    {F : Type} [EncodedFormat F] [BenchmarkCarrier F FloatFormat Model]
    (operation backend policyProfile : String) (expectedCalls precision : Nat)
    (workload : Nat → Array (ExecFloat F) →
      Array (ExecFloat F) →
      Array (ExecFloat F) → UInt64 → UInt64) : IO Unit := do
  let xs := inputsX F
  let ys := inputsY F
  let zs := xs.reverse
  let warmup ← IO.mkRef 0
  warmup.set (workload 32 xs ys zs 0)
  let iterations ← iterationsFor precision
  timeRow operation backend policyProfile expectedCalls precision iterations fun _ =>
    workload iterations xs ys zs 0

private def runUnary
    {F : Type} [EncodedFormat F] [carrier : BenchmarkCarrier F FloatFormat Model]
    (operation backend policyProfile : String) (expectedCalls precision : Nat)
    (workload : Nat → Array (ExecFloat F) → UInt64 → UInt64) : IO Unit := do
  let xs := inputsSqrt F
  let warmup ← IO.mkRef 0
  warmup.set (workload 32 xs 0)
  let iterations ← iterationsFor precision
  timeRow operation backend policyProfile expectedCalls precision iterations fun _ =>
    workload iterations xs 0

/-- Time public addition and record the certificate actually selected by the capability. -/
opaque runAdd
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F FloatFormat Model] [ExecFloat.Add F]
    (precision : Nat)
    (workload : Nat → Array (ExecFloat F) →
      Array (ExecFloat F) → UInt64 → UInt64) : IO Unit :=
  let policy := ExecFloat.Add.policy (F := F)
  runBinary "add" (ExecFloat.Add.selectedCandidate (F := F)).name
    policy.profileName policy.expectedCalls precision workload

/-- Time public subtraction and record the certificate actually selected by the capability. -/
opaque runSub
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F FloatFormat Model] [ExecFloat.Sub F]
    (precision : Nat)
    (workload : Nat → Array (ExecFloat F) →
      Array (ExecFloat F) → UInt64 → UInt64) : IO Unit :=
  let policy := ExecFloat.Sub.policy (F := F)
  runBinary "sub" (ExecFloat.Sub.selectedCandidate (F := F)).name
    policy.profileName policy.expectedCalls precision workload

/-- Time public multiplication and record the selected certificate. -/
opaque runMul
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F FloatFormat Model] [ExecFloat.Mul F]
    (precision : Nat)
    (workload : Nat → Array (ExecFloat F) →
      Array (ExecFloat F) → UInt64 → UInt64) : IO Unit :=
  let policy := ExecFloat.Mul.policy (F := F)
  runBinary "mul" (ExecFloat.Mul.selectedCandidate (F := F)).name
    policy.profileName policy.expectedCalls precision workload

/-- Time public division and record the selected certificate. -/
opaque runDiv
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F FloatFormat Model] [ExecFloat.Div F]
    (precision : Nat)
    (workload : Nat → Array (ExecFloat F) →
      Array (ExecFloat F) → UInt64 → UInt64) : IO Unit :=
  let policy := ExecFloat.Div.policy (F := F)
  runBinary "div" (ExecFloat.Div.selectedCandidate (F := F)).name
    policy.profileName policy.expectedCalls precision workload

/-- Time public square root and record the selected certificate. -/
opaque runSqrt
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F FloatFormat Model] [ExecFloat.Sqrt F]
    (precision : Nat)
    (workload : Nat → Array (ExecFloat F) → UInt64 → UInt64) : IO Unit :=
  let policy := ExecFloat.Sqrt.policy (F := F)
  runUnary "sqrt" (ExecFloat.Sqrt.selectedCandidate (F := F)).name
    policy.profileName policy.expectedCalls precision workload

/-- Time public FMA and record the certificate actually selected by the capability. -/
opaque runFma
    {F : Type} [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [BenchmarkCarrier F FloatFormat Model] [ExecFloat.Fma F]
    (precision : Nat)
    (workload : Nat → Array (ExecFloat F) →
      Array (ExecFloat F) →
      Array (ExecFloat F) → UInt64 → UInt64) : IO Unit :=
  let policy := ExecFloat.Fma.policy (F := F)
  runTernary "fma" (ExecFloat.Fma.selectedCandidate (F := F)).name
    policy.profileName policy.expectedCalls precision workload

end FloatLibBenchmarks.Public.Sweep
