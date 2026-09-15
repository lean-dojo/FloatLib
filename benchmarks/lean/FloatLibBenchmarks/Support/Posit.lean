/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Support.Carrier
public import FloatLibBenchmarks.Support.ExactWorkload
public import FloatLib.Floats.Formats.Posit.Configured

/-!
# Shared posit benchmark support

Public API sweeps and internal kernel calibrations must exercise identical encoded values. This
module owns the posit instance of the common carrier bridge, deterministic exact-rational input
generation, and observable result projection. Keeping these definitions outside either executable
prevents a benchmark from accidentally gaining a different workload while an implementation is
optimized.

The bridge is representation-independent: it operates through the configured posit codec and
therefore covers byte, native-word, fixed-limb, and wide carriers without exposing their storage
details to the benchmark loops.
-/

@[expose] public section

open FloatLib.Floats
open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit
open FloatLibBenchmarks.Support.ExactWorkload

namespace FloatLibBenchmarks.Support.Posit

instance configuredBenchmarkCarrier
    (format : Format) (plan : Configured.StoragePlan format) :
    BenchmarkCarrier
      (Configured.Family format (Configured.Code plan) plan) Format Model where
  format := format
  toModel := Configured.Family.toModel
  ofModel := Configured.Family.ofModel
  lowBits :=
    match plan with
    | .byte _ => fun value => UInt64.ofNat value.raw.1.toNat
    | .word16 _ => fun value => UInt64.ofNat value.raw.1.toNat
    | .word32 _ => fun value => UInt64.ofNat value.raw.1.toNat
    | .word64 _ => fun value => value.raw.1
    | .pair _ => fun value => value.raw.1.lo
    | .wide => fun value => UInt64.ofNat value.raw.toNatBits

/--
Benchmark-local default for a posit carrier, obtained by encoding exact zero.

This supports bounds-checked array access in clients of the posit benchmark harness. It is not a
global default for arbitrary numerical representations.
-/
instance benchmarkInhabited
    (F : Type) [EncodedFormat F] [carrier : BenchmarkCarrier F Format Model] :
    Inhabited (ExecFloat F) where
  default := carrier.ofModel (Model.zero carrier.format)

/-- First deterministic input vector, including both signs. -/
def inputsX
    (F : Type) [EncodedFormat F] [carrier : BenchmarkCarrier F Format Model] :
    Array (ExecFloat F) :=
  xs.map fun value =>
    carrier.ofModel <| Model.roundRat carrier.format value

/-- Second deterministic nonzero input vector, including both signs. -/
def inputsY
    (F : Type) [EncodedFormat F] [carrier : BenchmarkCarrier F Format Model] :
    Array (ExecFloat F) :=
  ys.map fun value =>
    carrier.ofModel <| Model.roundRat carrier.format value

/-- Nonnegative input vector used by square root. -/
def inputsSqrt
    (F : Type) [EncodedFormat F] [carrier : BenchmarkCarrier F Format Model] :
    Array (ExecFloat F) :=
  sqrtXs.map fun value =>
    carrier.ofModel <| Model.roundRat carrier.format value

/-- Low 64 result bits used only to make a timed result observable. -/
@[inline] def resultBits
    {F : Type} [EncodedFormat F] [carrier : BenchmarkCarrier F Format Model]
    (value : ExecFloat F) : UInt64 :=
  carrier.lowBits value

end FloatLibBenchmarks.Support.Posit
