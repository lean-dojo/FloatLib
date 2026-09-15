/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Carrier

/-!
# Representation-independent benchmark carriers

Benchmark harnesses need the same small bridge regardless of numerical family: a static format
descriptor, lossless access to that descriptor's exact model, and a cheap observable projection
for timed results. Rounding remains family-specific and therefore does not belong in this class.
-/

@[expose] public section

namespace FloatLibBenchmarks.Support

open FloatLib.Floats
open FloatLib.Numerics

universe u v w

/-- Exact-model bridge shared by benchmark harnesses for every numerical family. -/
class BenchmarkCarrier
    (F : Type u) [EncodedFormat F] (Format : Type v) (Model : Format → Type w) where
  /-- Static descriptor represented by `F`. -/
  format : Format
  /-- Decode the persistent executable carrier into the exact proof model. -/
  toModel : ExecFloat F → Model format
  /-- Pack the exact proof model into the persistent executable carrier. -/
  ofModel : Model format → ExecFloat F
  /-- Low result bits used to keep timed workloads externally observable. -/
  lowBits : ExecFloat F → UInt64

end FloatLibBenchmarks.Support
