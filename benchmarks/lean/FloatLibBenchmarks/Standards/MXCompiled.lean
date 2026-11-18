/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.OCP.MX.Standard.Compiled

/-!
# MX finite conversion benchmark

OCP MX v1.0, §5.3. Both implementations convert the same precomputed exact signed rationals.
The reference body is written out here so the compiler's replacement of `quantizeFinite`
does not silently replace the benchmark control. Each result contributes to a printed checksum.
This measures scalar conversion, not shared-scale selection or block quantization.
-/

open FloatLib.Numerics FloatLib.Floats.Formats.OCP.MX.Standard

namespace FloatLibBenchmarks.Standards.MXCompiled

private def profiles : List (String × Profile) :=
  [("e5m2", .e5m2), ("e4m3", .e4m3), ("e3m2", .e3m2),
    ("e2m3", .e2m3), ("e2m1", .e2m1), ("int8", .int8)]

@[noinline] private def exhaustive (profile : Profile) (input : SignedRat) : Nat :=
  (((Element.candidates profile).argmin (Element.roundingKey input)).getD (0, 0)).1.toNat

@[noinline] private def bisection (profile : Profile) (input : SignedRat) : Nat :=
  (Element.quantizeFinite profile input).toNat

private def inputs : Array SignedRat :=
  (List.range 1024).toArray.map fun (i : Nat) =>
    SignedRat.ofRat (mkRat ((i : Int) - 512) 37)

@[noinline] private def measure (f : SignedRat → Nat) (xs : Array SignedRat) (reps : Nat) :
    IO (Nat × Nat) := do
  let start ← IO.monoNanosNow
  let mut sink := 0
  for _ in [0:reps] do
    for x in xs do
      sink := sink + f x
  let stop ← IO.monoNanosNow
  return ((stop - start) / (reps * xs.size), sink)

end FloatLibBenchmarks.Standards.MXCompiled

open FloatLibBenchmarks.Standards.MXCompiled in
public def main : IO Unit := do
  let xs := inputs
  for (name, profile) in profiles do
    for x in xs do
      unless exhaustive profile x == bisection profile x do
        throw (IO.userError s!"MX conversion mismatch: {name}, {x.value}")
    for trial in [0:3] do
      let (slow, slowSink) ← measure (exhaustive profile) xs 2
      let (fast, fastSink) ← measure (bisection profile) xs 32
      unless fastSink == 16 * slowSink do
        throw (IO.userError s!"MX checksum mismatch: {name}")
      IO.println s!"MX_FINITE {name} bits={profile.width} trial={trial} reference_ns={slow} compiled_ns={fast} sink={fastSink}"
