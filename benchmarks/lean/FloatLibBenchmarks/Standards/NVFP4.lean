/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.Block.Configured
import FloatLib.Floats.Formats.Block.Stored
import FloatLib.Floats.Formats.Block.CodedDot

/-!
# Native NVFP4 stored-tensor observations

NVIDIA, arXiv:2509.25149v2, Appendix B.1–B.3, with FloatLib's exact rational policy.
Quantization observes every element and every local scale. Decoding and dot timings use
prequantized tensors. Input arrays and stored dot operands are prepared before timing.
Every result contributes to a printed checksum. The outer scale is supplied as one.
-/

open FloatLib.Numerics FloatLib.Floats.Formats
open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibBenchmarks.Standards.NVFP4

private def format (n : Nat) : Block.CodedFormat (Fin n) Nat :=
  Block.nvfp4Stored (fun _ => 0) (fun i => i.val / 16)

private def policy (n : Nat) : Block.Policy (Fin n) Nat :=
  Block.nvfp4Supplied (fun i => i.val / 16) (fun _ => 1)

private def inputs (n : Nat) : Array (Array SignedRat) :=
  (List.range 16).toArray.map fun (j : Nat) =>
    (List.range n).toArray.map fun (i : Nat) =>
      SignedRat.ofRat (mkRat ((i : Int) - n / 2 + j) 7)

@[noinline] private def quantize (n : Nat) (x : Array SignedRat) : Block.Tensor (format n) :=
  (format n).quantize (policy n) fun i => x.getD i.val 0

private def codeSum {n : Nat} (x : Block.Tensor (format n)) : Nat :=
  ((List.finRange n).map fun i => (x.elements i).toNat).sum +
    ((List.range (n / 16)).map fun b => (x.scales.2.1 b).toNat).sum

-- Tensor fields are functions. Force every code so timed reads do not redo quantization.
private def materialize {n : Nat} (x : Block.Tensor (format n)) : Block.Tensor (format n) :=
  let outer := x.scales.1 0
  let localScales := (List.range (n / 16)).toArray.map fun b => x.scales.2.1 b
  let elements := (List.finRange n).toArray.map x.elements
  { scales := (fun _ => outer, (fun b => localScales.getD b 0), ())
    elements := fun i => elements.getD i.val (0 : BitVec 4) }

private def decodedSum {n : Nat} (x : Block.Tensor (format n)) : Nat :=
  ((List.finRange n).map fun i =>
    match x.decode i with
    | .finite q => q.value.num.natAbs + q.value.den
    | .infinity s => 1 + s.toNat
    | .exceptional _ => 3).sum

@[noinline] private def measure {α : Type} (f : α → Nat) (xs : Array α) :
    IO (Nat × Nat) := do
  let start ← IO.monoNanosNow
  let mut sink := 0
  for _ in [0:4] do
    for x in xs do
      sink := sink + f x
  let stop ← IO.monoNanosNow
  return ((stop - start) / (4 * xs.size), sink)

private def run (n : Nat) : IO Unit := do
  let xs := inputs n
  let tensors := xs.map fun x => materialize (quantize n x)
  let reference := materialize (quantize n (xs.getD 0 #[]))
  let order := List.finRange n
  let blocks := (List.range (n / 16)).map fun b => order.filter fun i => i.val / 16 == b
  for x in xs do
    let raw := quantize n x
    let stored := materialize raw
    unless codeSum raw == codeSum stored do
      throw (IO.userError "NVFP4 stored-code checksum mismatch")
  for trial in [0:3] do
    let (qtime, qsink) ← measure (fun x => codeSum (quantize n x)) xs
    IO.println s!"NVFP4 quantize n={n} trial={trial} ns={qtime} sink={qsink}"
    let (dtime, dsink) ← measure decodedSum tensors
    IO.println s!"NVFP4 decode n={n} trial={trial} ns={dtime} sink={dsink}"
    let (time, sink) ← measure
      (fun x => (OCP.MX.Dot .binary32 x reference order).toNatBits) tensors
    IO.println s!"NVFP4 Dot n={n} trial={trial} ns={time} sink={sink}"
    let (time, sink) ← measure
      (fun x => (OCP.MX.DotGeneral .binary32 x reference blocks).toNatBits) tensors
    IO.println s!"NVFP4 DotGeneral n={n} trial={trial} ns={time} sink={sink}"

end FloatLibBenchmarks.Standards.NVFP4

open FloatLibBenchmarks.Standards.NVFP4 in
public def main : IO Unit := do
  for n in [16, 64] do
    run n
