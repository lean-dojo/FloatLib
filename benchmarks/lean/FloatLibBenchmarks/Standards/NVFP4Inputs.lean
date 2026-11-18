/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.Block.Stored
public import FloatLibBenchmarks.Standards.MX

/-!
# Complete stored NVFP4 observations

NVIDIA, arXiv:2509.25149v2, Appendix B.1–B.3. These fixtures use 16-element
blocks, E2M1 elements, E4M3 local scales and one binary32 outer scale.
Exact rational scale selection and supplied outer scales are separate cases.
Stored dot operands require no quantization. Complete observations include
every element and scale; native and kernel use the same first finite input.
-/

@[expose] public section

namespace FloatLibBenchmarks.Standards.NVFP4Inputs

open FloatLib.Numerics FloatLib.Floats.Formats BinaryInterchange

/-- Consecutive sixteen-position local groups inside one outer group. -/
def group {n : Nat} (i : Fin n) : Nat := i.val / 16

/-- NVIDIA's three stored code formats with sixteen-position local groups.

NVIDIA, *Pretraining Large Language Models with NVFP4* (2025), Appendix B. -/
def format (n : Nat) : Block.CodedFormat (Fin n) Nat :=
  Block.nvfp4Stored (fun _ => 0) (@group n)

/-- Exact rational scaling, with the outer scale selected from all positions. -/
def dynamicPolicy (n : Nat) : Block.Policy (Fin n) Nat :=
  Block.nvfp4Policy (fun _ => 0) (@group n)

/-- The outer binary32 scale is supplied as one; each local scale is selected. -/
def suppliedPolicy (n : Nat) : Block.Policy (Fin n) Nat :=
  Block.nvfp4Supplied (@group n) (fun _ => 1)

/-- Stored finite and exceptional code regimes, with no hidden quantization. -/
def tensorInput (n seed : Nat) : Block.Tensor (format n) :=
  { scales :=
      (fun _ => OFP8.sample .binary32 seed,
        (fun b => BitVec.ofNat 8 (if seed % 8 = 0 then 56 + b else 17 * seed + b)), ())
    elements := fun i => BitVec.ofNat 4 (if seed % 8 = 0 then 1 + i.val % 7
      else 3 * seed + i.val) }

/-- Pack every stored field in order, including the complete outer binary32 word. -/
def observeTensor {n : Nat} (value : Block.Tensor (format n)) : Nat :=
  let outer := 2 ^ 32 + (value.scales.1 0).toNatBits
  let localScales := (List.range ((n + 15) / 16)).foldl
    (fun acc b => acc * 256 + (value.scales.2.1 b).toNat) outer
  (List.finRange n).foldl (fun acc i => acc * 16 + (value.elements i).toNat) localScales

/-- Balanced natural pairing keeps complete variable-width observations linear in bit size. -/
def observeTree (values : Nat → Nat) : Nat → Nat → Nat
  | 0, first => values first
  | depth + 1, first =>
      Nat.pair (observeTree values depth first)
        (observeTree values depth (first + 2 ^ depth))

/-- Pair every decoded position, preserving signs, zero signs and exceptional metadata.
Padding to the next power of two and recording the length preserves all positions. -/
def observeDecoded {n : Nat} (value : Block.Tensor (format n)) : Nat :=
  Nat.pair n (observeTree
    (fun i => if h : i < n then OFP8.observeDecoded (value.decode ⟨i, h⟩) else 0)
    (Nat.log2 n + 1) 0)

/-- Four local groups for a 64-position ordered reduction. -/
def blocks (n : Nat) : List (List (Fin n)) :=
  (List.range ((n + 15) / 16)).map fun b =>
    (List.finRange n).filter fun i => group i == b

attribute [kernel_optimize unfold]
  group format dynamicPolicy suppliedPolicy tensorInput observeTensor observeTree observeDecoded blocks

end FloatLibBenchmarks.Standards.NVFP4Inputs
