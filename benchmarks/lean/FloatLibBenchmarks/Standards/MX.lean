/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.OCP.MX
public import FloatLib.Floats.Formats.Block.CodedDot
public import FloatLibBenchmarks.Standards.OFP8

/-!
# Whole-result MX timing observations

OCP MX v1.0, §§5.3–5.4 and 6.1–6.3. Block conversion observes every
element code and every E8M0 scale in order. Dot inputs contain supplied
stored codes, so those timings exclude quantization. The standard
32-position block and a two-block reduction are separate fixtures.
Native arrays include signed zeros, extrema and exceptional scales.
The tagged kernel fixture is the same first finite native input.
-/

@[expose] public section

namespace FloatLibBenchmarks.Standards.MX

open FloatLib.Numerics FloatLib.Floats.Formats
open OCP.MX OCP.MX.Standard BinaryInterchange

/-- Eight exact conversion inputs, including zeros, signs and nonfinite data. -/
def scalarInput (seed : Nat) : NumericalValue SignedRat :=
  match seed % 8 with
  | 0 => .finite (SignedRat.ofRat (7 / 3))
  | 1 => .finite (SignedRat.ofRat (-7 / 3))
  | 2 => .finite (SignedRat.ofRat 0)
  | 3 => .finite SignedRat.negZero
  | 4 => .finite (SignedRat.ofRat (1 / 65536))
  | 5 => .finite (SignedRat.ofRat 65536)
  | 6 => .infinity false
  | _ => .exceptional .nan

/-- Exact rational vector; its preparation is excluded from native conversion time. -/
def vectorInput (n seed : Nat) : Fin n → SignedRat :=
  fun i => SignedRat.ofRat (mkRat (7 * ((i.val : Int) + 1 - seed * 4)) 3)

/-- Consecutive standard blocks, each containing at most 32 positions. -/
def group {n : Nat} (i : Fin n) : Nat := i.val / 32

/-- The supplied scale regimes include both finite endpoints and NaN. -/
def scaleInput (seed : Nat) : E8M0 :=
  E8M0.ofNatBits ([127, 0, 254, 255, 126, 128, 1, 253][seed % 8]?.getD 127)

/-- Stored inputs whose fields require no conversion or scale search. -/
def tensorInput (n : Nat) (profile : Profile) (seed : Nat) :
    Block.Tensor (format (@group n) profile) :=
  { scales := (fun _ => scaleInput seed, ())
    elements := fun i =>
      BitVec.ofNat profile.width
        (if seed % 8 = 0 then 1 + i.val % 7
         else seed * 17 + i.val * 3) }

/-- Encode all fixed-width stored fields into one natural, preserving their order. -/
def observeTensor {n : Nat} {profile : Profile}
    (value : Block.Tensor (format (@group n) profile)) : Nat :=
  let scales := (List.range ((n + 31) / 32)).foldl
    (fun acc block => acc * 256 + (value.scales.1 block).toNatBits) 1
  (List.finRange n).foldl
    (fun acc i => acc * 2 ^ profile.width + (value.elements i).toNat) scales

/-- Observe every dyadic field, distinguishing a failed decode. -/
def observeDyadic : Option FloatLib.Numerics.Dyadic → Nat
  | none => 0
  | some value =>
      1 + Nat.pair value.significand
        (2 * FloatLibBenchmarks.Standards.observeInt value.exponent + value.negative.toNat)

/-- Ordered consecutive blocks for the general dot fixture. -/
def blocks (n : Nat) : List (List (Fin n)) :=
  (List.range ((n + 31) / 32)).map fun b =>
    (List.finRange n).filter fun i => group i == b

attribute [kernel_optimize unfold]
  scalarInput vectorInput group scaleInput tensorInput observeTensor observeDyadic blocks

end FloatLibBenchmarks.Standards.MX
