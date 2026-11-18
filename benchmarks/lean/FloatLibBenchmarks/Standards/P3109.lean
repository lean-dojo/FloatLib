/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.P3109
public import FloatLibBenchmarks.Standards.Protocol

/-!
# Inputs for the P3109 interim report v4.1 timing matrix

The signed extended descriptor has total width K and precision K − 3, giving
three exponent bits at every requested width. Samples use dense significands
near one. Unary functions use a positive operand below one, except ArcCosh,
which uses a value above one. Three-element blocks have exact rational scales
1/2, 3/2 and 5/4; result scales are 5/4. Every lane and the returned scale
contribute to the observation. No claim about other policies or block lengths
is inferred from this finite timing workload.

P3109 interim report v4.1, §3.1, specifies the descriptor fields.
-/

@[expose] public section

namespace FloatLibBenchmarks.Standards.P3109

open FloatLib.Floats Formats.P3109

/-- A fixed exponent width and increasing significand precision, signed and extended. -/
def format (width : Nat) (valid : 4 ≤ width) : Format :=
  Format.signed width (width - 3) .extended (by omega) (by omega) (by omega)

/-- Stored scalar operands and three independently scaled blocks. -/
structure Sample (width : Nat) (valid : 4 ≤ width) where
  x : ExecFloat.P3109 (format width valid)
  y : ExecFloat.P3109 (format width valid)
  z : ExecFloat.P3109 (format width valid)
  a : Block Rat (ExecFloat.P3109 (format width valid)) 3
  b : Block Rat (ExecFloat.P3109 (format width valid)) 3
  c : Block Rat (ExecFloat.P3109 (format width valid)) 3

/-- Assemble stored words and exact rational scales without evaluating any operation. -/
def sampleFromWords (width : Nat) (valid : 4 ≤ width) (a b c : Nat) : Sample width valid :=
  let x : ExecFloat.P3109 (format width valid) := ExecFloat.P3109.ofNatBits a
  let y : ExecFloat.P3109 (format width valid) := ExecFloat.P3109.ofNatBits b
  let z : ExecFloat.P3109 (format width valid) := ExecFloat.P3109.ofNatBits c
  { x, y, z
    a := ⟨mkRat 1 2, #v[x, x, x]⟩
    b := ⟨mkRat 3 2, #v[y, y, y]⟩
    c := ⟨mkRat 5 4, #v[z, z, z]⟩ }

/-- Eight seeds vary low stored bits while retaining finite, nonzero inputs. -/
def sample (width : Nat) (valid : 4 ≤ width) (seed : Nat) : Sample width valid :=
  let unit := 2 ^ (width - 4)
  let a := 4 * unit - unit / 3 - seed % 3
  let b := 4 * unit + unit / 5 + 1 + seed % 3
  sampleFromWords width valid a b (2 ^ (width - 1) + a)

/-- Full ordered observation of a vector of stored output words. -/
def observeValues {f : Format} {length : Nat} (values : Vector (ExecFloat.P3109 f) length) :
    Nat :=
  values.toList.foldl (fun acc value => acc * 2 ^ f.bitWidth + value.toNatBits) 1

/-- The stored scale and every output word contribute to a block observation. -/
def observeBlock {f : Format} {length : ℕ+} (block : Block Rat (ExecFloat.P3109 f) length) :
    Nat :=
  observeValues block.values +
    2 ^ (f.bitWidth * length) * (observeInt block.scale.num + block.scale.den)

/-- Complete enumeration of Table 2's classification result. -/
def observeClass : ClassEnum → Nat
  | .ClsNaN => 0
  | .ClsNegativeInfinity => 1
  | .ClsNegativeNormal => 2
  | .ClsNegativeSubnormal => 3
  | .ClsZero => 4
  | .ClsPositiveSubnormal => 5
  | .ClsPositiveNormal => 6
  | .ClsPositiveInfinity => 7

/-- Distinguish every rounding constructor and retain the complete supplied random word. -/
def observeRounding : RoundingMode → Nat
  | .towardZero => 0
  | .up => 1
  | .down => 2
  | .nearestAway => 3
  | .nearest => 4
  | .toOdd => 5
  | .stochasticA word => 6 + 3 * (2 ^ word.width + word.toNat)
  | .stochasticB word => 7 + 3 * (2 ^ word.width + word.toNat)
  | .stochasticC word => 8 + 3 * (2 ^ word.width + word.toNat)

/-- Complete observation of the three saturation modes. -/
def observeSaturation : SaturationMode → Nat
  | .none => 0
  | .finite => 1
  | .propagate => 2

/-- One lane policy for this timing workload: nearest-even, no saturation. -/
def blockPolicy : BlockPolicy 3 := {}

/-- The exact output scale used by the block timing rows. -/
def resultScale : Rat := mkRat 5 4

attribute [kernel_optimize unfold] format sampleFromWords sample observeValues observeBlock
  observeClass observeRounding observeSaturation blockPolicy resultScale

end FloatLibBenchmarks.Standards.P3109
