/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Formatting
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Core
public import FloatLib.Numerics.Core.Proof
public import FloatLib.Numerics.Operation.Semantics

/-!
# Block-scaled numerical systems

Microscaling formats store one E8M0 scale beside a block of low-precision element codes, and an
element word alone doesn't carry its full magnitude. So the numerical code is the whole block.
This module exposes that joint representation through `NumericalSystem`, and a successful decode
gives an array of exact dyadic values. Raw blocks can have any length. An empty block has no
element through which to read its scale, so it denotes the empty array even when the scale is NaN.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics

/-- One shared E8M0 scale and its policy-aware element codes. -/
structure BlockCode (fmt : FloatFormat) where
  /-- Shared E8M0 exponent code for the complete block. -/
  scale : E8M0
  /-- Element codes interpreted relative to the shared scale. -/
  values : Array (Model fmt)
  deriving DecidableEq, Repr

namespace BlockCode

/-- Decode the jointly stored scale and element words. -/
@[inline] def decode? {fmt : FloatFormat} (block : BlockCode fmt) :
    Option (Array Numerics.Dyadic) :=
  E8M0.decodeBlock? block.scale block.values

end BlockCode

/--
All-finite view of an E8M0-scaled block: the exact scaled element values when every element is
finite, and NaN otherwise. An element infinity, an element NaN and a NaN scale all make the whole
block NaN, which drops the per-lane values of OCP MX §5.1. `Standard.Block.decodeLane` keeps them,
decoding each lane of a concrete profile with its exceptional class.

The scale is read only through the elements, as in `E8M0.decodeBlock?`, so the empty block denotes
the empty array whatever its scale. Concrete OCP blocks, `Standard.Block`, always have 32
elements.
-/
def blockSystem (fmt : FloatFormat) : NumericalSystem where
  Code := BlockCode fmt
  Scalar := Array Numerics.Dyadic
  denote block :=
    match block.decode? with
    | some values => .finite values
    | none => .exceptional .nan

/-- A block represents `values` if and only if its joint decoder returns `values`. -/
theorem blockSystem_represents_iff {fmt : FloatFormat} (block : BlockCode fmt)
    (values : Array Numerics.Dyadic) :
    (blockSystem fmt).Represents block values ↔
      block.decode? = some values := by
  unfold NumericalSystem.Represents blockSystem
  cases hdecode : block.decode? with
  | none => simp [hdecode]
  | some decoded => simp [hdecode]

/-- A successfully decoded block with an erased proof of its exact dyadic array. -/
abbrev BlockAtFinite (fmt : FloatFormat) (values : Array Numerics.Dyadic) :=
  (blockSystem fmt).AtFinite values

/-- Attach a successful joint-decoding proof to a block code. -/
@[inline] def BlockCode.atFinite {fmt : FloatFormat} {values : Array Numerics.Dyadic}
    (block : BlockCode fmt) (hdecode : block.decode? = some values) :
    BlockAtFinite fmt values :=
  ⟨block, (blockSystem_represents_iff block values).2 hdecode⟩

/-- Joint block decoding is a checked exact operation. -/
theorem BlockCode.decode_refines (fmt : FloatFormat) :
    Operation.Checked1 (blockSystem fmt)
      (NumericalSystem.exact (Array Numerics.Dyadic)) BlockCode.decode?
      (fun values => .finite values) := by
  intro block values hblock
  have hdecode := (blockSystem_represents_iff block values).1 hblock
  rw [hdecode]
  rfl

end FloatLib.Floats.Formats.OCP.MX
