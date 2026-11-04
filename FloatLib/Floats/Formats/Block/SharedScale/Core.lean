/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.Representation
public import FloatLib.Numerics.Quantization.Deterministic
public import FloatLib.Numerics.Quantization.Spec
public import Init.Data.Vector.OfFn

/-!
# Shared-scale block model

A block code stores `lanes` rational values as one binary exponent and one integer significand
per lane, and each lane means `significand * 2 ^ exponent`. With exponent `-3` and significands `5`
and `-12`, the block holds `5/8` and `-3/2`. Quantization is contextual: the caller supplies the
shared exponent, and the universal format never infers one.

The layout follows the Open Compute Project microscaling model, but it fixes no element width and
no way of choosing the scale.

## Reference

* Open Compute Project, *OCP Microscaling Formats (MX) Specification, Version 1.0* (2023):
  <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Numerics

/-- Runtime storage for a block of integer significands with one shared binary exponent. -/
structure SharedScaleCode (lanes : Nat) where
  /-- Shared power-of-two exponent. -/
  exponent : Int
  /-- Per-lane integer significands. -/
  significands : Vector Int lanes
  deriving DecidableEq, Repr

/-- Type-level identity of an unbounded shared-scale block with `lanes` entries. -/
inductive SharedScale (lanes : Nat) where
  | format

instance (lanes : Nat) : EncodedFormat (SharedScale lanes) where
  Code := SharedScaleCode lanes
  Scalar := Vector Rat lanes

/-- Exact rational multiplier selected by a shared binary exponent. -/
@[inline] def scale (exponent : Int) : Rat :=
  (2 : Rat) ^ exponent

/-- Decode every lane using the one scale stored in the block. -/
@[inline] def decode {lanes : Nat} (code : SharedScaleCode lanes) : Vector Rat lanes :=
  if h : lanes = 0 then
    ⟨#[], by simp [h]⟩
  else
    let factor := scale code.exponent
    code.significands.map fun (significand : Int) => (significand : Rat) * factor

instance (lanes : Nat) : FormatSemantics (SharedScale lanes) :=
  FormatSemantics.ofFinite _ decode

/--
Exact block observation retaining the selected scale and stored significands.

Forgetting this observation decodes the rational vector and discards the choice of representation.
-/
def exactSemantics (lanes : Nat) : ExactSemantics (formatSystem (SharedScale lanes)) where
  Exact := SharedScaleCode lanes
  decode := id
  forget code := .finite (decode code)
  forget_decode _ := rfl

instance (lanes : Nat) : HasExactSemantics (SharedScale lanes) where
  exactSemantics := exactSemantics lanes

/--
Quantization at a caller-selected scale: retain the exponent and round each scaled lane to the
nearest integer, with ties to even.
-/
def QuantizesAt {lanes : Nat} (exponent : Int) (input : Vector Rat lanes)
    (result : SharedScaleCode lanes) : Prop :=
  result.exponent = exponent ∧
    ∀ lane : Fin lanes, result.significands[lane.val] =
      roundRatEven (input[lane.val] / scale exponent)

end FloatLib.Floats.Formats.Block
