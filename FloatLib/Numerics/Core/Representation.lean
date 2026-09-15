/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.ExactSemantics

/-!
# Encoded numerical formats

`EncodedFormat F` assigns a code type and finite scalar domain to a format identity `F`.
Codes can be machine words, limb records, blocks, codebook indices, or runtime-sized values.

`FormatSemantics F` supplies the denotation separately. A real-valued denotation can then be
noncomputable while storage and arithmetic remain executable. Together the classes define a
`NumericalSystem`; optional capabilities add laws and operations as needed.

These interfaces also cover representations without a radix/exponent description. For the
radix-based generic-format approach, see Boldo and Melquiond, *Flocq: A Unified Library for Proving
Floating-Point Algorithms in Coq* (2011), <https://doi.org/10.1109/ARITH.2011.40>.
-/

@[expose] public section

namespace FloatLib.Numerics

universe u v w x

set_option linter.checkUnivs false in
/-- Runtime storage and finite scalar domain associated with the format identity `F`. -/
class EncodedFormat (F : Type u) where
  /-- Concrete runtime storage selected by `F`. -/
  Code : Type v
  /-- Ordinary finite semantic domain selected by `F`. -/
  Scalar : Type w

/-- Complete semantic interpretation of a format's runtime codes. -/
class FormatSemantics (F : Type u) [EncodedFormat F] where
  /-- Meaning of every code, including infinities and exceptional values. -/
  denote : EncodedFormat.Code (F := F) → NumericalValue (EncodedFormat.Scalar (F := F))

/-- Runtime storage selected by `F`. -/
abbrev FormatCode (F : Type u) [EncodedFormat F] : Type _ :=
  EncodedFormat.Code (F := F)

/-- Ordinary finite semantic domain selected by `F`. -/
abbrev FormatScalar (F : Type u) [EncodedFormat F] : Type _ :=
  EncodedFormat.Scalar (F := F)

namespace FormatSemantics

/-- Build format semantics when every stored code has an ordinary finite interpretation. -/
@[instance_reducible] def ofFinite (F : Type u) [EncodedFormat F]
    (decode : FormatCode F → FormatScalar F) : FormatSemantics F where
  denote code := .finite (decode code)

end FormatSemantics

/-- Complete interpretation of one code in `F`. -/
@[inline] def denoteFormat (F : Type u) [EncodedFormat F] [FormatSemantics F]
    (code : FormatCode F) : NumericalValue (FormatScalar F) :=
  FormatSemantics.denote code

/--
The general numerical system assembled from a format's storage and denotation.

The wrapper is reducible so Lean can reuse structures on `FormatCode F` and `FormatScalar F`
through `NumericalSystem.Code` and `NumericalSystem.Scalar` without forwarding instances.
-/
@[reducible] def formatSystem (F : Type u) [EncodedFormat F] [FormatSemantics F] :
    NumericalSystem where
  Code := FormatCode F
  Scalar := FormatScalar F
  denote := denoteFormat F

/-- A format code represents the ordinary scalar `value`. -/
abbrev FormatRepresents (F : Type u) [EncodedFormat F] [FormatSemantics F]
    (code : FormatCode F) (value : FormatScalar F) : Prop :=
  (formatSystem F).Represents code value

/--
Optional rich exact semantics for a type-directed format.

This capability is proof-facing. Executable kernels should call concrete family decoders rather
than project through `exactSemantics` in an arithmetic loop.
-/
class HasExactSemantics (F : Type u) [EncodedFormat F] [FormatSemantics F] where
  /-- Exact interpretation and its coherence theorem for `F`. -/
  exactSemantics : ExactSemantics.{x} (formatSystem F)

end FloatLib.Numerics
