/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Carrier
public import FloatLib.Floats.Formats.BinaryInterchange.Model.NumericalSystem

/-!
# Binary-interchange descriptors in the universal carrier

`Descriptor format` gives an arbitrary validated binary format a type-level identity. Its runtime
code is the existing `Model format`, so packing and unpacking are representation-preserving.

This module intentionally contains no arithmetic backend. Carrier-only clients should not have to
load word kernels, dispatch proofs, or planner machinery merely to name a descriptor.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat

/--
Type identity for one validated binary `FloatFormat` descriptor.

The descriptor is static in the type. Width, bias, and exceptional-value encoding therefore
specialize independently for every IEEE, non-IEEE, or user-defined format.
-/
inductive Descriptor (_format : FloatFormat) : Type

instance encodedFormat (format : FloatFormat) :
    EncodedFormat (Descriptor format) where
  Code := Model format
  Scalar := ℝ

noncomputable instance formatSemantics (format : FloatFormat) :
    FormatSemantics (Descriptor format) where
  denote := Model.toNumericalValue

/--
The descriptor carrier stores its proof model directly, so encoding and decoding are identities.

Registering that identity codec lets descriptor arithmetic use the same executable lifts and
refinement theorems as every configured format.
-/
instance descriptorModelCodec (format : FloatFormat) :
    ModelCodec () (Model format) (Model format) where
  toModel := id
  ofModel := id
  toModel_ofModel := fun _ => rfl
  ofModel_toModel := fun _ => rfl

namespace Descriptor

variable {format : FloatFormat}

/-- Inject a binary model value into the universal carrier without changing its code. -/
@[inline] def pack (value : Model format) :
    FloatLib.Floats.ExecFloat (Descriptor format) :=
  ModelCodec.encode (plan := ()) value

/-- Recover the binary model value without changing its representation. -/
@[inline] def unpack (value : FloatLib.Floats.ExecFloat (Descriptor format)) :
    Model format :=
  ModelCodec.decode (Model := Model format) (plan := ()) value

/-- Packing and then unpacking a model value is the identity. -/
@[simp] theorem unpack_pack (value : Model format) :
    unpack (pack value) = value :=
  ModelCodec.decode_encode (plan := ()) value

/-- Unpacking and then packing a descriptor value is the identity. -/
@[simp] theorem pack_unpack
    (value : FloatLib.Floats.ExecFloat (Descriptor format)) :
    pack (unpack value) = value :=
  ModelCodec.encode_decode (Model := Model format) (plan := ()) value

end Descriptor

end FloatLib.Floats.Formats.BinaryInterchange
