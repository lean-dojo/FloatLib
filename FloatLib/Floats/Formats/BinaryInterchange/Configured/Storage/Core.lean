/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Selection.Metadata
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Core.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Carrier
public import FloatLib.Numerics.Representations.StaticStorage
public import Mathlib.Data.Real.Basic
public import FloatLib.Numerics.Core.Representation

/-!
# Static carriers for configured binary formats

`Configured.Family format code plan` separates the mathematical binary descriptor from its
persistent runtime representation. The proof-carrying `StoragePlan` chooses the smallest built-in
machine word that contains the complete encoding. Formats wider than a machine word retain the
exact-width proof model by default: the two-word kernels split it into native words on each call,
and the generic kernel computes on it directly. Formats wider than 128 bits may instead opt into
`StoragePlan.limbs`, a `LimbArray` of 32-bit limbs (`WideLimb.Value`) that is the carrier of the
wide-limb kernels; `ExecFloat.BinaryLimbs` names that choice. The limb carrier is not the
automatic choice because every operation without a limb kernel, and every comparison or
conversion, must first rebuild the proof model from the limbs.

The plan is part of the type, not data stored in each value. Closed configured formats therefore
specialize to the selected carrier with erased range evidence. This module defines only
the plan, carriers, and encoded-family identity; packing, proofs, codecs, and semantics live in
downstream modules.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Numerics

/--
A certified persistent-storage choice for one binary-interchange descriptor.

The proof stored by each constructor is erased. `wide` keeps the exact-width proof model as the
carrier and is selected automatically for every width above 64 bits. `limbs` stores a
runtime-sized array of 32-bit limbs for widths above 128 bits; it is chosen explicitly through
`ExecFloat.BinaryLimbs` to use direct limb addition, subtraction, multiplication, and fused
multiply-add, at the cost of conversions for operations that must rebuild the proof model.
-/
inductive StoragePlan (format : FloatFormat) where
  | byte (width_le : format.bitWidth ≤ 8)
  | word16 (width_le : format.bitWidth ≤ 16)
  | word32 (width_le : format.bitWidth ≤ 32)
  | word64 (width_le : format.bitWidth ≤ 64)
  | wide
  | limbs (width_gt : 128 < format.bitWidth)

namespace StoragePlan

/--
Choose the smallest built-in storage class from a known encoded width.

`width_eq` lets parameterized APIs expose the width as a reducible arithmetic expression. Thus
`ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)` reduces directly to the `word32`
branch without evaluating an opaque descriptor during typeclass search.
-/
abbrev forKnownWidth (format : FloatFormat) (width : Nat)
    (width_eq : format.bitWidth = width) : StoragePlan format :=
  if h8 : width ≤ 8 then
    .byte (by simpa [width_eq] using h8)
  else if h16 : width ≤ 16 then
    .word16 (by simpa [width_eq] using h16)
  else if h32 : width ≤ 32 then
    .word32 (by simpa [width_eq] using h32)
  else if h64 : width ≤ 64 then
    .word64 (by simpa [width_eq] using h64)
  else
    .wide

/-- The limb-array plan for a descriptor of known width above 128 bits. -/
abbrev limbsForKnownWidth (format : FloatFormat) (width : Nat)
    (width_eq : format.bitWidth = width) (width_gt : 128 < width) : StoragePlan format :=
  .limbs (by simpa [width_eq] using width_gt)

/-- Choose storage directly from a closed descriptor. -/
def automatic (format : FloatFormat) : StoragePlan format :=
  forKnownWidth format format.bitWidth rfl

/-- Common execution-planner storage metadata corresponding to a certified plan. -/
@[inline] def storageClass {format : FloatFormat} :
    StoragePlan format → FloatLib.Floats.ExecFloat.Backend.StorageClass
  | .byte _ => .byte
  | .word16 _ => .word16
  | .word32 _ => .word32
  | .word64 _ => .word64
  | .wide => .wideLimbs
  | .limbs _ => .wideLimbs

end StoragePlan

/--
Type-level identity of a configured binary format and its statically selected storage plan.

The runtime code is an explicit parameter instead of a dependent result computed inside the
`EncodedFormat` instance. Lean's compiler can therefore use its ordinary polymorphic calling
convention in generic definitions and still reduce a closed configured type to `UInt8`, `UInt16`,
`UInt32`, or `UInt64`.
-/
inductive Family
    (_format : FloatFormat) (_code : Type) (_plan : StoragePlan _format) : Type

/-- Valid direct `UInt16` code for one descriptor. The bound proof is erased. -/
abbrev Word16Code (format : FloatFormat) :=
  StaticStorage.Word16Code (2 ^ format.bitWidth)

/-- Valid direct `UInt32` code for one descriptor. The bound proof is erased. -/
abbrev Word32Code (format : FloatFormat) :=
  StaticStorage.Word32Code (2 ^ format.bitWidth)

/-- Valid direct `UInt64` code for one descriptor. The bound proof is erased. -/
abbrev Word64Code (format : FloatFormat) :=
  StaticStorage.Word64Code (2 ^ format.bitWidth)

/--
Runtime code selected by a static storage plan.

This is reducible intentionally. A closed configured type must expose its primitive carrier to
Lean's compiler; hiding the match behind an opaque definition makes a compiled `UInt8`/`UInt32`
result look like a boxed object at generic call sites.
-/
abbrev Code {format : FloatFormat} : StoragePlan format → Type
  | .byte _ => StaticStorage.ByteCode (2 ^ format.bitWidth)
  | .word16 _ => Word16Code format
  | .word32 _ => Word32Code format
  | .word64 _ => Word64Code format
  | .wide => Model format
  | .limbs _ => Model.WideLimb.Value format

instance (format : FloatFormat) (code : Type) (plan : StoragePlan format) :
    EncodedFormat (Family format code plan) where
  Code := code
  Scalar := ℝ

end FloatLib.Floats.Formats.BinaryInterchange.Configured
