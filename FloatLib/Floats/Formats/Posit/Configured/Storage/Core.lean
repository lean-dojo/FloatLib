/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Core
public import FloatLib.Floats.Formats.Posit.Model.Basic
public import FloatLib.Numerics.Representations.StaticStorage
public import FloatLib.Numerics.Core.Representation

/-!
# Static carriers for configured posits

A configured posit descriptor is independent of its persistent representation. `StoragePlan`
records a carrier and its width bound. `StoragePlan.forKnownWidth` chooses the first fitting
primitive word or two-limb carrier, using the exact-width model above 128 bits.

Storage evidence and subtype bounds are propositions and are erased by Lean. Closed formats
therefore retain primitive `UInt8`, `UInt16`, `UInt32`, `UInt64`, or two-limb payloads without
introducing a catalog of named posit types.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

open FloatLib.Numerics

/-- Certified persistent storage for one static posit width. -/
inductive StoragePlan (format : Format) where
  | byte (width_le : format.bits ≤ 8)
  | word16 (width_le : format.bits ≤ 16)
  | word32 (width_le : format.bits ≤ 32)
  | word64 (width_le : format.bits ≤ 64)
  | pair (width_le : format.bits ≤ 128)
  | wide

namespace StoragePlan

/-- Select the smallest built-in carrier from a definitionally known width. -/
abbrev forKnownWidth (format : Format) (width : Nat)
    (width_eq : format.bits = width) : StoragePlan format :=
  if h8 : width ≤ 8 then
    .byte (by simpa [width_eq] using h8)
  else if h16 : width ≤ 16 then
    .word16 (by simpa [width_eq] using h16)
  else if h32 : width ≤ 32 then
    .word32 (by simpa [width_eq] using h32)
  else if h64 : width ≤ 64 then
    .word64 (by simpa [width_eq] using h64)
  else if h128 : width ≤ 128 then
    .pair (by simpa [width_eq] using h128)
  else
    .wide

end StoragePlan

/-- Type-level identity of a posit descriptor and its statically chosen carrier. -/
inductive Family
    (_format : Format) (_code : Type) (_plan : StoragePlan _format) : Type

/-- Valid direct `UInt8` code for one posit descriptor. -/
abbrev ByteCode (format : Format) :=
  StaticStorage.ByteCode format.modulus

/-- Valid direct `UInt16` code for one posit descriptor. -/
abbrev Word16Code (format : Format) :=
  StaticStorage.Word16Code format.modulus

/-- Valid direct `UInt32` code for one posit descriptor. -/
abbrev Word32Code (format : Format) :=
  StaticStorage.Word32Code format.modulus

/-- Valid direct `UInt64` code for one posit descriptor. -/
abbrev Word64Code (format : Format) :=
  StaticStorage.Word64Code format.modulus

/-- Valid direct two-limb code for one posit descriptor. -/
abbrev PairCode (format : Format) :=
  StaticStorage.BoundedCode
    FloatLib.Numerics.FixedWord.UInt128
    FloatLib.Numerics.FixedWord.UInt128.toNat
    format.modulus

/-- Runtime carrier selected by a static storage plan. -/
abbrev Code {format : Format} : StoragePlan format → Type
  | .byte _ => ByteCode format
  | .word16 _ => Word16Code format
  | .word32 _ => Word32Code format
  | .word64 _ => Word64Code format
  | .pair _ => PairCode format
  | .wide => Model format

instance (format : Format) (code : Type) (plan : StoragePlan format) :
    EncodedFormat (Family format code plan) where
  Code := code
  Scalar := Rat

end FloatLib.Floats.Formats.Posit.Configured
