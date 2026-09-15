/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook.Configured.Core

/-!
# Executable configured-codebook operations

These operations expose storage and semantic decoding for any selected codebook. Arithmetic is
deliberately absent: a generic lookup table does not determine how its entries should combine.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Codebook

open FloatLib.Numerics

universe u

variable {width : Nat} {α : Type u} {book : Formats.Codebook width α}

/-- Wrap one complete codebook word without conversion. -/
@[inline] def ofCode (code : Formats.Codebook.Code book) :
    ExecFloat.Codebook book :=
  ExecFloat.ofRaw code

/-- Recover the complete codebook word without conversion. -/
@[inline] def toCode (value : ExecFloat.Codebook book) :
    Formats.Codebook.Code book :=
  value.raw

/-- Construct a codebook value from a natural-number bit pattern. -/
@[inline] def ofNatBits (bits : Nat) : ExecFloat.Codebook book :=
  ofCode (Formats.Codebook.ofNatBits book bits)

/-- Read the complete stored word as a natural number. -/
@[inline] def toNatBits (value : ExecFloat.Codebook book) : Nat :=
  Formats.Codebook.toNatBits book value.toCode

/-- Apply the selected table's complete finite or exceptional denotation. -/
@[inline] def decode (value : ExecFloat.Codebook book) : NumericalValue α :=
  book.denote value.toCode

end FloatLib.Floats.ExecFloat.Codebook
