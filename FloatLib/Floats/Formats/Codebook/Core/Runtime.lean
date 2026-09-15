/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.System
public import Mathlib.Data.BitVec

/-!
# Exact finite-codebook runtime model

A `Codebook width α` assigns a complete semantic value to each `BitVec width`. The runtime carrier
is always the exact-width bit vector; proof-indexed views are isolated in `Core.Proof`.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats

universe u

/-- Complete denotation of every word in an exact-width lookup encoding. -/
structure Codebook (width : Nat) (α : Type u) where
  /-- Meaning of each stored word. -/
  denote : BitVec width → NumericalValue α

namespace Codebook

variable {width : Nat} {α : Type u}

/--
Runtime storage type of a codebook.

The transparent definition compiles to the underlying `BitVec` while preserving the selected
codebook in elaborated types for inspection and family-specific APIs.
-/
@[reducible] def Code (_book : Codebook width α) :=
  BitVec width

/-- Construct a codebook value from a natural-number bit pattern. -/
@[inline] def ofNatBits (book : Codebook width α) (bits : Nat) : Code book :=
  BitVec.ofNat width bits

/-- Extract a codebook value as a natural-number bit pattern. -/
@[inline] def toNatBits (book : Codebook width α) (code : Code book) : Nat :=
  code.toNat

/-- Expose a codebook through the family-independent numerical-system interface. -/
def numericalSystem (book : Codebook width α) : NumericalSystem where
  Code := Code book
  Scalar := α
  denote := book.denote

end Codebook
end FloatLib.Floats.Formats
