/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook.Configured.Runtime
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Representation theorems for configured codebooks

Wrapping and unwrapping preserve the complete exact-width word. Natural-number construction
reduces modulo `2 ^ width`.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Codebook

universe u

variable {width : Nat} {α : Type u} {book : Formats.Codebook width α}

/-- Unwrapping a freshly wrapped codebook word returns the original word. -/
@[simp, grind =] theorem toCode_ofCode (code : Formats.Codebook.Code book) :
    toCode (ofCode code) = code :=
  rfl

/-- Rewrapping the word of a codebook value returns the original value. -/
@[simp, grind =] theorem ofCode_toCode (value : ExecFloat.Codebook book) :
    ofCode value.toCode = value :=
  ExecFloat.ofRaw_raw value

/-- Encoding then reading a natural bit pattern reduces it modulo `2 ^ width`. -/
@[simp, grind =] theorem toNatBits_ofNatBits (bits : Nat) :
    toNatBits (ofNatBits (book := book) bits) = bits % 2 ^ width := by
  simp [toNatBits, ofNatBits, Formats.Codebook.toNatBits,
    Formats.Codebook.ofNatBits, BitVec.toNat_ofNat]

end FloatLib.Floats.ExecFloat.Codebook
