/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook.Catalog.Runtime

/-!
# Executable arithmetic for catalog codebooks

The illustrative catalog encodings have direct executable bit kernels. Refinement against their
numerical systems is proved in `Arithmetic.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Codebook

namespace Catalog.bipolar1

/-- Exact additive inverse for the one-bit bipolar codebook. -/
@[inline] def neg
    (x : Code Catalog.bipolar1) : Code Catalog.bipolar1 :=
  if x.toNat == 0 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0

/-- Exact multiplication for the one-bit bipolar codebook. -/
@[inline] def mul
    (x y : Code Catalog.bipolar1) : Code Catalog.bipolar1 :=
  if x == y then BitVec.ofNat 1 1 else BitVec.ofNat 1 0

end Catalog.bipolar1

namespace Catalog.ternary2

/-- Exact ternary negation, rejecting the reserved word. -/
@[inline] def neg?
    (x : Code Catalog.ternary2) : Option (Code Catalog.ternary2) :=
  match x.toNat with
  | 0 => some (BitVec.ofNat 2 0)
  | 1 => some (BitVec.ofNat 2 2)
  | 2 => some (BitVec.ofNat 2 1)
  | _ => none

/-- Exact ternary multiplication, returning `none` if either operand is the reserved word. -/
@[inline] def mul?
    (x y : Code Catalog.ternary2) : Option (Code Catalog.ternary2) :=
  match x.toNat, y.toNat with
  | 3, _ | _, 3 => none
  | 0, _ | _, 0 => some (BitVec.ofNat 2 0)
  | 1, 1 | 2, 2 => some (BitVec.ofNat 2 1)
  | 1, 2 | 2, 1 => some (BitVec.ofNat 2 2)
  | _, _ => none

end Catalog.ternary2

end FloatLib.Floats.Formats.Codebook
