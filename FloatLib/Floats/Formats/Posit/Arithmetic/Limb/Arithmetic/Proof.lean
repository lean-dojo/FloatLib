/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Arithmetic.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.Proof

import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Spec
public import Mathlib.Analysis.Real.Sqrt

/-!
# Refinement of two-limb posit arithmetic

These kernels round exact dyadic results using two-limb candidates. Addition, subtraction,
multiplication, and fused multiply-add agree with the rational posit specification. Pair-word
division decodes the operands and delegates to the shared direct divider; `divWords_eq_div`
relates that adapter to model division.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbArithmetic

open FloatLib.Numerics

variable {format : Format}

/-- Two-limb-rounded addition refines the reference rational specification. -/
theorem add_eq_spec (heligible : NativeLimb.Eligible format)
    (left right : Model format) :
    add heligible left right = Spec.add left right := by
  unfold add Spec.add
  rw [Model.toRat?_eq_toDyadic?_map, Model.toRat?_eq_toDyadic?_map]
  cases left.toDyadic? <;> cases right.toDyadic? <;>
    simp [NativeLimbPacked.Boundary.binaryResult,
      NativeLimbRounding.round_eq_roundRat,
      FloatLib.Numerics.Dyadic.add_toRat]

/-- Two-limb-rounded subtraction refines the reference rational specification. -/
theorem sub_eq_spec (heligible : NativeLimb.Eligible format)
    (left right : Model format) :
    sub heligible left right = Spec.sub left right := by
  unfold sub Spec.sub
  rw [Model.toRat?_eq_toDyadic?_map, Model.toRat?_eq_toDyadic?_map]
  cases left.toDyadic? <;> cases right.toDyadic? <;>
    simp [NativeLimbPacked.Boundary.binaryResult,
      NativeLimbRounding.round_eq_roundRat,
      FloatLib.Numerics.Dyadic.sub_toRat]

/-- Two-limb-rounded multiplication refines the reference rational specification. -/
theorem mul_eq_spec (heligible : NativeLimb.Eligible format)
    (left right : Model format) :
    mul heligible left right = Spec.mul left right := by
  unfold mul Spec.mul
  rw [Model.toRat?_eq_toDyadic?_map, Model.toRat?_eq_toDyadic?_map]
  cases left.toDyadic? <;> cases right.toDyadic? <;>
    simp [NativeLimbPacked.Boundary.binaryResult,
      NativeLimbRounding.round_eq_roundRat,
      FloatLib.Numerics.Dyadic.mul_toRat]

/--
Pair-word division is exactly the shared direct divider applied to the corresponding model
values.
-/
theorem divWords_eq_div
    (format : Format)
    (left right : FloatLib.Numerics.FixedWord.UInt128)
    (heligible : NativeLimb.Eligible format)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    divWords format left right =
      DirectDyadicArithmetic.div
        (Model.ofNatBits (format := format) left.toNat)
        (Model.ofNatBits (format := format) right.toNat) := by
  unfold divWords DirectDyadicArithmetic.div
  rw [NativeLimb.toDyadic?_eq_model format left heligible hleft,
    NativeLimb.toDyadic?_eq_model format right heligible hright]

/-- Two-limb-rounded FMA refines the single-rounding specification. -/
theorem fma_eq_spec (heligible : NativeLimb.Eligible format)
    (left right addend : Model format) :
    fma heligible left right addend = Spec.fma left right addend := by
  unfold fma Spec.fma
  rw [Model.toRat?_eq_toDyadic?_map, Model.toRat?_eq_toDyadic?_map,
    Model.toRat?_eq_toDyadic?_map]
  cases left.toDyadic? <;> cases right.toDyadic? <;>
    cases addend.toDyadic? <;>
      simp [NativeLimbPacked.Boundary.ternaryResult,
        NativeLimbRounding.round_eq_roundRat,
        FloatLib.Numerics.Dyadic.add_toRat,
        FloatLib.Numerics.Dyadic.mul_toRat]

end FloatLib.Floats.Formats.Posit.Model.NativeLimbArithmetic
