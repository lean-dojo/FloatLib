/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Proof
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof

import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Spec

/-!
# Correctness of exact-dyadic posit arithmetic

These theorems prove that exact-dyadic addition, subtraction, multiplication, division, square
root, and fused multiply-add equal the independent rational `Model.Spec` operations. The
executable definitions live in `Dyadic.Runtime`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DyadicArithmetic

open FloatLib.Numerics

variable {format : Format}

/-- Exact-dyadic addition refines the reference rational specification. -/
theorem add_eq_spec (left right : Model format) :
    add left right = Spec.add left right := by
  unfold add Spec.add
  rw [Model.toRat?_eq_toDyadic?_map, Model.toRat?_eq_toDyadic?_map]
  cases left.toDyadic? <;> cases right.toDyadic? <;>
    simp [DyadicRounding.round_eq_roundRat,
      FloatLib.Numerics.Dyadic.add_toRat]

/-- Exact-dyadic subtraction refines the reference rational specification. -/
theorem sub_eq_spec (left right : Model format) :
    sub left right = Spec.sub left right := by
  unfold sub Spec.sub
  rw [Model.toRat?_eq_toDyadic?_map, Model.toRat?_eq_toDyadic?_map]
  cases left.toDyadic? <;> cases right.toDyadic? <;>
    simp [DyadicRounding.round_eq_roundRat,
      FloatLib.Numerics.Dyadic.sub_toRat]

/-- Exact-dyadic multiplication refines the reference rational specification. -/
theorem mul_eq_spec (left right : Model format) :
    mul left right = Spec.mul left right := by
  unfold mul Spec.mul
  rw [Model.toRat?_eq_toDyadic?_map, Model.toRat?_eq_toDyadic?_map]
  cases left.toDyadic? <;> cases right.toDyadic? <;>
    simp [DyadicRounding.round_eq_roundRat,
      FloatLib.Numerics.Dyadic.mul_toRat]

/-- Exact-dyadic cross-multiplied division refines the rational specification. -/
theorem div_eq_spec (left right : Model format) :
    div left right = Spec.div left right := by
  unfold div Spec.div
  rw [Model.toRat?_eq_toDyadic?_map, Model.toRat?_eq_toDyadic?_map]
  cases left.toDyadic? <;> cases right.toDyadic? <;>
    simp [DyadicQuotient.round_eq_reference]

/-- Exact-dyadic squared-comparison square root refines the rational specification. -/
theorem sqrt_eq_spec (value : Model format) :
    sqrt value = Spec.sqrt value := by
  unfold sqrt Spec.sqrt
  rw [Model.toRat?_eq_toDyadic?_map]
  cases hvalue : value.toDyadic? with
  | none =>
      rfl
  | some radicand =>
      simp only [Option.map_some]
      rw [FloatLib.Numerics.Dyadic.isLess_eq_decide,
        FloatLib.Numerics.Dyadic.zero_toRat]
      by_cases hnegative : radicand.toRat < 0
      · simp [hnegative]
      · simp [hnegative,
          DyadicSquareRoot.round_eq_reference_of_not_negative
            format radicand hnegative]

/-- Exact-dyadic fused multiply-add refines the reference rational specification. -/
theorem fma_eq_spec (left right addend : Model format) :
    fma left right addend = Spec.fma left right addend := by
  unfold fma Spec.fma
  rw [Model.toRat?_eq_toDyadic?_map, Model.toRat?_eq_toDyadic?_map,
    Model.toRat?_eq_toDyadic?_map]
  cases left.toDyadic? <;> cases right.toDyadic? <;> cases addend.toDyadic? <;>
    simp [DyadicRounding.round_eq_roundRat,
      FloatLib.Numerics.Dyadic.add_toRat, FloatLib.Numerics.Dyadic.mul_toRat]

end FloatLib.Floats.Formats.Posit.Model.DyadicArithmetic
