/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Direct.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Direct.Proof

import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Correctness of direct arbitrary-width exact-dyadic posit arithmetic

The direct-packing kernels agree with the rational specification. Addition, subtraction,
multiplication, square root, and FMA are related through the exact-dyadic implementation.
Division uses the quotient-prefix refinement directly. Executable definitions are in
`Direct.Runtime`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DirectDyadicArithmetic

open FloatLib.Numerics

variable {format : Format}

/-- Direct arbitrary-width addition equals the shared exact-dyadic implementation. -/
theorem add_eq_dyadic (left right : Model format) :
    add left right = DyadicArithmetic.add left right := by
  unfold add DyadicArithmetic.add
  cases left.toDyadic? <;> cases right.toDyadic? <;>
    simp [DirectDyadicPacking.round_eq_dyadic]

/-- Direct arbitrary-width subtraction equals the shared exact-dyadic implementation. -/
theorem sub_eq_dyadic (left right : Model format) :
    sub left right = DyadicArithmetic.sub left right := by
  unfold sub DyadicArithmetic.sub
  cases left.toDyadic? <;> cases right.toDyadic? <;>
    simp [DirectDyadicPacking.round_eq_dyadic]

/-- Direct arbitrary-width multiplication equals the shared exact-dyadic implementation. -/
theorem mul_eq_dyadic (left right : Model format) :
    mul left right = DyadicArithmetic.mul left right := by
  unfold mul DyadicArithmetic.mul
  cases left.toDyadic? <;> cases right.toDyadic? <;>
    simp [DirectDyadicPacking.round_eq_dyadic]

/-- Direct arbitrary-width square root equals squared-boundary rounding. -/
theorem sqrt_eq_dyadic (value : Model format) :
    sqrt value = DyadicArithmetic.sqrt value := by
  unfold sqrt DyadicArithmetic.sqrt
  cases hvalue : value.toDyadic? with
  | none =>
      rfl
  | some radicand =>
      simp only
      by_cases hnegative :
          radicand.isLess FloatLib.Numerics.Dyadic.zero = true
      · simp [hnegative]
      · simp only [hnegative, Bool.false_eq_true, ite_false]
        apply DirectDyadicSquareRoot.round_eq_dyadic_of_not_negative
        intro hlt
        apply hnegative
        rw [FloatLib.Numerics.Dyadic.isLess_eq_decide,
          FloatLib.Numerics.Dyadic.zero_toRat]
        exact decide_eq_true hlt

/-- Direct arbitrary-width FMA equals the shared exact-dyadic implementation. -/
theorem fma_eq_dyadic (left right addend : Model format) :
    fma left right addend = DyadicArithmetic.fma left right addend := by
  unfold fma DyadicArithmetic.fma
  cases left.toDyadic? <;> cases right.toDyadic? <;>
      cases addend.toDyadic? <;>
    simp [DirectDyadicPacking.round_eq_dyadic]

/-- Direct arbitrary-width addition refines the reference rational specification. -/
theorem add_eq_spec (left right : Model format) :
    add left right = Spec.add left right := by
  rw [add_eq_dyadic, DyadicArithmetic.add_eq_spec]

/-- Direct arbitrary-width subtraction refines the reference rational specification. -/
theorem sub_eq_spec (left right : Model format) :
    sub left right = Spec.sub left right := by
  rw [sub_eq_dyadic, DyadicArithmetic.sub_eq_spec]

/-- Direct arbitrary-width multiplication refines the reference rational specification. -/
theorem mul_eq_spec (left right : Model format) :
    mul left right = Spec.mul left right := by
  rw [mul_eq_dyadic, DyadicArithmetic.mul_eq_spec]

/-- Direct arbitrary-width division refines the reference rational specification. -/
theorem div_eq_spec (left right : Model format) :
    div left right = Spec.div left right := by
  unfold div divDecoded Spec.div
  rw [Model.toRat?_eq_toDyadic?_map, Model.toRat?_eq_toDyadic?_map]
  cases left.toDyadic? <;> cases right.toDyadic? <;>
    simp [DirectDyadicQuotient.round_eq_reference]

/-- Direct arbitrary-width square root refines the reference rational specification. -/
theorem sqrt_eq_spec (value : Model format) :
    sqrt value = Spec.sqrt value := by
  rw [sqrt_eq_dyadic, DyadicArithmetic.sqrt_eq_spec]

/-- Direct arbitrary-width FMA refines the single-rounding specification. -/
theorem fma_eq_spec (left right addend : Model format) :
    fma left right addend = Spec.fma left right addend := by
  rw [fma_eq_dyadic, DyadicArithmetic.fma_eq_spec]

end FloatLib.Floats.Formats.Posit.Model.DirectDyadicArithmetic
