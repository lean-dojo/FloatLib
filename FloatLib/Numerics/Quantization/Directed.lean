/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Ordered
public import FloatLib.Numerics.Quantization.Spec

/-!
# Directed relational quantization

These specifications characterize rounding toward negative and positive infinity as selection of
the lower or upper representable neighbor. They permit duplicate encodings of the same scalar and
therefore remain relational even when the selected mathematical value is unique.

The selected neighbor must be finite. These relations do not specify an overflow result when
the required finite neighbor does not exist.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Directed

open Ordered

/-- Relational specification for rounding toward negative infinity. -/
def towardNegative (system : NumericalSystem) [Preorder system.Scalar] :
    Spec Unit system.Scalar system.Code :=
  fun _ input code => LowerNeighbor system input code

/-- Relational specification for rounding toward positive infinity. -/
def towardPositive (system : NumericalSystem) [Preorder system.Scalar] :
    Spec Unit system.Scalar system.Code :=
  fun _ input code => UpperNeighbor system input code

/-- A downward-directed result has a finite denotation. -/
theorem towardNegative_isFinite {system : NumericalSystem} [Preorder system.Scalar]
    {input : system.Scalar} {code : system.Code}
    (hcode : towardNegative system () input code) :
    system.IsFinite code :=
  lowerNeighbor_isFinite hcode

/-- An upward-directed result has a finite denotation. -/
theorem towardPositive_isFinite {system : NumericalSystem} [Preorder system.Scalar]
    {input : system.Scalar} {code : system.Code}
    (hcode : towardPositive system () input code) :
    system.IsFinite code :=
  upperNeighbor_isFinite hcode

end FloatLib.Numerics.Quantization.Directed
