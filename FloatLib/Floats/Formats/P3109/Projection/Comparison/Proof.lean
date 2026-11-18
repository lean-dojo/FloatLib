/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Comparison.Runtime
public import FloatLib.Floats.Formats.P3109.Conversion.Range
public import FloatLib.Floats.Formats.P3109.Projection.Correctness
public import FloatLib.Numerics.Order.Bisection.Proof
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Compare

/-!
# Exact-comparison projection certificates

The search agrees with the independent greatest-index specification. Every
rounded candidate lies on the descriptor's precision grid, so saturation followed
by encoding preserves its numerical datum. Real comparison refinement checks the
search and supplied comparator; it shares the report policy decision formulas.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.ComparisonRounding

/-- Every selected quantum is at least the descriptor's minimum, including at zero. -/
theorem minimumQuantumExponent_le_decodeQuantum (format : Format) (index : Nat) :
    format.minimumQuantumExponent ≤ format.decodeQuantum index := by
  unfold Format.decodeQuantum
  split
  · exact le_rfl
  next hzero =>
    unfold Format.decodePositiveFinite
    simp only [hzero, ite_false]
    split
    · exact le_rfl
    next hrow =>
      dsimp only
      unfold Format.minimumQuantumExponent
      have hpositive : (0 : Int) < Int.ofNat (index / 2 ^ format.trailingBits) :=
        Int.ofNat_lt.mpr (Nat.pos_of_ne_zero hrow)
      simp only [Int.ofNat_eq_natCast] at *
      omega

/-- All rounding modes produce a valid grid record at every natural candidate index. -/
theorem roundedAt_fitsPrecisionGrid (format : Format) (mode : RoundingMode)
    (negative : Bool) (compareTarget : Rat → Ordering) (index : Nat) :
    format.FitsPrecisionGrid (roundedAt format mode negative compareTarget index) := by
  unfold roundedAt
  apply format.fitsPrecisionGrid_of_rounded
  · have h := format.decodePositiveFinite_significand_lt_precision index
    split <;> omega
  · exact minimumQuantumExponent_le_decodeQuantum format index

/-- Signed exact-comparison rounding always produces a valid precision-grid record. -/
theorem rounded_fitsPrecisionGrid (format : Format) (mode : RoundingMode)
    (compareTarget : Rat → Ordering) :
    format.FitsPrecisionGrid (rounded format mode compareTarget) := by
  unfold rounded
  split
  · exact Or.inl rfl
  · exact roundedAt_fitsPrecisionGrid _ _ _ _ _

/-- Saturation and encoding preserve the rounded datum for every supplied comparison procedure. -/
theorem sameDatum_decode_code (format : Format) (policy : ProjectionPolicy)
    (compareTarget : Rat → Ordering) :
    Format.SameDatum (format.decode (code format policy compareTarget))
      (value format policy compareTarget) := by
  unfold code value
  exact format.sameDatum_decode_encodeSaturate _ _
    (.finite (rounded format policy.rounding compareTarget))
    (rounded_fitsPrecisionGrid format policy.rounding compareTarget)

end FloatLib.Floats.Formats.P3109.ComparisonRounding
