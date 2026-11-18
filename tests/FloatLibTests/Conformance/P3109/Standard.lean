/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109

/-!
# P3109 interim report v4.1 query and mixed-format regression checks

The eight rows of Table 2 (§4.13.1), NaN-first total order (§4.12.1), policy
queries (§4.15), and independent source descriptors (§4.10) are checked here.
These closed cases supplement the universally quantified query proofs.
-/

@[expose] public section

namespace FloatLibTests.Conformance.P3109.Standard

open FloatLib.Floats
open Formats.P3109
open ExecFloat.P3109

private abbrev F := Format.binary8p4se

-- Each code is chosen from a different row of the report's classifier table.
example :
    ([128, 255, 196, 129, 0, 1, 68, 127].map fun code =>
      Class (ofNatBits code : ExecFloat.P3109 F)) =
      [.ClsNaN, .ClsNegativeInfinity, .ClsNegativeNormal, .ClsNegativeSubnormal,
       .ClsZero, .ClsPositiveSubnormal, .ClsPositiveNormal, .ClsPositiveInfinity] := by
  decide

-- The first NaN rule takes precedence when both operands are NaN.
example :
    TotalOrder (nan : ExecFloat.P3109 F) (nan : ExecFloat.P3109 .binary8p3se) = true ∧
    TotalOrder (nan : ExecFloat.P3109 F) (ofNatBits 64 : ExecFloat.P3109 .binary8p3se) = true ∧
    TotalOrder (ofNatBits 64 : ExecFloat.P3109 F) (nan : ExecFloat.P3109 .binary8p3se) = false := by
  decide

-- Different source precisions: 5/4 + 1/16 = 21/16, a target tie whose even code is 66.
example :
    (ExecFloat.P3109.Add
      (ofNatBits 65 : ExecFloat.P3109 .binary8p3se)
      (ofNatBits 32 : ExecFloat.P3109 F)
      (target := F)).toNatBits = 66 := by
  decide +kernel

-- A precision-one descriptor has no positive or negative subnormal class.
example (format : Format) (value : ExecFloat.P3109 format)
    (hprecision : format.precision = 1) :
    Class value ≠ .ClsPositiveSubnormal ∧ Class value ≠ .ClsNegativeSubnormal := by
  have hs := isSubnormal_eq_false_of_precision_eq_one value hprecision
  constructor <;> intro h
  · have hc := (class_eq_iff value .ClsPositiveSubnormal).mp h
    simp [ClassCondition, hs] at hc
  · have hc := (class_eq_iff value .ClsNegativeSubnormal).mp h
    simp [ClassCondition, hs] at hc

-- Projection queries are exact, independently of the chosen modes.
example (rounding : RoundingMode) (saturation : SaturationMode) :
    ({ rounding, saturation } : ProjectionPolicy).RoundOf = rounding ∧
    ({ rounding, saturation } : ProjectionPolicy).SatOf = saturation :=
  ⟨rfl, rfl⟩

end FloatLibTests.Conformance.P3109.Standard
