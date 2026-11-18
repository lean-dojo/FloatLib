/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109

/-!
# P3109 carrier arithmetic

Checks for the `ExecFloat.P3109` surface: literals, `IsInfinite`, `==` with NaN unequal to itself,
the `mode`, `saturation`, and `target` options of the arithmetic, `ofRat` with its default policy,
conversion with `(mode := ...)`, and `#eval` of a value. Closed cases use `binary8p4se`, whose
code `8e + t` has exponent field `e` and three trailing bits `t`.
-/

@[expose] public section

namespace FloatLibTests.Conformance.P3109.Arithmetic

open FloatLib.Floats
open FloatLib.Floats.Formats

-- Independent report formulas retain separate source and destination descriptors.
example {source : P3109.Format} (value : ExecFloat.P3109 source) (target : P3109.Format)
    (mode : P3109.RoundingMode) (sat : P3109.SaturationMode) (q : Rat)
    (hv : value.toClosedRat = .finite q) (hq : 0 ≤ q) :
    P3109.Format.SameDatum (ExecFloat.P3109.decode (value.Sqrt target mode sat))
      (P3109.ComparisonRounding.reportValue target ⟨mode, sat⟩ (Real.sqrt (q : ℝ))) :=
  ExecFloat.P3109.decode_sqrt_report value target mode sat q hv hq

example {source : P3109.Format} (value : ExecFloat.P3109 source) (target : P3109.Format)
    (mode : P3109.RoundingMode) (sat : P3109.SaturationMode) (q : Rat)
    (hv : value.toClosedRat = .finite q) (hq : 0 < q) :
    P3109.Format.SameDatum (ExecFloat.P3109.decode (value.RSqrt target mode sat))
      (P3109.ComparisonRounding.reportValue target ⟨mode, sat⟩
        (1 / Real.sqrt (q : ℝ))) :=
  ExecFloat.P3109.decode_rsqrt_report value target mode sat q hv hq

example {leftFormat rightFormat : P3109.Format}
    (left : ExecFloat.P3109 leftFormat) (right : ExecFloat.P3109 rightFormat)
    (target : P3109.Format) (mode : P3109.RoundingMode) (sat : P3109.SaturationMode)
    (x y : Rat) (hx : left.toClosedRat = .finite x) (hy : right.toClosedRat = .finite y) :
    P3109.Format.SameDatum (ExecFloat.P3109.decode (left.Hypot right target mode sat))
      (P3109.ComparisonRounding.reportValue target ⟨mode, sat⟩
        (Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))) :=
  ExecFloat.P3109.decode_hypot_report left right target mode sat x y hx hy

/-- The descriptor used by the closed checks. -/
abbrev B8P4 := ExecFloat.P3109 .binary8p4se

-- Literals round once to nearest, ties to even, with no saturation request: 300 exceeds the
-- largest finite value 224 and becomes positive infinity, code 127.
example :
    ((1.5 : B8P4).toNatBits, (-1.5 : B8P4).toNatBits, (300 : B8P4).toNatBits,
      (0 : B8P4).toNatBits) = (68, 196, 127, 0) := by
  decide +kernel

-- `IsInfinite` tests either infinity.
example :
    (300 : B8P4).IsInfinite = true ∧ (-300 : B8P4).IsInfinite = true ∧
      (224 : B8P4).IsInfinite = false ∧ (ExecFloat.P3109.nan : B8P4).IsInfinite = false := by
  decide +kernel

-- `==` is numerical equality: NaN is unequal to itself, and `compare` leaves NaN unordered.
example :
    ((ExecFloat.P3109.nan : B8P4) == ExecFloat.P3109.nan) = false ∧
      ((1.5 : B8P4) == 1.5) = true ∧ ((1.5 : B8P4) == 2) = false ∧
      ExecFloat.compare (1.5 : B8P4) 2 = some .lt ∧
      ExecFloat.compare (ExecFloat.P3109.nan : B8P4) 2 = none := by
  decide +kernel

-- `1 + 1/16` is the midpoint of 1 and 9/8: nearest-even keeps 1, the upward and ties-away
-- modes take 9/8, and the downward mode keeps 1.
example :
    ((ExecFloat.P3109.Add (1 : B8P4) (0.0625 : B8P4)).toNatBits,
      (ExecFloat.P3109.Add (1 : B8P4) (0.0625 : B8P4) (mode := .up)).toNatBits,
      (ExecFloat.P3109.Add (1 : B8P4) (0.0625 : B8P4) (mode := .nearestAway)).toNatBits,
      (ExecFloat.P3109.Add (1 : B8P4) (0.0625 : B8P4) (mode := .down)).toNatBits) =
      (64, 65, 65, 64) := by
  decide +kernel

-- `16 * 16` overflows: no saturation request gives infinity, finite saturation the largest
-- finite code 126.
example :
    ((ExecFloat.P3109.Multiply (16 : B8P4) (16 : B8P4)).toNatBits,
      (ExecFloat.P3109.Multiply (16 : B8P4) (16 : B8P4) (saturation := .finite)).toNatBits) =
      (127, 126) := by
  decide +kernel

-- `target` projects into another descriptor: upward rounding of `1 + 1/16` in binary8p3se gives
-- 5/4, code `4e + t` with `e = 16` and `t = 1`.
example :
    (ExecFloat.P3109.Add (1 : B8P4) (0.0625 : B8P4)
      (target := .binary8p3se) (mode := .up)).toNatBits = 65 := by
  decide +kernel

-- Square root rounds the exact real root: `√2` lies between 11/8 and 3/2, nearer the first.
example :
    ((ExecFloat.P3109.Sqrt (2 : B8P4)).toNatBits,
      (ExecFloat.P3109.Sqrt (2 : B8P4) (mode := .up)).toNatBits) = (67, 68) := by
  decide +kernel

-- `ofRat` defaults to nearest-even with no saturation request, and conversion takes the same
-- rounding modes through `(mode := ...)`. One third is `(1 + 2.67/8) / 4`.
example :
    ((ExecFloat.P3109.ofRat (format := .binary8p4se) (1 / 3)).toNatBits,
      (ExecFloat.P3109.ofRat (format := .binary8p4se) (1 / 3) (mode := .towardZero)).toNatBits,
      (ExecFloat.convert (1 / 3 : Rat) (target := B8P4)).value?.map (·.toNatBits),
      (ExecFloat.convert (1 / 3 : Rat) (target := B8P4) (mode := .towardZero)).value?.map
        (·.toNatBits)) =
      (51, 50, some 51, some 50) := by
  decide +kernel

-- With P3109 loaded, a binary model still decodes through the binary signed-rational decoder.
example :
    (inferInstance : ExecFloat.ExactDecoder (BinaryInterchange.Model .binary32)
        FloatLib.Numerics.SignedRat) =
      ExecFloat.Binary.Conversion.modelDecoder .binary32 :=
  rfl

/-- Binary32 negative zero and a quiet NaN with payload 5, as model operands. -/
private def modelOperands : List (BinaryInterchange.Model .binary32) :=
  [BinaryInterchange.Model.ofNatBits 0x80000000, BinaryInterchange.Model.ofNatBits 0x7fc00005]

-- Mixed report arithmetic erases a model operand's zero sign and NaN payload (§4.8.1), so the
-- negative zero acts as zero and the NaN as the report's one NaN, code 128.
example :
    modelOperands.map P3109.Arithmetic.Mixed.decode = [.finite 0, P3109.Arithmetic.nan] ∧
      modelOperands.map (fun operand =>
        (P3109.Arithmetic.Mixed.Add (P3109.Arithmetic.Destination.p3109 .binary8p4se) operand
          (1 : Rat)).toNatBits) = [64, 128] := by
  decide +kernel

/-- A stand-in display, so that the check below does not depend on the family's printer. -/
local instance :
    ExecFloat.FormatDisplay (ExecFloat.Codebook.Family P3109.Format.binary8p4se.codebook) where
  format _ := "a P3109 value"

-- `#eval` reduces the type of its value while it looks for a `ToExpr` instance. The irreducible
-- `Format.codebook` keeps that reduction from expanding the descriptor's decoder.
/-- info: a P3109 value -/
#guard_msgs in
#eval (1.5 : B8P4)

end FloatLibTests.Conformance.P3109.Arithmetic
