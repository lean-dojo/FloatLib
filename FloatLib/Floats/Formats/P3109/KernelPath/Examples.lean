/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109
public import FloatLib.Tactic.FloatDecide

/-!
# P3109 computations checked by Lean's kernel

P3109 Interim Report v4.1 (14 September 2026), §§4.7 to 4.11, an unapproved draft. Each theorem is
one closed computation in the report's Binary8p4se, decided by Lean's kernel: the arithmetic that
`float_decide` rewrites with the rules of `P3109.KernelPath.Rules` to the flat operations on
natural-number encodings (operands of two formats, a destination of a third, directed rounding
and saturation included), the extrema and comparisons, and the format queries. They are the
regression checks of those entry points inside the library; the statements for every descriptor,
mode and operand are the theorems of `P3109.KernelPath.Arithmetic` and `P3109.Arithmetic.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.KernelPath.Examples

open FloatLib.Floats FloatLib.Floats.ExecFloat

/-- The report's Binary8p4se. -/
abbrev B8P4 := ExecFloat.P3109 .binary8p4se

/-- `1.5 + 2.25 = 3.75`, `3 - 1.75 = 1.25`, `1.5 * 2.25 = 3.375`, `2.25 / 1.5 = 1.5` and
`1.5 * 2 + 0.25 = 3.25` in Binary8p4se, nearest-even with no saturation. -/
theorem arithmetic :
    ((1.5 : B8P4) + 2.25).toNatBits = (3.75 : B8P4).toNatBits ∧
      ((3 : B8P4) - 1.75).toNatBits = (1.25 : B8P4).toNatBits ∧
      ((1.5 : B8P4) * 2.25).toNatBits = (3.375 : B8P4).toNatBits ∧
      ((2.25 : B8P4) / 1.5).toNatBits = (1.5 : B8P4).toNatBits ∧
      ExecFloat.P3109.toNatBits (ExecFloat.fma (1.5 : B8P4) 2 0.25) =
        (3.25 : B8P4).toNatBits := by
  float_decide

/-- Operands of two formats and a destination of a third; rounding up; and the two saturation
modes at the largest finite value. -/
theorem mixed :
    (ExecFloat.P3109.Add (1.5 : B8P4) (2.5 : ExecFloat.P3109 .binary8p3se)
        (target := Format.unsigned 16 5 .finite)).toNatBits =
        (4 : ExecFloat.P3109 (Format.unsigned 16 5 .finite)).toNatBits ∧
      (ExecFloat.P3109.Add (2 : B8P4) (0.125 : B8P4) (mode := .up)).toNatBits =
        (2.25 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Multiply (ExecFloat.P3109.ofNatBits 126 : B8P4) (2 : B8P4)
        (saturation := .finite)).toNatBits = 126 ∧
      (ExecFloat.P3109.Divide (ExecFloat.P3109.ofNatBits 126 : B8P4) (0.5 : B8P4)).toNatBits =
        127 ∧
      (ExecFloat.P3109.Subtract (0 : B8P4) (1 : B8P4)
        (target := Format.unsigned 8 4 .extended) (saturation := .finite)).toNatBits = 0 := by
  float_decide

/-- Negation, the absolute value and the conversion to Binary8p3se of `1.5`. -/
theorem unary :
    (ExecFloat.P3109.Abs (ExecFloat.P3109.Negate (1.5 : B8P4))).toNatBits =
        (1.5 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Negate (ExecFloat.P3109.Negate (1.5 : B8P4))).toNatBits =
        (1.5 : B8P4).toNatBits ∧
      (ExecFloat.P3109.projectRat (format := .binary8p3se) (1.5 : B8P4).toClosedRat).toNatBits =
        (1.5 : ExecFloat.P3109 .binary8p3se).toNatBits ∧
      (ExecFloat.P3109.ofRat (1 / 3) : B8P4).toNatBits = 51 := by
  float_decide

/-- P3109 interim report v4.1, §4.11: the ten extrema of `1.5` and `2.25` in Binary8p4se. -/
theorem extrema :
    [(ExecFloat.P3109.Maximum (1.5 : B8P4) (2.25 : B8P4)).toNatBits,
      (ExecFloat.P3109.Minimum (1.5 : B8P4) (2.25 : B8P4)).toNatBits,
      (ExecFloat.P3109.MaximumNumber (1.5 : B8P4) (2.25 : B8P4)).toNatBits,
      (ExecFloat.P3109.MinimumNumber (1.5 : B8P4) (2.25 : B8P4)).toNatBits,
      (ExecFloat.P3109.MaximumMagnitude (1.5 : B8P4) (2.25 : B8P4)).toNatBits,
      (ExecFloat.P3109.MinimumMagnitude (1.5 : B8P4) (2.25 : B8P4)).toNatBits,
      (ExecFloat.P3109.MaximumMagnitudeNumber (1.5 : B8P4) (2.25 : B8P4)).toNatBits,
      (ExecFloat.P3109.MinimumMagnitudeNumber (1.5 : B8P4) (2.25 : B8P4)).toNatBits,
      (ExecFloat.P3109.MaximumFinite (1.5 : B8P4) (2.25 : B8P4)).toNatBits,
      (ExecFloat.P3109.MinimumFinite (1.5 : B8P4) (2.25 : B8P4)).toNatBits] =
      [73, 68, 73, 68, 73, 68, 73, 68, 73, 68] := by
  float_decide

/-- P3109 interim report v4.1, §4.11: `1.5` is neither equal to, greater than, nor at least
    `2.25`. -/
theorem comparison :
    [ExecFloat.P3109.CompareEqual (1.5 : B8P4) (2.25 : B8P4),
      ExecFloat.P3109.CompareGreater (1.5 : B8P4) (2.25 : B8P4),
      ExecFloat.P3109.CompareGreaterEqual (1.5 : B8P4) (2.25 : B8P4)] =
      [false, false, false] := by
  float_decide

/-- P3109 interim report v4.1, §4.8: the widths, the bias and the kind of Binary8p4se. -/
theorem queries :
    [Format.BitwidthOf .binary8p4se, Format.PrecisionOf .binary8p4se,
      Format.ExponentBitwidthOf .binary8p4se, Format.TrailingSignificandBitwidthOf .binary8p4se,
      Format.ExponentBiasOf .binary8p4se] = [8, 4, 4, 3, 8] ∧
      Format.SignednessOf .binary8p4se = .signed ∧ Format.DomainOf .binary8p4se = .extended := by
  decide +kernel

/-- P3109 interim report v4.1, §4.8: the encodings of the largest and the smallest finite value,
    the smallest
positive value and the smallest normal value of Binary8p4se. -/
theorem limits :
    [(Format.MaxFiniteOf .binary8p4se).toNatBits, (Format.MinFiniteOf .binary8p4se).toNatBits,
      (Format.MinPositiveOf .binary8p4se).toNatBits,
      (Format.MinNormalOf .binary8p4se).toNatBits] = [126, 254, 1, 8] := by
  float_decide

/-- P3109 interim report v4.1, §4.8 for an external IEEE 754 descriptor: the widths and the kind
    of binary32,
and the encodings of its largest and smallest finite values, its smallest positive value, its
largest subnormal and its smallest normal value. -/
theorem external_queries :
    [Arithmetic.External.BitwidthOf .binary32, Arithmetic.External.ExponentBitwidthOf .binary32,
      Arithmetic.External.TrailingSignificandBitwidthOf .binary32] = [32, 8, 23] ∧
      Arithmetic.External.SignednessOf .binary32 = .signed ∧
      Arithmetic.External.DomainOf .binary32 = .extended ∧
      [(Arithmetic.External.MaxFiniteOf .binary32).toNatBits,
        (Arithmetic.External.MinFiniteOf .binary32).toNatBits,
        (Arithmetic.External.MinPositiveOf .binary32).toNatBits,
        (Arithmetic.External.MaxSubnormalOf .binary32).toNatBits,
        (Arithmetic.External.MinNormalOf .binary32).toNatBits] =
        [0x7F7FFFFF, 0xFF7FFFFF, 1, 0x7FFFFF, 0x800000] := by
  decide +kernel

end FloatLib.Floats.Formats.P3109.KernelPath.Examples
