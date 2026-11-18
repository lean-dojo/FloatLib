/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit
public import FloatLib.Tactic.FloatDecide

/-!
# Posit computations checked by Lean's kernel

Posit Standard (2022), §§5.3 to 5.5 and 5.11. Each theorem is one closed computation that
`float_decide` rewrites with the rules of `Posit.KernelPath.Model`, `Posit.KernelPath.QuireProof`
and `Posit.Configured.KernelPath` to the flat operations on natural-number encodings and that
Lean's kernel then evaluates: the arithmetic of a posit type, its literals, its comparisons and
unary operations, and the accumulation, conversion and rounding of its quire. They are the
regression checks of those rules inside the library; the statements for every width and every
operand are the theorems of `Posit.KernelPath.Standard` and `Posit.KernelPath.QuireProof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.KernelPath.Examples

open FloatLib.Floats FloatLib.Floats.ExecFloat

/-- `1.5 + 2.25 = 3.75`, `3.75 - 2.25 = 1.5`, `1.5 * 2.5 = 3.75` and `7.5 / 2 = 3.75` in
posit16. -/
theorem arithmetic :
    ExecFloat.Posit.toNatBits ((1.5 : Posit16) + 2.25) =
        ExecFloat.Posit.toNatBits (3.75 : Posit16) ∧
      ExecFloat.Posit.toNatBits ((3.75 : Posit16) - 2.25) =
        ExecFloat.Posit.toNatBits (1.5 : Posit16) ∧
      ExecFloat.Posit.toNatBits ((1.5 : Posit16) * 2.5) =
        ExecFloat.Posit.toNatBits (3.75 : Posit16) ∧
      ExecFloat.Posit.toNatBits ((7.5 : Posit16) / 2) =
        ExecFloat.Posit.toNatBits (3.75 : Posit16) := by
  float_decide

/-- `sqrt 6.25 = 2.5` and `1.5 * 2.5 + 0.25 = 4` with one rounding, in posit32. -/
theorem root_fma :
    ExecFloat.Posit.toNatBits (ExecFloat.sqrt (6.25 : Posit32)) =
        ExecFloat.Posit.toNatBits (2.5 : Posit32) ∧
      ExecFloat.Posit.toNatBits (ExecFloat.fma (1.5 : Posit32) 2.5 0.25) =
        ExecFloat.Posit.toNatBits (4 : Posit32) := by
  float_decide

/-- A decimal literal that is not a dyadic number, and a rational, are rounded once: `0.1` in
posit32 and `1 / 3` in posit8. -/
theorem literal :
    ExecFloat.Posit.toNatBits (0.1 : Posit32) = 617401549 ∧
      ExecFloat.Posit.toNatBits (ExecFloat.Posit.ofRat (1 / 3) : Posit8) = 51 := by
  float_decide

/-- The six comparisons of `1.5` with `2.25` in posit16. -/
theorem comparison :
    ExecFloat.Posit.compareLess (1.5 : Posit16) 2.25 = true ∧
      ExecFloat.Posit.compareLessEqual (1.5 : Posit16) 2.25 = true ∧
      ExecFloat.Posit.compareGreater (1.5 : Posit16) 2.25 = false ∧
      ExecFloat.Posit.compareGreaterEqual (1.5 : Posit16) 2.25 = false ∧
      ExecFloat.Posit.compareEqual (1.5 : Posit16) 2.25 = false ∧
      ExecFloat.Posit.compareNotEqual (1.5 : Posit16) 2.25 = true := by
  float_decide

/-- The absolute value undoes a negation, and the next encoding undoes the prior one, at `1.5`
in posit16. -/
theorem unary :
    ExecFloat.Posit.toNatBits (ExecFloat.Posit.abs (ExecFloat.Posit.negate (1.5 : Posit16))) =
        ExecFloat.Posit.toNatBits (1.5 : Posit16) ∧
      ExecFloat.Posit.toNatBits (ExecFloat.Posit.next (ExecFloat.Posit.prior (1.5 : Posit16))) =
        ExecFloat.Posit.toNatBits (1.5 : Posit16) := by
  float_decide

/-- Three in posit16. -/
abbrev three : Posit16 := 3

/-- Five in posit16. -/
abbrev five : Posit16 := 5

open ExecFloat.Posit.Quire in
/-- `3 + 3 * 5 = 18`, `(3 + 5) - 5 = 3`, `(3 + 3 * 5) - 3 * 5 = 3` and `|-3| = 3`, each
accumulated exactly in the quire of posit16 and rounded once. -/
theorem quire :
    ExecFloat.Posit.toNatBits (qToP (qMulAdd (pToQ three) three five) : Posit16) =
        ExecFloat.Posit.toNatBits (18 : Posit16) ∧
      ExecFloat.Posit.toNatBits (qToP (qSubP (qAddP (pToQ three) five) five) : Posit16) =
        ExecFloat.Posit.toNatBits three ∧
      ExecFloat.Posit.toNatBits
          (qToP (qMulSub (qMulAdd (pToQ three) three five) three five) : Posit16) =
        ExecFloat.Posit.toNatBits three ∧
      ExecFloat.Posit.toNatBits (qToP (qAbs (qNegate (pToQ three))) : Posit16) =
        ExecFloat.Posit.toNatBits three := by
  float_decide

open ExecFloat.Posit.Quire in
/-- The sum and the difference of two quires: `(3 + 5) + (3 - 5) = 6` and
`(3 + 5) - (3 - 5) = 10` in the quire of posit16. -/
theorem quire_sum :
    ExecFloat.Posit.toNatBits
          (qToP (qAddQ (qAddP (pToQ three) five) (qSubP (pToQ three) five)) : Posit16) =
        ExecFloat.Posit.toNatBits (6 : Posit16) ∧
      ExecFloat.Posit.toNatBits
          (qToP (qSubQ (qAddP (pToQ three) five) (qSubP (pToQ three) five)) : Posit16) =
        ExecFloat.Posit.toNatBits (10 : Posit16) := by
  float_decide

end FloatLib.Floats.Formats.Posit.KernelPath.Examples
