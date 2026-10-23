/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib

/-!
# P3109 carrier arithmetic

Checks for the `ExecFloat.P3109` surface: literals, `==` with NaN unequal to itself, the `mode`,
`saturation`, and `target` options of the arithmetic, `ofRat` with its default policy,
conversion with `(mode := ...)`, and `#eval` of a value. Closed cases use `binary8p4se`, whose
code `8e + t` has exponent field `e` and three trailing bits `t`.
-/

@[expose] public section

namespace FloatLibTests.Conformance.P3109.Arithmetic

open FloatLib.Floats
open FloatLib.Floats.Formats

/-- The descriptor used by the closed checks. -/
abbrev B8P4 := ExecFloat.P3109 .binary8p4se

-- Literals round once to nearest, ties to even, with no saturation request: 300 exceeds the
-- largest finite value 224 and becomes positive infinity, code 127.
example :
    ((1.5 : B8P4).toNatBits, (-1.5 : B8P4).toNatBits, (300 : B8P4).toNatBits,
      (0 : B8P4).toNatBits) = (68, 196, 127, 0) := by
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
    ((ExecFloat.P3109.add (1 : B8P4) 0.0625).toNatBits,
      (ExecFloat.P3109.add (1 : B8P4) 0.0625 (mode := .up)).toNatBits,
      (ExecFloat.P3109.add (1 : B8P4) 0.0625 (mode := .nearestAway)).toNatBits,
      (ExecFloat.P3109.add (1 : B8P4) 0.0625 (mode := .down)).toNatBits) =
      (64, 65, 65, 64) := by
  decide +kernel

-- `16 * 16` overflows: no saturation request gives infinity, finite saturation the largest
-- finite code 126.
example :
    ((ExecFloat.P3109.mul (16 : B8P4) 16).toNatBits,
      (ExecFloat.P3109.mul (16 : B8P4) 16 (saturation := .finite)).toNatBits) =
      (127, 126) := by
  decide +kernel

-- `target` projects into another descriptor: upward rounding of `1 + 1/16` in binary8p3se gives
-- 5/4, code `4e + t` with `e = 16` and `t = 1`.
example :
    (ExecFloat.P3109.add (1 : B8P4) 0.0625 (target := .binary8p3se) (mode := .up)).toNatBits =
      65 := by
  decide +kernel

-- Square root rounds the exact real root: `√2` lies between 11/8 and 3/2, nearer the first.
example :
    ((ExecFloat.P3109.sqrt (2 : B8P4)).toNatBits,
      (ExecFloat.P3109.sqrt (2 : B8P4) (mode := .up)).toNatBits) = (67, 68) := by
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
