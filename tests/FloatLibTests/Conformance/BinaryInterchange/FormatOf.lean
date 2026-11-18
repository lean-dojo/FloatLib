/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange
public meta import FloatLib.Floats.Formats.BinaryInterchange

/-!
# The formatOf operations of IEEE 754-2019 §5.4.1

`cases` holds concrete results of `Model.formatOfAddition` and its siblings with operands in
binary64 and binary16 and the destination binary32: one rounding where a cast after the
operation rounds twice, the special cases, and the flags. Compiled evaluation checks them when
this module is elaborated. `tests/oracles/ieee2019.sh` compares the operations exhaustively on
small formats.

The second half applies the theorems to the interchange formats.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.FormatOf

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model

/-- The binary64 value with the encoding `bits`. -/
def b64 (bits : Nat) : Model FloatFormat.binary64 := Model.ofNatBits bits

/-- The binary16 value with the encoding `bits`. -/
def b16 (bits : Nat) : Model FloatFormat.binary16 := Model.ofNatBits bits

/--
The encoding of a binary32 result and its flags as the sum of invalid 1, divideByZero 2,
overflow 4, underflow 8 and inexact 16.
-/
def result (outcome : IEEEOutcome FloatFormat.binary32) : Nat × Nat :=
  (outcome.value.toNatBits,
    (if outcome.status.invalid then 1 else 0) + (if outcome.status.divideByZero then 2 else 0) +
      (if outcome.status.overflow then 4 else 0) + (if outcome.status.underflow then 8 else 0) +
      (if outcome.status.inexact then 16 else 0))

/-- `1 + 2 ^ -24` in binary64, the midpoint of two binary32 values. -/
def midpoint : Model FloatFormat.binary64 := b64 0x3FF0000010000000

/-- `2 ^ -54` in binary64, a quarter of a unit in the last place of `midpoint`. -/
def quarterUlp : Model FloatFormat.binary64 := b64 0x3C90000000000000

/--
The cases: a name and whether the case holds. In binary64 `0x3FF0000000000000` is one and
`0x7FF0000000000000` infinity; in binary16 `0x3C00` is one and `0x7D00` a signaling NaN; in
binary32 `0x3F800000` is one, `0x7FC00000` the quiet NaN and `0x7F800000` infinity.
-/
def cases : List (String × Bool) :=
  [ ("the exact sum is rounded once: 1 + 2^-24 + 2^-54 rounds up",
      result (formatOfAddition FloatFormat.binary32 midpoint quarterUlp) == (0x3F800001, 16)),
    ("a cast after the binary64 sum rounds twice and gives 1",
      (cast FloatFormat.binary64 FloatFormat.binary32 (add midpoint quarterUlp)).toNatBits ==
        0x3F800000),
    ("operands of two formats: 1 (binary64) + 1 (binary16) is 2",
      result (formatOfAddition FloatFormat.binary32 (b64 0x3FF0000000000000) (b16 0x3C00)) ==
        (0x40000000, 0)),
    ("1 - 1 is +0", result (formatOfSubtraction FloatFormat.binary32 (b64 0x3FF0000000000000)
        (b16 0x3C00)) == (0x00000000, 0)),
    ("1 - 1 toward negative is -0",
      result (formatOfSubtraction FloatFormat.binary32 (b64 0x3FF0000000000000) (b16 0x3C00) .down)
        == (0x80000000, 0)),
    ("the binary64 maximum times 2 overflows binary32",
      result (formatOfMultiplication FloatFormat.binary32 (b64 0x7FEFFFFFFFFFFFFF) (b16 0x4000))
        == (0x7F800000, 20)),
    ("the same toward zero gives the binary32 maximum",
      result (formatOfMultiplication FloatFormat.binary32 (b64 0x7FEFFFFFFFFFFFFF) (b16 0x4000)
        .towardZero) == (0x7F7FFFFF, 20)),
    ("infinity times zero is invalid",
      result (formatOfMultiplication FloatFormat.binary32 (b64 0x7FF0000000000000) (b16 0x0000))
        == (0x7FC00000, 1)),
    ("1 / 3 is rounded once", result (formatOfDivision FloatFormat.binary32
        (b64 0x3FF0000000000000) (b16 0x4200)) == (0x3EAAAAAB, 16)),
    ("1 / 0 is infinity with divideByZero", result (formatOfDivision FloatFormat.binary32
        (b64 0x3FF0000000000000) (b16 0x0000)) == (0x7F800000, 2)),
    ("0 / 0 is invalid", result (formatOfDivision FloatFormat.binary32
        (b64 0x0000000000000000) (b16 0x8000)) == (0x7FC00000, 1)),
    ("a signaling NaN operand of binary16 is quieted and keeps its payload 0x100, with invalid",
      result (formatOfAddition FloatFormat.binary32 (b64 0x3FF0000000000000) (b16 0x7D00)) ==
        (0x7FC00100, 1)),
    ("the fused operation rounds 1 * (1 + 2^-24) + 2^-54 once",
      result (formatOfFusedMultiplyAdd FloatFormat.binary32 (b16 0x3C00) midpoint quarterUlp) ==
        (0x3F800001, 16)),
    ("zero times infinity plus a quiet NaN is the NaN, with invalid",
      result (formatOfFusedMultiplyAdd FloatFormat.binary32 (b16 0x0000)
        (b64 0x7FF0000000000000) (b64 0x7FF8000000000000)) == (0x7FC00000, 1)) ]

#eval show IO Unit from do
  let failures := cases.filter fun entry => !entry.2
  unless failures.isEmpty do
    throw <| IO.userError s!"formatOf cases that fail: {failures.map (·.1)}"
  IO.println s!"{cases.length} cases of the formatOf operations hold"

/-! ## The theorems on the interchange formats -/

section Contracts

variable {x : Model FloatFormat.binary64} {y : Model FloatFormat.binary16}
  {z : Model FloatFormat.binary128}

example (hx : isFinite x = true) (hy : isFinite y = true)
    (hfinite : isFinite (formatOfAddition FloatFormat.binary32 x y).value = true) :
    toReal (formatOfAddition FloatFormat.binary32 x y).value =
      roundAt FloatFormat.binary32 (toReal x + toReal y) :=
  toReal_formatOfAddition rfl x y hx hy hfinite

example (hx : isFinite x = true) (hy : isFinite y = true)
    (hfinite : isFinite (formatOfSubtraction FloatFormat.binary32 x y).value = true) :
    toReal (formatOfSubtraction FloatFormat.binary32 x y).value =
      roundAt FloatFormat.binary32 (toReal x - toReal y) :=
  toReal_formatOfSubtraction rfl x y hx hy hfinite

example (hx : isFinite x = true) (hy : isFinite y = true)
    (hfinite : isFinite (formatOfMultiplication FloatFormat.binary32 x y).value = true) :
    toReal (formatOfMultiplication FloatFormat.binary32 x y).value =
      roundAt FloatFormat.binary32 (toReal x * toReal y) :=
  toReal_formatOfMultiplication rfl x y hx hy hfinite

example (hx : isFinite x = true) (hy : isFinite y = true) (hy0 : isZero y = false)
    (hfinite : isFinite (formatOfDivision FloatFormat.binary32 x y).value = true) :
    toReal (formatOfDivision FloatFormat.binary32 x y).value =
      roundAt FloatFormat.binary32 (toReal x / toReal y) :=
  toReal_formatOfDivision rfl x y hx hy hy0 hfinite

example (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (hfinite : isFinite (formatOfFusedMultiplyAdd FloatFormat.binary32 x y z).value = true) :
    toReal (formatOfFusedMultiplyAdd FloatFormat.binary32 x y z).value =
      roundAt FloatFormat.binary32 (toReal x * toReal y + toReal z) :=
  toReal_formatOfFusedMultiplyAdd rfl x y z hx hy hz hfinite

/-- In one format the formatOf operations are the operations of that format, in every direction. -/
example {u v w : Model FloatFormat.binary32} (mode : IEEERoundingMode)
    (hu : isFinite u = true) (hv : isFinite v = true) (hw : isFinite w = true) :
    (formatOfAddition FloatFormat.binary32 u v mode).value = add u v (mode := mode) ∧
      (formatOfSubtraction FloatFormat.binary32 u v mode).value = sub u v (mode := mode) ∧
      (formatOfMultiplication FloatFormat.binary32 u v mode).value = mul u v (mode := mode) ∧
      (formatOfDivision FloatFormat.binary32 u v mode).value = div u v (mode := mode) ∧
      (formatOfFusedMultiplyAdd FloatFormat.binary32 u v w mode).value =
        fma u v w (mode := mode) :=
  ⟨formatOfAddition_value_eq_add u v mode hu hv, formatOfSubtraction_value_eq_sub u v mode hu hv,
    formatOfMultiplication_value_eq_mul u v mode hu hv,
        formatOfDivision_value_eq_div u v mode hu hv,
    formatOfFusedMultiplyAdd_value_eq_fma u v w mode hu hv hw⟩

end Contracts

end FloatLibTests.Conformance.BinaryInterchange.FormatOf
