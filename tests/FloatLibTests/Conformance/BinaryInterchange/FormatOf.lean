/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.SquareRoot.Proof
public meta import FloatLib.Floats.Formats.BinaryInterchange

/-!
# The formatOf operations of IEEE 754-2019 §5.4.1

`cases` holds concrete results of `Model.formatOfAddition` and its siblings with operands in
binary64 and binary16 and the destination binary32: one rounding where a cast after the
operation rounds twice, the special cases, and the flags. `rootCases` compares the formatOf
square root in one format with `Model.sqrt`, value, flags and ternary value, on every encoding
of E5M2, E4M3, E4M3FNUZ and E2M1 in six rounding directions. Compiled evaluation checks both
when this module is elaborated. `tests/oracles/ieee2019.sh` compares the operations
exhaustively on small formats.

The second half applies the theorems to the interchange formats and to the eight-bit formats.
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

/-- `(1 + 2 ^ -24) ^ 2 + 2 ^ -52` in binary64: its root is just above a binary32 midpoint. -/
def aboveMidpointSquare : Model FloatFormat.binary64 := b64 0x3FF0000020000011

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
        (b64 0x7FF0000000000000) (b64 0x7FF8000000000000)) == (0x7FC00000, 1)),
    ("the root of a binary64 value just above the square of a binary32 midpoint rounds up",
      result (formatOfSquareRoot FloatFormat.binary32 aboveMidpointSquare) == (0x3F800001, 16)),
    ("a cast after the binary64 square root rounds twice and gives 1",
      (cast FloatFormat.binary64 FloatFormat.binary32 (sqrt aboveMidpointSquare)).toNatBits ==
        0x3F800000),
    ("the root of 4 in binary16 is 2 in binary32, exact",
      result (formatOfSquareRoot FloatFormat.binary32 (b16 0x4400)) == (0x40000000, 0)),
    ("the root of 2 toward zero", result (formatOfSquareRoot FloatFormat.binary32
        (b64 0x4000000000000000) .towardZero) == (0x3FB504F3, 16)),
    ("the root of 2 toward positive", result (formatOfSquareRoot FloatFormat.binary32
        (b64 0x4000000000000000) .up) == (0x3FB504F4, 16)),
    ("the root of -0 is -0", result (formatOfSquareRoot FloatFormat.binary32
        (b64 0x8000000000000000)) == (0x80000000, 0)),
    ("the root of a negative number is invalid", result (formatOfSquareRoot FloatFormat.binary32
        (b64 0xBFF0000000000000)) == (0x7FC00000, 1)),
    ("the root of +inf is +inf", result (formatOfSquareRoot FloatFormat.binary32
        (b64 0x7FF0000000000000)) == (0x7F800000, 0)),
    ("the root of -inf is invalid", result (formatOfSquareRoot FloatFormat.binary32
        (b64 0xFFF0000000000000)) == (0x7FC00000, 1)),
    ("the root of a signaling NaN of binary16 is that NaN quieted, with invalid",
      result (formatOfSquareRoot FloatFormat.binary32 (b16 0x7D00)) == (0x7FC00100, 1)) ]

/-- Whether two outcomes have the same value, the same flags and the same ternary value. -/
def same {fmt : FloatFormat} (left right : IEEEOutcome fmt) : Bool :=
  left.value.toNatBits == right.value.toNatBits && left.status.invalid == right.status.invalid &&
    left.status.divideByZero == right.status.divideByZero &&
    left.status.overflow == right.status.overflow &&
    left.status.underflow == right.status.underflow &&
    left.status.inexact == right.status.inexact && left.ternary == right.ternary

/--
In one format the formatOf square root is `Model.sqrt` with its flags and its ternary value: on
every encoding of E5M2 (an IEEE format), E4M3 (a NaN and no infinity), E4M3FNUZ (one zero) and
E2M1 (every encoding finite), in six rounding directions.
-/
def rootCases : List (String × Bool) :=
  let modes : List (String × IEEERoundingMode) :=
    [("nearest", .nearest), ("nearestAway", .nearestAway), ("towardZero", .towardZero),
      ("up", .up), ("down", .down), ("away", .away)]
  let formats : List (String × FloatFormat) :=
    [("E5M2", FloatFormat.e5m2), ("E4M3", FloatFormat.e4m3), ("E4M3FNUZ", FloatFormat.e4m3fnuz),
      ("E2M1", FloatFormat.e2m1)]
  formats.flatMap fun (name, fmt) =>
    (List.range (2 ^ fmt.bitWidth)).flatMap fun bits =>
      let x : Model fmt := Model.ofNatBits bits
      modes.map fun (direction, mode) =>
        (s!"{name} square root of the encoding {bits}, {direction}",
          same (formatOfSquareRoot fmt x mode) (sqrt x (mode := mode) (status := true)))

#eval show IO Unit from do
  let failures := (cases ++ rootCases).filter fun entry => !entry.2
  unless failures.isEmpty do
    throw <| IO.userError s!"formatOf cases that fail: {failures.map (·.1)}"
  IO.println <| s!"{cases.length} cases of the formatOf operations hold, and the square root " ++
    s!"agrees with Model.sqrt in {rootCases.length} cases"

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

/-- Across three formats and in every rounding direction, an exact result within the range of
the destination is rounded once. -/
example (mode : IEEERoundingMode) (hx : isFinite x = true) (hy : isFinite y = true)
    (hz : isFinite z = true)
    (hsum : |toReal x + toReal y| ≤ toReal (posMaxFinite FloatFormat.binary32))
    (hdifference : |toReal x - toReal y| ≤ toReal (posMaxFinite FloatFormat.binary32))
    (hproduct : |toReal x * toReal y| ≤ toReal (posMaxFinite FloatFormat.binary32))
    (hfused : |toReal x * toReal y + toReal z| ≤ toReal (posMaxFinite FloatFormat.binary32)) :
    toReal (formatOfAddition FloatFormat.binary32 x y mode).value =
        roundAt FloatFormat.binary32 (toReal x + toReal y) mode ∧
      toReal (formatOfSubtraction FloatFormat.binary32 x y mode).value =
        roundAt FloatFormat.binary32 (toReal x - toReal y) mode ∧
      toReal (formatOfMultiplication FloatFormat.binary32 x y mode).value =
        roundAt FloatFormat.binary32 (toReal x * toReal y) mode ∧
      toReal (formatOfFusedMultiplyAdd FloatFormat.binary32 x y z mode).value =
        roundAt FloatFormat.binary32 (toReal x * toReal y + toReal z) mode :=
  ⟨(formatOfAddition_finite_roundAt rfl mode x y hx hy hsum).2,
    (formatOfSubtraction_finite_roundAt rfl mode x y hx hy hdifference).2,
    (formatOfMultiplication_finite_roundAt rfl mode x y hx hy hproduct).2,
    (formatOfFusedMultiplyAdd_finite_roundAt rfl mode x y z hx hy hz hfused).2⟩

/--
In one format the formatOf operations are the operations of that format with their flags and
their ternary value, in every direction and for every operand: finite, infinite or NaN.
-/
example {u v w : Model FloatFormat.binary32} (mode : IEEERoundingMode) :
    formatOfAddition FloatFormat.binary32 u v mode = add u v (mode := mode) (status := true) ∧
      formatOfSubtraction FloatFormat.binary32 u v mode =
        sub u v (mode := mode) (status := true) ∧
      formatOfMultiplication FloatFormat.binary32 u v mode =
        mul u v (mode := mode) (status := true) ∧
      formatOfDivision FloatFormat.binary32 u v mode = div u v (mode := mode) (status := true) ∧
      formatOfFusedMultiplyAdd FloatFormat.binary32 u v w mode =
        fma u v w (mode := mode) (status := true) :=
  ⟨formatOfAddition_eq_add u v mode, formatOfSubtraction_eq_sub u v mode,
    formatOfMultiplication_eq_mul u v mode, formatOfDivision_eq_div u v mode,
    formatOfFusedMultiplyAdd_eq_fma u v w mode⟩

/-- The same on E4M3, which has a NaN and no infinity, and on E4M3FNUZ, which has one zero. -/
example {u v w : Model FloatFormat.e4m3} {r s : Model FloatFormat.e4m3fnuz}
    (mode : IEEERoundingMode) :
    formatOfFusedMultiplyAdd FloatFormat.e4m3 u v w mode =
        fma u v w (mode := mode) (status := true) ∧
      formatOfDivision FloatFormat.e4m3fnuz r s mode = div r s (mode := mode) (status := true) :=
  ⟨formatOfFusedMultiplyAdd_eq_fma u v w mode, formatOfDivision_eq_div r s mode⟩

/-- The delivered values, for every operand. -/
example {u v w : Model FloatFormat.binary32} (mode : IEEERoundingMode) :
    (formatOfAddition FloatFormat.binary32 u v mode).value = add u v (mode := mode) ∧
      (formatOfSubtraction FloatFormat.binary32 u v mode).value = sub u v (mode := mode) ∧
      (formatOfMultiplication FloatFormat.binary32 u v mode).value = mul u v (mode := mode) ∧
      (formatOfDivision FloatFormat.binary32 u v mode).value = div u v (mode := mode) ∧
      (formatOfFusedMultiplyAdd FloatFormat.binary32 u v w mode).value =
        fma u v w (mode := mode) :=
  ⟨formatOfAddition_value_eq_add u v mode, formatOfSubtraction_value_eq_sub u v mode,
    formatOfMultiplication_value_eq_mul u v mode, formatOfDivision_value_eq_div u v mode,
    formatOfFusedMultiplyAdd_value_eq_fma u v w mode⟩

/-- In one format the square root of a NaN, of an infinity and of a negative number is the
outcome of `Model.sqrt`, in every direction. -/
example {u : Model FloatFormat.binary32} (mode : IEEERoundingMode)
    (hu : isFinite u = false ∨ isZero u = true ∨ signBit u = true) :
    formatOfSquareRoot FloatFormat.binary32 u mode = sqrt u (mode := mode) (status := true) :=
  formatOfSquareRoot_eq_sqrt mode hu

/-- The formatOf square root is correctly rounded in every direction, into every destination
and from every operand format. -/
example (mode : IEEERoundingMode) {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q) :
    RoundsTo FloatFormat.binary32 mode (Real.sqrt q) false
      (formatOfSquareRoot FloatFormat.binary32 x mode).value :=
  formatOfSquareRoot_roundsTo hq hpos

example {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q)
    (hfinite : isFinite (formatOfSquareRoot FloatFormat.binary32 x).value = true) :
    toReal (formatOfSquareRoot FloatFormat.binary32 x).value =
      roundAt FloatFormat.binary32 (Real.sqrt q) :=
  toReal_formatOfSquareRoot rfl hq hpos hfinite

example (mode : IEEERoundingMode) {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q)
    (hfinite : isFinite (formatOfSquareRoot FloatFormat.binary16 x mode).value = true) :
    (formatOfSquareRoot FloatFormat.binary16 x mode).status.inexact = true ↔
      toReal (formatOfSquareRoot FloatFormat.binary16 x mode).value ≠ Real.sqrt q :=
  formatOfSquareRoot_inexact_iff hq hpos mode hfinite

/-- In one format the value to nearest-even is `Model.sqrt`. -/
example {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q) :
    (formatOfSquareRoot FloatFormat.binary64 x).value = sqrt x :=
  formatOfSquareRoot_value_eq_sqrt rfl hq hpos

example (mode : IEEERoundingMode) (hzero : isZero x = true) :
    formatOfSquareRoot FloatFormat.binary32 x mode =
      { value := zero FloatFormat.binary32 (signBit x), status := .clear, ternary := .eq } :=
  formatOfSquareRoot_of_isZero hzero mode

end Contracts

end FloatLibTests.Conformance.BinaryInterchange.FormatOf
