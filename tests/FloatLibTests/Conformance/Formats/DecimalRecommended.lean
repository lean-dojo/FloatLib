/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange
public meta import FloatLib.Floats.Formats.DecimalInterchange
public import FloatLib.Tactic.FloatDecide

/-!
# Decimal quantum, minimum and maximum, payloads, encodings, reductions and the kernel path

Special cases of the decimal operations of IEEE 754-2019 §5.3.2, §5.5.2, §9.4, §9.6 and §9.7 on
decimal64, with the examples of Cowlishaw's General Decimal Arithmetic Specification 1.70 for
`max` and `min` (pages 31 and 32) and the special cases of ISO/IEC TS 18661-4 (N1797) F.10.10a
for the reductions. `cases` holds every case once, checked by compiled evaluation
when this module is elaborated.

The kernel path is checked by `float_decide`, which rewrites a decimal sum, difference or
product with `KernelPath.add_eq`, `sub_eq` and `mul_eq`, a comparison or a minimum or maximum
with `KernelPath.compareQuiet_eq`, `compareSignaling_eq` and `extremum_eq`, the total order
with `KernelPath.totalOrder_eq`, and `quantize`, the integral roundings, the conversions to an
integer, `logB`, `nextUp`, `div`, `sqrt`, `rSqrt`, `hypot`, `pown` and the four reductions with
`KernelPath.quantize_eq`, `roundToIntegral_eq`, `roundToIntegralExact_eq`,
`convertToInteger_eq`, `logB_eq`, `nextUp_eq`, `div_eq`, `sqrt_eq`, `rSqrt_eq`, `hypot_eq`,
`pown_eq`, `sum_eq`, `sumAbs_eq`, `sumSquare_eq` and `dot_eq`, before Lean's kernel decides it.
The statements over `oneDigit` run through every finite datum of a format with one digit. The
last part applies the theorems of the operations to decimal64 data.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.DecimalRecommended

open FloatLib.Floats.Formats.DecimalInterchange
open FloatLib.Floats.Formats.DecimalInterchange.Arithmetic

/-- The positive datum `coefficient × 10 ^ exponent`. -/
def pos (coefficient : Nat) (exponent : Int) : Datum := .finite false coefficient exponent

/-- The negative datum `-coefficient × 10 ^ exponent`. -/
def neg (coefficient : Nat) (exponent : Int) : Datum := .finite true coefficient exponent

/-- A quiet NaN with payload zero. -/
def quietNaN : Datum := .nan false false 0

/-- A signaling NaN with payload zero. -/
def signalingNaN : Datum := .nan false true 0

/-- The special cases: a name and whether the case holds, on decimal64. -/
def cases : List (String × Bool) :=
  let f := Format.decimal64
  [ ("quantum 1.23 is 0.01", (quantum f (pos 123 (-2))).value == pos 1 (-2)),
    ("quantum -5E+3 is 1E+3", (quantum f (neg 5 3)).value == pos 1 3),
    ("quantum of an infinity is +inf", (quantum f (.infinity true)).value == .infinity false),
    ("quantum of a NaN is a NaN", (quantum f quietNaN).value == quietNaN),
    ("quantum of a signaling NaN raises invalid",
      (quantum f signalingNaN).status == { invalid := true }),
    ("max 3 2", (maximum f (pos 3 0) (pos 2 0)).value == pos 3 0),
    ("max -10 3", (maximum f (neg 10 0) (pos 3 0)).value == pos 3 0),
    ("max 1.0 1 is 1", (maximum f (pos 10 (-1)) (pos 1 0)).value == pos 1 0),
    ("min 1.0 1 is 1.0", (minimum f (pos 10 (-1)) (pos 1 0)).value == pos 10 (-1)),
    ("min -1.0 -1 is -1", (minimum f (neg 10 (-1)) (neg 1 0)).value == neg 1 0),
    ("maximumNumber 7 NaN is 7", (maximumNumber f (pos 7 0) quietNaN).value == pos 7 0),
    ("maximum 7 NaN is the NaN", (maximum f (pos 7 0) quietNaN).value == quietNaN),
    ("minimum +0 -0 is -0", (minimum f (pos 0 0) (neg 0 0)).value == neg 0 0),
    ("maximum -0 +0 is +0", (maximum f (neg 0 0) (pos 0 0)).value == pos 0 0),
    ("minimumMagnitude -1 1 is -1", (minimumMagnitude f (neg 1 0) (pos 1 0)).value == neg 1 0),
    ("maximumMagnitude -2 1 is -2", (maximumMagnitude f (neg 2 0) (pos 1 0)).value == neg 2 0),
    ("minimumMagnitudeNumber NaN -3 is -3",
      (minimumMagnitudeNumber f quietNaN (neg 3 0)).value == neg 3 0),
    ("maximumMagnitudeNumber sNaN 1 is 1 with invalid",
      maximumMagnitudeNumber f signalingNaN (pos 1 0) ==
        { value := pos 1 0, status := { invalid := true } }),
    ("maximum inf 1", (maximum f (.infinity false) (pos 1 0)).value == .infinity false),
    ("minimum -inf 5", (minimum f (.infinity true) (pos 5 0)).value == .infinity true),
    ("two NaNs give the first, quiet",
      (minimumNumber f (.nan true true 7) (.nan false false 9)) ==
        { value := .nan true false 7, status := { invalid := true } }),
    ("getPayload of a NaN", (Datum.nan true false 123).getPayload == pos 123 0),
    ("getPayload of a number is -1", (pos 5 0).getPayload == neg 1 0),
    ("setPayload 5", Datum.setPayload f (pos 5 0) == .nan false false 5),
    ("setPayload 5.0", Datum.setPayload f (pos 50 (-1)) == .nan false false 5),
    ("setPayload 5E+2", Datum.setPayload f (pos 5 2) == .nan false false 500),
    ("setPayload 0.5 is +0", Datum.setPayload f (pos 5 (-1)) == pos 0 0),
    ("setPayload -5 is +0", Datum.setPayload f (neg 5 0) == pos 0 0),
    ("setPayload 1E+15 is +0", Datum.setPayload f (pos 1 15) == pos 0 0),
    ("setPayload 999999999999999",
      Datum.setPayload f (pos 999999999999999 0) == .nan false false 999999999999999),
    ("setPayloadSignaling 0", Datum.setPayloadSignaling f (pos 0 0) == .nan false true 0),
    ("decodeDecimal after encodeDecimal",
      (encodeDecimal f (neg 1234567890123456 (-20))).map (decodeDecimal f) ==
        some (neg 1234567890123456 (-20))),
    ("decodeBinary after encodeBinary",
      (encodeBinary f (.nan true true 42)).map (decodeBinary f) == some (.nan true true 42)),
    ("the two encodings differ",
      encodeBinary f (pos 1234567890123456 0) != encodeDecimal f (pos 1234567890123456 0)),
    ("compareQuietLess 1 2", (Datum.compareQuietLess (pos 1 0) (pos 2 0)).value),
    ("compareSignalingGreaterEqual 1.0 1",
      (Datum.compareSignalingGreaterEqual (pos 10 (-1)) (pos 1 0)).value),
    ("compareQuietUnordered NaN 1", (Datum.compareQuietUnordered quietNaN (pos 1 0)).value),
    ("compareSignalingLess NaN 1 raises invalid",
      (Datum.compareSignalingLess quietNaN (pos 1 0)).status == { invalid := true }),
    ("kernel add", KernelPath.add f .nearest (pos 12345 (-2)) (pos 67 0) ==
      Arithmetic.add f .nearest (pos 12345 (-2)) (pos 67 0)),
    ("kernel sub rounds", KernelPath.sub f .down (pos 1234567890123456 (-2)) (pos 7 (-20)) ==
      Arithmetic.sub f .down (pos 1234567890123456 (-2)) (pos 7 (-20))),
    ("kernel mul overflows", KernelPath.mul f .up (pos 9999999999999999 369) (pos 9 300) ==
      Arithmetic.mul f .up (pos 9999999999999999 369) (pos 9 300)),
    ("sum 1 2 3 is 6", (sum f .nearest #[pos 1 0, pos 2 0, pos 3 0]).value == pos 6 0),
    ("sum 1.0 2.00 is 3.00, the least quantum",
      (sum f .nearest #[pos 10 (-1), pos 200 (-2)]).value == pos 300 (-2)),
    ("the empty sum is +0", (sum f .nearest #[]).value == pos 0 0),
    ("sum 1 -1 is +0", (sum f .nearest #[pos 1 0, neg 1 0]).value == pos 0 0),
    ("sum 1 -1 toward negative is -0", (sum f .down #[pos 1 0, neg 1 0]).value == neg 0 0),
    ("sum -0 -0 is -0", (sum f .nearest #[neg 0 0, neg 0 0]).value == neg 0 0),
    ("sum 1E+384 1E+384 -1E+384 does not overflow in between",
      sum f .nearest #[pos 1000000000000000 369, pos 1000000000000000 369,
        neg 1000000000000000 369] == { value := pos 1000000000000000 369 }),
    ("sum with a NaN is the NaN", (sum f .nearest #[pos 1 0, quietNaN, .infinity false]).value ==
      quietNaN),
    ("sum with a signaling NaN raises invalid",
      sum f .nearest #[pos 1 0, signalingNaN] ==
        { value := quietNaN, status := { invalid := true } }),
    ("sum +inf 1 is +inf", sum f .nearest #[.infinity false, pos 1 0] ==
      { value := .infinity false }),
    ("sum +inf -inf is invalid", sum f .nearest #[.infinity false, .infinity true] ==
      { value := quietNaN, status := { invalid := true } }),
    ("sumAbs -3 4 is 7", (sumAbs f .nearest #[neg 3 0, pos 4 0]).value == pos 7 0),
    ("sumAbs -inf NaN is +inf", sumAbs f .nearest #[.infinity true, quietNaN] ==
      { value := .infinity false }),
    ("sumAbs sNaN inf is a NaN with invalid", sumAbs f .nearest #[signalingNaN, .infinity false] ==
      { value := quietNaN, status := { invalid := true } }),
    ("sumSquare 3 4 is 25", (sumSquare f .nearest #[pos 3 0, neg 4 0]).value == pos 25 0),
    ("sumSquare 0.5 has quantum 0.01", (sumSquare f .nearest #[pos 5 (-1)]).value == pos 25 (-2)),
    ("sumSquare -inf is +inf", sumSquare f .nearest #[.infinity true] ==
      { value := .infinity false }),
    ("dot (1, 2) (3, 4) is 11",
      (dot f .nearest #[pos 1 0, pos 2 0] #[pos 3 0, pos 4 0]).toOption.map (·.value) ==
        some (pos 11 0)),
    ("dot 0 inf is invalid", (dot f .nearest #[pos 0 0] #[.infinity false]).toOption ==
      some { value := quietNaN, status := { invalid := true } }),
    ("dot inf 1 and -inf 1 is invalid",
      (dot f .nearest #[.infinity false, .infinity true] #[pos 1 0, pos 1 0]).toOption ==
        some { value := quietNaN, status := { invalid := true } }),
    ("dot of arrays of different lengths is rejected",
      (dot f .nearest #[pos 1 0] #[]).toOption.isNone) ]

/-- The names of the cases that fail. -/
def failing : List String :=
  cases.filterMap fun (name, holds) => if holds then none else some name

#eval show IO Unit from do
  unless failing.isEmpty do
    throw (IO.userError s!"decimal special cases that fail: {failing}")

/-! ## The kernel path under `float_decide` -/

example : (Arithmetic.add .decimal64 .nearest (.finite false 12345 (-2)) (.finite false 67 0)).1 =
    .finite false 19045 (-2) := by
  float_decide

example : (Arithmetic.sub .decimal64 .nearest (.finite false 12345 (-2)) (.finite false 67 0)).1 =
    .finite false 5645 (-2) := by
  float_decide

example : (Arithmetic.mul .decimal64 .nearest (.finite false 12345 (-2)) (.finite false 67 0)).1 =
    .finite false 827115 (-2) := by
  float_decide

/-- A fused multiply-add: `123.45 × 67 + 0.005` is exact, and the product alone would be too. -/
example : (Arithmetic.fma .decimal64 .nearest (.finite false 12345 (-2)) (.finite false 67 0)
      (.finite false 5 (-3))).1 = .finite false 8271155 (-3) := by
  float_decide

/--
A fused multiply-add rounds once: the 32-digit product of two 16-digit coefficients minus
its leading part leaves the low digits, which a rounded product would have lost.
-/
example : Arithmetic.fma .decimal64 .nearest (.finite false 9999999999999999 0)
      (.finite false 9999999999999999 0) (.finite true 9999999999999998 16) =
    { value := .finite false 1 0 } := by
  float_decide

/-- A sum that drops seven digits and raises `inexact`. -/
example : Arithmetic.add .decimal64 .nearest (.finite false 1234567890123456 (-2))
      (.finite false 6700000000000007 5) =
    { value := .finite false 6700000123456796 5, status := { inexact := true } } := by
  rw [KernelPath.add_eq]
  decide +kernel

/-- A product in decimal128 that overflows when rounding upward. -/
example : (Arithmetic.mul .decimal128 .up (.finite false 9 6111) (.finite false 2 40)).status =
    { overflow := true, inexact := true } := by
  rw [KernelPath.mul_eq]
  decide +kernel

/-- A comparison under its name is its predicate at the kernel comparison of the data. -/
example (x y : Datum) : Datum.compareQuietLess x y =
    { value := FloatLib.Numerics.IEEEComparison.Predicate.less.accepts (KernelPath.compare x y)
      status := { invalid := x.isSignaling || y.isSignaling } } := by
  simp only [kernel_optimize]

/-- A minimum or maximum under its name is the kernel selection, in every format. -/
example (f : Format) (x y : Datum) :
    minimumMagnitude f x y = KernelPath.extremum f false true false x y ∧
      maximumNumber f x y = KernelPath.extremum f true false true x y := by
  simp only [kernel_optimize, and_self]

/--
Comparisons on the fields of the data: members of one cohort and the two zeros are equal, an
infinity lies beyond every finite datum, and a NaN is unordered, with `invalid` for a signaling
NaN in a quiet comparison and for any NaN in a signaling one.
-/
theorem decimal_comparisons :
    (Datum.compareQuietLess (.finite false 12345 (-2)) (.finite false 67 1)).value = true ∧
      (Datum.compareQuietEqual (.finite false 10 (-1)) (.finite false 1 0)).value = true ∧
      (Datum.compareQuietEqual (.finite true 0 5) (.finite false 0 (-3))).value = true ∧
      (Datum.compareQuietGreater (.finite true 1 (-400)) (.infinity true)).value = true ∧
      (Datum.compareQuietLessEqual (.finite true 5 0) (.finite false 1 (-398))).value = true ∧
      (Datum.compareQuietGreaterEqual (.finite true 5 0) (.finite true 49 (-1))).value = false ∧
      (Datum.compareQuietUnordered (.nan false false 7) (.finite false 1 0)).value = true ∧
      (Datum.compareQuietLess (.nan false true 0) (.finite false 1 0)).status.invalid = true ∧
      (Datum.compareSignalingNotGreater (.nan false false 0) (.finite false 1 0)).value = true ∧
      (Datum.compareSignalingLess (.finite false 1 0) (.nan true false 0)).status.invalid =
        true := by
  float_decide

/-- info: 'FloatLibTests.Conformance.Formats.DecimalRecommended.decimal_comparisons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decimal_comparisons

/--
Minimum and maximum through the kernel comparison: by value, by magnitude, with a number
preferred to a signaling NaN, and between `1.0` and `1` by the total order.
-/
theorem decimal_extrema :
    (minimum .decimal64 (.finite false 12345 (-2)) (.finite false 67 1)).value =
        .finite false 12345 (-2) ∧
      (maximum .decimal64 (.finite false 12345 (-2)) (.finite false 67 1)).value =
        .finite false 67 1 ∧
      (maximumMagnitude .decimal64 (.finite true 9 0) (.finite false 5 0)).value =
        .finite true 9 0 ∧
      (minimumMagnitude .decimal64 (.finite true 9 0) (.infinity false)).value =
        .finite true 9 0 ∧
      maximumNumber .decimal64 (.nan false true 3) (.finite false 5 0) =
        { value := .finite false 5 0, status := { invalid := true } } ∧
      (minimum .decimal64 (.nan true false 3) (.finite false 5 0)).value.isNaN = true ∧
      (maximum .decimal64 (.finite false 10 (-1)) (.finite false 1 0)).value =
        .finite false 1 0 := by
  float_decide

/--
The total order of §5.10 through its kernel form: `-0` before `+0`, members of one cohort by
their exponents (reversed for negative data), NaNs at the two ends by their signs, a positive
signaling NaN before a positive quiet one, and payloads in order (reversed for negative NaNs).
-/
theorem decimal_totalOrder :
    Datum.totalOrder (.finite true 0 0) (.finite false 0 0) = true ∧
      Datum.totalOrder (.finite false 0 0) (.finite true 0 0) = false ∧
      Datum.totalOrder (.finite false 10 (-1)) (.finite false 1 0) = true ∧
      Datum.totalOrder (.finite false 1 0) (.finite false 10 (-1)) = false ∧
      Datum.totalOrder (.finite true 1 0) (.finite true 10 (-1)) = true ∧
      Datum.totalOrder (.finite false 12345 (-2)) (.finite false 67 1) = true ∧
      Datum.totalOrder (.nan true false 0) (.infinity true) = true ∧
      Datum.totalOrder (.infinity false) (.nan false true 1) = true ∧
      Datum.totalOrder (.nan false true 5) (.nan false false 1) = true ∧
      Datum.totalOrder (.nan false false 1) (.nan false false 2) = true ∧
      Datum.totalOrder (.nan true false 1) (.nan true false 2) = false ∧
      Datum.totalOrderMag (.finite true 5 0) (.finite false 7 0) = true ∧
      Datum.totalOrderMag (.nan true false 3) (.finite false 7 0) = false := by
  float_decide

/--
The classification of §5.7.2 through its kernel form, at the boundary of the normal range of
decimal64 (`1 × 10^-383`): sixteen digits at the least quantum are normal, fifteen are
subnormal, and a zero is neither.
-/
theorem decimal_classification :
    Datum.classify .decimal64 (.finite false 1000000000000000 (-398)) = .positiveNormal ∧
      Datum.classify .decimal64 (.finite true 999999999999999 (-398)) = .negativeSubnormal ∧
      Datum.classify .decimal64 (.finite false 1 (-383)) = .positiveNormal ∧
      Datum.classify .decimal64 (.finite false 1 (-384)) = .positiveSubnormal ∧
      Datum.classify .decimal64 (.finite true 0 3) = .negativeZero ∧
      Datum.classify .decimal64 (.infinity true) = .negativeInfinity ∧
      Datum.classify .decimal64 (.nan false true 5) = .signalingNaN ∧
      Datum.isNormal .decimal64 (.finite false 1 (-383)) = true ∧
      Datum.isNormal .decimal64 (.finite false 0 0) = false ∧
      Datum.isSubnormal .decimal64 (.finite false 1 (-384)) = true ∧
      Datum.isSubnormal .decimal64 (.finite false 0 (-398)) = false ∧
      Datum.isSubnormal .decimal32 (.finite false 999999 (-101)) = true ∧
      Datum.isNormal .decimal32 (.finite false 1000000 (-101)) = true := by
  float_decide

/--
`scaleB`, the conversion between formats and the conversion from an integer through their
kernel forms: an exact scaling keeps its coefficient, a scaling beyond the range overflows or
underflows, a narrower format rounds the coefficient once, and an integer of eight digits is
rounded into seven.
-/
theorem decimal_conversions :
    (Arithmetic.scale .decimal64 .nearest (.finite false 12345 (-2)) 3).value =
        .finite false 12345 1 ∧
      (Arithmetic.scale .decimal64 .nearest (.finite true 1 0) 400).status.overflow = true ∧
      (Arithmetic.scale .decimal64 .nearest (.finite false 7 0) (-500)).status.underflow = true ∧
      (Conversion.convertFormat .decimal32 .nearest (.finite false 1234567890123456 (-10))).value =
        .finite false 1234568 (-1) ∧
      (Conversion.convertFormat .decimal32 .nearest
        (.finite false 1234567890123456 (-10))).status.inexact = true ∧
      (Conversion.convertFormat .decimal128 .nearest (.finite true 12345 (-2))).value =
        .finite true 12345 (-2) ∧
      (Conversion.Integer.convertFromInt .decimal32 .nearest (-12345678)).value =
        .finite true 1234568 1 ∧
      (Conversion.Integer.convertFromInt .decimal64 .nearest 0).value = .finite false 0 0 := by
  float_decide

/--
`quantize` and the conversions to an integer through their kernel forms: ties in the two
nearest directions, the directed directions on both signs, a coefficient that no longer fits
the precision, a sign kept on a zero result, the `inexact` signal of the exact conversions
only, and results outside the range of the integer format.
-/
theorem decimal_quantum :
    Arithmetic.quantize .decimal64 .nearest (.finite false 12345 (-2)) (.finite false 1 0) =
        { value := .finite false 123 0, status := { inexact := true } } ∧
      (Arithmetic.quantize .decimal64 .nearest (.finite false 12350 (-2))
        (.finite true 7 (-1))).value = .finite false 1235 (-1) ∧
      (Arithmetic.quantize .decimal64 .nearest (.finite false 125 (-1)) (.finite false 1 0)).value =
        .finite false 12 0 ∧
      (Arithmetic.quantize .decimal64 .up (.finite false 121 (-1)) (.finite false 1 0)).value =
        .finite false 13 0 ∧
      (Arithmetic.quantize .decimal64 .nearest (.finite false 1 0)
        (.finite false 1 (-20))).status.invalid = true ∧
      (Arithmetic.quantize .decimal64 .nearest (.finite true 5 0) (.finite false 1 3)).value =
        .finite true 0 3 ∧
      (Conversion.Integer.convertToIntegerTiesToEven (.signed 64) (.finite false 25 (-1))).value =
        2 ∧
      (Conversion.Integer.convertToIntegerTiesToAway (.signed 64) (.finite false 25 (-1))).value =
        3 ∧
      (Conversion.Integer.convertToIntegerTowardZero (.signed 64) (.finite true 29 (-1))).value =
        -2 ∧
      (Conversion.Integer.convertToIntegerTowardNegative (.signed 64)
        (.finite true 21 (-1))).value = -3 ∧
      (Conversion.Integer.convertToIntegerExactTowardPositive (.signed 64)
        (.finite false 21 (-1))).status.inexact = true ∧
      (Conversion.Integer.convertToIntegerTowardPositive (.signed 64)
        (.finite false 21 (-1))).status.inexact = false ∧
      (Conversion.Integer.convertToIntegerTiesToEven (.signed 8)
        (.finite false 2 2)).status.invalid = true ∧
      (Conversion.Integer.convertToIntegerTiesToEven (.unsigned 8) (.finite false 2 2)).value =
        200 ∧
      (Conversion.Integer.convertToIntegerTiesToEven (.signed 64)
        (.infinity false)).status.invalid = true := by
  float_decide

/--
The range tests of the kernel forms at their boundaries: the two ends of a signed and of an
unsigned integer format, a negative fraction that rounds to an unsigned zero, the integer
format of width zero, the least and the largest quantum exponent of decimal64, and a
coefficient of 16 and of 17 digits.
-/
theorem decimal_quantum_range :
    (Conversion.Integer.convertToIntegerTiesToEven (.signed 8) (.finite true 128 0)).value =
        -128 ∧
      (Conversion.Integer.convertToIntegerTiesToEven (.signed 8)
        (.finite true 129 0)).status.invalid = true ∧
      (Conversion.Integer.convertToIntegerTiesToEven (.signed 8) (.finite false 127 0)).value =
        127 ∧
      (Conversion.Integer.convertToIntegerTiesToEven (.signed 8)
        (.finite false 128 0)).status.invalid = true ∧
      (Conversion.Integer.convertToIntegerTiesToEven (.unsigned 8)
        (.finite true 4 (-1))).status.invalid = false ∧
      (Conversion.Integer.convertToIntegerTiesToEven (.unsigned 8)
        (.finite true 6 (-1))).status.invalid = true ∧
      (Conversion.Integer.convertToIntegerTowardZero (.unsigned 8)
        (.finite false 2559 (-1))).value = 255 ∧
      (Conversion.Integer.convertToIntegerTowardPositive (.unsigned 8)
        (.finite false 2551 (-1))).status.invalid = true ∧
      (Conversion.Integer.convertToIntegerTiesToEven (.signed 0)
        (.finite true 4 (-1))).status.invalid = false ∧
      (Conversion.Integer.convertToIntegerTiesToEven (.signed 0)
        (.finite true 1 0)).status.invalid = true ∧
      (Arithmetic.quantize .decimal64 .nearest (.finite false 0 0)
        (.finite false 1 (-398))).value = .finite false 0 (-398) ∧
      (Arithmetic.quantize .decimal64 .nearest (.finite false 0 0)
        (.finite false 1 (-399))).status.invalid = true ∧
      (Arithmetic.quantize .decimal64 .nearest (.finite false 0 0)
        (.finite false 1 369)).value = .finite false 0 369 ∧
      (Arithmetic.quantize .decimal64 .nearest (.finite false 0 0)
        (.finite false 1 370)).status.invalid = true ∧
      (Arithmetic.quantize .decimal64 .nearest (.finite false 1 0)
        (.finite false 1 (-15))).value = .finite false 1000000000000000 (-15) ∧
      (Arithmetic.quantize .decimal64 .nearest (.finite false 1 0)
        (.finite false 1 (-16))).status.invalid = true := by
  float_decide

/--
The integral roundings through their kernel form: a tie in the two nearest directions, the
directed directions on both signs, the `inexact` signal of `roundToIntegralExact` only, a
quantum exponent above zero that is kept, the sign of a zero result, an infinity and a
signaling NaN.
-/
theorem decimal_integral :
    (Arithmetic.roundToIntegralTiesToEven .decimal64 (.finite false 125 (-1))).value =
        .finite false 12 0 ∧
      (Arithmetic.roundToIntegralTiesToAway .decimal64 (.finite false 125 (-1))).value =
        .finite false 13 0 ∧
      (Arithmetic.roundToIntegralTowardZero .decimal64 (.finite true 129 (-1))).value =
        .finite true 12 0 ∧
      (Arithmetic.roundToIntegralTowardPositive .decimal64 (.finite false 121 (-1))).value =
        .finite false 13 0 ∧
      (Arithmetic.roundToIntegralTowardNegative .decimal64 (.finite true 121 (-1))).value =
        .finite true 13 0 ∧
      Arithmetic.roundToIntegralExact .decimal64 .nearest (.finite false 125 (-1)) =
        { value := .finite false 12 0, status := { inexact := true } } ∧
      Arithmetic.roundToIntegralTiesToEven .decimal64 (.finite false 125 (-1)) =
        { value := .finite false 12 0 } ∧
      Arithmetic.roundToIntegralExact .decimal64 .nearest (.finite false 12 2) =
        { value := .finite false 12 2 } ∧
      (Arithmetic.roundToIntegralTiesToEven .decimal64 (.finite true 4 (-1))).value =
        .finite true 0 0 ∧
      (Arithmetic.roundToIntegralTowardZero .decimal64 (.infinity true)).value =
        .infinity true ∧
      (Arithmetic.roundToIntegralExact .decimal64 .nearest (.nan false true 7)).status.invalid =
        true ∧
      (Arithmetic.roundToIntegralTiesToEven .decimal64 (.nan false true 7)).status.invalid =
        true := by
  float_decide

/--
`logB` through its kernel form: the exponent of the leading digit of a coefficient of one, of
seven and of sixteen digits, and the invalid results of a zero, an infinity and a NaN.
-/
theorem decimal_logB :
    (Arithmetic.logB .decimal64 (.finite false 1 0)).value = 0 ∧
      (Arithmetic.logB .decimal64 (.finite true 1234567 (-3))).value = 3 ∧
      (Arithmetic.logB .decimal64 (.finite false 9999999999999999 369)).value = 384 ∧
      (Arithmetic.logB .decimal64 (.finite false 1000000000000000 (-398))).value = -383 ∧
      (Arithmetic.logB .decimal64 (.finite false 10 (-1))).value = 0 ∧
      (Arithmetic.logB .decimal64 (.finite false 9 (-1))).value = -1 ∧
      (Arithmetic.logB .decimal64 (.finite true 0 5)).status.invalid = true ∧
      (Arithmetic.logB .decimal64 (.infinity false)).status.invalid = true ∧
      (Arithmetic.logB .decimal64 (.nan false false 0)).status.invalid = true ∧
      (Arithmetic.logB .decimal64 (.finite false 1 0)).status.invalid = false := by
  float_decide

/--
`nextUp` and `nextDown` through their kernel form: a step on the finest quantum, a step across
a power of ten in both directions, the two ends of the exponent range, the neighbours of a
zero and of the infinities, and a coefficient that is first scaled to full precision.
-/
theorem decimal_neighbors :
    (Arithmetic.nextUp .decimal32 (.finite false 1 0)).value = .finite false 1000001 (-6) ∧
      (Arithmetic.nextDown .decimal32 (.finite false 1 0)).value = .finite false 9999999 (-7) ∧
      (Arithmetic.nextUp .decimal64 (.finite true 1 0)).value =
        .finite true 9999999999999999 (-16) ∧
      (Arithmetic.nextDown .decimal64 (.finite true 1 0)).value =
        .finite true 1000000000000001 (-15) ∧
      (Arithmetic.nextUp .decimal64 (.finite false 9999999999999999 0)).value =
        .finite false 1000000000000000 1 ∧
      (Arithmetic.nextUp .decimal64 (.finite false 9999999999999999 369)).value =
        .infinity false ∧
      (Arithmetic.nextDown .decimal64 (.finite true 9999999999999999 369)).value =
        .infinity true ∧
      (Arithmetic.nextUp .decimal64 (.finite false 0 0)).value = .finite false 1 (-398) ∧
      (Arithmetic.nextDown .decimal64 (.finite false 0 0)).value = .finite true 1 (-398) ∧
      (Arithmetic.nextUp .decimal64 (.finite true 1 (-398))).value = .finite true 0 (-398) ∧
      (Arithmetic.nextDown .decimal64 (.finite false 1 (-398))).value =
        .finite false 0 (-398) ∧
      (Arithmetic.nextUp .decimal64 (.finite false 123 (-398))).value =
        .finite false 124 (-398) ∧
      (Arithmetic.nextUp .decimal64 (.infinity true)).value =
        .finite true 9999999999999999 369 ∧
      (Arithmetic.nextUp .decimal64 (.infinity false)).value = .infinity false ∧
      (Arithmetic.nextDown .decimal64 (.infinity false)).value =
        .finite false 9999999999999999 369 ∧
      (Arithmetic.nextUp .decimal64 (.nan false true 3)).status.invalid = true := by
  float_decide

/--
Division through its kernel form: exact quotients at the preferred exponent, the difference of
the two quantum exponents, or as near to it as the digits allow; quotients that drop digits in
three rounding directions; the sign and the exponent of a zero quotient; an overflow, an exact
subnormal quotient and an underflow; and a zero divisor.
-/
theorem decimal_division :
    Arithmetic.div .decimal64 .nearest (.finite false 1 0) (.finite false 4 0) =
        { value := .finite false 25 (-2) } ∧
      Arithmetic.div .decimal64 .nearest (.finite false 10 0) (.finite false 2 0) =
        { value := .finite false 5 0 } ∧
      Arithmetic.div .decimal64 .nearest (.finite false 10 (-1)) (.finite false 1 0) =
        { value := .finite false 10 (-1) } ∧
      Arithmetic.div .decimal64 .nearest (.finite false 1 2) (.finite false 1 0) =
        { value := .finite false 1 2 } ∧
      Arithmetic.div .decimal64 .nearest (.finite false 100 0) (.finite false 1 2) =
        { value := .finite false 100 (-2) } ∧
      Arithmetic.div .decimal64 .nearest (.finite false 1 0) (.finite false 3 0) =
        { value := .finite false 3333333333333333 (-16), status := { inexact := true } } ∧
      (Arithmetic.div .decimal64 .nearest (.finite true 2 0) (.finite false 3 0)).value =
        .finite true 6666666666666667 (-16) ∧
      (Arithmetic.div .decimal64 .towardZero (.finite false 2 0) (.finite true 3 0)).value =
        .finite true 6666666666666666 (-16) ∧
      (Arithmetic.div .decimal64 .down (.finite true 2 0) (.finite false 3 0)).value =
        .finite true 6666666666666667 (-16) ∧
      (Arithmetic.div .decimal32 .nearest (.finite false 1 0) (.finite false 3 0)).value =
        .finite false 3333333 (-7) ∧
      (Arithmetic.div .decimal64 .nearest (.finite true 0 3) (.finite false 5 (-2))).value =
        .finite true 0 5 ∧
      (Arithmetic.div .decimal64 .nearest (.finite false 1 369) (.finite false 1 (-10))).value =
        .finite false 10000000000 369 ∧
      Arithmetic.div .decimal64 .nearest (.finite false 9999999999999999 369)
          (.finite false 1 (-398)) =
        { value := .infinity false, status := { overflow := true, inexact := true } } ∧
      Arithmetic.div .decimal64 .nearest (.finite false 4 (-398)) (.finite false 2 0) =
        { value := .finite false 2 (-398) } ∧
      Arithmetic.div .decimal64 .nearest (.finite false 1 (-398)) (.finite false 3 0) =
        { value := .finite false 0 (-398), status := { underflow := true, inexact := true } } ∧
      (Arithmetic.div .decimal64 .nearest (.finite false 5 0) (.finite true 0 0)) =
        { value := .infinity true, status := { divideByZero := true } } ∧
      (Arithmetic.div .decimal64 .nearest (.finite false 0 0) (.finite false 0 0)).status.invalid =
        true := by
  float_decide

/--
The square root through its kernel form: exact roots at the preferred exponent, half the
quantum exponent rounded down; roots that drop digits to nearest, toward zero and toward
positive infinity; the two ends of the exponent range; a zero, a negative datum and an
infinity. The values to nearest are those of Python's `decimal` at 16 digits.
-/
theorem decimal_squareRoot :
    Arithmetic.sqrt .decimal64 .nearest (.finite false 4 0) = { value := .finite false 2 0 } ∧
      Arithmetic.sqrt .decimal64 .nearest (.finite false 2 0) =
        { value := .finite false 1414213562373095 (-15), status := { inexact := true } } ∧
      (Arithmetic.sqrt .decimal64 .up (.finite false 2 0)).value =
        .finite false 1414213562373096 (-15) ∧
      (Arithmetic.sqrt .decimal64 .towardZero (.finite false 3 0)).value =
        .finite false 1732050807568877 (-15) ∧
      (Arithmetic.sqrt .decimal64 .up (.finite false 3 0)).value =
        .finite false 1732050807568878 (-15) ∧
      Arithmetic.sqrt .decimal64 .nearest (.finite false 25 (-2)) =
        { value := .finite false 5 (-1) } ∧
      Arithmetic.sqrt .decimal64 .nearest (.finite false 100 (-2)) =
        { value := .finite false 10 (-1) } ∧
      Arithmetic.sqrt .decimal64 .nearest (.finite false 1 2) = { value := .finite false 1 1 } ∧
      (Arithmetic.sqrt .decimal64 .nearest (.finite false 1 1)).value =
        .finite false 3162277660168379 (-15) ∧
      (Arithmetic.sqrt .decimal64 .nearest (.finite false 4 (-3))).value =
        .finite false 6324555320336759 (-17) ∧
      (Arithmetic.sqrt .decimal64 .nearest (.finite false 9999999999999999 369)).value =
        .finite false 3162277660168379 177 ∧
      Arithmetic.sqrt .decimal64 .nearest (.finite false 9 (-398)) =
        { value := .finite false 3 (-199) } ∧
      (Arithmetic.sqrt .decimal64 .nearest (.finite false 1 (-397))).value =
        .finite false 3162277660168379 (-214) ∧
      (Arithmetic.sqrt .decimal64 .nearest (.finite false 123456789 0)).value =
        .finite false 1111111106055556 (-11) ∧
      (Arithmetic.sqrt .decimal32 .nearest (.finite false 2 0)).value =
        .finite false 1414214 (-6) ∧
      (Arithmetic.sqrt .decimal64 .nearest (.finite true 0 3)).value = .finite true 0 1 ∧
      (Arithmetic.sqrt .decimal64 .nearest (.finite true 1 0)).status.invalid = true ∧
      (Arithmetic.sqrt .decimal64 .nearest (.infinity false)).value = .infinity false := by
  float_decide

/--
The reciprocal square root and a square root far below the format, through their kernel
forms: exact results at the preferred exponent, half the negated quantum exponent rounded
down; results that drop digits (the values to nearest computed with exact rational
arithmetic); the least positive datum; a radicand below the square of the least quantum; a
zero and a negative datum.
-/
theorem decimal_rSqrt :
    Arithmetic.rSqrt .decimal64 .nearest (.finite false 4 0) =
        { value := .finite false 5 (-1) } ∧
      Arithmetic.rSqrt .decimal64 .nearest (.finite false 1 2) =
        { value := .finite false 1 (-1) } ∧
      Arithmetic.rSqrt .decimal64 .nearest (.finite false 25 (-2)) =
        { value := .finite false 2 0 } ∧
      Arithmetic.rSqrt .decimal64 .nearest (.finite false 2 0) =
        { value := .finite false 7071067811865475 (-16), status := { inexact := true } } ∧
      (Arithmetic.rSqrt .decimal64 .up (.finite false 2 0)).value =
        .finite false 7071067811865476 (-16) ∧
      (Arithmetic.rSqrt .decimal64 .nearest (.finite false 3 0)).value =
        .finite false 5773502691896258 (-16) ∧
      (Arithmetic.rSqrt .decimal64 .nearest (.finite false 1 (-1))).value =
        .finite false 3162277660168379 (-15) ∧
      Arithmetic.rSqrt .decimal64 .nearest (.finite false 1 (-398)) =
        { value := .finite false 1 199 } ∧
      (Arithmetic.rSqrt .decimal64 .nearest (.finite false 0 0)).status.divideByZero = true ∧
      (Arithmetic.rSqrt .decimal64 .nearest (.finite true 1 0)).status.invalid = true ∧
      Arithmetic.sqrt .decimal64 .nearest (.finite false 1 (-1000)) =
        { value := .finite false 0 (-398), status := { underflow := true, inexact := true } } ∧
      (Arithmetic.sqrt .decimal64 .up (.finite false 1 (-1000))).value =
        .finite false 1 (-398) := by
  float_decide

/--
The hypotenuse through its kernel form: exact results at the smaller of the two quantum
exponents, a result that drops digits, operands of both signs, zeros, the least positive
datum, and an infinity beside a NaN.
-/
theorem decimal_hypot :
    Arithmetic.hypot .decimal64 .nearest (.finite false 3 0) (.finite false 4 0) =
        { value := .finite false 5 0 } ∧
      Arithmetic.hypot .decimal64 .nearest (.finite true 3 2) (.finite false 4 2) =
        { value := .finite false 5 2 } ∧
      Arithmetic.hypot .decimal64 .nearest (.finite false 30 (-1)) (.finite true 4 0) =
        { value := .finite false 50 (-1) } ∧
      Arithmetic.hypot .decimal64 .nearest (.finite false 1 0) (.finite false 1 0) =
        { value := .finite false 1414213562373095 (-15), status := { inexact := true } } ∧
      (Arithmetic.hypot .decimal64 .up (.finite false 1 0) (.finite true 1 0)).value =
        .finite false 1414213562373096 (-15) ∧
      Arithmetic.hypot .decimal64 .nearest (.finite true 0 0) (.finite false 0 3) =
        { value := .finite false 0 0 } ∧
      Arithmetic.hypot .decimal64 .nearest (.finite false 1 (-398)) (.finite false 0 0) =
        { value := .finite false 1 (-398) } ∧
      (Arithmetic.hypot .decimal64 .nearest (.infinity true) (.nan false false 0)).value =
        .infinity false := by
  float_decide

/--
The reductions through their kernel form: an exact sum at the least quantum exponent, a sum
that the exact accumulation rounds once (`1 + 6e-16 + 6e-16` is `1.000000000000001`, where two
rounded additions give `1.000000000000002`), a cancellation in two rounding directions, the
empty sum, magnitudes, squares, a dot product, arrays of different lengths, and a NaN and an
infinity, which the specification decides.
-/
theorem decimal_reductions :
    Arithmetic.sum .decimal64 .nearest
        #[.finite false 1 0, .finite false 2 (-1), .finite true 3 (-2)] =
        { value := .finite false 117 (-2) } ∧
      Arithmetic.sum .decimal64 .nearest
        #[.finite false 1 0, .finite false 6 (-16), .finite false 6 (-16)] =
        { value := .finite false 1000000000000001 (-15), status := { inexact := true } } ∧
      (Arithmetic.sum .decimal64 .nearest #[.finite false 1 0, .finite true 1 0]).value =
        .finite false 0 0 ∧
      (Arithmetic.sum .decimal64 .down #[.finite false 1 0, .finite true 10 (-1)]).value =
        .finite true 0 (-1) ∧
      Arithmetic.sum .decimal64 .nearest #[] = { value := .finite false 0 0 } ∧
      Arithmetic.sumAbs .decimal64 .nearest
        #[.finite true 1 0, .finite false 2 0, .finite true 3 (-1)] =
        { value := .finite false 33 (-1) } ∧
      Arithmetic.sumSquare .decimal64 .nearest #[.finite false 3 0, .finite true 4 0] =
        { value := .finite false 25 0 } ∧
      Arithmetic.sumSquare .decimal64 .nearest #[.finite true 1 (-1)] =
        { value := .finite false 1 (-2) } ∧
      (Arithmetic.dot .decimal64 .nearest #[.finite false 1 0, .finite false 2 0]
        #[.finite false 3 0, .finite true 4 0]).toOption = some { value := .finite true 5 0 } ∧
      (Arithmetic.dot .decimal64 .nearest #[.finite false 1 0] #[]).toOption = none ∧
      (Arithmetic.sum .decimal64 .nearest #[.finite false 1 0, .infinity true]).value =
        .infinity true ∧
      (Arithmetic.sum .decimal64 .nearest
        #[.finite false 1 0, .nan false true 5]).status.invalid = true := by
  float_decide

/--
The integer power through its kernel form: exact powers at the quantum exponent times the
exponent of the power, odd and even powers of a negative datum, exact and rounded reciprocal
powers, a power that drops one digit, the power zero, a zero base, the largest power of ten
and an overflow.
-/
theorem decimal_pown :
    Arithmetic.pown .decimal64 .nearest (.finite false 2 0) 10 =
        { value := .finite false 1024 0 } ∧
      Arithmetic.pown .decimal64 .nearest (.finite true 2 0) 3 = { value := .finite true 8 0 } ∧
      Arithmetic.pown .decimal64 .nearest (.finite true 2 0) 2 = { value := .finite false 4 0 } ∧
      Arithmetic.pown .decimal64 .nearest (.finite false 15 (-1)) 2 =
        { value := .finite false 225 (-2) } ∧
      Arithmetic.pown .decimal64 .nearest (.finite false 2 0) (-1) =
        { value := .finite false 5 (-1) } ∧
      Arithmetic.pown .decimal64 .nearest (.finite true 2 0) (-3) =
        { value := .finite true 125 (-3) } ∧
      Arithmetic.pown .decimal64 .nearest (.finite false 3 0) (-1) =
        { value := .finite false 3333333333333333 (-16), status := { inexact := true } } ∧
      Arithmetic.pown .decimal64 .nearest (.finite false 7 0) 20 =
        { value := .finite false 7979226629761200 1, status := { inexact := true } } ∧
      Arithmetic.pown .decimal64 .nearest (.finite true 7 3) 0 = { value := .finite false 1 0 } ∧
      Arithmetic.pown .decimal64 .nearest (.finite true 0 0) 3 = { value := .finite true 0 0 } ∧
      (Arithmetic.pown .decimal64 .nearest (.finite true 0 0) (-3)).status.divideByZero = true ∧
      Arithmetic.pown .decimal64 .nearest (.finite false 1 1) 369 =
        { value := .finite false 1 369 } ∧
      Arithmetic.pown .decimal64 .nearest (.finite false 1 1) 400 =
        { value := .infinity false, status := { overflow := true, inexact := true } } := by
  float_decide

/-! ## Every finite datum of a one-digit format -/

/-- A decimal layout of one digit with the quantum exponents from -5 to 6: 240 finite data. -/
def oneDigit : Format := { declets := 0, exponentBits := 2, bias := 5 }

/--
The datum of `oneDigit` with the coefficient `c % 10`, the quantum exponent `q % 12 - 5` and a
negative sign when `q` is at least 12.
-/
def oneDigitDatum (c q : Nat) : Datum :=
  .finite (decide (12 ≤ q)) (c % 10) (((q % 12 : Nat) : Int) - 5)

/--
On every finite datum of the one-digit format, zeros and the two ends of the range included:
`nextUp` is above its operand and `nextDown` below, each undoes the other in value, and
`roundToIntegralExact` returns its operand in value exactly when it does not signal `inexact`.
-/
theorem oneDigit_neighbors : ∀ c q : Fin 24,
    (Datum.compareQuietLess (oneDigitDatum c q)
        (Arithmetic.nextUp oneDigit (oneDigitDatum c q)).value).value = true ∧
      (Datum.compareQuietLess (Arithmetic.nextDown oneDigit (oneDigitDatum c q)).value
        (oneDigitDatum c q)).value = true ∧
      (Datum.compareQuietEqual
        (Arithmetic.nextDown oneDigit (Arithmetic.nextUp oneDigit (oneDigitDatum c q)).value).value
        (oneDigitDatum c q)).value = true ∧
      (Datum.compareQuietEqual
        (Arithmetic.nextUp oneDigit (Arithmetic.nextDown oneDigit (oneDigitDatum c q)).value).value
        (oneDigitDatum c q)).value = true ∧
      (Datum.compareQuietEqual
        (Arithmetic.roundToIntegralExact oneDigit .nearest (oneDigitDatum c q)).value
        (oneDigitDatum c q)).value =
        !(Arithmetic.roundToIntegralExact oneDigit .nearest
          (oneDigitDatum c q)).status.inexact := by
  float_decide

/--
On 576 pairs of finite data of the one-digit format with a nonzero divisor: the quotient
rounded toward negative infinity is not above the quotient rounded toward positive infinity,
and a quotient that does not signal `inexact` gives the dividend back when it is multiplied by
the divisor.
-/
theorem oneDigit_division : ∀ c q : Fin 24,
    (oneDigitDatum q c).isZero = true ∨
      (Datum.compareQuietLessEqual
          (Arithmetic.div oneDigit .down (oneDigitDatum c q) (oneDigitDatum q c)).value
          (Arithmetic.div oneDigit .up (oneDigitDatum c q) (oneDigitDatum q c)).value).value =
        true ∧
      ((Arithmetic.div oneDigit .nearest (oneDigitDatum c q) (oneDigitDatum q c)).status.inexact =
          true ∨
        (Datum.compareQuietEqual
          (Arithmetic.mul oneDigit .nearest
            (Arithmetic.div oneDigit .nearest (oneDigitDatum c q) (oneDigitDatum q c)).value
            (oneDigitDatum q c)).value
          (oneDigitDatum c q)).value = true) := by
  float_decide

/--
On every finite datum of the one-digit format that is not negative: the square of the root
rounded toward negative infinity is not above the datum, the square of the root rounded toward
positive infinity is not below it, and a root that does not signal `inexact` squares to the
datum.
-/
theorem oneDigit_squareRoot : ∀ c q : Fin 24,
    ((oneDigitDatum c q).isSignMinus && !(oneDigitDatum c q).isZero) = true ∨
      (Datum.compareQuietLessEqual
          (Arithmetic.mul oneDigit .down
            (Arithmetic.sqrt oneDigit .down (oneDigitDatum c q)).value
            (Arithmetic.sqrt oneDigit .down (oneDigitDatum c q)).value).value
          (oneDigitDatum c q)).value = true ∧
      (Datum.compareQuietLessEqual (oneDigitDatum c q)
          (Arithmetic.mul oneDigit .up
            (Arithmetic.sqrt oneDigit .up (oneDigitDatum c q)).value
            (Arithmetic.sqrt oneDigit .up (oneDigitDatum c q)).value).value).value = true ∧
      ((Arithmetic.sqrt oneDigit .nearest (oneDigitDatum c q)).status.inexact = true ∨
        (Datum.compareQuietEqual
          (Arithmetic.mul oneDigit .nearest
            (Arithmetic.sqrt oneDigit .nearest (oneDigitDatum c q)).value
            (Arithmetic.sqrt oneDigit .nearest (oneDigitDatum c q)).value).value
          (oneDigitDatum c q)).value = true) := by
  float_decide

/--
On every positive finite datum of the one-digit format: the datum times the square of its
reciprocal square root is at most one when everything is rounded toward negative infinity, and
at least one when everything is rounded toward positive infinity.
-/
theorem oneDigit_rSqrt : ∀ c q : Fin 24,
    ((oneDigitDatum c q).isSignMinus || (oneDigitDatum c q).isZero) = true ∨
      (Datum.compareQuietLessEqual
          (Arithmetic.mul oneDigit .down
            (Arithmetic.mul oneDigit .down
              (Arithmetic.rSqrt oneDigit .down (oneDigitDatum c q)).value
              (Arithmetic.rSqrt oneDigit .down (oneDigitDatum c q)).value).value
            (oneDigitDatum c q)).value
          (.finite false 1 0)).value = true ∧
      (Datum.compareQuietLessEqual (.finite false 1 0)
          (Arithmetic.mul oneDigit .up
            (Arithmetic.mul oneDigit .up
              (Arithmetic.rSqrt oneDigit .up (oneDigitDatum c q)).value
              (Arithmetic.rSqrt oneDigit .up (oneDigitDatum c q)).value).value
            (oneDigitDatum c q)).value).value = true := by
  float_decide

/--
On 576 pairs of finite data of the one-digit format: the hypotenuse rounded toward positive
infinity is not below the magnitude of either operand, and the hypotenuse rounded toward
negative infinity is not above the sum of the two magnitudes rounded toward positive infinity.
-/
theorem oneDigit_hypot : ∀ c q : Fin 24,
    (Datum.compareQuietLessEqual (oneDigitDatum c q).abs
        (Arithmetic.hypot oneDigit .up (oneDigitDatum c q) (oneDigitDatum q c)).value).value =
        true ∧
      (Datum.compareQuietLessEqual (oneDigitDatum q c).abs
        (Arithmetic.hypot oneDigit .up (oneDigitDatum c q) (oneDigitDatum q c)).value).value =
        true ∧
      (Datum.compareQuietLessEqual
        (Arithmetic.hypot oneDigit .down (oneDigitDatum c q) (oneDigitDatum q c)).value
        (Arithmetic.add oneDigit .up (oneDigitDatum c q).abs (oneDigitDatum q c).abs).value).value =
        true := by
  float_decide

/--
On 576 pairs of finite data of the one-digit format the reductions of one and two terms are
the operations they generalize, datum and flags: a sum of two terms is their addition in two
rounding directions, a sum of two magnitudes the addition of the magnitudes, a dot product of
one pair their product, and a sum of one square the product of the datum with itself.
-/
theorem oneDigit_reductions : ∀ c q : Fin 24,
    Arithmetic.sum oneDigit .nearest #[oneDigitDatum c q, oneDigitDatum q c] =
        Arithmetic.add oneDigit .nearest (oneDigitDatum c q) (oneDigitDatum q c) ∧
      Arithmetic.sum oneDigit .down #[oneDigitDatum c q, oneDigitDatum q c] =
        Arithmetic.add oneDigit .down (oneDigitDatum c q) (oneDigitDatum q c) ∧
      Arithmetic.sumAbs oneDigit .nearest #[oneDigitDatum c q, oneDigitDatum q c] =
        Arithmetic.add oneDigit .nearest (oneDigitDatum c q).abs (oneDigitDatum q c).abs ∧
      (Arithmetic.dot oneDigit .nearest #[oneDigitDatum c q] #[oneDigitDatum q c]).toOption =
        some (Arithmetic.mul oneDigit .nearest (oneDigitDatum c q) (oneDigitDatum q c)) ∧
      Arithmetic.sumSquare oneDigit .up #[oneDigitDatum c q] =
        Arithmetic.mul oneDigit .up (oneDigitDatum c q) (oneDigitDatum c q) := by
  float_decide

/--
On 576 finite data of the one-digit format the powers one, two and minus one are the
operations they generalize, datum and flags: the datum itself, its product with itself, and
the quotient of one by it, a zero included.
-/
theorem oneDigit_pown : ∀ c q : Fin 24,
    Arithmetic.pown oneDigit .nearest (oneDigitDatum c q) 1 = { value := oneDigitDatum c q } ∧
      Arithmetic.pown oneDigit .nearest (oneDigitDatum c q) 2 =
        Arithmetic.mul oneDigit .nearest (oneDigitDatum c q) (oneDigitDatum c q) ∧
      Arithmetic.pown oneDigit .up (oneDigitDatum c q) (-1) =
        Arithmetic.div oneDigit .up (.finite false 1 0) (oneDigitDatum c q) := by
  float_decide

/-- The rewrite of `float_decide` reaches the named members and puts the kernel forms there. -/
example (x y : Datum) :
    Arithmetic.roundToIntegralTowardPositive .decimal64 x =
        KernelPath.roundToIntegral .decimal64 .up false x ∧
      Arithmetic.roundToIntegralExact .decimal64 .nearest x =
        KernelPath.roundToIntegral .decimal64 .nearest true x ∧
      Arithmetic.quantize .decimal64 .down x y = KernelPath.quantize .decimal64 .down x y ∧
      Conversion.Integer.convertToIntegerExactTiesToAway (.signed 32) x =
        KernelPath.convertToInteger (.signed 32) .nearestAway true x ∧
      Arithmetic.logB .decimal64 x = KernelPath.logB .decimal64 x ∧
      Arithmetic.div .decimal64 .up x y = KernelPath.div .decimal64 .up x y ∧
      Arithmetic.sqrt .decimal64 .down x = KernelPath.sqrt .decimal64 .down x ∧
      Arithmetic.rSqrt .decimal64 .nearest x = KernelPath.rSqrt .decimal64 .nearest x ∧
      Arithmetic.hypot .decimal64 .nearest x y = KernelPath.hypot .decimal64 .nearest x y ∧
      Arithmetic.pown .decimal64 .nearest x 5 = KernelPath.pown .decimal64 .nearest x 5 ∧
      Arithmetic.sum .decimal64 .nearest #[x, y] = KernelPath.sum .decimal64 .nearest #[x, y] ∧
      Arithmetic.dot .decimal64 .nearest #[x] #[y] = KernelPath.dot .decimal64 .nearest #[x] #[y] ∧
      Arithmetic.nextUp .decimal64 x = KernelPath.nextUp .decimal64 x ∧
      (Arithmetic.nextDown .decimal64 x).value =
        (KernelPath.nextUp .decimal64 x.negate).value.negate := by
  simp only [kernel_optimize, and_self]

/-! ## The theorems on decimal64 data -/

example (s : Bool) (c : Nat) (q : Int) :
    Datum.sameQuantum (.finite s c q) (quantum .decimal64 (.finite s c q)).value = true ∧
      (quantum .decimal64 (.finite s c q)).value.toRat? = some ((10 : ℚ) ^ q) :=
  ⟨sameQuantum_quantum _ s c q, toRat?_quantum _ s c q⟩

example (larger magnitude number : Bool) (x y : Datum) :
    (extremum .decimal64 larger magnitude number x y).status =
      { invalid := x.isSignaling || y.isSignaling } :=
  extremum_status _ larger magnitude number x y

/-- The maximum of `1.0` and `1` is one of the two data, and its value is one. -/
example :
    ((maximum .decimal64 (pos 10 (-1)) (pos 1 0)).value = pos 10 (-1) ∨
        (maximum .decimal64 (pos 10 (-1)) (pos 1 0)).value = pos 1 0) :=
  extremum_value_eq_or _ true false false rfl rfl

example {x y : Datum} {a b : NumericValue} (hx : x.numericValue? = some a)
    (hy : y.numericValue? = some b) :
    (minimum .decimal64 x y).value.numericValue? = some (min a b) ∧
      (maximum .decimal64 x y).value.numericValue? = some (max a b) :=
  ⟨numericValue?_minimum _ hx hy, numericValue?_maximum _ hx hy⟩

example (larger : Bool) {x y : Datum} {a b : NumericValue} (hx : x.abs.numericValue? = some a)
    (hy : y.abs.numericValue? = some b) :
    (selectByMagnitude larger x y).abs.numericValue? =
      some (if larger then max a b else min a b) :=
  numericValue?_abs_selectByMagnitude larger hx hy

/-- A number is preferred to a signaling NaN on either side, with `invalid`. -/
example :
    minimumNumber .decimal64 signalingNaN (pos 3 0) =
        { value := pos 3 0, status := { invalid := true } } ∧
      minimumNumber .decimal64 (pos 3 0) signalingNaN =
        { value := pos 3 0, status := { invalid := true } } :=
  ⟨extremum_number_nan_left _ false false false true 0 rfl,
    extremum_number_nan_right _ false false false true 0 rfl⟩

/-- `5.0` names the payload five: it denotes five, and the NaN built from it is valid. -/
example :
    (pos 50 (-1)).toRat? = some ((5 : Nat) : ℚ) ∧
      (Datum.setPayload .decimal64 (pos 50 (-1))).Valid .decimal64 :=
  have h : (pos 50 (-1)).admissiblePayload? .decimal64 = some 5 := by decide
  ⟨Datum.toRat?_of_admissiblePayload? h, Datum.setPayload_valid h⟩

example (s t : Bool) :
    Datum.setPayloadSignaling .decimal64 (Datum.nan s t 42).getPayload = .nan false true 42 :=
  Datum.setPayloadSignaling_getPayload s t (by decide)

example (datum : Datum) (word : BitVec Format.decimal64.bitWidth) :
    (encodeDecimal .decimal64 datum = some word → decodeDecimal .decimal64 word = datum) ∧
      (encodeBinary .decimal64 datum = some word → decodeBinary .decimal64 word = datum) :=
  ⟨decodeDecimal_of_encodeDecimal_eq_some _ datum word,
    decodeBinary_of_encodeBinary_eq_some _ datum word⟩

/-! ## The decimal reductions -/

/-- The reductions round the exact sum once, here for three finite decimal128 data. -/
example (mode : RoundingMode) (x y z : Datum) (a b c : ℚ) (hx : x.toRat? = some a)
    (hy : y.toRat? = some b) (hz : z.toRat? = some c) :
    ∃ preferred negativeZero, sum .decimal128 mode #[x, y, z] =
      project .decimal128 mode [a, b, c].sum preferred negativeZero :=
  sum_eq_project .decimal128 mode #[x, y, z] [a, b, c] (by simp [hx, hy, hz])

example (mode : RoundingMode) (values : Array Datum) :
    (sum .decimal64 mode values).value.Valid .decimal64 ∧
      (sumAbs .decimal64 mode values).value.Valid .decimal64 ∧
      (sumSquare .decimal64 mode values).value.Valid .decimal64 :=
  ⟨sum_valid _ mode values, sumAbs_valid _ mode values, sumSquare_valid _ mode values⟩

example (mode : RoundingMode) (values : Array Datum) (exacts : List ℚ)
    (hexact : values.toList.map Datum.toRat? = exacts.map some) :
    (∃ preferred negativeZero, sumAbs .decimal64 mode values =
        project .decimal64 mode (exacts.map abs).sum preferred negativeZero) ∧
      ∃ preferred negativeZero, sumSquare .decimal64 mode values =
        project .decimal64 mode (exacts.map fun exact => exact * exact).sum preferred
          negativeZero :=
  ⟨sumAbs_eq_project _ mode values exacts hexact, sumSquare_eq_project _ mode values exacts hexact⟩

example (values : Array Datum) (exacts : List ℚ)
    (hexact : values.toList.map Datum.toRat? = exacts.map some)
    (hfinite : (sum .decimal64 .nearest values).status.overflow = false) :
    ∃ value, (sum .decimal64 .nearest values).value.toRat? = some value ∧
      |value - exacts.sum| ≤ (10 : ℚ) ^ roundingQuantum .decimal64 |exacts.sum| / 2 :=
  sum_error_le_half _ _ (.inl rfl) values exacts hexact hfinite

example (mode : RoundingMode) (values : Array Datum) (exacts : List ℚ)
    (hexact : values.toList.map Datum.toRat? = exacts.map some) (value : ℚ)
    (hvalue : (sum .decimal64 mode values).value.toRat? = some value) :
    (sum .decimal64 mode values).status.inexact = true ↔ value ≠ exacts.sum :=
  sum_inexact_iff _ mode values exacts hexact value hvalue

example (mode : RoundingMode) (left right : Array Datum) (xs ys : List ℚ)
    (hleft : left.toList.map Datum.toRat? = xs.map some)
    (hright : right.toList.map Datum.toRat? = ys.map some) (hsize : left.size = right.size) :
    ∃ preferred negativeZero, dot .decimal64 mode left right =
      .ok (project .decimal64 mode (List.zipWith (· * ·) xs ys).sum preferred negativeZero) :=
  dot_eq_project _ mode left right xs ys hleft hright hsize

end FloatLibTests.Conformance.Formats.DecimalRecommended
