/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Proof
public meta import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded.Proof
public meta import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Proof

/-!
# The recommended functions of IEEE 754-2019 §9.2 on decimal formats, in five directions

Results of `Transcendentals.CorrectlyRounded` on decimal data, with their flags. `cases` holds
every case once, checked by compiled evaluation when this module is elaborated: correctly
rounded results in several rounding directions, the special cases at zeros, infinities and
NaNs, the domain errors with `invalid`, the poles with `divideByZero`, exact results without a
flag, and overflows and underflows. `certifiedCases` compare the total functions with the
certified ones: wherever `Transcendentals.Certified` returns a result, the total function to
nearest-even returns the same datum. `comparatorCases` round rational numbers by their
comparators and compare the outcome, flags and quantum exponent included, with the projection
of decimal arithmetic. The results at pseudo-random operands are compared with `mpmath` by
`tests/oracles/ieee2019.sh`.

The last part applies the theorems to the named functions and to the three interchange
formats.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.DecimalRecommendedFunctions

open FloatLib.Floats.Formats.DecimalInterchange
open FloatLib.Floats.Formats.DecimalInterchange.Transcendentals
open FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.CorrectlyRounded (Function)

/-- The positive datum `coefficient × 10 ^ exponent`. -/
def pos (coefficient : Nat) (exponent : Int) : Datum := .finite false coefficient exponent

/-- The negative datum `-coefficient × 10 ^ exponent`. -/
def neg (coefficient : Nat) (exponent : Int) : Datum := .finite true coefficient exponent

/-- The flags of an outcome as the sum of invalid 1, divideByZero 2, overflow 4, underflow 8 and
inexact 16. -/
def flags (outcome : Outcome) : Nat :=
  (if outcome.status.invalid then 1 else 0) + (if outcome.status.divideByZero then 2 else 0) +
    (if outcome.status.overflow then 4 else 0) + (if outcome.status.underflow then 8 else 0) +
    (if outcome.status.inexact then 16 else 0)

/-- Whether an outcome is the datum `value` with the flags `expected`. -/
def holds (outcome : Outcome) (value : Datum) (expected : Nat) : Bool :=
  outcome.value == value && flags outcome == expected

/-- Whether an outcome is a quiet NaN with the flags `expected`. -/
def isQuietNaN (outcome : Outcome) (expected : Nat) : Bool :=
  outcome.value.isQNaN && flags outcome == expected

/-- The cases: a name and whether the case holds. -/
def cases : List (String × Bool) :=
  [ ("sin 0.5 to nearest-even in decimal64",
      holds (CorrectlyRounded.sin .decimal64 .nearest (pos 5 (-1)))
        (pos 4794255386042030 (-16)) 16),
    ("sin 0.5 toward positive",
      holds (CorrectlyRounded.sin .decimal64 .up (pos 5 (-1))) (pos 4794255386042031 (-16)) 16),
    ("sin 0.5 toward negative",
      holds (CorrectlyRounded.sin .decimal64 .down (pos 5 (-1))) (pos 4794255386042030 (-16)) 16),
    ("sin -0.5 toward zero",
      holds (CorrectlyRounded.sin .decimal64 .towardZero (neg 5 (-1)))
        (neg 4794255386042030 (-16)) 16),
    ("sin -0.5 toward negative",
      holds (CorrectlyRounded.sin .decimal64 .down (neg 5 (-1)))
        (neg 4794255386042031 (-16)) 16),
    ("sin 0.5 in decimal128",
      holds (CorrectlyRounded.sin .decimal128 .nearest (pos 5 (-1)))
        (pos 4794255386042030002732879352155714 (-34)) 16),
    ("exp 1 is e", holds (CorrectlyRounded.exp .decimal64 .nearest (pos 1 0))
        (pos 2718281828459045 (-15)) 16),
    ("exp 1 toward positive", holds (CorrectlyRounded.exp .decimal64 .up (pos 1 0))
        (pos 2718281828459046 (-15)) 16),
    ("exp -0 is 1 with a full coefficient",
      holds (CorrectlyRounded.exp .decimal64 .nearest (neg 0 3)) (pos 1000000000000000 (-15)) 0),
    ("exp -inf is +0", holds (CorrectlyRounded.exp .decimal64 .nearest (.infinity true))
        (pos 0 (-398)) 0),
    ("exp +inf is +inf", holds (CorrectlyRounded.exp .decimal64 .nearest (.infinity false))
        (.infinity false) 0),
    ("exp 1000 overflows to +inf",
      holds (CorrectlyRounded.exp .decimal64 .nearest (pos 1000 0)) (.infinity false) 20),
    ("exp 1000 toward zero is the largest finite value",
      holds (CorrectlyRounded.exp .decimal64 .towardZero (pos 1000 0))
        (pos 9999999999999999 369) 20),
    ("exp -1000 underflows to +0",
      holds (CorrectlyRounded.exp .decimal64 .nearest (neg 1000 0)) (pos 0 (-398)) 24),
    ("exp -1000 toward positive is the least subnormal",
      holds (CorrectlyRounded.exp .decimal64 .up (neg 1000 0)) (pos 1 (-398)) 24),
    ("expm1 of a zero is that zero",
      holds (CorrectlyRounded.expm1 .decimal64 .nearest (neg 0 (-3))) (neg 0 (-3)) 0),
    ("expm1 -inf is -1", holds (CorrectlyRounded.expm1 .decimal64 .nearest (.infinity true))
        (neg 1000000000000000 (-15)) 0),
    ("expm1 1E-30 toward negative",
      holds (CorrectlyRounded.expm1 .decimal64 .down (pos 1 (-30)))
        (pos 1000000000000000 (-45)) 16),
    ("expm1 1E-30 toward positive",
      holds (CorrectlyRounded.expm1 .decimal64 .up (pos 1 (-30)))
        (pos 1000000000000001 (-45)) 16),
    ("log 1 is +0", holds (CorrectlyRounded.log .decimal64 .down (pos 1 0)) (pos 0 (-398)) 0),
    ("log 10", holds (CorrectlyRounded.log .decimal64 .nearest (pos 10 0))
        (pos 2302585092994046 (-15)) 16),
    ("log +0 is -inf with divideByZero",
      holds (CorrectlyRounded.log .decimal64 .nearest (pos 0 0)) (.infinity true) 2),
    ("log of a negative number is invalid",
      isQuietNaN (CorrectlyRounded.log .decimal64 .nearest (neg 3 0)) 1),
    ("log -inf is invalid",
      isQuietNaN (CorrectlyRounded.log .decimal64 .nearest (.infinity true)) 1),
    ("logp1 -1 is -inf with divideByZero",
      holds (CorrectlyRounded.logp1 .decimal64 .nearest (neg 1 0)) (.infinity true) 2),
    ("logp1 +0E+5 is that zero",
      holds (CorrectlyRounded.logp1 .decimal64 .nearest (pos 0 5)) (pos 0 5) 0),
    ("logp1 of a zero with a quantum beyond the format is that zero at the largest quantum",
      holds (CorrectlyRounded.logp1 .decimal64 .nearest (pos 0 1000)) (pos 0 369) 0),
    ("exp2 10 is 1024, exact", holds (CorrectlyRounded.exp2 .decimal64 .up (pos 10 0))
        (pos 1024000000000000 (-12)) 0),
    ("exp10 -390 is an exact subnormal",
      holds (CorrectlyRounded.exp10 .decimal64 .nearest (neg 390 0)) (pos 100000000 (-398)) 0),
    ("exp10 -400 toward positive is the least subnormal, underflow",
      holds (CorrectlyRounded.exp10 .decimal64 .up (neg 400 0)) (pos 1 (-398)) 24),
    ("exp10 385 overflows toward zero to the largest finite value",
      holds (CorrectlyRounded.exp10 .decimal64 .towardZero (pos 385 0))
        (pos 9999999999999999 369) 20),
    ("exp10 384 is exact at the top of the range",
      holds (CorrectlyRounded.exp10 .decimal64 .nearest (pos 384 0))
        (pos 1000000000000000 369) 0),
    ("log10 1000 is 3, exact", holds (CorrectlyRounded.log10 .decimal64 .nearest (pos 1000 0))
        (pos 3000000000000000 (-15)) 0),
    ("log2 of a negative number is invalid",
      isQuietNaN (CorrectlyRounded.log2 .decimal64 .nearest (neg 3 0)) 1),
    ("sin -0E-3 is that zero",
      holds (CorrectlyRounded.sin .decimal64 .nearest (neg 0 (-3))) (neg 0 (-3)) 0),
    ("cos -0 is 1", holds (CorrectlyRounded.cos .decimal64 .nearest (neg 0 (-3)))
        (pos 1000000000000000 (-15)) 0),
    ("sin of an infinity is invalid",
      isQuietNaN (CorrectlyRounded.sin .decimal64 .nearest (.infinity false)) 1),
    ("sin of a quiet NaN is that NaN",
      holds (CorrectlyRounded.sin .decimal64 .nearest (.nan true false 7)) (.nan true false 7) 0),
    ("sin of a signaling NaN is that NaN quieted, invalid",
      holds (CorrectlyRounded.sin .decimal64 .nearest (.nan false true 7)) (.nan false false 7) 1),
    ("sinPi 0.5 is 1, exact", holds (CorrectlyRounded.sinPi .decimal64 .nearest (pos 5 (-1)))
        (pos 1000000000000000 (-15)) 0),
    ("sinPi -3 is -0", holds (CorrectlyRounded.sinPi .decimal64 .nearest (neg 3 0))
        (neg 0 (-398)) 0),
    ("cosPi 0.5 is +0", holds (CorrectlyRounded.cosPi .decimal64 .nearest (pos 5 (-1)))
        (pos 0 (-398)) 0),
    ("tanPi 0.5 is +inf with divideByZero",
      holds (CorrectlyRounded.tanPi .decimal64 .nearest (pos 5 (-1))) (.infinity false) 2),
    ("tanPi 1.5 is -inf with divideByZero",
      holds (CorrectlyRounded.tanPi .decimal64 .nearest (pos 15 (-1))) (.infinity true) 2),
    ("asin 2 is invalid", isQuietNaN (CorrectlyRounded.asin .decimal64 .nearest (pos 2 0)) 1),
    ("acos 1 is +0", holds (CorrectlyRounded.acos .decimal64 .nearest (pos 1 0))
        (pos 0 (-398)) 0),
    ("atan 1 is a quarter of pi",
      holds (CorrectlyRounded.atan .decimal64 .nearest (pos 1 0)) (pos 7853981633974483 (-16)) 16),
    ("atan +inf is half of pi",
      holds (CorrectlyRounded.atan .decimal64 .nearest (.infinity false))
        (pos 1570796326794897 (-15)) 16),
    ("atanPi -inf is -1/2", holds (CorrectlyRounded.atanPi .decimal64 .nearest (.infinity true))
        (neg 5000000000000000 (-16)) 0),
    ("atanh 1 is +inf with divideByZero",
      holds (CorrectlyRounded.atanh .decimal64 .nearest (pos 1 0)) (.infinity false) 2),
    ("atanh 0.5", holds (CorrectlyRounded.atanh .decimal64 .nearest (pos 5 (-1)))
        (pos 5493061443340548 (-16)) 16),
    ("acosh 2", holds (CorrectlyRounded.acosh .decimal64 .nearest (pos 2 0))
        (pos 1316957896924817 (-15)) 16),
    ("acosh 0.5 is invalid",
      isQuietNaN (CorrectlyRounded.acosh .decimal64 .nearest (pos 5 (-1))) 1),
    ("tanh +inf is 1", holds (CorrectlyRounded.tanh .decimal64 .nearest (.infinity false))
        (pos 1000000000000000 (-15)) 0),
    ("tanh of 1.23E-7 in decimal32",
      holds (CorrectlyRounded.tanh .decimal32 .nearest (pos 123 (-9))) (pos 1230000 (-13)) 16),
    ("exp2 of a million overflows",
      holds (CorrectlyRounded.exp2 .decimal64 .nearest (pos 1 6)) (.infinity false) 20),
    ("sin of a datum with 17 digits in decimal64 reads its exact value",
      holds (CorrectlyRounded.sin .decimal64 .nearest (pos 50000000000000000 (-17)))
        (pos 4794255386042030 (-16)) 16),
    ("powr 2 0.5 is the square root of two",
      holds (CorrectlyRounded.powr .decimal64 .nearest (pos 2 0) (pos 5 (-1)))
        (pos 1414213562373095 (-15)) 16),
    ("powr of a negative base is invalid",
      isQuietNaN (CorrectlyRounded.powr .decimal64 .nearest (neg 2 0) (pos 5 (-1))) 1),
    ("powr +0 -1 is +inf with divideByZero",
      holds (CorrectlyRounded.powr .decimal64 .nearest (pos 0 0) (neg 1 0)) (.infinity false) 2),
    ("pow 2 0.5 toward positive",
      holds (CorrectlyRounded.pow .decimal64 .up (pos 2 0) (pos 5 (-1)))
        (pos 1414213562373096 (-15)) 16),
    ("pow -2 3 is -8, exact",
      holds (CorrectlyRounded.pow .decimal64 .nearest (neg 2 0) (pos 3 0))
        (neg 8000000000000000 (-15)) 0),
    ("pow -2 -3 is -0.125, exact",
      holds (CorrectlyRounded.pow .decimal64 .nearest (neg 2 0) (neg 3 0))
        (neg 1250000000000000 (-16)) 0),
    ("pow -2 0.5 is invalid",
      isQuietNaN (CorrectlyRounded.pow .decimal64 .nearest (neg 2 0) (pos 5 (-1))) 1),
    ("pow of a quiet NaN and a zero is 1",
      holds (CorrectlyRounded.pow .decimal64 .nearest (.nan false false 0) (neg 0 0))
        (pos 1000000000000000 (-15)) 0),
    ("pow of a signaling NaN and a zero is invalid",
      isQuietNaN (CorrectlyRounded.pow .decimal64 .nearest (.nan false true 0) (pos 0 0)) 1),
    ("pow 1 of a quiet NaN is 1",
      holds (CorrectlyRounded.pow .decimal64 .nearest (pos 10 (-1)) (.nan false false 0))
        (pos 1000000000000000 (-15)) 0),
    ("pow -0 -3 is -inf with divideByZero",
      holds (CorrectlyRounded.pow .decimal64 .nearest (neg 0 0) (neg 3 0)) (.infinity true) 2),
    ("pow -0 -2 is +inf with divideByZero",
      holds (CorrectlyRounded.pow .decimal64 .nearest (neg 0 0) (neg 2 0)) (.infinity false) 2),
    ("pow -0 3 is -0", holds (CorrectlyRounded.pow .decimal64 .nearest (neg 0 0) (pos 3 0))
        (neg 0 (-398)) 0),
    ("pow -1 +inf is 1",
      holds (CorrectlyRounded.pow .decimal64 .nearest (neg 1 0) (.infinity false))
        (pos 1000000000000000 (-15)) 0),
    ("pow -inf 3 is -inf",
      holds (CorrectlyRounded.pow .decimal64 .nearest (.infinity true) (pos 3 0))
        (.infinity true) 0),
    ("pow -inf -3 is -0",
      holds (CorrectlyRounded.pow .decimal64 .nearest (.infinity true) (neg 3 0))
        (neg 0 (-398)) 0),
    ("pow 0.5 +inf is +0",
      holds (CorrectlyRounded.pow .decimal64 .nearest (pos 5 (-1)) (.infinity false))
        (pos 0 (-398)) 0),
    ("compound 0.05 10 is 1.05 ^ 10",
      holds (CorrectlyRounded.compound .decimal64 .nearest (pos 5 (-2)) 10)
        (pos 1628894626777441 (-15)) 16),
    ("compound -2 3 is invalid",
      isQuietNaN (CorrectlyRounded.compound .decimal64 .nearest (neg 2 0) 3) 1),
    ("compound -1 -2 is +inf with divideByZero",
      holds (CorrectlyRounded.compound .decimal64 .nearest (neg 1 0) (-2)) (.infinity false) 2),
    ("compound of a quiet NaN with exponent 0 is 1",
      holds (CorrectlyRounded.compound .decimal64 .nearest (.nan false false 0) 0)
        (pos 1000000000000000 (-15)) 0),
    ("atan2 1 1 is a quarter of pi",
      holds (CorrectlyRounded.atan2 .decimal64 .nearest (pos 1 0) (pos 1 0))
        (pos 7853981633974483 (-16)) 16),
    ("atan2 -0 -1 is -pi, rounded toward negative",
      holds (CorrectlyRounded.atan2 .decimal64 .down (neg 0 0) (neg 1 0))
        (neg 3141592653589794 (-15)) 16),
    ("atan2 +0 1 is +0",
      holds (CorrectlyRounded.atan2 .decimal64 .nearest (pos 0 0) (pos 1 0)) (pos 0 (-398)) 0),
    ("atan2Pi 1 1 is 1/4, exact",
      holds (CorrectlyRounded.atan2Pi .decimal64 .nearest (pos 1 0) (pos 1 0))
        (pos 2500000000000000 (-16)) 0),
    ("atan2Pi -1 -inf is -1",
      holds (CorrectlyRounded.atan2Pi .decimal64 .nearest (neg 1 0) (.infinity true))
        (neg 1000000000000000 (-15)) 0),
    ("atan2 of two NaNs is the first, quieted, invalid for a signaling one",
      holds (CorrectlyRounded.atan2 .decimal64 .nearest (.nan false false 3) (.nan true true 5))
        (.nan false false 3) 1) ]

/-- The members of `Function` by their names. -/
def functions : List (String × Function) :=
  [("exp2", .exp2), ("exp2m1", .exp2m1), ("exp10", .exp10), ("exp10m1", .exp10m1),
    ("log2", .log2), ("log10", .log10), ("log2p1", .log2p1), ("log10p1", .log10p1),
    ("sin", .sin), ("cos", .cos), ("tan", .tan), ("sinPi", .sinPi), ("cosPi", .cosPi),
    ("tanPi", .tanPi), ("asin", .asin), ("acos", .acos), ("atan", .atan), ("asinPi", .asinPi),
    ("acosPi", .acosPi), ("atanPi", .atanPi), ("sinh", .sinh), ("cosh", .cosh), ("tanh", .tanh),
    ("asinh", .asinh), ("acosh", .acosh), ("atanh", .atanh)]

/--
Wherever a certified function returns a result, the total function to nearest-even returns the
same datum: every member of `Function` at eight operands in each of the three interchange
formats, and `exp`, `log`, `expm1`, `logp1`, `powr` and `compound`.
-/
def certifiedCases : List (String × Bool) :=
  let formats : List (String × Format) :=
    [("decimal32", .decimal32), ("decimal64", .decimal64), ("decimal128", .decimal128)]
  let operands : List Datum :=
    [pos 5 (-1), neg 25 (-2), pos 123 (-3), pos 15 (-1), neg 3 0, pos 7 (-5), pos 99 (-2),
      pos 0 2]
  let agrees (certified : Option Datum) (total : Outcome) : Bool :=
    match certified with
    | some result => total.value == result
    | none => true
  formats.flatMap fun (formatName, f) =>
    (functions.flatMap fun (name, function) =>
      operands.map fun x =>
        (s!"{name} of {x} in {formatName} agrees with the certified function",
          agrees (Certified.apply f function x) (CorrectlyRounded.apply f function .nearest x))) ++
    operands.flatMap fun x =>
      [(s!"exp of {x} in {formatName}",
          agrees (Certified.exp f x) (CorrectlyRounded.exp f .nearest x)),
        (s!"log of {x} in {formatName}",
          agrees (Certified.log f x) (CorrectlyRounded.log f .nearest x)),
        (s!"expm1 of {x} in {formatName}",
          agrees (Certified.expm1 f x) (CorrectlyRounded.expm1 f .nearest x)),
        (s!"logp1 of {x} in {formatName}",
          agrees (Certified.logp1 f x) (CorrectlyRounded.logp1 f .nearest x)),
        (s!"powr of {x} and 0.75 in {formatName}",
          agrees (Certified.powr f x (pos 75 (-2)))
            (CorrectlyRounded.powr f .nearest x (pos 75 (-2)))),
        (s!"compound of {x} with exponent 7 in {formatName}",
          agrees (Certified.compound f x 7) (CorrectlyRounded.compound f .nearest x 7))]

/--
Rounding a rational number by its comparator gives the outcome of decimal arithmetic for it
with the least quantum exponent preferred: the datum and the flags agree, in the five
directions, at exact values, ties, subnormal values, underflows and overflows of decimal32.
-/
def comparatorCases : List (String × Bool) :=
  let modes : List (String × RoundingMode) :=
    [("nearest", .nearest), ("nearestAway", .nearestAway), ("towardZero", .towardZero),
      ("up", .up), ("down", .down)]
  let samples : List ℚ :=
    [1, 1 / 3, 2 / 3, 1234567 / 1000, 12345675 / 10000, 12345665 / 10000, 9999999, 99999995 / 10,
      99999994 / 10, 1 / 7 * 10 ^ 90, 9999999 * 10 ^ 90, 99999995 * 10 ^ 89, 10 ^ 97,
      99999999 * 10 ^ 89, 1 / 10 ^ 101, 1 / (2 * 10 ^ 101), 1 / (3 * 10 ^ 101), 15 / 10 ^ 102,
      25 / 10 ^ 102, 7 / 10 ^ 95, 1234567 / 10 ^ 101, 12345674 / 10 ^ 102, 999999 / 10 ^ 101,
      9999995 / 10 ^ 102, 99999999 / 10 ^ 103, 5 / 10 ^ 102, 49 / 10 ^ 103, 51 / 10 ^ 103, 0]
  modes.flatMap fun (modeName, mode) =>
    (samples ++ samples.map (-·)).map fun x =>
      (s!"the comparator of {x} rounded {modeName} in decimal32",
        ComparisonRounding.round .decimal32 mode (fun candidate => compare x candidate) ==
          project .decimal32 mode x Format.decimal32.minQuantum)

#eval show IO Unit from do
  let failures := (cases ++ certifiedCases ++ comparatorCases).filter fun entry => !entry.2
  unless failures.isEmpty do
    throw <| IO.userError s!"decimal recommended function cases that fail: {failures.map (·.1)}"
  IO.println <| s!"{cases.length} cases of the decimal recommended functions hold, " ++
    s!"{certifiedCases.length} results agree with the certified functions, and " ++
    s!"{comparatorCases.length} comparator roundings agree with decimal arithmetic"

/-! ## The theorems -/

section Contracts

variable {x y : Datum} {p q : ℚ}

/-- A named function is `apply` at its member, so the one theorem applies to it: in every
decimal format and every direction, the outcome is the rounding of the real function. -/
example (f : Format) (mode : RoundingMode) (hx : x.toRat? = some q) (hne : Real.sin q ≠ 0) :
    RoundsTo f mode (Real.sin q) (decide (Real.sin q < 0)) (CorrectlyRounded.sin f mode x) :=
  CorrectlyRounded.apply_roundsTo f .sin mode hx trivial hne

/-- In range the value is a valid finite datum that denotes the rounding in the direction. -/
example (mode : RoundingMode) (hx : x.toRat? = some q) (hdomain : 0 < q)
    (hne : Real.logb 10 q ≠ 0)
    (hrange : |roundTo .decimal64 mode (Real.logb 10 q)| ≤
      toReal (Format.decimal64.maxFinite false)) :
    (CorrectlyRounded.log10 .decimal64 mode x).value.Valid .decimal64 ∧
      toReal (CorrectlyRounded.log10 .decimal64 mode x).value =
        roundTo .decimal64 mode (Real.logb 10 q) :=
  ((CorrectlyRounded.apply_roundsTo .decimal64 .log10 mode hx hdomain hne).finite hrange).2

/-- `inexact` and `underflow` have the meaning that the standard gives them. -/
example (mode : RoundingMode) (hx : x.toRat? = some q) (hne : Real.sinh q ≠ 0)
    (hrange : |roundTo .decimal128 mode (Real.sinh q)| ≤
      toReal (Format.decimal128.maxFinite false)) :
    ((CorrectlyRounded.sinh .decimal128 mode x).status.inexact = true ↔
        roundTo .decimal128 mode (Real.sinh q) ≠ Real.sinh q) ∧
      ((CorrectlyRounded.sinh .decimal128 mode x).status.underflow = true ↔
        |Real.sinh q| < (Format.decimal128.minNormal : ℝ) ∧
          roundTo .decimal128 mode (Real.sinh q) ≠ Real.sinh q) :=
  let h := (CorrectlyRounded.apply_roundsTo .decimal128 .sinh mode hx trivial hne).flags hrange
  ⟨h.1, h.2.1⟩

/-- Beyond the range the outcome is the overflow result of the direction. -/
example (mode : RoundingMode) (hx : x.toRat? = some q)
    (hover : toReal (Format.decimal32.maxFinite false) <
      |roundTo .decimal32 mode (Real.exp q)|) :
    CorrectlyRounded.exp .decimal32 mode x = KernelPath.overflow .decimal32 mode false :=
  (CorrectlyRounded.exp_roundsTo .decimal32 mode hx).overflow hover

/-- To nearest-even the rounding is `roundAt`, the specification of the certified functions. -/
example (f : Format) (r : ℝ) : roundTo f .nearest r = roundAt f r :=
  roundTo_nearest f r

example (f : Format) (mode : RoundingMode) (hx : x.toRat? = some q) (hne : q ≠ 0) :
    RoundsTo f mode (Real.exp q - 1) (decide (Real.exp q - 1 < 0))
      (CorrectlyRounded.expm1 f mode x) :=
  CorrectlyRounded.expm1_roundsTo f mode hx hne

example (f : Format) (mode : RoundingMode) (hx : x.toRat? = some q) (hpos : 0 < q)
    (hne : q ≠ 1) :
    RoundsTo f mode (Real.log q) (decide (Real.log q < 0)) (CorrectlyRounded.log f mode x) :=
  CorrectlyRounded.log_roundsTo f mode hx hpos hne

example (f : Format) (mode : RoundingMode) (hx : x.toRat? = some q) (hdomain : -1 < q)
    (hne : q ≠ 0) :
    RoundsTo f mode (Real.log ((q : ℝ) + 1)) (decide (Real.log ((q : ℝ) + 1) < 0))
      (CorrectlyRounded.logp1 f mode x) :=
  CorrectlyRounded.logp1_roundsTo f mode hx hdomain hne

/-- The functions of two arguments. -/
example (f : Format) (mode : RoundingMode) (hx : x.toRat? = some p) (hy : y.toRat? = some q)
    (hp : 0 < p) :
    RoundsTo f mode ((p : ℝ) ^ (q : ℝ)) false (CorrectlyRounded.powr f mode x y) :=
  CorrectlyRounded.powr_roundsTo f mode hx hy hp

example (f : Format) (mode : RoundingMode) (hx : x.toRat? = some p) (hy : y.toRat? = some q)
    (hp : 0 < p) :
    RoundsTo f mode ((p : ℝ) ^ (q : ℝ)) false (CorrectlyRounded.pow f mode x y) :=
  CorrectlyRounded.pow_roundsTo_of_pos f mode hx hy hp

example (f : Format) (mode : RoundingMode) (n : ℤ) (hx : x.toRat? = some p)
    (hy : y.toRat? = some (n : ℚ)) (hp : p < 0) :
    RoundsTo f mode ((p : ℝ) ^ n) (decide ((p : ℝ) ^ n < 0)) (CorrectlyRounded.pow f mode x y) :=
  CorrectlyRounded.pow_roundsTo_of_neg f mode hx hy hp

example (f : Format) (mode : RoundingMode) (hx : x.toRat? = some q) (hq : -1 < q) (n : ℤ) :
    RoundsTo f mode ((1 + (q : ℝ)) ^ (n : ℝ)) false (CorrectlyRounded.compound f mode x n) :=
  CorrectlyRounded.compound_roundsTo f mode hx hq n

example (f : Format) (mode : RoundingMode) (hy : y.toRat? = some q) (hx : x.toRat? = some p)
    (hne : q ≠ 0) :
    RoundsTo f mode (Complex.arg ⟨(p : ℝ), (q : ℝ)⟩)
      (decide (Complex.arg ⟨(p : ℝ), (q : ℝ)⟩ < 0)) (CorrectlyRounded.atan2 f mode y x) :=
  CorrectlyRounded.atan2_roundsTo f mode hy hx hne

example (f : Format) (mode : RoundingMode) (hy : y.toRat? = some q) (hx : x.toRat? = some p)
    (hne : q ≠ 0) :
    RoundsTo f mode (Complex.arg ⟨(p : ℝ), (q : ℝ)⟩ / Real.pi)
      (decide (Complex.arg ⟨(p : ℝ), (q : ℝ)⟩ / Real.pi < 0))
      (CorrectlyRounded.atan2Pi f mode y x) :=
  CorrectlyRounded.atan2Pi_roundsTo f mode hy hx hne

/-- The comparator-level statement, with a comparator that exists: the one of a rational. -/
example (f : Format) (mode : RoundingMode) :
    RoundsTo f mode (((1 / 3 : ℚ) : ℝ)) (decide ((((1 / 3 : ℚ) : ℝ)) < 0))
      (ComparisonRounding.round f mode fun candidate => cmp (1 / 3 : ℚ) candidate) :=
  ComparisonRounding.round_roundsTo f mode (by norm_num)
    (FloatLib.Floats.Formats.BinaryInterchange.Model.ComparisonRounding.Rule.locates_rational
      (1 / 3))

/-- An enclosure of the number does not change a comparator. -/
example (interval : FloatLib.Numerics.RationalInterval) (compare : ℚ → Ordering) (target : ℝ)
    (hcontains : interval.Contains target)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (candidate : ℚ) :
    ComparisonRounding.within interval compare candidate = cmp target (candidate : ℝ) :=
  ComparisonRounding.within_eq hcontains hcompare candidate

/-- Every direction of the grid rounding is monotone. -/
example (f : Format) (mode : RoundingMode) {r s : ℝ} (h : r ≤ s) :
    roundTo f mode r ≤ roundTo f mode s :=
  roundTo_mono f mode h

/-- A rule that locates zero delivers a zero with the least quantum exponent, without a flag. -/
example (f : Format) (mode : RoundingMode) :
    ∃ negative, ComparisonRounding.deliver f mode (fun _ => none)
        (FloatLib.Floats.Formats.BinaryInterchange.Model.ComparisonRounding.Rule.rational 0) =
      { value := .finite negative 0 f.minQuantum } :=
  ComparisonRounding.deliver_of_eq_zero f mode
    (by simpa using
      FloatLib.Floats.Formats.BinaryInterchange.Model.ComparisonRounding.Rule.locates_rational 0)
    (fun _ h => absurd h (by simp))

/-- A zero operand of a function that is zero at zero keeps its sign, without a flag. -/
example (f : Format) (mode : RoundingMode) (negative : Bool) (quantum : ℤ) :
    CorrectlyRounded.apply f .sinh mode (.finite negative 0 quantum) =
      { value := .finite negative 0 (max f.minQuantum (min quantum f.maxQuantum)) } :=
  CorrectlyRounded.apply_zero f .sinh mode negative quantum rfl

end Contracts

end FloatLibTests.Conformance.Formats.DecimalRecommendedFunctions
