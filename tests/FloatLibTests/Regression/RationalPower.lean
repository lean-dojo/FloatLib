/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Algebraic.RationalPower.Runtime
public import FloatLib.Floats.Formats.Posit.Logarithm.Runtime
public import FloatLib.Numerics.Exact.RationalPower.Runtime
public import FloatLib.Numerics.Exact.Reciprocal.Runtime
public import FloatLib.Numerics.Exact.Trigonometric.Atan2.Runtime
public import FloatLib.Numerics.Exact.Trigonometric.Runtime
public import FloatLibTests.Accounting

/-!
# Rational powers and comparator adapters

These checks run the exact rational-power comparator and the reciprocal, offset and π adapters.

* Exact values: `4 ^ (1/2) = 2` and `(9/4) ^ (3/2) = 27/8` are found by the exact-root
  descriptor, compared as equal, and built as dyadics, and posit16 `pow` returns them exactly.
* `2 ^ 1023.5` has no descriptor, so it is irrational.
* Hard inputs: `(1 + 2^-52) ^ (2^60)` and the binary64 pair `0x1.0000008000001p+0 ^ 17179869184.5`
  are compared with their binary64 neighbors and midpoints. The exact value of the second power
  has an odd significand of about `8.9 * 10^11` bits, which the comparator never forms. The expected
  orderings come from 150-digit decimal evaluation. Exponents `2^-1074` and `±2^1023` check that
  huge exponent denominators and numerators create no large integers.
* Agreement: for small bases and exponents, equality and ordering agree with the comparison that
  clears the exponent denominator, and the integer kernels agree with direct evaluation.
* Posit regressions: `pow`, `exp2`, `exp10`, their `Minus1` forms, `log2`, `log10` and their
  `Plus1` forms give the same codes as before the comparator change. The posit8 tables, and the
  digests of the posit16, posit32 and posit8 `pow` samples, were recorded with the previous
  comparator.

`check powers` runs these groups and prints the time of each.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
set_option compiler.extract_closed false

namespace FloatLibTests.Regression.RationalPower

open FloatLib.Numerics
open FloatLib.Numerics.RationalPower
open FloatLib.Floats.Formats.Posit
open FloatLibTests.Accounting

/-- The posit8 descriptor. -/
abbrev posit8 : Format := { bits := 8, bits_ge_two := by decide }

/-- The posit16 descriptor. -/
abbrev posit16 : Format := { bits := 16, bits_ge_two := by decide }

/-- The posit32 descriptor. -/
abbrev posit32 : Format := { bits := 32, bits_ge_two := by decide }

/-- The described power `root ^ numerator` as a rational. Tests use it only for small exponents. -/
def describedValue (exact : ExactRoot) : ℚ :=
  exact.root ^ exact.numerator

/--
The comparison used before the boundary-equality comparator, for a positive base: clear the
exponent denominator and compare exact rational powers.
-/
def referenceCompare (base exponent target : ℚ) : Ordering :=
  if target ≤ 0 then .gt else cmp (base ^ exponent.num) (target ^ exponent.den)

/-- Whether a small natural number is a perfect power, by search. -/
def isPerfectPower (degree value : Nat) : Bool :=
  (List.range (value + 1)).any fun root => root ^ degree == value

/-- The odd part of a positive natural number. -/
def oddPart (value : Nat) : Nat := Id.run do
  let mut odd := value
  for _ in List.range (value.log2 + 1) do
    if odd != 0 && odd % 2 == 0 then
      odd := odd / 2
  return odd

/-- A positive rational is a dyadic whose odd significand is below `2 ^ bits`. -/
def isSmallDyadic (value : ℚ) (bits : Nat) : Bool :=
  value.den == 2 ^ value.den.log2 && oddPart value.num.natAbs < 2 ^ bits

/-- Exact values, irrationality, and the exact dyadic builder. -/
def exactValueFailures : Thunk Nat := ⟨fun _ =>
  let half : ℚ := 1 / 2
  let threeHalves : ℚ := 3 / 2
  let positive (q : ℚ) : Model posit16 := Model.roundRat posit16 q
  countFailures
    [ exactRoot? 4 half == some { root := 2, numerator := 1 }
    , exactRoot? (9 / 4) threeHalves == some { root := 3 / 2, numerator := 3 }
    , exactRoot? (8 / 27) (-2 / 3) == some { root := 2 / 3, numerator := -2 }
    , exactRoot? 3 half == none
    , exactRoot? 2 (2047 / 2) == none
    , powEq 4 half 2
    , powEq (9 / 4) threeHalves (27 / 8)
    , powEq (8 / 27) (-2 / 3) (9 / 4)
    , !powEq 4 half (2 + 1 / 2 ^ 60)
    , !powEq 4 half (-2)
    , compare 4 half 2 == .eq
    , compare (9 / 4) threeHalves (27 / 8) == .eq
    , compare (8 / 27) (-2 / 3) (9 / 4) == .eq
    , compare 4 half (2 - 1 / 2 ^ 60) == .gt
    , compare 4 half (2 + 1 / 2 ^ 60) == .lt
    , compare (9 / 4) threeHalves (27 / 8 + 1 / 2 ^ 70) == .lt
    , compare 0 half 0 == .eq
    , compare 0 0 1 == .eq
    , ((exactRoot? 4 half).bind (·.toDyadic? 53)).map (·.toRat) == some 2
    , ((exactRoot? (9 / 4) threeHalves).bind (·.toDyadic? 53)).map (·.toRat) == some (27 / 8)
    , ((exactRoot? (9 / 4) threeHalves).bind (·.toDyadic? 1)).isNone
    , ((exactRoot? 2 (2 ^ 60)).bind (·.toDyadic? 53)) ==
        some { negative := false, significand := 1, exponent := 2 ^ 60 }
    , ((exactRoot? 2 (-2 ^ 60)).bind (·.toDyadic? 53)) ==
        some { negative := false, significand := 1, exponent := -2 ^ 60 }
    , ((exactRoot? (3 / 2) 2).bind (·.toDyadic? 53)).map (·.toRat) == some (9 / 4)
    , ((exactRoot? (1 / 3) 1).bind (·.toDyadic? 53)).isNone
    , (Model.pow (positive 4) (positive half)).toRat? == some 2
    , (Model.pow (positive (9 / 4)) (positive threeHalves)).toRat? == some (27 / 8)
    , (Model.log2 (positive 8)).toRat? == some 3
    ]⟩

/-- `(m * 2 ^ scale, (m + 1) * 2 ^ scale, (2 * m + 1) * 2 ^ (scale - 1))` for a binary64 cell. -/
def binary64Cell (significand scale : Nat) : ℚ × ℚ × ℚ :=
  ((significand : ℚ) * 2 ^ scale, ((significand + 1 : Nat) : ℚ) * 2 ^ scale,
    ((2 * significand + 1 : Nat) : ℚ) * 2 ^ scale / 2)

/--
Inputs whose exact powers are far too large to construct. Each power is compared with the two
binary64 values around it and with their midpoint.
-/
def hardFailures : Thunk Nat := ⟨fun _ =>
  let nearOne : ℚ := (2 ^ 52 + 1) / 2 ^ 52
  let large : ℚ := 2 ^ 60
  let x : ℚ := ((2 ^ 26 + 1) / 2 ^ 26) ^ 2
  let y : ℚ := (2 ^ 35 + 1) / 2
  let root2 : ℚ := 2047 / 2
  let (low1, high1, middle1) := binary64Cell 5660812128861721 317
  let (low2, high2, middle2) := binary64Cell 7115346577450741 686
  let (low3, high3, middle3) := binary64Cell 6369051672525772 971
  countFailures
    [ exactRoot? nearOne large == some { root := nearOne, numerator := 2 ^ 60 }
    , exactRoot? x y == some { root := (2 ^ 26 + 1) / 2 ^ 26, numerator := 2 ^ 35 + 1 }
    , ((exactRoot? nearOne large).bind (·.toDyadic? 53)).isNone
    , ((exactRoot? x y).bind (·.toDyadic? 53)).isNone
    , !powEq nearOne large low1
    , !powEq x y middle2
    , compare nearOne large low1 == .gt
    , compare nearOne large high1 == .lt
    , compare nearOne large middle1 == .lt
    , compare x y low2 == .gt
    , compare x y high2 == .lt
    , compare x y middle2 == .lt
    , compare 2 root2 low3 == .gt
    , compare 2 root2 high3 == .lt
    , compare 2 root2 middle3 == .gt
    , compare 3 (1 / 2 ^ 1074) 1 == .gt
    , compare 3 (1 / 2 ^ 1074) (1 + 1 / 2 ^ 52) == .lt
    , compare (1 / 3) (1 / 2 ^ 1074) 1 == .lt
    , compare 3 (2 ^ 1023) (2 ^ 1024) == .gt
    , compare 3 (-2 ^ 1023) (1 / 2 ^ 1074) == .lt
    ]⟩

/-- Bases `p / q` with `1 ≤ p, q ≤ 9`. -/
def smallBases : List ℚ :=
  (List.range 9).flatMap fun p => (List.range 9).map fun q =>
    ((p + 1 : Nat) : ℚ) / ((q + 1 : Nat) : ℚ)

/-- Exponents `n / d` with `-4 ≤ n ≤ 4` and `d ∈ {1, 2, 3, 4, 6}`. -/
def smallExponents : List ℚ :=
  (List.range 9).flatMap fun n => [1, 2, 3, 4, 6].map fun d => ((n : ℚ) - 4) / (d : ℚ)

/-- Targets compared with every small power, besides the power itself and its neighbors. -/
def genericTargets : List ℚ :=
  [-1, 0, 1 / 3, 1 / 2, 1, 3 / 2, 2, 5 / 2, 27 / 8, 4, 9, 100]

/--
For small bases and exponents, the descriptor, the equality test, the ordering and the dyadic
builder agree with exact rational evaluation.
-/
def smallFailures : Thunk Nat := ⟨fun _ => Id.run do
  let mut failures := 0
  for base in smallBases do
    for exponent in smallExponents do
      let rational := isPerfectPower exponent.den base.num.natAbs &&
        isPerfectPower exponent.den base.den
      let mut targets := genericTargets
      match exactRoot? base exponent with
      | some exact =>
        let value := describedValue exact
        failures := failures + failureCount
          (rational && exact.root ^ exponent.den == base && exact.numerator == exponent.num)
        targets := targets ++ [value, value + 1 / 2 ^ 20, value - 1 / 2 ^ 20]
        match exact.toDyadic? 10 with
        | some dyadic =>
          failures := failures + failureCount (dyadic.toRat == value && !dyadic.negative &&
            dyadic.significand < 2 ^ 13)
        | none => failures := failures + failureCount (!isSmallDyadic value 13)
      | none => failures := failures + failureCount !rational
      for target in targets do
        let expected := referenceCompare base exponent target
        failures := failures + failureCount (compare base exponent target == expected)
        failures := failures + failureCount (powEq base exponent target == (expected == .eq))
  return failures⟩

-- A symbolic degree must not force a seed power just to return zero or one.
example (degree : Nat) : IntegerRoot.newton (degree + 2) 0 = 0 := rfl

example (degree : Nat) : IntegerRoot.newton (degree + 2) 1 = 1 := rfl

/-- The integer kernels agree with direct evaluation, and huge exponents cost little. -/
def kernelFailures : Thunk Nat := ⟨fun _ => Id.run do
  let mut failures := 0
  for base in List.range 7 do
    for exponent in List.range 9 do
      for target in List.range 301 do
        failures := failures + failureCount
          (natPowEq base exponent target == decide (base ^ exponent = target))
  for base in List.range 6 do
    for exponent in List.range 11 do
      for cap in List.range 201 do
        let power := (base + 1) ^ exponent
        failures := failures + failureCount (cappedPow? (base + 1) exponent cap ==
          if power ≤ cap then some power else none)
  for degree in List.range 7 do
    for value in List.range 2001 do
      let expected := (List.range 46).find? fun root => root ^ (degree + 1) == value
      let expected := if degree = 0 then some value else expected
      failures := failures + failureCount (perfectRoot? (degree + 1) value == expected)
  return failures + countFailures
    [ !natPowEq 3 (2 ^ 100) (3 ^ 5)
    , natPowEq 1 (2 ^ 1000) 1
    , natPowEq 0 (2 ^ 1000) 0
    , natPowEq 2 64 (2 ^ 64)
    , !natPowEq 2 64 (2 ^ 64 + 1)
    , !natPowEq (2 ^ 26 + 1) (2 ^ 35 + 1) (2 ^ 700)
    , cappedPow? 2 100 (2 ^ 100) == some (2 ^ 100)
    , cappedPow? 2 100 (2 ^ 100 - 1) == none
    , cappedPow? 3 (2 ^ 80) (10 ^ 6) == none
    , cappedPow? 1 (2 ^ 80) 1 == some 1
    , perfectRoot? (2 ^ 1074) 3 == none
    , perfectRoot? (2 ^ 1074) 1 == some 1
    , perfectRoot? 2 (2 ^ 1074) == some (2 ^ 537)
    , perfectRoot? 3 (2 ^ 1074) == some (2 ^ 358)
    , perfectRoot? 4 (2 ^ 1074) == none
    , IntegerRoot.newton (2 ^ 1000) 0 == 0
    , IntegerRoot.newton (2 ^ 1000) 1 == 1
    ]⟩

/-- The reciprocal, offset and π adapters agree with the exact real values they describe. -/
def adapterFailures : Thunk Nat := ⟨fun _ =>
  let rationalTargets : List ℚ := [3, -3, 1 / 7, -2 / 5, 5 / 2]
  let boundaries : List ℚ :=
    [-4, -3, -5 / 2, -2 / 5, -1 / 3, -1 / 7, 0, 1 / 7, 1 / 3, 2 / 5, 1 / 2, 2, 5 / 2, 3, 7]
  let rational := rationalTargets.flatMap fun t => boundaries.map fun b =>
    compareReciprocal (fun q => cmp t q) b == cmp t⁻¹ b
  -- `1 / cos 1 = 1.85081571...`, `1 / sin (-1) = -1.18839510...`, `π = 3.14159265...`,
  -- and `sqrt 2 - 1 = 0.41421356...`.
  let secant := compareReciprocal (TrigonometricComparison.prepareCos 1 4).compare
  let cosecant := compareReciprocal (TrigonometricComparison.prepareSin (-1) 4).compare
  let pi := (TrigonometricComparison.prepareAtan2 (-1) 0 4).compare
  let rootTwoMinusOne := fun b : ℚ => compare 2 (1 / 2) (b + 1)
  countFailures (rational ++
    [ secant (185 / 100) == .gt
    , secant (1851 / 1000) == .lt
    , secant 0 == .gt
    , secant (-2) == .gt
    , cosecant (-119 / 100) == .gt
    , cosecant (-118 / 100) == .lt
    , cosecant 0 == .lt
    , cosecant 1 == .lt
    , pi (355 / 113) == .lt
    , pi (333 / 106) == .gt
    , pi (22 / 7) == .lt
    , pi 3 == .gt
    , rootTwoMinusOne (4142 / 10000) == .gt
    , rootTwoMinusOne (4143 / 10000) == .lt
    , rootTwoMinusOne 0 == .gt
    ])⟩

/-- A polynomial digest of result codes. -/
def digest (codes : List Nat) : Nat :=
  codes.foldl (fun acc code => (acc * 1000003 + code + 1) % 2 ^ 64) 0

/-- Two lowercase hex digits for a byte. -/
def hexByte (n : Nat) : String :=
  let digit (d : Nat) : Char := "0123456789abcdef".toList.getD d '0'
  String.ofList [digit (n / 16 % 16), digit (n % 16)]

/-- The eight unary posit functions that use the rational-power comparator, by name. -/
def unary {format : Format} (name : String) (x : Model format) : Model format :=
  match name with
  | "exp2" => Model.exp2 x
  | "exp10" => Model.exp10 x
  | "exp2Minus1" => Model.exp2Minus1 x
  | "exp10Minus1" => Model.exp10Minus1 x
  | "log2" => Model.log2 x
  | "log10" => Model.log10 x
  | "log2Plus1" => Model.log2Plus1 x
  | _ => Model.log10Plus1 x

/-- Sampled posit16 codes: the special values, then a stride through all codes. -/
def codes16 : List Nat :=
  [0, 1, 0x7fff, 0x8000, 0x8001, 0xffff, 0x4000, 0xc000] ++
    (List.range 120).map fun k => (k * 547 + 3) % 65536

/-- Sampled posit32 codes: the special values, then a stride through all codes. -/
def codes32 : List Nat :=
  [0, 1, 0x7fffffff, 0x80000000, 0x80000001, 0xffffffff, 0x40000000, 0xc0000000] ++
    (List.range 56).map fun k => (k * 76695841 + 12345) % 2 ^ 32

/-- Results of the eight unary functions on every posit8 code, two hex digits per code. -/
def unary8Expected : List (String × String) :=
  [ ("exp2",
      "4040404040404040404040404040404040404040404040404040404040404040" ++
      "4040404041414141414141414141414142424242424343434344444545464747" ++
      "48494a4a4b4c4d4f50525355585a5b5d60626466686a6c6e7072747678797a7b" ++
      "7c7e7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f" ++
      "8001010101010101010101010101010101010101010101010101010101010102" ++
      "04050607080a0c0e10121416181a1c1e20222325282a2b2d3031323233343537" ++
      "383839393a3a3a3b3b3c3c3c3c3d3d3d3d3e3e3e3e3e3e3f3f3f3f3f3f3f3f3f" ++
      "3f3f3f4040404040404040404040404040404040404040404040404040404040")
  , ("exp10",
      "4040404040404040404040404040404040404040404040404040404141414141" ++
      "4141424242424242434343444445454646474849494a4b4c4d4f505253555759" ++
      "5a5d6062646567696a6e707274757778797b7c7d7e7e7f7f7f7f7f7f7f7f7f7f" ++
      "7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f" ++
      "8001010101010101010101010101010101010101010101010101010101010101" ++
      "010101010101010101010102020304050707090a0c0e0f121517191a1c1d1f22" ++
      "2527292a2b2d2f31323334353537383839393a3a3a3b3b3c3c3c3c3d3d3d3d3e" ++
      "3e3e3e3f3f3f3f3f3f4040404040404040404040404040404040404040404040")
  , ("exp2Minus1",
      "00010203040405060708090a0b0c0d0e0f0f101112131415161718191a1b1c1d" ++
      "1e1e1f202121222324252728292a2a2b2c2e2f31313233343537393a3b3c3d3f" ++
      "404143454748494b4c4f515356595a5c5f616466686a6c6e7072747678797a7b" ++
      "7c7e7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f" ++
      "80c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0" ++
      "c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c1c1c1c1c2c2c2c3c3c4c4c5c5c6c6c7c7" ++
      "c8c9c9cacbcccdcecfcfd0d0d1d2d4d5d6d6d7d8d8dadbdcdddedfdfe0e1e1e2" ++
      "e3e3e4e5e7e7e8e9eaebecedeeeff0f1f1f2f3f4f5f6f7f8f9fafbfcfcfdfeff")
  , ("exp10Minus1",
      "00010304050607080a0b0c0d0e0f111315161718191a1b1c1d1e1f2022242729" ++
      "2a2b2d2e2f30313233343638393a3a3b3c3f404243444648494b4d4f51535557" ++
      "595c6062646567696a6e707274757778797b7c7d7e7e7f7f7f7f7f7f7f7f7f7f" ++
      "7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f" ++
      "80c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0" ++
      "c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c1c1c1c1" ++
      "c2c2c2c2c3c3c4c4c5c5c6c6c7c7c8c9cacbcbcccdcececfd0d1d2d3d4d5d5d6" ++
      "d7d9dbdddfe0e1e2e3e4e5e6e7e8e9eaebedeff1f2f3f4f5f6f8f9fafbfcfdff")
  , ("log2",
      "809e9fa0a0a1a2a3a4a5a5a6a6a7a7a8a8a9a9aaaaababacacadadaeaeafafb0" ++
      "b0b1b1b2b2b3b3b4b4b5b5b6b6b7b7b8b8b9bbbcbdbebebfc0c3c5c7cbced4dc" ++
      "002b3237393b3d3f40414344454646474849494a4a4b4b4c4c4d4d4e4e4f4f50" ++
      "505151525253535454555556565757585859595a5a5b5b5c5c5d5e5f60606162" ++
      "8080808080808080808080808080808080808080808080808080808080808080" ++
      "8080808080808080808080808080808080808080808080808080808080808080" ++
      "8080808080808080808080808080808080808080808080808080808080808080" ++
      "8080808080808080808080808080808080808080808080808080808080808080")
  , ("log10",
      "80aaacadaeafb0b0b2b2b3b3b4b5b5b6b6b7b7b7b8b8b9b9bababbbbbcbdbdbe" ++
      "bebfbfbfc0c0c1c1c2c2c3c4c4c5c5c6c6c7c8c9cacbcdcdced0d3d6d8dce1e5" ++
      "001f24292b2d303132333536373839393a3a3b3c3c3d3e3e3e3f404041414141" ++
      "424243444445454646474848484949494a4a4b4c4c4d4d4e4e50505152535456" ++
      "8080808080808080808080808080808080808080808080808080808080808080" ++
      "8080808080808080808080808080808080808080808080808080808080808080" ++
      "8080808080808080808080808080808080808080808080808080808080808080" ++
      "8080808080808080808080808080808080808080808080808080808080808080")
  , ("log2Plus1",
      "0001020304050607090a0b0c0d0e0f1012131415161718191a1b1c1d1e1f2022" ++
      "2325262728292a2a2b2c2d2f303131323233353637383839393a3b3c3d3e3f3f" ++
      "40414142434344444546464748484949494a4a4b4b4c4c4c4d4d4e4e4f4f5050" ++
      "505151525253535454555556565757585859595a5a5b5b5c5c5d5e5f60616162" ++
      "8080808080808080808080808080808080808080808080808080808080808080" ++
      "8080808080808080808080808080808080808080808080808080808080808080" ++
      "80b0b4b6b8bbbdbec0c1c3c4c5c6c7c9cbcccdcececfd0d2d4d4d5d6d7d8d9db" ++
      "dcdedfe1e2e3e4e5e6e7e8e9eaebecedeef0f1f2f3f4f5f6f7f9fafbfcfdfeff")
  , ("log10Plus1",
      "000102020304050607070809090b0b0d0d0e0f0f0f101112131415161718191a" ++
      "1b1c1c1d1d1d1e1e1f1f2021222223242426272829292a2b2b2c2d2f30303131" ++
      "3232333435353637373839393a3a3a3b3b3c3c3d3e3e3e3f3f40404141414142" ++
      "424343444445464647474848484949494a4a4b4c4c4d4d4e4e50505152535456" ++
      "8080808080808080808080808080808080808080808080808080808080808080" ++
      "8080808080808080808080808080808080808080808080808080808080808080" ++
      "80bec2c4c6c8cacdcecfd0d2d3d4d6d7d8d9dadbdcdedfe0e1e1e2e2e3e3e3e4" ++
      "e5e6e7e8e9eaebecedeeeff0f1f1f1f2f3f3f5f5f7f7f8f9f9fafbfcfdfefeff")
  ]

/-- Digests of posit8 `pow` over every base code, for each sampled exponent code. -/
def pow8Expected : List (Nat × Nat) :=
  [ (0x00, 11353298362059313024)
  , (0x01, 3052838385840013120)
  , (0x10, 6009788128043438417)
  , (0x20, 1779106712715226915)
  , (0x28, 14110202142731840693)
  , (0x30, 3336746328913118346)
  , (0x38, 14406275719556944520)
  , (0x40, 13410134780872709760)
  , (0x44, 10047086557456016885)
  , (0x48, 18381368348963288556)
  , (0x50, 10313713027426794142)
  , (0x58, 17773477228194906632)
  , (0x60, 10307961691000492558)
  , (0x68, 3187965846563089642)
  , (0x70, 1099585855068084736)
  , (0x7f, 1099585855068084736)
  , (0x80, 9661672770166364672)
  , (0x81, 13038224462545670016)
  , (0xa0, 11204766558077797140)
  , (0xc0, 3070154290658289408)
  , (0xd0, 13137439699634907110)
  , (0xe0, 1425951434198010674)
  , (0xff, 11621624792344884416)
  ]

/-- Digests of the eight unary functions on the sampled posit16 codes. -/
def unary16Expected : List (String × Nat) :=
  [ ("exp2", 16517446429414469152)
  , ("exp10", 6951480158044577128)
  , ("exp2Minus1", 16782183051762519430)
  , ("exp10Minus1", 3281041180409230637)
  , ("log2", 9223556439741562221)
  , ("log10", 2900125142584611156)
  , ("log2Plus1", 2118560720971867282)
  , ("log10Plus1", 1165492140899108956)
  ]

/-- Digests of the eight unary functions on the sampled posit32 codes. -/
def unary32Expected : List (String × Nat) :=
  [ ("exp2", 14519322005639780407)
  , ("exp10", 2276250251085722837)
  , ("exp2Minus1", 5404425075543478935)
  , ("exp10Minus1", 10578320637070567270)
  , ("log2", 15299990363032185942)
  , ("log10", 1235773953457133901)
  , ("log2Plus1", 18213608170128205281)
  , ("log10Plus1", 88479368701456737)
  ]

/-- Digest of posit16 `pow` over the sampled base and exponent codes. -/
def pow16Expected : Nat := 8371302416509139840

/-- Digest of posit32 `pow` over the sampled base and exponent codes. -/
def pow32Expected : Nat := 5007826292605556495

/-- Posit power and logarithm codes are unchanged by the comparator switch. -/
def positFailures : Thunk Nat := ⟨fun _ =>
  let table8 := unary8Expected.map fun (name, expected) =>
    String.join ((List.range 256).map fun code =>
      hexByte (unary name (Model.ofNatBits (format := posit8) code)).toNatBits) == expected
  let pow8 := pow8Expected.map fun (exponent, expected) =>
    digest ((List.range 256).map fun base =>
      (Model.pow (Model.ofNatBits (format := posit8) base)
        (Model.ofNatBits exponent)).toNatBits) == expected
  let unary16 := unary16Expected.map fun (name, expected) =>
    digest (codes16.map fun code =>
      (unary name (Model.ofNatBits (format := posit16) code)).toNatBits) == expected
  let unary32 := unary32Expected.map fun (name, expected) =>
    digest (codes32.map fun code =>
      (unary name (Model.ofNatBits (format := posit32) code)).toNatBits) == expected
  let pow16 := digest ((codes16.take 24).flatMap fun base => (codes16.take 24).map fun exponent =>
    (Model.pow (Model.ofNatBits (format := posit16) base)
      (Model.ofNatBits exponent)).toNatBits) == pow16Expected
  let pow32 := digest ((codes32.take 12).flatMap fun base => (codes32.take 12).map fun exponent =>
    (Model.pow (Model.ofNatBits (format := posit32) base)
      (Model.ofNatBits exponent)).toNatBits) == pow32Expected
  countFailures (table8 ++ pow8 ++ unary16 ++ unary32 ++ [pow16, pow32])⟩

/-- The named groups run by `check powers`, in order. -/
def checks : List (String × Thunk Nat) :=
  [ ("exactValues", exactValueFailures)
  , ("hardPowers", hardFailures)
  , ("smallPowers", smallFailures)
  , ("integerKernels", kernelFailures)
  , ("comparatorAdapters", adapterFailures)
  , ("positRegressions", positFailures)
  ]

end FloatLibTests.Regression.RationalPower
