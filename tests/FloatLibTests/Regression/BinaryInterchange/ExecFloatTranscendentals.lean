/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals
public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals
public import FloatLibTests.Accounting
public import FloatLibTests.Fixtures.Transcendentals
public import FloatLibTests.Regression.BinaryInterchange.Harness

/-!
# Regression checks for format-generic executable transcendentals

These checks evaluate the fixtures of `FloatLibTests.Fixtures.Transcendentals`: named inputs with
their MPFR 4.1.0 results (huge sine and cosine arguments, earlier misroundings and the branch
boundaries of the exponential), the special-value matrix in six formats, and the signaling-NaN and
payload matrix that MPFR cannot check. They also check the cached constants of
`Numerics.Enclosure.Constants` against an independent series at every precision to 128 bits and at
doublings to 32768, and `Model.pi` against MPFR in ten layouts.

Other checks confirm that wide exponent fields keep generation cheap, that sine and cosine reduce
huge binary128 and binary256 arguments at the first attempt and stop at their resource limit, and
that the certified stable functions keep tiny inputs and signed zeros and reject domains or
refinement budgets that cannot certify a result. The last ones cover the certified power's
accepted and rejected cases, and confirm that the configured `exp`, `log`, and `pow` with
`certify := true` return the certified result or the failure, never the approximation.

Run the native report with:

```text
lake -d tests exe check transcendentals
```

`lake -d tests exe check reduction` checks the slow fixtures, which compute the `2^20`- and
`2^21`-bit levels of `2 / pi`.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only. Elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.ExecFloatTranscendentals

abbrev f32 := FloatFormat.binary32

open FloatLibTests.Accounting
open FloatLibTests.Fixtures.Transcendentals

/-- FloatLib's default result of a fixture operation. -/
def applyOperation {fmt : FloatFormat} (operation : Operation) (arguments : List (Model fmt)) :
    Model fmt :=
  let x := arguments.getD 0 (Model.posZero fmt)
  match operation with
  | .exp => Model.exp x
  | .log => Model.log x
  | .sin => Model.sin x
  | .cos => Model.cos x
  | .sinh => Model.sinh x
  | .cosh => Model.cosh x
  | .tanh => Model.tanh x
  | .pow => Model.pow x (arguments.getD 1 (Model.posZero fmt))

/--
A fixture holds when FloatLib returns the MPFR encoding or, for a recorded known failure, exactly
the encoding recorded as today's result.
-/
def fixtureHolds (fixture : Fixture) : Bool :=
  let fmt := fixture.format.descriptor
  let result := (applyOperation fixture.operation
    (fixture.arguments.map (Model.ofNatBits (fmt := fmt)))).toNatBits
  match fixture.knownFailure with
  | none => result == fixture.expected
  | some failure => result == failure.result && failure.result != fixture.expected

/-- Every input with an MPFR 4.1.0 result, matched bit for bit or at its recorded failure. -/
def failMpfrFixtures : Thunk Nat := ⟨fun _ =>
  countWhereFailures mpfrFixtures fixtureHolds⟩

/-- A special operand or result in `fmt`. -/
def specialValue (fmt : FloatFormat) : Special → Model fmt
  | .positiveZero => Model.posZero fmt
  | .negativeZero => Model.negZero fmt
  | .one => Model.posOne fmt
  | .negativeOne => Model.negOne fmt
  | .two => Model.roundDyadic fmt { negative := false, significand := 2, exponent := 0 }
  | .negativeTwo => Model.roundDyadic fmt { negative := true, significand := 2, exponent := 0 }
  | .three => Model.roundDyadic fmt { negative := false, significand := 3, exponent := 0 }
  | .negativeThree => Model.roundDyadic fmt { negative := true, significand := 3, exponent := 0 }
  | .half => Model.roundDyadic fmt { negative := false, significand := 1, exponent := -1 }
  | .negativeHalf => Model.roundDyadic fmt { negative := true, significand := 1, exponent := -1 }
  | .positiveInfinity => Model.posInf fmt
  | .negativeInfinity => Model.negInf fmt
  | .largest => Model.maxFinite fmt false
  | .negativeLargest => Model.maxFinite fmt true
  | .smallestSubnormal => Model.posMinSubnormal fmt
  | .negativeSmallestSubnormal => Model.neg (Model.posMinSubnormal fmt)
  | .canonicalNaN => Model.canonicalNaN fmt

/-- Formats of the special-value matrix, including a custom four-bit-fraction format. -/
def specialValueFormats : List FloatFormat :=
  [.binary16, .bfloat16, .binary32, .binary64, .binary128, .ieee 3 4]

/-- One special-value row holds in `fmt` when the result has the expected encoding. -/
def specialCaseHolds (fmt : FloatFormat) (row : SpecialCase) : Bool :=
  Harness.sameBits (applyOperation row.operation (row.arguments.map (specialValue fmt)))
    (specialValue fmt row.result)

/-- The special-value matrix in every format of `specialValueFormats`. -/
def failSpecialValueMatrix : Thunk Nat := ⟨fun _ =>
  specialValueFormats.foldl
    (fun failures fmt => failures + countWhereFailures specialCases (specialCaseHolds fmt)) 0⟩

/-- A NaN operand of the matrix in `fmt`. -/
def nanValue (fmt : FloatFormat) (operand : NaNOperand) : Model fmt :=
  if operand.signaling then
    Model.ofFields fmt operand.negative fmt.expAllOnesNat operand.payload
  else
    Model.propagatedNaN fmt operand.negative operand.payload

/-- A `pow` operand of the NaN matrix in `fmt`. -/
def powOperand (fmt : FloatFormat) : PowOperand → Model fmt
  | .nan operand => nanValue fmt operand
  | .special value => specialValue fmt value

/-- The expected `pow` result of a NaN-matrix row in `fmt`. -/
def powNaNExpected (fmt : FloatFormat) (row : PowNaNCase) : Model fmt :=
  match row.result with
  | .one => Model.posOne fmt
  | .quietBase => Model.quietNaN (powOperand fmt row.base)
  | .quietExponent => Model.quietNaN (powOperand fmt row.exponent)

/-- Unary functions keep the sign and payload of a NaN and quiet it, and `pow` follows its rows. -/
def nanPayloadFailures (fmt : FloatFormat) : Nat :=
  countPairFailures unaryOperations unaryNaNOperands (fun operation operand =>
    Harness.sameBits (applyOperation operation [nanValue fmt operand])
      (Model.quietNaN (nanValue fmt operand))) +
  countWhereFailures powNaNCases fun row =>
    Harness.sameBits (Model.pow (powOperand fmt row.base) (powOperand fmt row.exponent))
      (powNaNExpected fmt row)

/--
The NaN matrix in the five catalog formats wide enough for its payloads, and literal binary64
encodings: a signaling NaN with payload `0x42` raised to either zero, and its `rootN` at degree
zero, keep the payload.
-/
def failNaNPayloads : Thunk Nat := ⟨fun _ =>
  let signaling := Model.ofNatBits (fmt := FloatFormat.binary64) 0x7ff0000000000042
  [FloatFormat.binary16, .bfloat16, .binary32, .binary64, .binary128].foldl
    (fun failures fmt => failures + nanPayloadFailures fmt) 0 +
  countFailures
    [ (Model.pow signaling (Model.posZero _)).toNatBits == 0x7ff8000000000042
    , (Model.pow signaling (Model.negZero _)).toNatBits == 0x7ff8000000000042
    , (Model.rootN signaling 0).toNatBits == 0x7ff8000000000042
    ]⟩

/-! ## Proved constants -/

/--
Directed bounds of `2 ^ scale` times `atan (1 / m)` (`alternating`) or `atanh (1 / m)`, for
`m ≥ 2`, from the series `sum_k (±1)^k / ((2k + 1) m^(2k+1))`, independent of the binary splitting
under test. Each term is rounded down for the lower and up for the upper bound. An even number of
alternating terms leaves a remainder between zero and the first omitted term, which is below one
unit. The atanh remainder is below `1 / (1 - m^-2)` times that term: `9/8` for `m = 3`, the only
atanh series used, and at most `4/3` for every `m ≥ 2`.
-/
def seriesBounds (m scale : Nat) (alternating : Bool) : Int × Int := Id.run do
  let one := 2 ^ scale
  let half := scale / (2 * Nat.log2 m) + 2
  let terms := half + half % 2
  let mut power := m
  let mut lower : Int := 0
  let mut upper : Int := 0
  for k in [0:terms] do
    let denominator := power * (2 * k + 1)
    let down : Int := one / denominator
    let up : Int := (one + denominator - 1) / denominator
    if alternating && k % 2 == 1 then
      lower := lower - up
      upper := upper - down
    else
      lower := lower + down
      upper := upper + up
    power := power * (m * m)
  return (lower, upper + 2)

/-- Bounds of `π / 2 * 2 ^ scale` from `π / 2 = 8 atan (1/5) - 2 atan (1/239)`. -/
def halfPiSeriesBounds (scale : Nat) : Int × Int :=
  let five := seriesBounds 5 scale true
  let large := seriesBounds 239 scale true
  (8 * five.1 - 2 * large.2, 8 * five.2 - 2 * large.1)

/-- Bounds of `log 2 * 2 ^ scale` from `log 2 = 2 atanh (1/3)`. -/
def ln2SeriesBounds (scale : Nat) : Int × Int :=
  let third := seriesBounds 3 scale false
  (2 * third.1, 2 * third.2)

/-- `value ≤ c * 2 ^ bits < value + 2`, given bounds of `c * 2 ^ (bits + 64)`. -/
def lowerWithinTwo (bounds : Int × Int) (value : Nat) : Bool :=
  decide ((value : Int) * 2 ^ 64 ≤ bounds.1) && decide (bounds.2 < ((value : Int) + 2) * 2 ^ 64)

/-- `|value - c * 2 ^ bits| < 1`, given bounds of `c * 2 ^ (bits + 64)`. -/
def withinOne (bounds : Int × Int) (value : Nat) : Bool :=
  decide (((value : Int) - 1) * 2 ^ 64 < bounds.1) &&
    decide (bounds.2 < ((value : Int) + 1) * 2 ^ 64)

/--
`value ≤ 2 / π * 2 ^ bits < value + 2`, given bounds `(L, H)` of `π / 2 * 2 ^ (bits + 64)`:
`2 / π * 2 ^ bits = 2 ^ (2 bits + 64) / (π / 2 * 2 ^ (bits + 64))`.
-/
def reciprocalLowerWithinTwo (bits : Nat) (bounds : Int × Int) (value : Nat) : Bool :=
  decide ((value : Int) * bounds.2 ≤ 2 ^ (2 * bits + 64)) &&
    decide (2 ^ (2 * bits + 64) < ((value : Int) + 2) * bounds.1)

/-- Precisions at which the cached constants are checked: every size to 128, then doublings. -/
def constantPrecisions : List Nat :=
  List.range 129 ++ [192, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768]

open FloatLib.Numerics.Enclosure.Constants in
/-- The constants at one precision: direct, cached, and nearest reads. -/
def constantFailures (bits : Nat) : Nat :=
  let halfPi := halfPiSeriesBounds (bits + 64)
  let ln2 := ln2SeriesBounds (bits + 64)
  let level := piLevel bits
  countFailures
    [ lowerWithinTwo halfPi level.halfPi
    , reciprocalLowerWithinTwo bits halfPi level.twoOverPi
    , lowerWithinTwo ln2 (ln2Fixed bits)
    , lowerWithinTwo halfPi (halfPiLower bits)
    , reciprocalLowerWithinTwo bits halfPi (twoOverPiLower bits)
    , lowerWithinTwo ln2 (ln2Lower bits)
    , withinOne ln2 (ln2Faithful bits)
    ]

open FloatLib.Numerics.Enclosure.Constants in
/--
The cached constants are within their proved bounds at every checked precision, against the
independent series above. The pinned binary32 table keeps its nearest `log 2` at 48 bits, which
equals `ln2Lower 48`. It is checked against the proved two-unit bound, not for equality.
-/
def failProvedConstants : Thunk Nat := ⟨fun _ =>
  let config := Model.Transcendentals.Config.binary32
  let ln2 : Int := ln2Lower config.fixed
  constantPrecisions.foldl (fun failures bits => failures + constantFailures bits) 0 +
  countFailures
    [ decide (0 ≤ config.ln2Fixed - ln2) && decide (config.ln2Fixed - ln2 ≤ 2)
    ]⟩

/--
`Model.pi` against MPFR 4.1.0 `const_pi`: the catalog formats, the smallest IEEE layout `ieee 2 1`
(largest finite value 3), two small custom layouts, and the finite-only E4M3 layout, which takes
the exact comparator. The comparator alone also rounds binary64 and `ieee 2 1` correctly.
-/
def failPi : Thunk Nat := ⟨fun _ =>
  let quarter := FloatLib.Numerics.TrigonometricComparison.prepareArctan 1 16
  let compare (boundary : ℚ) : Ordering := quarter.compare (boundary / 4)
  countFailures
    [ (Model.pi FloatFormat.binary16).toNatBits == 0x4248
    , (Model.pi FloatFormat.bfloat16).toNatBits == 0x4049
    , (Model.pi FloatFormat.binary32).toNatBits == 0x40490fdb
    , (Model.pi FloatFormat.binary64).toNatBits == 0x400921fb54442d18
    , (Model.pi FloatFormat.binary128).toNatBits == 0x4000921fb54442d18469898cc51701b8
    , (Model.pi FloatFormat.binary256).toNatBits ==
        0x40000921fb54442d18469898cc51701b839a252049c1114cf98e804177d4c762
    , (Model.pi (FloatFormat.ieee 2 1)).toNatBits == 0x5
    , (Model.pi (FloatFormat.ieee 3 4)).toNatBits == 0x49
    , (Model.pi (FloatFormat.ieee 4 3)).toNatBits == 0x45
    , (Model.pi (FloatFormat.finiteMaxNaN 4 3)).toNatBits == 0x45
    , (Model.AlgebraicRounding.round FloatFormat.binary64 false compare).toNatBits ==
        0x400921fb54442d18
    , (Model.AlgebraicRounding.round (FloatFormat.ieee 2 1) false compare).toNatBits == 0x5
    ]⟩

abbrev wideExponentFormat : FloatFormat :=
  FloatFormat.ieee 20 37

/--
Check that generated data depends on the fraction width only.

A wide exponent field once forced a `pi / 2` with hundreds of thousands of bits into the
configuration. Reduction now reads the cached `2 / pi` at the size each argument needs, and the
configuration holds no constant of `pi`.
-/
def failGeneratedScale : Thunk Nat := ⟨fun _ =>
  let policy := Model.Transcendentals.GenerationPolicy.standard
  let config := Model.Transcendentals.Config.generated wideExponentFormat
  countFailures
    [ config.fixed == wideExponentFormat.fracWidth + policy.guardBits
    , config.sinCoeffsAsc.length == wideExponentFormat.fracWidth / 6 + 8
    ]⟩

/-- A caller-supplied configuration with few guard bits still reduces large arguments. -/
def failExplicitConfigurationReduction : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.ieee 5 7
  let config := Model.Transcendentals.Config.generatedWith { guardBits := 2 } fmt
  let large := Model.roundDyadic fmt { negative := false, significand := 3, exponent := 13 }
  let tiny := Model.posMinSubnormal fmt
  let result := Model.sinCosWith config large
  countFailures
    [ Model.isFinite result.1
    , Model.isFinite result.2
    , Harness.sameBits (Model.sinCosWith config tiny).1 tiny
    , Harness.sameBits (Model.sinCosWith config tiny).2 (Model.posOne fmt)
    ]⟩

/-- How the default sine and cosine kernel reduces a finite argument. -/
inductive ReductionOutcome where
  /-- No reduction: zero, an exceptional value, or an argument below three quarters. -/
  | exact
  /-- The first window would read a cache level above `trigReductionLevelLimit`. -/
  | beyondLimit
  /-- Attempt `attempt` is the first accepted one, and `fuel` doublings stay within the limit. -/
  | accepted (attempt fuel : Nat)
  /-- None of the `fuel + 1` attempts within the limit is accepted. -/
  | rejected (fuel : Nat)
  deriving DecidableEq, Repr

open FloatLib.Numerics.Enclosure.ArgumentReduction in
/--
How `Model.Transcendentals.sinCosScaledWith` reduces a dyadic argument for `fmt`: zero and
arguments below three quarters need no reduction. Otherwise `fuelWithin?` gives the doublings
within `trigReductionLevelLimit`, and the first accepted attempt is found among them.
-/
def dyadicReduction (fmt : FloatFormat) (value : FloatLib.Numerics.Dyadic) : ReductionOutcome :=
  let m := value.significand
  let leading := Int.ofNat (Nat.log2 m) + value.exponent
  let bits := fmt.fracWidth + 1 + Model.Transcendentals.trigGuardBits
  let p := Nat.log2 m + 1
  if m == 0 || Model.Transcendentals.belowThreeQuarters m leading then
    .exact
  else
    match fuelWithin? value.exponent p bits Model.Transcendentals.trigReductionLevelLimit
        Model.Transcendentals.trigReductionFuel with
    | none => .beyondLimit
    | some fuel =>
        let accepted (attempt : Nat) : Bool :=
          (reduceWindow m value.exponent (attemptWindow p bits attempt)).accepts bits
        match (List.range (fuel + 1)).find? accepted with
        | some attempt => .accepted attempt fuel
        | none => .rejected fuel

/-- How the default sine and cosine kernel reduces `x`. Exceptional values need no reduction. -/
def reduction {fmt : FloatFormat} (x : Model fmt) : ReductionOutcome :=
  match Model.toDyadic? x with
  | none => .exact
  | some exact => dyadicReduction fmt exact

/--
Reduction sizes its window from the argument and checks its resource limit attempt by attempt.

`halfPiLower 2000 * 2^-2000` lies within `2^-1999` of `pi / 2`. Its 2001-bit significand sets the
window, so one attempt keeps the tiny remainder: sine rounds to one and cosine is a tiny positive
number. One, written with the 65,484-bit significand `2^65483`, has a first window of 131,073 bits
at level 12. Its fourth doubling would need level 16, so three doublings are allowed, and the first
attempt gives the MPFR 4.1.0 binary64 sine and cosine of one. The largest finite `ieee 31 23`
argument would need a cache level of about `2^30` bits and gives the invalid result at once. So do
`1.5 * 2^2097046`, the first binade of `ieee 31 23` whose first window needs a level above
`trigReductionLevelLimit`, and the dyadic `2^2097152`.
-/
def failReductionProgress : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.binary128
  let halfPi := FloatLib.Numerics.Enclosure.Constants.halfPiLower 2000
  let nearHalfPi : FloatLib.Numerics.Dyadic :=
    { negative := false, significand := halfPi, exponent := -2000 }
  let result := Model.Transcendentals.sinCosScaledWith fmt
    (Model.Transcendentals.Config.forFormat fmt) nearHalfPi
  let double := FloatFormat.binary64
  let longOne : FloatLib.Numerics.Dyadic :=
    { negative := false, significand := 2 ^ 65483, exponent := -65483 }
  let one := Model.Transcendentals.sinCosScaledWith double
    (Model.Transcendentals.Config.forFormat double) longOne
  let wide := FloatFormat.ieee 31 23
  let largest := Model.maxFinite wide false
  let pastLimit : Model wide := Model.ofNatBits 0x200fffcac00000
  let beyondLimit : FloatLib.Numerics.Dyadic :=
    { negative := false, significand := 1, exponent := 2097152 }
  let config := Model.Transcendentals.Config.forFormat fmt
  let beyond := Model.Transcendentals.sinCosScaledWith fmt config beyondLimit
  countFailures
    [ Harness.sameBits result.1 (Model.posOne fmt)
    , Model.isFinite result.2 && !Model.isZero result.2 && !Model.signBit result.2
    , one.1.toNatBits == 0x3feaed548f090cee
    , one.2.toNatBits == 0x3fe14a280fb5068c
    , dyadicReduction double longOne == .accepted 0 3
    , Model.isNaN (Model.sin largest)
    , Model.isNaN (Model.cos largest)
    , Model.isNaN (Model.sin pastLimit) && Model.isNaN (Model.cos pastLimit)
    , reduction pastLimit == .beyondLimit
    , Harness.sameBits (Model.exp largest) (Model.posInf wide)
    , Model.isNaN beyond.1 && Model.isNaN beyond.2
    , dyadicReduction fmt beyondLimit == .beyondLimit
    ]⟩

/--
No finite binary128 or binary256 argument at `±2^4096`, `±2^4097` and `±2^5000`, nor the largest
finite values, gives a NaN sine or cosine. A fixed exponent budget once rejected binary128
arguments from `2^4097` on.
-/
def failLargeArguments : Thunk Nat := ⟨fun _ =>
  let finite {fmt : FloatFormat} (x : Model fmt) : Bool :=
    let result := Model.sinCos x
    Model.isFinite result.1 && Model.isFinite result.2
  let check (fmt : FloatFormat) : List Bool :=
    ([4096, 4097, 5000].flatMap fun exponent =>
      let x := Model.roundDyadic fmt { negative := false, significand := 1, exponent }
      [finite x, finite (Model.neg x)]) ++
    [finite (Model.maxFinite fmt false), finite (Model.maxFinite fmt true)]
  countFailures (check .binary128 ++ check .binary256)⟩

/--
The sine and cosine rows of `fixtures` that the first reduction window does not settle: those
retried, rejected, or beyond the level limit.
-/
def reductionsBeyondFirstAttempt (fixtures : List Fixture) : Nat :=
  countWhereFailures fixtures fun fixture =>
    match fixture.operation with
    | .sin | .cos =>
        let fmt := fixture.format.descriptor
        match reduction (Model.ofNatBits (fmt := fmt) (fixture.arguments.getD 0 0)) with
        | .exact | .accepted 0 _ => true
        | _ => false
    | _ => true

/--
Every sine and cosine fixture reduces at its first attempt. The fixtures include the two inputs
of each format closest to a multiple of `pi / 2` in the hard-case corpus, and the start window
`startWindow p bits` covers them all. A retry would be slower but not wrong. The count is the
number of fixtures that the first window does not settle.
-/
def failReductionAttempts : Thunk Nat := ⟨fun _ =>
  reductionsBeyondFirstAttempt mpfrFixtures⟩

/--
The rows of `slowTrigReduction`, whose reduction computes the `2^20`- and `2^21`-bit levels of
`2 / pi`, match MPFR and reduce at their first attempt. At `1.5 * 2^2095186` three doublings stay
within `trigReductionLevelLimit`. At `1.5 * 2^2097045` the first window already needs all `2^21`
bits of the last permitted level, so none does.
-/
def failSlowTrigReduction : Thunk Nat := ⟨fun _ =>
  let wide := FloatFormat.ieee 31 23
  countWhereFailures slowTrigReduction fixtureHolds +
    reductionsBeyondFirstAttempt slowTrigReduction +
    countFailures
      [ reduction (Model.ofNatBits (fmt := wide) 0x200ffc28c00000) == .accepted 0 3
      , reduction (Model.ofNatBits (fmt := wide) 0x200fffca400000) == .accepted 0 0
      ]⟩

/--
Tiny dyadic arguments of the public reduction entry point, without work proportional to their
exponent. `(2^53 + 3) * 2^-110` is a binary64 rounding midpoint, and its sine lies just below it.
Written with a 113-bit significand, or raised by `2^-176`, the midpoint has too many bits for the
quarter-unit shortcut of `tinySine`, so the Taylor sum over every sine coefficient decides the
rounding, and the argument alone would round up. A one-bit argument with exponent `-2^30` underflows
to zero at once.
-/
def failTinyDyadicSine : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.binary64
  let config := Model.Transcendentals.Config.forFormat fmt
  let midpoint : FloatLib.Numerics.Dyadic :=
    { negative := false, significand := 2 ^ 53 + 3, exponent := -110 }
  let longMidpoint : FloatLib.Numerics.Dyadic :=
    { negative := false, significand := (2 ^ 53 + 3) * 2 ^ 59, exponent := -169 }
  let aboveMidpoint : FloatLib.Numerics.Dyadic :=
    { negative := false, significand := (2 ^ 53 + 3) * 2 ^ 66 + 1, exponent := -176 }
  let farBelow : FloatLib.Numerics.Dyadic :=
    { negative := false, significand := 1, exponent := -1073741824 }
  let sine (value : FloatLib.Numerics.Dyadic) : Nat :=
    (Model.Transcendentals.sinCosScaledWith fmt config value).1.toNatBits
  countFailures
    [ sine midpoint == 0x3c60000000000001
    , sine { midpoint with negative := true } == 0xbc60000000000001
    , sine longMidpoint == 0x3c60000000000001
    , sine { longMidpoint with negative := true } == 0xbc60000000000001
    , sine aboveMidpoint == 0x3c60000000000001
    , sine { aboveMidpoint with negative := true } == 0xbc60000000000001
    , sine farBelow == 0
    , Harness.sameBits (Model.Transcendentals.sinCosScaledWith fmt config farBelow).2
        (Model.posOne fmt)
    ]⟩

/-- Tiny arguments survive exact enclosure arithmetic, including their sign. -/
def certifiedStableFailures (fmt : FloatFormat) : Nat :=
  let positive := Model.roundDyadic fmt
    { negative := false, significand := 1, exponent := -(fmt.fracWidth + 3 : Int) }
  let acceptedAs (actual : Except Model.Transcendentals.Certified.Failure (Model fmt))
      (expected : Model fmt) : Bool :=
    match actual with
    | .error _ => false
    | .ok result => Harness.sameBits result expected
  countFailures <|
    [positive, Model.neg positive, Model.posZero fmt, Model.negZero fmt].flatMap fun x =>
      [ acceptedAs (Model.Transcendentals.Certified.expMinus1 x) x
      , acceptedAs (Model.Transcendentals.Certified.logPlus1 x) x
      ]

def failCertifiedStable : Thunk Nat := ⟨fun _ =>
  [FloatFormat.ieee 4 3, .binary16, .binary32, .binary64, .binary128].foldl
    (fun failures fmt => failures + certifiedStableFailures fmt) 0⟩

/-- Whether a certified call failed with exactly `failure`. -/
def failedWith {fmt : FloatFormat}
    (actual : Except Model.Transcendentals.Certified.Failure (Model fmt))
    (failure : Model.Transcendentals.Certified.Failure) : Bool :=
  match actual with
  | .error reason => reason == failure
  | .ok _ => false

/--
Domain, range, nonfinite-input, and unsupported-format failures, and an empty search budget, give
their own failure and never an uncertified approximation. An empty budget in a 63-bit exponent
format must not construct its enormous overflow threshold. The rational `11.0902` lies between the
logarithms of binary16's overflow threshold `65520` and of `2^16`, so the exponential passes the
range screen and its search ends at the exact overflow comparison.
-/
def failCertifiedStableRejection : Thunk Nat := ⟨fun _ =>
  let one := Model.posOne f32
  let negativeOne := Model.negOne f32
  let e4m3 := FloatFormat.e4m3fn
  countFailures
    [ failedWith (Model.Transcendentals.Certified.logPlus1 negativeOne) .domain
    , failedWith (Model.Transcendentals.Certified.logPlus1 (Model.negInf f32)) .nonfiniteInput
    , failedWith (Model.Transcendentals.Certified.expMinus1 (Model.canonicalNaN f32))
        .nonfiniteInput
    , failedWith (Model.Transcendentals.Certified.expMinus1 one { maxSteps := 0 }) .inconclusive
    , failedWith (Model.Transcendentals.Certified.logPlus1 one { maxSteps := 0 }) .inconclusive
    , failedWith (Model.Transcendentals.Certified.expRat (FloatFormat.ieee 63 23) 1
        { maxSteps := 0 }) .inconclusive
    , failedWith (Model.Transcendentals.Certified.expMinus1Rat (FloatFormat.ieee 63 23) 1
        { maxSteps := 0 }) .inconclusive
    , failedWith (Model.Transcendentals.Certified.log negativeOne) .domain
    , failedWith (Model.Transcendentals.Certified.log (Model.posZero f32)) .domain
    , failedWith
        (Model.Transcendentals.Certified.exp (Model.ofNatBits (fmt := f32) 0x42c80000)) .range
    , failedWith
        (Model.Transcendentals.Certified.expMinus1 (Model.ofNatBits (fmt := f32) 0x42c80000))
        .range
    , failedWith (Model.Transcendentals.Certified.expRat .binary16 (110902 / 10000)) .range
    , failedWith (Model.Transcendentals.Certified.exp (Model.posOne e4m3)) .unsupportedFormat
    ]⟩

/--
The certified power, with the budget `Model.pow` gives it, settles exact and irrational results,
the binary16 tie `4^-12.5` at `+0`, and `2^(1024 - 2^-43)` just below binary64's overflow
threshold. It rounds an underflow to `+0` and leaves overflow, the exact midpoints of the
fixtures, and nonpositive bases to their failures. `Model.pow` then falls back and still overflows
to infinity, also for `2^(1024 + 2^-42)` just above the threshold. An empty budget is inconclusive
only when the screens do not decide the result: in the 31-bit-exponent format the least subnormal
raised to `1.5` underflows to `+0` without a refinement attempt, and without forming half the least
subnormal, a rational of about a billion bits. In that format, three to the least subnormal power
rounds to one from the stored fields alone. Expected encodings are MPFR 4.1.0 results.
-/
def failCertifiedPow : Thunk Nat := ⟨fun _ =>
  let f64 := FloatFormat.binary64
  let wide := FloatFormat.ieee 31 23
  let double (bits : Nat) : Model f64 := Model.ofNatBits bits
  let certified {fmt : FloatFormat} (base exponent : Model fmt) :
      Except Model.Transcendentals.Certified.Failure (Model fmt) :=
    Model.Transcendentals.Certified.pow base exponent Model.Power.certifiedOptions
  let acceptedAs {fmt : FloatFormat}
      (actual : Except Model.Transcendentals.Certified.Failure (Model fmt)) (expected : Nat) :
      Bool :=
    match actual with
    | .error _ => false
    | .ok result => result.toNatBits == expected
  let two := double 0x4000000000000000
  let half := double 0x3fe0000000000000
  let leastWide := Model.posMinSubnormal wide
  let wideThreeHalves : Model wide := Model.ofNatBits 0x1fffffffc00000
  countFailures
    [ acceptedAs (certified (double 0x4022000000000000) half) 0x4008000000000000
    , acceptedAs (certified two (double 0xbfe0000000000000)) 0x3fe6a09e667f3bcd
    , acceptedAs (Model.Transcendentals.Certified.powRat f64 8 (1 / 3)
        Model.Power.certifiedOptions) 0x4000000000000000
    , acceptedAs (certified (Model.ofNatBits (fmt := .binary16) 0x4400)
        (Model.ofNatBits 0xca40)) 0
    , acceptedAs (certified two (double 0x408fffffffffffff)) 0x7feffffffffffd3a
    , acceptedAs (certified half (double 0x409f420000000000)) 0
    , failedWith (certified (double 0x4024000000000000) (double 0x4079080000000000)) .range
    , (Model.pow (double 0x4024000000000000) (double 0x4079080000000000)).toNatBits ==
        0x7ff0000000000000
    , failedWith (certified two (double 0x4090000000000001)) .range
    , (Model.pow two (double 0x4090000000000001)).toNatBits == 0x7ff0000000000000
    , failedWith (certified (double 0x422ffff000020000) (double 0x3ff8000000000000))
        .inconclusive
    , failedWith (certified (Model.ofNatBits (fmt := f32) 0x47810080) (Model.ofNatBits 0x3fc00000))
        .inconclusive
    , failedWith (certified (double 0xc000000000000000) half) .domain
    , failedWith (certified (Model.posZero f64) half) .domain
    , failedWith (Model.Transcendentals.Certified.powRat f64 0 (1 / 2)) .domain
    , failedWith (Model.Transcendentals.Certified.pow two half { maxSteps := 0 }) .inconclusive
    , failedWith (certified (Model.canonicalNaN f64) half) .nonfiniteInput
    , acceptedAs (certified leastWide wideThreeHalves) 0
    , acceptedAs (Model.Transcendentals.Certified.pow leastWide wideThreeHalves
        { maxSteps := 0 }) 0
    , (Model.pow leastWide wideThreeHalves).toNatBits == 0
    , acceptedAs (certified (Model.ofNatBits (fmt := wide) 0x20000000400000)
        (Model.posMinSubnormal wide)) 0x1fffffff800000
    ]⟩

open FloatLib.Floats in
/--
The configured `certify := true` option returns the certified kernel's encoding or its failure:
`exp 1` and `log 2` in binary32, `2 ^ 0.5` and `10 ^ 0.5` in binary64, where the default `pow`
agrees, and the domain, range, nonfinite-input, and budget failures, where the default calls
return the approximation or the IEEE special value instead. `expMinus1` and `logPlus1` keep the
binary32 input `2^-26`.
-/
def failConfiguredCertified : Thunk Nat := ⟨fun _ =>
  let certified32 (result : Except Model.Transcendentals.Certified.Failure Binary32)
      (expected : Nat) : Bool :=
    match result with
    | .ok value => ExecFloat.Binary.toNatBits value == expected
    | .error _ => false
  let certified64 (result : Except Model.Transcendentals.Certified.Failure Binary64)
      (expected : Nat) : Bool :=
    match result with
    | .ok value => ExecFloat.Binary.toNatBits value == expected
    | .error _ => false
  let failed {α : Type} (result : Except Model.Transcendentals.Certified.Failure α)
      (failure : Model.Transcendentals.Certified.Failure) : Bool :=
    match result with
    | .ok _ => false
    | .error reason => reason == failure
  let tiny : Binary32 := ExecFloat.Binary.ofNatBits 0x32800000
  let half : Binary64 := 0.5
  countFailures
    [ certified32 (ExecFloat.Binary.exp (1 : Binary32) (certify := true)
        (budget := { initialDegree := 8, maxSteps := 12 })) 1076754516
    , certified32 (ExecFloat.Binary.log (2 : Binary32) (certify := true)) 1060205080
    , certified64 (ExecFloat.Binary.pow (2 : Binary64) half (certify := true)) 0x3ff6a09e667f3bcd
    , ExecFloat.Binary.toNatBits (ExecFloat.Binary.pow (2 : Binary64) half) == 0x3ff6a09e667f3bcd
    , certified64 (ExecFloat.Binary.pow (10 : Binary64) half (certify := true))
        (ExecFloat.Binary.toNatBits (ExecFloat.Binary.pow (10 : Binary64) half))
    , failed (ExecFloat.Binary.log (-1 : Binary32) (certify := true)) .domain
    , failed (ExecFloat.Binary.exp (ExecFloat.Binary.canonicalNaN : Binary32) (certify := true))
        .nonfiniteInput
    , failed (ExecFloat.Binary.exp (1 : Binary32) (certify := true) (budget := { maxSteps := 0 }))
        .inconclusive
    , failed (ExecFloat.Binary.pow (-2 : Binary64) half (certify := true)) .domain
    , ExecFloat.Binary.isNaN (ExecFloat.Binary.pow (-2 : Binary64) half)
    , failed (ExecFloat.Binary.pow (10 : Binary64) 400.5 (certify := true)) .range
    , ExecFloat.Binary.isInfinite (ExecFloat.Binary.pow (10 : Binary64) 400.5)
    , failed (ExecFloat.Binary.logPlus1 (-1 : Binary32)) .domain
    , certified32 (ExecFloat.Binary.expMinus1 tiny) 0x32800000
    , certified32 (ExecFloat.Binary.logPlus1 tiny) 0x32800000
    ]⟩

def report : Thunk String := ⟨fun _ =>
  let rows :=
    [ ("mpfrFixtures", failMpfrFixtures.get)
    , ("specialValueMatrix", failSpecialValueMatrix.get)
    , ("nanPayloads", failNaNPayloads.get)
    , ("provedConstants", failProvedConstants.get)
    , ("pi", failPi.get)
    , ("generatedScale", failGeneratedScale.get)
    , ("explicitConfigurationReduction", failExplicitConfigurationReduction.get)
    , ("reductionProgress", failReductionProgress.get)
    , ("largeArguments", failLargeArguments.get)
    , ("reductionAttempts", failReductionAttempts.get)
    , ("tinyDyadicSine", failTinyDyadicSine.get)
    , ("certifiedStable", failCertifiedStable.get)
    , ("certifiedStableRejection", failCertifiedStableRejection.get)
    , ("certifiedPow", failCertifiedPow.get)
    , ("configuredCertified", failConfiguredCertified.get)
    ]
  renderFailureReport rows⟩

end FloatLibTests.Regression.BinaryInterchange.ExecFloatTranscendentals
