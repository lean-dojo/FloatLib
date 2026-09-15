/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.FixedPoint
public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog

/-!
# Configuration for format-generic transcendental execution

IEEE 754 §9.2 recommends elementary operations with a correct-rounding contract; it does not
require them in every implementation or prescribe their algorithms. These kernels provide
deterministic approximations. `Config` records their integer approximation data, while accuracy
and correct rounding require separate proofs. The binary32 configuration is pinned explicitly
for reproducible results. Other formats use a generated configuration controlled by an explicit
`GenerationPolicy`.

The default policy bounds the exponent range accepted by trigonometric reduction. The checked
trigonometric entry points report inputs beyond this budget as failures; the value-only entry
points return the format's invalid result. This prevents a wide exponent field from silently
constructing constants with hundreds of thousands or billions of bits. `generatedFullRange`
remains available as an explicit expensive choice.

Generated data is an execution policy, not an accuracy theorem. Real-error claims remain separate
approximation contracts.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.Transcendentals

/--
Resource policy for generated transcendental approximation data.

`trigExponentBudget` bounds the destination exponent contribution to the fixed-point scale used for
trigonometric reduction. Reduction rejects arguments beyond that budget instead of using an
insufficiently precise approximation to `pi / 2`.
-/
structure GenerationPolicy where
  /-- Extra fixed-point precision used for generated constants and working arithmetic. -/
  guardBits : Nat := 32
  /-- Cap on the exponent-range contribution to trigonometric working precision. -/
  trigExponentBudget : Nat := 4096
  deriving Repr, DecidableEq

namespace GenerationPolicy

/-- Default bounded generation policy. -/
def standard : GenerationPolicy := {}

end GenerationPolicy

/--
Integer approximation data consumed by the transcendental kernels.

The fields store coefficients and scales without proofs of their accuracy or validity.
`binary32` and `generatedWith` supply the Taylor coefficients and positive denominators described
below; callers constructing their own configurations must establish the properties they need.
-/
structure Config where
  /--
  Base working scale for `exp` and `log`, also reserved after trigonometric reduction.
  `log` increases it near one.
  -/
  fixed : FixedPoint
  /-- Fixed-point approximation to `log 2`. -/
  ln2Fixed : Int
  /-- Fixed-point approximation to `1 / log 2`. -/
  invLn2Fixed : Int
  /-- Descending fixed-point coefficients for the reduced `2 ^ x` polynomial. -/
  exp2PolyCoeffsDesc : List Int
  /-- Number of odd atanh-series terms used by `log`. -/
  logTerms : Nat
  /--
  Ascending exact numerator coefficients of the odd Taylor polynomial in `x ^ 2` shared by the
  small-argument branches of `sinh` and `tanh`; entry `i` is `sinhDenominator / (2i+1)!`.
  -/
  sinhCoeffsAsc : List Int
  /-- Positive common denominator for `sinhCoeffsAsc`. -/
  sinhDenominator : Nat
  /-- Working scale used for trigonometric argument reduction. -/
  trigFixed : FixedPoint
  /-- Fixed-point approximation to `pi / 2` at scale `trigFixed`. -/
  halfPiFixed : Int
  /-- Ascending exact numerator coefficients for the reduced sine polynomial. -/
  sinCoeffsAsc : List Int
  /-- Positive common denominator for `sinCoeffsAsc`. -/
  sinDenominator : Nat
  /-- Ascending exact numerator coefficients for the reduced cosine polynomial. -/
  cosCoeffsAsc : List Int
  /-- Positive common denominator for `cosCoeffsAsc`. -/
  cosDenominator : Nat
  deriving Repr, DecidableEq

namespace Config

/--
Largest leading input exponent accepted by trigonometric reduction.

Reserving `fixed` bits after reduction leaves `trigFixed - fixed` bits for the argument's
exponent. For generated configurations this is exactly the capped exponent contribution.
This resource check is not an accuracy certificate for the constants or polynomials.
-/
def trigMaxExponent (config : Config) : Int :=
  Int.ofNat config.trigFixed - Int.ofNat config.fixed

/-- Factorial used to construct exact common-denominator Taylor polynomials. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/--
Approximate the first `terms` terms of the odd reciprocal series

`sum_k sign(k) / ((2k+1) * q^(2k+1))`

at the supplied fixed-point scale, with `q > 1`. The infinite series is `atanh (1/q)` when
`alternating = false` and `atan (1/q)` when `alternating = true`. Each division rounds to the
working scale.
-/
def oddReciprocalSeries
    (fixed : FixedPoint) (q terms : Nat) (alternating : Bool) : Int :=
  let qSquared := Int.ofNat (q * q)
  let initialPower := FixedPoint.roundQuotientEven fixed.one (Int.ofNat q)
  let step (state : Int × Int) (index : Nat) : Int × Int :=
    let power := state.1
    let denominator := 2 * index + 1
    let term := fixed.divByNat power denominator
    let accumulator :=
      if alternating && index % 2 == 1 then state.2 - term else state.2 + term
    let nextPower := FixedPoint.roundQuotientEven power qSquared
    (nextPower, accumulator)
  ((List.range terms).foldl step (initialPower, 0)).2

/--
Approximate `log 2 * 2^scale` using `log 2 = 2 * atanh (1/3)` and an explicit guard budget.
The truncated fixed-point series is rounded back to the requested scale.
-/
def generateLn2FixedWith (guardBits scale : Nat) : Int :=
  let work : FixedPoint := scale + guardBits
  let terms := scale / 3 + guardBits / 2 + 4
  FixedPoint.roundDivPow2Even
    (2 * oddReciprocalSeries work 3 terms false) guardBits

/-- Approximate `log 2 * 2^scale` with the default guard budget. -/
def generateLn2Fixed (scale : Nat) : Int :=
  generateLn2FixedWith 32 scale

/--
Approximate `(pi/2) * 2^scale` with Machin's formula
`pi/2 = 8 * atan (1/5) - 2 * atan (1/239)` and an explicit guard budget.
-/
def generateHalfPiFixedWith (guardBits scale : Nat) : Int :=
  let work : FixedPoint := scale + guardBits
  let atanFiveTerms := scale / 4 + guardBits / 2 + 4
  let atanTwoThirtyNineTerms := scale / 14 + guardBits / 8 + 4
  let atanFive := oddReciprocalSeries work 5 atanFiveTerms true
  let atanTwoThirtyNine := oddReciprocalSeries work 239 atanTwoThirtyNineTerms true
  FixedPoint.roundDivPow2Even (8 * atanFive - 2 * atanTwoThirtyNine) guardBits

/-- Approximate `(pi/2) * 2^scale` with the default guard budget. -/
def generateHalfPiFixed (scale : Nat) : Int :=
  generateHalfPiFixedWith 32 scale

/-- Generate descending coefficients for a Taylor polynomial approximating `2 ^ x`. -/
def generateExp2CoeffsDesc
    (fixed : FixedPoint) (ln2Fixed : Int) (degree : Nat) : List Int :=
  let step (state : Int × List Int) (index : Nat) : Int × List Int :=
    let next := fixed.divByNat (fixed.mul state.1 ln2Fixed) (index + 1)
    (next, next :: state.2)
  ((List.range degree).foldl step (fixed.one, [fixed.one])).2

/--
Exact common-denominator coefficients for
`sum i in [0, max terms 1), (-1)^i x^(2i+1)/(2i+1)!`.
-/
def sinTaylorData (terms : Nat) : Nat × List Int :=
  let count := Nat.max terms 1
  let degree := 2 * count - 1
  let denominator := factorial degree
  let coefficients := (List.range count).map fun index =>
    let magnitude := denominator / factorial (2 * index + 1)
    if index % 2 == 0 then Int.ofNat magnitude else -(Int.ofNat magnitude)
  (denominator, coefficients)

/--
Exact common-denominator coefficients for the odd series
`sum i in [0, max terms 1), x^(2i+1)/(2i+1)!`
of `sinh`. With `n = max terms 1`, the pair is `((2*n - 1)!, coefficients)`, with every
coefficient positive.
-/
def sinhTaylorData (terms : Nat) : Nat × List Int :=
  let count := Nat.max terms 1
  let degree := 2 * count - 1
  let denominator := factorial degree
  let coefficients := (List.range count).map fun index =>
    Int.ofNat (denominator / factorial (2 * index + 1))
  (denominator, coefficients)

/--
Search upward from `count` for the first term count whose truncation target is met; `fuel`
bounds the search so the definition is structurally total.
-/
def sinhTermsAux (target : Nat) : Nat → Nat → Nat
  | 0, count => count
  | fuel + 1, count =>
      if target ≤ Model.pow2 (2 * count) * factorial (2 * count + 1) then count
      else sinhTermsAux target fuel (count + 1)

/--
Number of odd Taylor terms of `sinh` selected for a fraction width.

The search targets the first `n ≥ 1` with
`2^(2n) * (2n+1)! ≥ 2^(fracWidth + 4)`. This condition comes from the usual Taylor-tail estimate
for `|x| ≤ 1/2`, and the linear fuel budget is chosen to exceed the point where the power-of-two
factor alone reaches the target. The corresponding analytic error argument is not yet formalized
as a theorem in this library.
-/
def sinhTerms (fracWidth : Nat) : Nat :=
  sinhTermsAux (Model.pow2 (fracWidth + 4)) (fracWidth + 4) 1

/--
Exact common-denominator coefficients for
`sum i in [0, max terms 1), (-1)^i x^(2i)/(2i)!`.
-/
def cosTaylorData (terms : Nat) : Nat × List Int :=
  let count := Nat.max terms 1
  let degree := 2 * (count - 1)
  let denominator := factorial degree
  let coefficients := (List.range count).map fun index =>
    let magnitude := denominator / factorial (2 * index)
    if index % 2 == 0 then Int.ofNat magnitude else -(Int.ofNat magnitude)
  (denominator, coefficients)

/-- Pinned binary32 configuration for stable, reproducible transcendental results. -/
def binary32 : Config where
  fixed := 48
  ln2Fixed := 195103586505167
  invLn2Fixed := 406082553034800
  exp2PolyCoeffsDesc :=
    [ 1985781
    , 28648765
    , 371982884
    , 4293262892
    , 43357083587
    , 375306296874
    , 2707262666570
    , 15623017693776
    , 67617750451595
    , 195103586505167
    , 281474976710656
    ]
  logTerms := 8
  sinhCoeffsAsc := [39916800, 6652800, 332640, 7920, 110, 1]
  sinhDenominator := 39916800
  trigFixed := 256
  halfPiFixed :=
    181885788445883162140117471388864931326696688664196214979386075558969447233093
  sinCoeffsAsc :=
    [6227020800, -1037836800, 51891840, -1235520, 17160, -156, 1]
  sinDenominator := 6227020800
  cosCoeffsAsc :=
    [479001600, -239500800, 19958400, -665280, 11880, -132, 1]
  cosDenominator := 479001600

/--
Fixed-point scale used for trigonometric reduction under `policy`.

The fraction width and guard bits contribute in full; the exponent-range contribution is capped.
-/
def generatedTrigScale (policy : GenerationPolicy) (fmt : FloatFormat) : Nat :=
  Nat.min (Int.toNat fmt.maxNormalExponent) policy.trigExponentBudget +
    fmt.fracWidth + policy.guardBits

/--
Generate a deterministic configuration sized for `fmt` under an explicit resource policy.

The bounded trigonometric scale keeps ordinary generation practical for formats with wide exponent
fields. This is a deterministic approximation policy and does not imply a proved error bound.
-/
def generatedWith (policy : GenerationPolicy) (fmt : FloatFormat) : Config :=
  let fixed : FixedPoint := fmt.fracWidth + policy.guardBits
  let ln2Fixed := generateLn2FixedWith policy.guardBits fixed
  let invLn2Fixed := fixed.div fixed.one ln2Fixed
  let expDegree := fmt.fracWidth / 3 + 10
  let trigFixed : FixedPoint := generatedTrigScale policy fmt
  let trigTerms := fmt.fracWidth / 6 + 8
  let sinData := sinTaylorData trigTerms
  let cosData := cosTaylorData trigTerms
  let sinhData := sinhTaylorData (sinhTerms fmt.fracWidth)
  { fixed
    ln2Fixed
    invLn2Fixed
    exp2PolyCoeffsDesc := generateExp2CoeffsDesc fixed ln2Fixed expDegree
    logTerms := fmt.fracWidth / 3 + 10
    sinhCoeffsAsc := sinhData.2
    sinhDenominator := sinhData.1
    trigFixed
    halfPiFixed := generateHalfPiFixedWith policy.guardBits trigFixed
    sinCoeffsAsc := sinData.2
    sinDenominator := sinData.1
    cosCoeffsAsc := cosData.2
    cosDenominator := cosData.1 }

/-- Generated reduction data accepts exactly its declared exponent contribution. -/
theorem trigMaxExponent_generatedWith (policy : GenerationPolicy) (fmt : FloatFormat) :
    (generatedWith policy fmt).trigMaxExponent =
      Int.ofNat (Nat.min (Int.toNat fmt.maxNormalExponent) policy.trigExponentBudget) := by
  simp [trigMaxExponent, generatedWith, generatedTrigScale, Nat.cast_add]

/-- Generate a configuration with the default bounded resource policy. -/
def generated (fmt : FloatFormat) : Config :=
  generatedWith GenerationPolicy.standard fmt

/-- Generate a full-range configuration with a caller-selected guard budget. -/
def generatedFullRangeWith (guardBits : Nat) (fmt : FloatFormat) : Config :=
  generatedWith
    { guardBits
      trigExponentBudget := Int.toNat fmt.maxNormalExponent }
    fmt

/--
Generate an unbounded full-exponent-range configuration.

For formats with wide exponent fields this can allocate extremely large integers. Callers should
normally prefer `generated`.
-/
def generatedFullRange (fmt : FloatFormat) : Config :=
  generatedFullRangeWith 32 fmt

/--
Default configuration for a format.

Binary32 selects its pinned table; every other layout receives bounded generated data.
Callers that need a different speed/accuracy point can use `generatedWith`, `generatedFullRange`,
or construct and reuse an explicit `Config`.
-/
def forFormat (fmt : FloatFormat) : Config :=
  if fmt = FloatFormat.binary32 then binary32 else generated fmt

end Config

end Model.Transcendentals
end FloatLib.Floats.Formats.BinaryInterchange
