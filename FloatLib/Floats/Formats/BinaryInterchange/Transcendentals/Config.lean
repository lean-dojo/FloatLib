/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.FixedPoint
public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
public import FloatLib.Numerics.Enclosure.Constants.Runtime

/-!
# Configuration for format-generic transcendental execution

IEEE 754 §9.2 recommends elementary operations with a correct-rounding contract, but it does not
require them in every implementation or prescribe their algorithms. These kernels provide
deterministic approximations. `Config` records their integer approximation data, and accuracy
and correct rounding need their own proofs. The binary32 configuration is pinned for reproducible
results, and other formats use a configuration generated under a `GenerationPolicy`.

Generated configurations depend on the fraction width only, never on the exponent range:
trigonometric reduction and the reduction of large exponential arguments take their extra
precision from the shared constants cache of `Numerics.Enclosure.Constants` at the size each
argument needs. The generated `log 2` is its `ln2Faithful` read, proved within one unit.

Generated data is an execution policy, not an accuracy theorem. Real-error claims are separate
approximation contracts.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.Transcendentals

/-- Resource policy for generated transcendental approximation data. -/
structure GenerationPolicy where
  /-- Extra fixed-point precision used for generated constants and working arithmetic. -/
  guardBits : Nat := 32
  deriving Repr, DecidableEq

namespace GenerationPolicy

/-- Default bounded generation policy. -/
def standard : GenerationPolicy := {}

end GenerationPolicy

/--
Integer approximation data consumed by the transcendental kernels.

The fields store coefficients and scales without proofs of their accuracy or validity.
`binary32` and `generatedWith` supply the Taylor coefficients and positive denominators described
below. Callers constructing their own configurations must establish the properties they need.
-/
structure Config where
  /-- Base working scale for `exp` and `log`, which `log` increases near one. -/
  fixed : FixedPoint
  /-- Fixed-point approximation to `log 2` at scale `fixed`. -/
  ln2Fixed : Int
  /-- Fixed-point approximation to `1 / log 2`. -/
  invLn2Fixed : Int
  /-- Descending fixed-point coefficients for the reduced `2 ^ x` polynomial. -/
  exp2PolyCoeffsDesc : List Int
  /-- Number of odd atanh-series terms used by `log`. -/
  logTerms : Nat
  /--
  Ascending exact numerator coefficients of the odd Taylor polynomial in `x ^ 2` shared by the
  small-argument branches of `sinh`, `cosh` and `tanh`. Entry `i` is `sinhDenominator / (2i+1)!`.
  -/
  sinhCoeffsAsc : List Int
  /-- Positive common denominator for `sinhCoeffsAsc`. -/
  sinhDenominator : Nat
  /--
  Ascending exact numerator coefficients of the alternating Taylor series of sine in `x ^ 2`;
  entry `i` is `(-1)^i * sinDenominator / (2i+1)!`. The kernel evaluates a prefix of the list
  whose length it chooses from the argument, and the whole list for tiny arguments.
  -/
  sinCoeffsAsc : List Int
  /-- Positive common denominator for `sinCoeffsAsc`. -/
  sinDenominator : Nat
  /--
  Ascending exact numerator coefficients of the alternating Taylor series of cosine in `x ^ 2`;
  entry `i` is `(-1)^i * cosDenominator / (2i)!`. The kernel evaluates a prefix of the list whose
  length it chooses from the argument.
  -/
  cosCoeffsAsc : List Int
  /-- Positive common denominator for `cosCoeffsAsc`. -/
  cosDenominator : Nat
  deriving Repr, DecidableEq

namespace Config

/-- Factorial used to construct exact common-denominator Taylor polynomials. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

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
Search upward from `count` for the first term count whose truncation target is met. `fuel`
bounds the search so the definition is structurally total.
-/
def sinhTermsAux (target : Nat) : Nat → Nat → Nat
  | 0, count => count
  | fuel + 1, count =>
      if target ≤ Model.pow2 (2 * count) * factorial (2 * count + 1) then count
      else sinhTermsAux target fuel (count + 1)

/-- Bits kept beyond the destination fraction width by the small-argument `sinh` series. -/
def sinhGuardBits : Nat := 36

/--
Number of odd Taylor terms of `sinh` selected for a fraction width.

The search targets the first `n ≥ 1` with
`2^(2n) * (2n+1)! ≥ 2^(fracWidth + sinhGuardBits)`, so for `|x| ≤ 1/2` the first omitted term
is below `2^-(fracWidth + sinhGuardBits + 1)`. The small-argument branches of `sinh`, `cosh` and
`tanh` share this series, and a target only four bits beyond the fraction width misrounded
binary128 results near one half. The linear fuel budget is chosen to exceed the point where the
power-of-two factor alone reaches the target. The corresponding analytic error argument is not
formalized as a theorem in this library.
-/
def sinhTerms (fracWidth : Nat) : Nat :=
  sinhTermsAux (Model.pow2 (fracWidth + sinhGuardBits)) (fracWidth + sinhGuardBits) 1

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
  sinCoeffsAsc :=
    [6227020800, -1037836800, 51891840, -1235520, 17160, -156, 1]
  sinDenominator := 6227020800
  cosCoeffsAsc :=
    [479001600, -239500800, 19958400, -665280, 11880, -132, 1]
  cosDenominator := 479001600

/--
Generate a deterministic configuration sized for `fmt` under a resource policy.

Every field depends on the fraction width only. `log 2` comes from the shared constants cache and
is within one unit of its exact scaled value. The other fields are a deterministic approximation
policy and carry no proved error bound.
-/
def generatedWith (policy : GenerationPolicy) (fmt : FloatFormat) : Config :=
  let fixed : FixedPoint := fmt.fracWidth + policy.guardBits
  let ln2Fixed : Int := Numerics.Enclosure.Constants.ln2Faithful fixed
  let invLn2Fixed := fixed.div fixed.one ln2Fixed
  let expDegree := fmt.fracWidth / 3 + 10
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
    sinCoeffsAsc := sinData.2
    sinDenominator := sinData.1
    cosCoeffsAsc := cosData.2
    cosDenominator := cosData.1 }

/-- Generate a configuration with the default resource policy. -/
def generated (fmt : FloatFormat) : Config :=
  generatedWith GenerationPolicy.standard fmt

/--
`generated fmt`, kept out of line and out of closed-term extraction so the cached catalog
configurations below are generated on first use rather than at module initialization.
-/
@[noinline, never_extract] def Internal.generate (fmt : FloatFormat) : Config :=
  generated fmt

/-- Generated binary16 configuration, computed on first use and then reused. -/
def Internal.generatedBinary16 : Thunk Config :=
  Thunk.mk fun _ => Internal.generate FloatFormat.binary16

/-- Generated bfloat16 configuration, computed on first use and then reused. -/
def Internal.generatedBFloat16 : Thunk Config :=
  Thunk.mk fun _ => Internal.generate FloatFormat.bfloat16

/-- Generated binary64 configuration, computed on first use and then reused. -/
def Internal.generatedBinary64 : Thunk Config :=
  Thunk.mk fun _ => Internal.generate FloatFormat.binary64

/-- Generated binary128 configuration, computed on first use and then reused. -/
def Internal.generatedBinary128 : Thunk Config :=
  Thunk.mk fun _ => Internal.generate FloatFormat.binary128

/-- Generated binary256 configuration, computed on first use and then reused. -/
def Internal.generatedBinary256 : Thunk Config :=
  Thunk.mk fun _ => Internal.generate FloatFormat.binary256

/--
Default configuration for a format.

Binary32 selects its pinned table. The other catalog binary formats reuse one generated
configuration per program run, and every other layout generates its data on each call. The result
equals `generated fmt` for every layout except binary32. Callers that need a different
speed/accuracy point can use `generatedWith`, or build and reuse a `Config`.
-/
def forFormat (fmt : FloatFormat) : Config :=
  if fmt = FloatFormat.binary32 then binary32
  else if fmt = FloatFormat.binary64 then Numerics.Internal.forceCache Internal.generatedBinary64
  else if fmt = FloatFormat.binary128 then Numerics.Internal.forceCache Internal.generatedBinary128
  else if fmt = FloatFormat.binary16 then Numerics.Internal.forceCache Internal.generatedBinary16
  else if fmt = FloatFormat.bfloat16 then Numerics.Internal.forceCache Internal.generatedBFloat16
  else if fmt = FloatFormat.binary256 then Numerics.Internal.forceCache Internal.generatedBinary256
  else generated fmt

/-- The cached catalog configurations are the generated ones. -/
theorem forFormat_eq (fmt : FloatFormat) :
    forFormat fmt = if fmt = FloatFormat.binary32 then binary32 else generated fmt := by
  unfold forFormat
  by_cases h32 : fmt = FloatFormat.binary32
  · simp [h32]
  · simp only [h32, ite_false]
    split_ifs <;> subst_vars <;> rfl

end Config

end Model.Transcendentals
end FloatLib.Floats.Formats.BinaryInterchange
