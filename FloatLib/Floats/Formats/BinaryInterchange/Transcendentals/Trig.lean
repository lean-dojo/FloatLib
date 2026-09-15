/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Hyperbolic

/-!
# Format-generic executable sine and cosine

Finite arguments are reduced against a configurable fixed-point approximation of `pi / 2`.
Reduced sine and cosine values are evaluated from exact common-denominator Taylor polynomials and
rounded once to `Model fmt`. Reduction checks `Config.trigMaxExponent` before constructing the
scaled argument. `sinCosResult` and `sinCosWithResult` expose a budget failure; the value-only
operations return the format's invalid result on failure. A full-range configuration can be
requested explicitly.

For leading exponents below `-(fracWidth + 2)`, the provider returns the input and one, preserving
tiny sine results without converting them to the fixed-point reduction scale. The kernels remain
deterministic approximations without a whole-algorithm accuracy or correct-rounding certificate.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

namespace Transcendentals

/-- A finite argument exceeds the exponent budget of the selected reduction data. -/
structure TrigReductionError where
  /-- Leading binary exponent of the argument's absolute value. -/
  inputExponent : Int
  /-- Largest leading exponent accepted by the configuration. -/
  maxExponent : Int
  deriving Repr, DecidableEq

/-- Evaluate the reduced sine and cosine kernels and round each result once. -/
def sinCosTaylorSmallWith (fmt : FloatFormat) (config : Config)
    (value : Numerics.Dyadic) : Model fmt × Model fmt :=
  let squared : Numerics.Dyadic :=
    { negative := false
      significand := value.significand * value.significand
      exponent := value.exponent + value.exponent }
  let sinNumerator := evalDyadicPolyAsc config.sinCoeffsAsc squared
  let cosNumerator := evalDyadicPolyAsc config.cosCoeffsAsc squared
  let sinDyadic := mulDyadic value sinNumerator
  ( roundDyadicDivNat fmt sinDyadic config.sinDenominator
  , roundDyadicDivNat fmt cosNumerator config.cosDenominator )

/--
Reduce a dyadic argument only within the configuration's exponent budget.

Zero and tiny inputs need no reduction. An `ok` result records successful evaluation of the
approximation policy; it does not certify numerical accuracy.
-/
def sinCosScaledWithResult (fmt : FloatFormat) (config : Config)
    (value : Numerics.Dyadic) :
    Except TrigReductionError (Model fmt × Model fmt) :=
  let leadingExponent := Int.ofNat (Nat.log2 value.significand) + value.exponent
  if value.significand == 0 then
    .ok (zero fmt value.negative, posOne fmt)
  else if leadingExponent < -(Int.ofNat (fmt.fracWidth + 2)) then
    .ok (roundDyadic fmt value, posOne fmt)
  else if leadingExponent > config.trigMaxExponent then
    .error ⟨leadingExponent, config.trigMaxExponent⟩
  else
    let fixedValue := config.trigFixed.ofDyadic value
    let quadrant := FixedPoint.roundQuotientEven fixedValue config.halfPiFixed
    let remainder := fixedValue - quadrant * config.halfPiFixed
    let reduced := sinCosTaylorSmallWith fmt config (config.trigFixed.toDyadic remainder)
    .ok <| match quadrant % 4 with
      | 0 => reduced
      | 1 => (reduced.2, neg reduced.1)
      | 2 => (neg reduced.1, neg reduced.2)
      | _ => (neg reduced.2, reduced.1)

/-- An oversized nonzero argument is rejected before fixed-point reduction, for every format. -/
theorem sinCosScaledWithResult_exponentBudget (fmt : FloatFormat) (config : Config)
    (value : Numerics.Dyadic) (hnonzero : value.significand ≠ 0)
    (hlarge : 0 ≤ Int.ofNat (Nat.log2 value.significand) + value.exponent)
    (hbudget : config.trigMaxExponent <
      Int.ofNat (Nat.log2 value.significand) + value.exponent) :
    sinCosScaledWithResult fmt config value =
      .error ⟨Int.ofNat (Nat.log2 value.significand) + value.exponent,
        config.trigMaxExponent⟩ := by
  have hsmall : ¬ Int.ofNat (Nat.log2 value.significand) + value.exponent <
      -(Int.ofNat (fmt.fracWidth + 2)) :=
    not_lt_of_ge ((neg_nonpos.mpr (Int.natCast_nonneg _)).trans hlarge)
  simp only [sinCosScaledWithResult, beq_iff_eq, hnonzero, hsmall, hbudget, ite_false, ite_true]

/-- Reduce a dyadic argument, returning invalid results when the exponent budget is exceeded. -/
def sinCosScaledWith (fmt : FloatFormat) (config : Config)
    (value : Numerics.Dyadic) : Model fmt × Model fmt :=
  match sinCosScaledWithResult fmt config value with
  | .ok result => result
  | .error _ => (invalidResult fmt, invalidResult fmt)

end Transcendentals

/--
Evaluate sine and cosine, preserving a reduction-budget failure in the result type.

The provider is called only for finite, nonzero inputs outside the tiny-argument branch.
Exceptional inputs retain their ordinary encoded results; this error type is not IEEE status.
-/
def sinCosWithProviderResult {fmt : FloatFormat}
    (getConfig : Unit → Transcendentals.Config)
    (x : Model fmt) :
    Except Transcendentals.TrigReductionError (Model fmt × Model fmt) :=
  if isNaN x then
    let quiet := quietNaN x
    .ok (quiet, quiet)
  else if isInf x then
    .ok (invalidResult fmt, invalidResult fmt)
  else if isZero x then
    .ok (x, posOne fmt)
  else
    match toDyadic? x with
    | none => .ok (invalidResult fmt, invalidResult fmt)
    | some exact =>
        let leadingExponent := Int.ofNat (Nat.log2 exact.significand) + exact.exponent
        if leadingExponent < -(Int.ofNat (fmt.fracWidth + 2)) then
          .ok (x, posOne fmt)
        else
          Transcendentals.sinCosScaledWithResult fmt (getConfig ()) exact

/-- Evaluate sine and cosine, mapping reduction-budget failures to the format's invalid result. -/
def sinCosWithProvider {fmt : FloatFormat}
    (getConfig : Unit → Transcendentals.Config)
    (x : Model fmt) : Model fmt × Model fmt :=
  match sinCosWithProviderResult getConfig x with
  | .ok result => result
  | .error _ => (invalidResult fmt, invalidResult fmt)

/-- Joint sine/cosine approximation with explicit data and a separate reduction-budget error. -/
def sinCosWithResult {fmt : FloatFormat}
    (config : Transcendentals.Config) (x : Model fmt) :
    Except Transcendentals.TrigReductionError (Model fmt × Model fmt) :=
  sinCosWithProviderResult (fun _ => config) x

/-- Joint deterministic sine/cosine evaluation with explicit approximation data. -/
def sinCosWith {fmt : FloatFormat}
    (config : Transcendentals.Config) (x : Model fmt) : Model fmt × Model fmt :=
  sinCosWithProvider (fun _ => config) x

/-- Deterministic sine with explicit approximation data. -/
@[inline] def sinWith {fmt : FloatFormat}
    (config : Transcendentals.Config) (x : Model fmt) : Model fmt :=
  (sinCosWith config x).1

/-- Deterministic cosine with explicit approximation data. -/
@[inline] def cosWith {fmt : FloatFormat}
    (config : Transcendentals.Config) (x : Model fmt) : Model fmt :=
  (sinCosWith config x).2

/-- The configured approximation to pi, rounded once to the destination format. -/
def piWith (fmt : FloatFormat) (config : Transcendentals.Config) : Model fmt :=
  roundDyadic fmt (config.trigFixed.toDyadic (2 * config.halfPiFixed))

/-- Joint sine/cosine evaluation using the default configuration. -/
@[inline] def sinCos {fmt : FloatFormat} (x : Model fmt) : Model fmt × Model fmt :=
  sinCosWithProvider (fun _ => Transcendentals.Config.forFormat fmt) x

/-- Joint sine/cosine approximation with an explicit failure when default reduction is too small. -/
@[inline] def sinCosResult {fmt : FloatFormat} (x : Model fmt) :
    Except Transcendentals.TrigReductionError (Model fmt × Model fmt) :=
  sinCosWithProviderResult (fun _ => Transcendentals.Config.forFormat fmt) x

/-- Sine using the default configuration; a reduction-budget failure gives `invalidResult`. -/
@[inline] def sin {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  (sinCosWithProvider (fun _ => Transcendentals.Config.forFormat fmt) x).1

/-- Cosine using the default configuration; a reduction-budget failure gives `invalidResult`. -/
@[inline] def cos {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  (sinCosWithProvider (fun _ => Transcendentals.Config.forFormat fmt) x).2

/-- Pi using the default configuration for the destination format. -/
@[inline] def pi (fmt : FloatFormat) : Model fmt :=
  piWith fmt (Transcendentals.Config.forFormat fmt)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
