/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Enclosure.Runtime
public import FloatLib.Numerics.Exact.Elementary.Runtime
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridRuntime
public import FloatLib.Numerics.Enclosure.Refinement

/-!
# Certified binary exponential and logarithm by enclosure refinement

Exact input decoding and outward-rounded binary-grid enclosures feed a nearest-even endpoint
check. Refinement increases the Taylor degree while the interval shrinks rapidly, and increases
the working precision when that progress stalls. The cases `exp 0 = 1` and `log 1 = 0` use point
enclosures.

Exponential uses format-derived rational argument bounds to skip impossible underflow and overflow
checks. Beyond these bounds, total logarithm-based comparisons handle extreme inputs. These
comparisons terminate independently of the options, which bound the direct enclosure search.
Unsupported descriptors, nonfinite inputs, nonpositive logarithm arguments, overflow, and exhausted
searches return `none`. Every accepted result has a finite real-rounding certificate.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Certified

open FloatLib.Numerics

/-- Degree and attempt budget for direct enclosure refinement. -/
structure Options where
  /-- First Taylor degree. Zero is promoted to one before refinement. -/
  initialDegree : Nat := 8
  /-- Maximum enclosure attempts, including retries at higher degree or precision. -/
  maxSteps : Nat := 16
  deriving DecidableEq, Repr

/-- Try successive enclosures, stopping immediately when the endpoints certify one encoding. -/
@[inline] def refine (fmt : FloatFormat) (enclose : Nat → Nat → RationalInterval)
    (degree precision steps : Nat) : Option (Model fmt) :=
  RationalInterval.refine enclose (Enclosure.round? fmt) degree precision steps

/-- The interval from zero to half the least subnormal, including the even tie at zero. -/
def expUnderflowInterval (fmt : FloatFormat) : RationalInterval :=
  ⟨0, (Numerics.Dyadic.mk false 1 (fmt.minSubnormalExponent - 1)).toRat⟩

/-- First power of two above the normal range, used before direct exponential evaluation. -/
def expUpperBound (fmt : FloatFormat) : ℚ :=
  (Numerics.Dyadic.mk false 1 (fmt.maxNormalExponent + 1)).toRat

/-- Argument lower bound that excludes exponential underflow, using `log 2 > 1/2`. -/
@[inline] def expUnderflowArgumentBound (fmt : FloatFormat) : ℚ :=
  ((fmt.minSubnormalExponent - 1 : ℤ) : ℚ) / 2

/-- Argument upper bound below the exponential overflow guard on supported descriptors. -/
@[inline] def expUpperArgumentBound (fmt : FloatFormat) : ℚ :=
  ((fmt.maxNormalExponent + 1 : ℤ) : ℚ) / 2

/-- Round the exponential of an exact rational if the enclosure budget certifies a finite result. -/
@[inline] def expRat (fmt : FloatFormat) (argument : ℚ) (options : Options := {}) :
    Option (Model fmt) :=
  if !fmt.isIEEE then none
  else if argument = 0 then Enclosure.round? fmt (RationalInterval.point 1)
  else if argument < expUnderflowArgumentBound fmt ∧
      ElementaryComparison.compareExp argument (expUnderflowInterval fmt).hi ≠ .gt then
    Enclosure.round? fmt (expUnderflowInterval fmt)
  else if expUpperArgumentBound fmt < argument ∧
      ElementaryComparison.compareExp argument (expUpperBound fmt) ≠ .lt then none
  else
    let degree := max 1 options.initialDegree
    let precision := FloatLib.Numerics.Enclosure.BinaryGrid.expPrecision
      (fmt.fracWidth + 1) argument degree
    refine fmt (FloatLib.Numerics.Enclosure.BinaryGrid.exp argument)
      degree precision options.maxSteps

/-- Certify a finite rounded logarithm of a positive rational; reject other arguments. -/
@[inline] def logRat (fmt : FloatFormat) (argument : ℚ) (options : Options := {}) :
    Option (Model fmt) :=
  if !fmt.isIEEE then none
  else if argument ≤ 0 then none
  else if argument = 1 then Enclosure.round? fmt (RationalInterval.point 0)
  else
    let degree := max 1 options.initialDegree
    let precision := FloatLib.Numerics.Enclosure.BinaryGrid.logPrecision
      (fmt.fracWidth + 1) argument degree
    refine fmt (FloatLib.Numerics.Enclosure.BinaryGrid.log argument)
      degree precision options.maxSteps

/--
Certify `exp argument - 1`, subtracting one from the exact rational enclosure before rounding.

This retains small results which would be lost by rounding the exponential to one first.
The same comparison shortcut as `expRat` handles very negative arguments without constructing
their exponential. Unsupported descriptors, overflow, and an exhausted budget return `none`.
-/
@[inline] def expMinus1Rat (fmt : FloatFormat) (argument : ℚ) (options : Options := {}) :
    Option (Model fmt) :=
  if !fmt.isIEEE then none
  else if argument = 0 then
    Enclosure.round? fmt (RationalInterval.point 0)
  else if argument < expUnderflowArgumentBound fmt ∧
      ElementaryComparison.compareExp argument (expUnderflowInterval fmt).hi ≠ .gt then
    Enclosure.round? fmt ((expUnderflowInterval fmt).sub (RationalInterval.point 1))
  else if expUpperArgumentBound fmt < argument ∧
      ElementaryComparison.compareExp argument (expUpperBound fmt + 1) ≠ .lt then none
  else
    let degree := max 1 options.initialDegree
    let precision := FloatLib.Numerics.Enclosure.BinaryGrid.expPrecision
      (fmt.fracWidth + 1) argument degree true
    refine fmt
      (fun degree precision => (FloatLib.Numerics.Enclosure.BinaryGrid.exp argument
        degree precision).sub (RationalInterval.point 1))
      degree precision options.maxSteps

/--
Certify `log (1 + argument)`, forming the sum exactly before enclosing the logarithm.

In particular, a small nonzero argument is not lost by rounding `1 + argument` to one.
Arguments at or below `-1` return `none`, as do the other failure cases of `logRat`.
-/
@[inline] def logPlus1Rat (fmt : FloatFormat) (argument : ℚ) (options : Options := {}) :
    Option (Model fmt) :=
  logRat fmt (1 + argument) options

/-- Certify a finite exponential using exact decoding and outward-rounded enclosures. -/
def exp {fmt : FloatFormat} (input : Model fmt) (options : Options := {}) :
    Option (Model fmt) :=
  match toRat? input with
  | none => none
  | some argument => expRat fmt argument options

/-- Certify a finite logarithm; `log 1` returns positive zero. -/
def log {fmt : FloatFormat} (input : Model fmt) (options : Options := {}) :
    Option (Model fmt) :=
  match toRat? input with
  | none => none
  | some argument => logRat fmt argument options

/-- Certify `exp x - 1` with one final rounding, preserving either IEEE signed zero. -/
@[inline] def expMinus1 {fmt : FloatFormat} (input : Model fmt) (options : Options := {}) :
    Option (Model fmt) :=
  if fmt.isIEEE && isZero input then some input
  else
    match toRat? input with
    | none => none
    | some argument => expMinus1Rat fmt argument options

/-- Certify `log (1 + x)` with one final rounding, preserving either IEEE signed zero. -/
@[inline] def logPlus1 {fmt : FloatFormat} (input : Model fmt) (options : Options := {}) :
    Option (Model fmt) :=
  if fmt.isIEEE && isZero input then some input
  else
    match toRat? input with
    | none => none
    | some argument => logPlus1Rat fmt argument options

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Certified
