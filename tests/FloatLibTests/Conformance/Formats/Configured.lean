/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.Block.Configured.Proof
public import FloatLib.Floats.Formats.Codebook.Catalog.Proof
public import FloatLib.Floats.Formats.Codebook.Configured.Catalog
public import FloatLib.Floats.Formats.Codebook.Configured.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Scaling.Runtime
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Proof
public import FloatLib.Floats.Formats.FixedPoint.Configured.Instances
public import FloatLib.Floats.Formats.Logarithmic.Configured.Instances
public import FloatLib.Floats.Formats.OCP.MX.Configured.Proof
public import FloatLib.Floats.ExecFloat.Proof.Arithmetic
public meta import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Runtime
public meta import FloatLib.Floats.Formats.FixedPoint.Configured.Runtime
public meta import FloatLib.Numerics.Capabilities.Radix

/-!
# Configured format checks

Public-API checks for binary comparisons, exact logarithmic and fixed-point values, bounded
overflow, decimal roots, codebooks, shared-scale blocks, and OCP MX. The examples check selected
kernels, representation round trips, and rewriting public arithmetic to its specification.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.Configured

open FloatLib.Numerics
open FloatLib.Floats

private abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

-- Field notation must reach the certified default operations, including on limb-backed values.
example (x y z : Binary32) :
    x.sqrt = ExecFloat.Spec.sqrt x ∧ x.fma y z = ExecFloat.Spec.fma x y z :=
  ⟨ExecFloat.Proof.sqrt_eq_spec x, ExecFloat.Proof.fma_eq_spec x y z⟩

example (x y z : ExecFloat.BinaryLimbs 19 236) :
    x.sqrt = ExecFloat.Spec.sqrt x ∧ x.fma y z = ExecFloat.Spec.fma x y z :=
  ⟨ExecFloat.Proof.sqrt_eq_spec x, ExecFloat.Proof.fma_eq_spec x y z⟩

-- Chained representation methods and directed rounding retain the configured receiver type.
example :
    (-4 : Binary32).abs.nextUp.toNatBits = 0x40800001 ∧
      (4 : Binary32).isFinite = true ∧
      ((4 : Binary32).sqrtWithRounding .towardPositiveInfinity).toNatBits = 0x40000000 := by
  decide +kernel

example (x : ExecFloat.BinaryLimbs 19 236) :
    x.abs.nextUp.toNatBits = ExecFloat.Binary.toNatBits
      (ExecFloat.Binary.nextUp (ExecFloat.Binary.abs x)) := rfl

-- A codec for an unrelated format must not change inference for a concrete binary receiver.
example {format : Formats.BinaryInterchange.FloatFormat}
    {plan : Formats.BinaryInterchange.Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Formats.BinaryInterchange.Model format) code]
    (x : ExecFloat.Binary 8 23) :
    (Formats.BinaryInterchange.Model.castWithStatus _ format x.abs.nextUp.toModel).value =
      (Formats.BinaryInterchange.Model.castWithStatus _ format
        (ExecFloat.Binary.toModel (ExecFloat.Binary.nextUp (ExecFloat.Binary.abs x)))).value := rfl

/-- Numerical comparison keeps signed-zero equality and NaN unorderedness separate from bits. -/
example :
    let nan : Binary32 := ExecFloat.Binary.canonicalNaN
    [ ExecFloat.compareEqual (ExecFloat.Binary.zero false : Binary32)
        (ExecFloat.Binary.zero true)
    , ExecFloat.compareEqual nan nan
    , ExecFloat.compareNotEqual nan nan
    , ExecFloat.compareLess nan (1 : Binary32)
    , ExecFloat.compareLess (1 : Binary32) nan
    ] = [true, false, true, false, false] ∧
      ExecFloat.compare nan (1 : Binary32) = none := by
  decide +kernel

/-- All ordered predicates use the configured value's numerical order. -/
example :
    [ ExecFloat.compareEqual (1 : Binary32) (1 : Binary32)
    , ExecFloat.compareLess (1 : Binary32) (2 : Binary32)
    , ExecFloat.compareLessEqual (1 : Binary32) (1 : Binary32)
    , ExecFloat.compareGreater (2 : Binary32) (1 : Binary32)
    , ExecFloat.compareGreaterEqual (1 : Binary32) (1 : Binary32)
    ] = [true, true, true, true, true] := by
  decide +kernel

/-- The semantic view preserves exact finite values and distinguishes infinity from NaN. -/
example :
    ExecFloat.Binary.toRat? (1.5 : Binary32) = some (3 / 2 : Rat) ∧
      ExecFloat.Binary.decode (ExecFloat.Binary.infinity false : Binary32) =
        .infinity false ∧
      ExecFloat.Binary.toRat? (ExecFloat.Binary.canonicalNaN : Binary32) = none := by
  decide +kernel

abbrev Log2 := ExecFloat.Logarithmic binaryRadix

def logLeft : Log2 := ExecFloat.Logarithmic.ofSignExponent false 3
def logRight : Log2 := ExecFloat.Logarithmic.ofSignExponent true (-1)

example :
    ExecFloat.mul logLeft logRight =
      ExecFloat.Spec.mul logLeft logRight :=
  ExecFloat.Proof.mul_eq_spec logLeft logRight

example :
    ExecFloat.Logarithmic.toCode (logLeft * logRight) =
      Formats.Logarithmic.Code.value true 2 := by
  rfl

abbrev Fixed2 := ExecFloat.FixedPoint decimalRadix 2

def fixedLeft : Fixed2 := ExecFloat.FixedPoint.ofCoefficient 125
def fixedRight : Fixed2 := ExecFloat.FixedPoint.ofCoefficient (-25)
def fixedLiteral : Fixed2 := 1.25

example : ExecFloat.FixedPoint.coefficient fixedLiteral = 125 := by
  native_decide

example :
    fixedLeft + fixedRight = ExecFloat.Spec.add fixedLeft fixedRight :=
  ExecFloat.Proof.add_eq_spec fixedLeft fixedRight

example : ExecFloat.FixedPoint.coefficient (fixedLeft + fixedRight) = 100 := by
  rfl

example :
    ExecFloat.FixedPoint.coefficient
      (ExecFloat.FixedPoint.mul fixedLeft fixedRight) = -3125 := by
  rfl

abbrev Bounded8 := ExecFloat.BoundedFixedPoint decimalRadix 2 8

def boundedMaximum : Bounded8 := ExecFloat.BoundedFixedPoint.ofCoefficient 127
def boundedOne : Bounded8 := ExecFloat.BoundedFixedPoint.ofCoefficient 1

example :
    (ExecFloat.BoundedFixedPoint.ofRat? (radix := decimalRadix)
      (fractionalDigits := 2) (width := 8) (5 / 4)).map
        ExecFloat.BoundedFixedPoint.coefficient = some 125 := by
  native_decide

example :
    ExecFloat.BoundedFixedPoint.coefficient
      (ExecFloat.BoundedFixedPoint.wrapAdd boundedMaximum boundedOne) = -128 := by
  decide

example :
    ExecFloat.BoundedFixedPoint.checkedAdd boundedMaximum boundedOne = none := by
  decide

example :
    ExecFloat.BoundedFixedPoint.coefficient
      (ExecFloat.BoundedFixedPoint.saturatingAdd boundedMaximum boundedOne) = 127 := by
  decide

abbrev Bipolar := ExecFloat.Codebook Formats.Codebook.Catalog.bipolar1

def bipolarNegative : Bipolar := ExecFloat.Codebook.ofNatBits 0
def bipolarPositive : Bipolar := ExecFloat.Codebook.ofNatBits 1

example :
    Formats.Codebook.Catalog.bipolar1.denote
        (Formats.Codebook.Catalog.bipolar1.ofNatBits 0) =
      .finite (-1) := by
  simp [Formats.Codebook.ofNatBits]

example :
    ExecFloat.mul bipolarNegative bipolarPositive =
      ExecFloat.Spec.mul bipolarNegative bipolarPositive :=
  ExecFloat.Proof.mul_eq_spec bipolarNegative bipolarPositive

example : ExecFloat.Codebook.toNatBits (bipolarNegative * bipolarPositive) = 0 := by
  decide

abbrev Ternary := ExecFloat.Codebook Formats.Codebook.Catalog.ternary2

def ternaryReserved : Ternary := ExecFloat.Codebook.ofNatBits 3

example :
    Formats.Codebook.Catalog.ternary2.neg?
        (Formats.Codebook.Catalog.ternary2.ofNatBits 2) =
      some (Formats.Codebook.Catalog.ternary2.ofNatBits 1) := by
  decide

example :
    Formats.Codebook.Catalog.ternary2.mul?
        (Formats.Codebook.Catalog.ternary2.ofNatBits 2)
        (Formats.Codebook.Catalog.ternary2.ofNatBits 2) =
      some (Formats.Codebook.Catalog.ternary2.ofNatBits 1) := by
  decide

example :
    ExecFloat.Codebook.Catalog.ternary2.neg? ternaryReserved = none := by
  decide

abbrev Shared3 := ExecFloat.SharedScale 3

def sharedInput : Vector Rat 3 :=
  Vector.ofFn fun lane => (lane.val : Rat) / 2

def shared : Shared3 := ExecFloat.SharedScale.quantizeAt (-1) sharedInput

example : ExecFloat.SharedScale.exponent shared = -1 := rfl

example :
    (ExecFloat.OCP.MX.E8M0.ofExponent? 0).map
      ExecFloat.OCP.MX.E8M0.exponent? = some (some 0) := by
  decide

namespace Decimal

open Formats.DecimalInterchange Formats.DecimalInterchange.Arithmetic

private def oneDigit : Format := ⟨0, 1, 1, by decide⟩
private def fourDigits : Format := ⟨1, 1, 4, by decide⟩
private def positiveQuantum : Format := ⟨0, 1, -2, by decide⟩

-- Rounding the squares first changes the one-digit hypotenuse from 7 to 6.
example :
    hypot oneDigit .nearestEven (.finite false 5 0) (.finite false 5 0) =
      { value := .finite false 7 0, status := { inexact := true } } ∧
    sqrt oneDigit .nearestEven
      (add oneDigit .nearestEven
        (square oneDigit .nearestEven (.finite false 5 0)).value
        (square oneDigit .nearestEven (.finite false 5 0)).value).value =
      { value := .finite false 6 0, status := { inexact := true } } := by
  decide +kernel

-- Rounding the reciprocal first changes 1 / sqrt(7) from 0.4 to 0.3.
example :
    rsqrt oneDigit .nearestEven (.finite false 7 0) =
      { value := .finite false 4 (-1), status := { inexact := true } } ∧
    sqrt oneDigit .nearestEven
      (div oneDigit .nearestEven (.finite false 1 0) (.finite false 7 0)).value =
      { value := .finite false 3 (-1), status := { inexact := true } } := by
  decide +kernel

-- Cube-root midpoints exercise both parities and the reversal for negative directed results.
example :
    [RoundingMode.nearestEven.rootRound false 3 (125 / 8),
      RoundingMode.nearestEven.rootRound false 3 (343 / 8),
      RoundingMode.nearestAway.rootRound false 3 (125 / 8),
      RoundingMode.towardPositive.rootRound true 3 (125 / 8),
      RoundingMode.towardNegative.rootRound true 3 (125 / 8),
      RoundingMode.towardZero.rootRound true 3 (125 / 8)] =
      [2, 4, 3, 2, 3, 2] := by
  decide +kernel

example :
    rsqrt oneDigit .nearestEven (.finite true 0 0) =
      { value := .infinity true, status := { divideByZero := true } } ∧
    rootN oneDigit .nearestEven (.finite true 0 0) 2 =
      { value := .finite false 0 0 } ∧
    rootN oneDigit .nearestEven (.finite true 0 0) 3 =
      { value := .finite true 0 0 } := by
  decide +kernel

example :
    hypot fourDigits .nearestEven (.infinity true) (.nan true false 17) =
      { value := .infinity false } ∧
    hypot fourDigits .nearestEven (.infinity true) (.nan true true 17) =
      { value := .nan true false 17, status := { invalid := true } } := by
  decide +kernel

-- Exact powers and roots keep the preferred decimal cohort: 2.0³ = 8.000.
example :
    powInt fourDigits .nearestEven (.finite false 20 (-1)) 3 =
      { value := .finite false 8000 (-3) } ∧
    rootN fourDigits .nearestEven (.finite false 8000 (-3)) 3 =
      { value := .finite false 20 (-1) } := by
  decide +kernel

-- The smallest quantum here is +2; root(100, 2) lies between zero and 100 on this grid.
example :
    rootN positiveQuantum .nearestEven (.finite false 1 2) 2 =
      { value := .finite false 0 2, status := { underflow := true, inexact := true } } ∧
    rootN positiveQuantum .towardPositive (.finite false 1 2) 2 =
      { value := .finite false 1 2, status := { underflow := true, inexact := true } } := by
  decide +kernel

-- Apply a real error theorem to the delivered cube root of two.
example : |(1 : ℝ) - integerRoot 3 2| ≤ (1 : ℝ) / 2 := by
  obtain ⟨value, hv, herror⟩ :=
    rootN_error_le_half oneDigit .nearestEven (Or.inl rfl)
      (.finite false 2 0) 2 (by decide +kernel) (by decide) 3 (by decide)
      (by norm_num) (by decide +kernel)
  have hdelivered :
      (rootN oneDigit .nearestEven (.finite false 2 0) 3).value.toRat? = some (1 : ℚ) := by
    decide +kernel
  rw [hdelivered] at hv
  have hvalue : value = (1 : ℚ) := (Option.some.inj hv).symm
  subst value
  have hquantum :
      rootQuantum oneDigit (3 : Int).natAbs (integerRootRadicand 3 2) = 0 := by
    decide +kernel
  simpa only [hquantum, Rat.cast_one, Rat.cast_ofNat, zpow_zero] using herror

-- The integer logB of zero, infinity, and NaN lies outside ±2(emax + p - 1), IEEE 754-2019
-- §5.3.3. The bounds are 204, 798, and 12354.
example :
    (decimalExponent .decimal32 (.finite false 0 0)).value = -205 ∧
    (decimalExponent .decimal32 (.infinity true)).value = 205 ∧
    (decimalExponent .decimal64 (.finite true 0 3)).value = -799 ∧
    (decimalExponent .decimal64 (.nan false true 1)).value = 799 ∧
    (decimalExponent .decimal128 (.finite false 0 0)).value = -12355 ∧
    (decimalExponent .decimal128 (.nan false false 0)).value = 12355 := by
  decide +kernel

end Decimal

end FloatLibTests.Conformance.Formats.Configured
