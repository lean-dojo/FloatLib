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

-- Field notation reaches the configured operations, which decode to the model operation, also on
-- limb-backed values. `ExecFloat.sqrt` and `ExecFloat.fma` are the certified selected defaults.
example (x y z : Binary32) :
    x.sqrt.toModel = Formats.BinaryInterchange.Model.sqrt x.toModel ∧
      (x.fma y z).toModel = Formats.BinaryInterchange.Model.fma x.toModel y.toModel z.toModel :=
  ⟨ExecFloat.Binary.toModel_sqrt x .nearest, ExecFloat.Binary.toModel_fma x y z .nearest⟩

example (x y z : ExecFloat.BinaryLimbs 19 236) :
    x.sqrt.toModel = Formats.BinaryInterchange.Model.sqrt x.toModel ∧
      (x.fma y z).toModel = Formats.BinaryInterchange.Model.fma x.toModel y.toModel z.toModel :=
  ⟨ExecFloat.Binary.toModel_sqrt x .nearest, ExecFloat.Binary.toModel_fma x y z .nearest⟩

example (x y z : Binary32) :
    ExecFloat.sqrt x = ExecFloat.Spec.sqrt x ∧ ExecFloat.fma x y z = ExecFloat.Spec.fma x y z :=
  ⟨ExecFloat.Proof.sqrt_eq_spec x, ExecFloat.Proof.fma_eq_spec x y z⟩

example (x y z : ExecFloat.BinaryLimbs 19 236) :
    ExecFloat.sqrt x = ExecFloat.Spec.sqrt x ∧ ExecFloat.fma x y z = ExecFloat.Spec.fma x y z :=
  ⟨ExecFloat.Proof.sqrt_eq_spec x, ExecFloat.Proof.fma_eq_spec x y z⟩

-- Chained representation methods and directed rounding retain the configured receiver type.
example :
    (-4 : Binary32).abs.nextUp.toNatBits = 0x40800001 ∧
      (4 : Binary32).isFinite = true ∧
      ((4 : Binary32).sqrt (mode := .up)).toNatBits = 0x40000000 := by
  decide +kernel

example (x : ExecFloat.BinaryLimbs 19 236) :
    x.abs.nextUp.toNatBits = ExecFloat.Binary.toNatBits
      (ExecFloat.Binary.nextUp (ExecFloat.Binary.abs x)) := rfl

-- The default configured operation is the selected kernel that the operators run, whether it is
-- written qualified, with an explicit nearest-even mode, or by field notation.
-- benchmarks/scripts/checks/configured-binary-codegen.sh checks the generated code.
example (x y z : Binary32) :
    x.add y = x + y ∧ ExecFloat.Binary.sub x y (mode := .nearest) = x - y ∧ x.mul y = x * y ∧
      x.div y = x / y ∧ x.sqrt = ExecFloat.sqrt x ∧ x.fma y z = ExecFloat.fma x y z :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Partial application and higher-order use keep the default options.
example (xs ys : List Binary32) :
    List.zipWith ExecFloat.Binary.add xs ys = List.zipWith (· + ·) xs ys := rfl

example : (ExecFloat.Binary.sqrt : Binary32 → Binary32) = ExecFloat.sqrt := rfl

-- A symbolic `status` determines the result type by cases.
example (x y : Binary32) (status : Bool) :
    ExecFloat.Binary.add x y (mode := .up) (status := status) =
      match status with
      | true => ExecFloat.Binary.add x y (mode := .up) (status := true)
      | false => ExecFloat.Binary.add x y (mode := .up) := by
  cases status <;> rfl

-- A codec for an unrelated format must not change inference for a concrete binary receiver.
example {format : Formats.BinaryInterchange.FloatFormat}
    {plan : Formats.BinaryInterchange.Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Formats.BinaryInterchange.Model format) code]
    (x : ExecFloat.Binary 8 23) :
    (Formats.BinaryInterchange.Model.cast _ format x.abs.nextUp.toModel (status := true)).value =
      (Formats.BinaryInterchange.Model.cast _ format
        (ExecFloat.Binary.toModel (ExecFloat.Binary.nextUp (ExecFloat.Binary.abs x)))
        (status := true)).value := rfl

-- The same unrelated codec leaves configured arithmetic on its selected capability, and the
-- decoding theorem still applies by `simp`, with instance search proving its capability-reference
-- argument.
example {format : Formats.BinaryInterchange.FloatFormat}
    {plan : Formats.BinaryInterchange.Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Formats.BinaryInterchange.Model format) code]
    (x y : ExecFloat.Binary 8 23) :
    x.add y = x + y ∧ (x.add y).toModel = Formats.BinaryInterchange.Model.add x.toModel y.toModel :=
  ⟨rfl, by simp⟩

/-!
## Capability references of the decoding theorems

The configured decoding theorems `ExecFloat.Binary.toModel_add` through `toModel_sqrt` and the
projections `value_add` through `value_sqrt` take the instance argument
`ExecFloat.Capability.HasSpec cap Configured.Spec.add` (and its siblings). Instance search proves it
when the selected capability's reference operation unfolds to the configured model operation, as
for every capability the library declares. A capability whose reference is only propositionally
equal needs an explicit witness, and one with a different reference does not get the theorems.
-/

section CapabilityReference

open Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Model format) code]
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

-- On a receiver with a caller-supplied codec and planning policy, the generic capabilities name
-- the configured model operations, so the decoding and projection theorems apply by name and by
-- `simp` in every rounding direction.
example (x y z : ExecFloat (Configured.Family format code plan)) (mode : Model.IEEERoundingMode) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.add x y (mode := mode)) =
        Model.add (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) (mode := mode) ∧
      (ExecFloat.Binary.fma x y z (mode := mode) (status := true)).value =
        ExecFloat.Binary.fma x y z (mode := mode) :=
  ⟨ExecFloat.Binary.toModel_add x y mode, ExecFloat.Binary.value_fma x y z mode⟩

example (x y z : ExecFloat (Configured.Family format code plan)) (mode : Model.IEEERoundingMode) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.sub x y (mode := mode)) =
        Model.sub (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) (mode := mode) ∧
      ExecFloat.Binary.toModel (ExecFloat.Binary.mul x y (mode := mode)) =
        Model.mul (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) (mode := mode) ∧
      ExecFloat.Binary.toModel (ExecFloat.Binary.div x y (mode := mode)) =
        Model.div (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) (mode := mode) ∧
      ExecFloat.Binary.toModel (ExecFloat.Binary.sqrt x (mode := mode)) =
        Model.sqrt (ExecFloat.Binary.toModel x) (mode := mode) ∧
      ExecFloat.Binary.toModel (ExecFloat.Binary.fma x y z (mode := mode)) =
        Model.fma (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)
          (ExecFloat.Binary.toModel z) (mode := mode) ∧
      (ExecFloat.Binary.add x y (mode := mode) (status := true)).value =
        ExecFloat.Binary.add x y (mode := mode) ∧
      (ExecFloat.Binary.sub x y (mode := mode) (status := true)).value =
        ExecFloat.Binary.sub x y (mode := mode) ∧
      (ExecFloat.Binary.mul x y (mode := mode) (status := true)).value =
        ExecFloat.Binary.mul x y (mode := mode) ∧
      (ExecFloat.Binary.div x y (mode := mode) (status := true)).value =
        ExecFloat.Binary.div x y (mode := mode) ∧
      (ExecFloat.Binary.sqrt x (mode := mode) (status := true)).value =
        ExecFloat.Binary.sqrt x (mode := mode) := by
  simp

/-- An addition capability whose reference re-encodes the decoded configured sum. -/
@[instance_reducible] private def reencodedAdd :
    ExecFloat.Add (Configured.Family format code plan) :=
  ExecFloat.Capability.ofCertified .add
    (ExecFloat.Backend.Certified.reference
      { name := "reencoded", kind := .generic, steadyCost := 1 }
      (fun x y => ExecFloat.ModelCodec.encode (F := Configured.Family format code plan)
        (Model := Model format) (plan := plan)
        (ExecFloat.ModelCodec.decode (Model := Model format) (plan := plan)
          (Configured.Spec.add x y))))

/-- The re-encoded reference is configured model addition by the codec's round-trip law. -/
private theorem reencodedAdd_hasSpec :
    ExecFloat.Capability.HasSpec (reencodedAdd (format := format) (plan := plan) (code := code))
      Configured.Spec.add :=
  ⟨funext fun _ => funext fun _ => ExecFloat.ModelCodec.encode_decode _⟩

-- That equality is not definitional, so instance search does not find it.
/--
error: failed to synthesize instance of type class
  ExecFloat.Capability.HasSpec reencodedAdd Configured.Spec.add
-/
#guard_msgs (substring := true) in
example :
    ExecFloat.Capability.HasSpec (reencodedAdd (format := format) (plan := plan) (code := code))
      Configured.Spec.add :=
  inferInstance

attribute [local instance] reencodedAdd reencodedAdd_hasSpec

-- With the capability selected and its witness in scope, both theorems apply to it.
example : (inferInstance : ExecFloat.Add (Configured.Family format code plan)) = reencodedAdd :=
  rfl

example (x y : ExecFloat (Configured.Family format code plan)) (mode : Model.IEEERoundingMode) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.add x y (mode := mode)) =
        Model.add (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) (mode := mode) ∧
      (ExecFloat.Binary.add x y (mode := mode) (status := true)).value =
        ExecFloat.Binary.add x y (mode := mode) :=
  ⟨ExecFloat.Binary.toModel_add x y mode, ExecFloat.Binary.value_add x y mode⟩

end CapabilityReference

section MismatchedReference

open Formats.BinaryInterchange

/-- An addition capability whose reference operation is configured subtraction. -/
@[instance_reducible] private def subtractingAdd
    {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Model format) code]
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] :
    ExecFloat.Add (Configured.Family format code plan) :=
  ExecFloat.Capability.ofCertified .add
    (ExecFloat.Backend.Certified.reference
      { name := "subtracting", kind := .generic, steadyCost := 1 } Configured.Spec.sub)

attribute [local instance] subtractingAdd

-- The default call runs the capability and the status call runs the model, so with this capability
-- `value_add` would be false: `1 + 1` is zero by default and two with status.
example :
    ExecFloat.Binary.toNatBits ((1 : Binary32).add 1) = 0 ∧
      ExecFloat.Binary.toNatBits ((1 : Binary32).add 1 (status := true)).value = 0x40000000 := by
  decide +kernel

-- Without a witness, which cannot exist here, neither theorem applies.
/--
error: failed to synthesize instance of type class
  ExecFloat.Capability.HasSpec subtractingAdd Configured.Spec.add
-/
#guard_msgs (substring := true) in
example (x y : Binary32) : (x.add y).toModel = Model.add x.toModel y.toModel :=
  ExecFloat.Binary.toModel_add x y .nearest

/--
error: failed to synthesize instance of type class
  ExecFloat.Capability.HasSpec subtractingAdd Configured.Spec.add
-/
#guard_msgs (substring := true) in
example (x y : Binary32) : (x.add y (status := true)).value = x.add y :=
  ExecFloat.Binary.value_add x y .nearest

example (x y : Binary32) (_h : (x.add y).toModel ≠ Model.add x.toModel y.toModel) : True := by
  fail_if_success simp only [ExecFloat.Binary.toModel_add] at _h
  trivial

end MismatchedReference

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
    (ExecFloat.BoundedFixedPoint.ofRat (radix := decimalRadix)
      (fractionalDigits := 2) (width := 8) (5 / 4)).map
        ExecFloat.BoundedFixedPoint.coefficient = some 125 := by
  native_decide

-- The coefficient 200 of `2` does not fit eight bits: the default rejects it, `.wrap` reduces it
-- to `200 - 256`, and `.saturate` clamps it to 127.
example :
    let ofRat := ExecFloat.BoundedFixedPoint.ofRat (radix := decimalRadix)
      (fractionalDigits := 2) (width := 8) 2
    (ofRat.map ExecFloat.BoundedFixedPoint.coefficient,
      (ExecFloat.BoundedFixedPoint.ofRat (radix := decimalRadix) (fractionalDigits := 2)
        (width := 8) 2 (overflow := .wrap)).coefficient,
      (ExecFloat.BoundedFixedPoint.ofRat (radix := decimalRadix) (fractionalDigits := 2)
        (width := 8) 2 (overflow := .saturate)).coefficient) = (none, -56, 127) := by
  decide +kernel

example :
    ExecFloat.BoundedFixedPoint.coefficient
      (ExecFloat.BoundedFixedPoint.add boundedMaximum boundedOne (overflow := .wrap)) = -128 := by
  decide

example :
    ExecFloat.BoundedFixedPoint.add boundedMaximum boundedOne = none := by
  decide

example :
    ExecFloat.BoundedFixedPoint.coefficient
      (ExecFloat.BoundedFixedPoint.add boundedMaximum boundedOne (overflow := .saturate)) =
        127 := by
  decide

-- The exact product 16129 needs fifteen bits: eight bits reject, wrap to 1, or saturate to 127,
-- and sixteen bits hold it.
example :
    ((ExecFloat.BoundedFixedPoint.mul 8 boundedMaximum boundedMaximum).map
        ExecFloat.BoundedFixedPoint.coefficient,
      (ExecFloat.BoundedFixedPoint.mul 8 boundedMaximum boundedMaximum .wrap).coefficient,
      (ExecFloat.BoundedFixedPoint.mul 8 boundedMaximum boundedMaximum .saturate).coefficient,
      (ExecFloat.BoundedFixedPoint.mul 16 boundedMaximum boundedMaximum).map
        ExecFloat.BoundedFixedPoint.coefficient) = (none, 1, 127, some 16129) := by
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

def sharedInput : Vector Rat 3 :=
  Vector.ofFn fun lane => (lane.val : Rat) / 2

def shared : ExecFloat.SharedScale 3 := ExecFloat.SharedScale.quantizeAt (-1) sharedInput

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

-- Degree zero is invalid even for a quiet or signaling NaN input.
example :
    rootN oneDigit .nearestEven (.nan true false 3) 0 =
      { value := .nan false false 0, status := { invalid := true } } ∧
    rootN oneDigit .nearestEven (.nan true true 3) 0 =
      { value := .nan false false 0, status := { invalid := true } } := by
  decide +kernel

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

-- The smallest quantum here is +2, so root(100, 2) lies between zero and 100 on this grid.
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
