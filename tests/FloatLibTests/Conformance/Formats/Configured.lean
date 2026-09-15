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
overflow, codebooks, shared-scale blocks, and OCP MX. The examples check selected kernels,
representation round trips, and rewriting public arithmetic to its specification.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.Configured

open FloatLib.Numerics
open FloatLib.Floats

private abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

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

end FloatLibTests.Conformance.Formats.Configured
