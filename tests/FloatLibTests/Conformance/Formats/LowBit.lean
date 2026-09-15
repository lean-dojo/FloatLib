/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat
public import FloatLib.Floats.Formats.FiniteOnly
public import FloatLib.Floats.Formats.OCP
public import FloatLibTests.Accounting

/-!
# Nominal low-bit format regression checks

These tests exercise the public, format-independent `ExecFloat` API through the nominal OCP FP8,
OCP MX, and finite-only FNUZ types. The proof below checks that every family exposes all six
refinement equations; the executable report checks canonical construction and representative
arithmetic codes.

The exhaustive table-to-specification proofs remain beside their kernels in
`ExecFloat.Backends.TinyTable`. This module instead guards the new nominal packaging and direct
byte boundary against integration regressions. It also checks the distinct E8M0 shared-scale
contract and representative block decoding behavior.

## References

* Open Compute Project, *8-bit Floating Point Specification*, revision 1.0,
  <https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1>.
* Open Compute Project, *Microscaling Formats (MX) Specification*, version 1.0,
  <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
* ONNX, *Float stored in 8 bits*,
  <https://onnx.ai/onnx/technical/float8.html>.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

namespace FloatLibTests.Conformance.Formats.LowBit

open FloatLib

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.FiniteOnly
open FloatLib.Floats.Formats.OCP.FP8
open FloatLib.Floats.Formats.OCP.MX
open FloatLibTests.Accounting

universe u

/-- Every static-byte family supplies the universal six-operation refinement interface. -/
theorem all_operations_refine (F : Type u) [StaticByte.Family F]
    (left right addend : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.add left right =
        FloatLib.Floats.ExecFloat.Spec.add left right ∧
      FloatLib.Floats.ExecFloat.sub left right =
        FloatLib.Floats.ExecFloat.Spec.sub left right ∧
      FloatLib.Floats.ExecFloat.mul left right =
        FloatLib.Floats.ExecFloat.Spec.mul left right ∧
      FloatLib.Floats.ExecFloat.div left right =
        FloatLib.Floats.ExecFloat.Spec.div left right ∧
      FloatLib.Floats.ExecFloat.sqrt left =
        FloatLib.Floats.ExecFloat.Spec.sqrt left ∧
      FloatLib.Floats.ExecFloat.fma left right addend =
        FloatLib.Floats.ExecFloat.Spec.fma left right addend := by
  exact
    ⟨ FloatLib.Floats.ExecFloat.Proof.add_eq_spec left right
    , FloatLib.Floats.ExecFloat.Proof.sub_eq_spec left right
    , FloatLib.Floats.ExecFloat.Proof.mul_eq_spec left right
    , FloatLib.Floats.ExecFloat.Proof.div_eq_spec left right
    , FloatLib.Floats.ExecFloat.Proof.sqrt_eq_spec left
    , FloatLib.Floats.ExecFloat.Proof.fma_eq_spec left right addend ⟩

/-- Count constructor codes that do not reduce canonically to the family width. -/
def constructorFailures (F : Type) [StaticByte.Family F] (codeCount samples : Nat) : Nat :=
  countWhereFailures (List.range samples) fun bits =>
    StaticByte.toNatBits (StaticByte.ofNatBits F bits) == bits % codeCount

/-- Representative public additions guard the nominal dispatch and byte repacking boundaries. -/
def arithmeticFailures : Thunk Nat := ⟨fun _ =>
  countFailures
    [ E4M3FN.toUInt8
      (FloatLib.Floats.ExecFloat.add (E4M3FN.ofNatBits 0x38) (E4M3FN.ofNatBits 0x40)) ==
        0x44
    , E5M2.toUInt8
      (FloatLib.Floats.ExecFloat.add (E5M2.ofNatBits 0x3c) (E5M2.ofNatBits 0x40)) ==
        0x42
    , E2M1.toUInt8
      (FloatLib.Floats.ExecFloat.add (E2M1.ofNatBits 0x2) (E2M1.ofNatBits 0x4)) ==
        0x5
    , E2M3.toUInt8
      (FloatLib.Floats.ExecFloat.add (E2M3.ofNatBits 0x8) (E2M3.ofNatBits 0x10)) ==
        0x14
    , E3M2.toUInt8
      (FloatLib.Floats.ExecFloat.add (E3M2.ofNatBits 0xc) (E3M2.ofNatBits 0x10)) ==
        0x12
    , E4M3FNUZ.toUInt8
      (FloatLib.Floats.ExecFloat.add
        (E4M3FNUZ.ofNatBits 0x40) (E4M3FNUZ.ofNatBits 0x48)) ==
        0x4c
    , E5M2FNUZ.toUInt8
      (FloatLib.Floats.ExecFloat.add
        (E5M2FNUZ.ofNatBits 0x40) (E5M2FNUZ.ofNatBits 0x44)) ==
        0x46
    , E2M1.toUInt8 (1 : FloatLib.Floats.ExecFloat E2M1) == 0x02
    , E2M1.toUInt8 (-1 : FloatLib.Floats.ExecFloat E2M1) == 0x0a
    ]⟩

/-! ## E8M0 shared-scale checks -/

section E8M0

open FloatLib.Floats.Formats.OCP.MX.E8M0
open FloatLib.Numerics

example {scaleValue value : Numerics.Dyadic}
    (scale : AtFinite scaleValue)
    (x : (NumericalSystem.exact Numerics.Dyadic).AtFinite value) :
    Option.map (NumericalSystem.exact Numerics.Dyadic).denote
        (scaleDyadic? scale.1 x.1) =
      some (.finite (scaledValue scaleValue value)) := by
  exact Operation.Checked2.map_denote scaleDyadic_refines scale x

example : exponent? (ofNatBits 128) = some 1 := by
  numerics_reduce

example : exponent? (ofNatBits 0) = some (-127) := by
  native_decide

example : exponent? (ofNatBits 254) = some 127 := by
  native_decide

example : isNaN (ofNatBits 255) = true := by
  native_decide

example :
    decodeBlock? (ofNatBits 128)
      #[Model.ofNatBits (fmt := FloatFormat.e2m1) 0x02,
        Model.ofNatBits (fmt := FloatFormat.e2m1) 0x07] =
      some #[{ negative := false, significand := 2, exponent := 0 },
        { negative := false, significand := 3, exponent := 2 }] := by
  native_decide

example (scale : FloatLib.Floats.ExecFloat.OCP.MX.E8M0)
    (elements : Array (FloatLib.Floats.ExecFloat E2M1)) :
    FloatLib.Floats.ExecFloat.OCP.MX.Block.values
        (FloatLib.Floats.ExecFloat.OCP.MX.Block.ofElements scale elements) =
      elements.map fun value => StaticByte.toModel value := by
  exact FloatLib.Floats.ExecFloat.OCP.MX.Block.values_ofElements scale elements

end E8M0

/-- Number of nominal low-bit packaging regressions. -/
def totalFailures : Thunk Nat := ⟨fun _ =>
  constructorFailures E2M1 16 512 +
  constructorFailures E2M3 64 512 +
  constructorFailures E3M2 64 512 +
  constructorFailures E4M3FN 256 512 +
  constructorFailures E5M2 256 512 +
  constructorFailures E4M3FNUZ 256 512 +
  constructorFailures E5M2FNUZ 256 512 +
  arithmeticFailures.get⟩

/-- Check nominal construction and arithmetic when the core suite runs. -/
def report : Thunk ReportSection := ⟨fun _ =>
  let failures := totalFailures.get
  { title := "low-bit formats"
    body := s!"TOTAL: {failures}"
    failures }⟩

end FloatLibTests.Conformance.Formats.LowBit
