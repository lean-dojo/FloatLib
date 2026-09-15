/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# OCP MX E2M1

`E2M1` is the four-bit floating element used by OCP microscaling formats. This nominal package
stores its code in the low four bits of a `UInt8`; the high-bit invariant is erased at runtime.
Balanced and throughput planning select exhaustive proved tables for all six operations,
including the 4,096-entry fused-multiply-add table. Latency planning selects arithmetic kernels.

This package implements the scalar element format. OCP block semantics and scale selection are
defined under `FloatLib.Floats.Formats.OCP.MX.Standard`.

## Reference

* Open Compute Project, *Microscaling Formats (MX) Specification*, version 1.0, E2M1,
  <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange

/-- OCP MX E2M1 four-bit element format with byte-backed storage. -/
inductive E2M1 : Type

/-- The E2M1 encoding fits in its direct byte carrier. -/
theorem e2m1_width_le_eight : FloatFormat.e2m1.bitWidth ≤ 8 := by decide

/-- Certified direct-byte E2M1 addition table. -/
def e2m1AddTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m1 e2m1_width_le_eight) Model.Spec.add :=
  StaticByte.Tables.add FloatFormat.e2m1 e2m1_width_le_eight

/-- Certified direct-byte E2M1 subtraction table. -/
def e2m1SubTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m1 e2m1_width_le_eight) Model.Spec.sub :=
  StaticByte.Tables.sub FloatFormat.e2m1 e2m1_width_le_eight

/-- Certified direct-byte E2M1 multiplication table. -/
def e2m1MulTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m1 e2m1_width_le_eight) Model.Spec.mul :=
  StaticByte.Tables.mul FloatFormat.e2m1 e2m1_width_le_eight

/-- Certified direct-byte E2M1 division table. -/
def e2m1DivTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m1 e2m1_width_le_eight) Model.Spec.div :=
  StaticByte.Tables.div FloatFormat.e2m1 e2m1_width_le_eight

/-- Certified direct-byte E2M1 square-root table. -/
def e2m1SqrtTable :
    TinyTable.CertifiedUnary
      (StaticByte.encoding FloatFormat.e2m1 e2m1_width_le_eight) Model.Spec.sqrt :=
  StaticByte.Tables.sqrt FloatFormat.e2m1 e2m1_width_le_eight

/-- Certified direct-byte E2M1 fused-multiply-add table. -/
def e2m1FmaTable :
    TinyTable.CertifiedTernary
      (StaticByte.encoding FloatFormat.e2m1 e2m1_width_le_eight) Model.Spec.fma :=
  StaticByte.Tables.fma FloatFormat.e2m1 e2m1_width_le_eight

@[always_inline] instance : StaticByte.Family E2M1 where
  format := FloatFormat.e2m1
  width_le_eight := e2m1_width_le_eight
  kernels := StaticByte.Kernels.fromTables e2m1_width_le_eight
    e2m1AddTable e2m1SubTable e2m1MulTable e2m1DivTable e2m1SqrtTable e2m1FmaTable

meta instance : StaticByte.FamilyInfo E2M1 where
  standard := "Open Compute Project MX E2M1 element format"

@[always_inline, instance_reducible] instance : StaticByte.Plans.TablePlan E2M1 where
  namePrefix := "OCP MX E2M1"
  addSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  addTable := e2m1AddTable
  subSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  subTable := e2m1SubTable
  mulSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  mulTable := e2m1MulTable
  divSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  divTable := e2m1DivTable
  sqrtSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  sqrtTable := e2m1SqrtTable

@[always_inline, instance_reducible] instance
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor E2M1] :
    FloatLib.Floats.ExecFloat.Fma E2M1 :=
  StaticByte.Plans.fmaTableCapability
    "OCP MX E2M1 fused-multiply-add table"
    (.balancedAndThroughput (by decide) (by decide) (by decide))
    e2m1_width_le_eight e2m1FmaTable
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

/-- Construct E2M1 from a natural pattern, reduced to four bits. -/
@[inline] def E2M1.ofNatBits (bits : Nat) : FloatLib.Floats.ExecFloat E2M1 :=
  StaticByte.ofNatBits E2M1 bits

/-- Read the byte whose low four bits contain the E2M1 code. -/
@[inline] def E2M1.toUInt8 (value : FloatLib.Floats.ExecFloat E2M1) : UInt8 :=
  StaticByte.toUInt8 value

end FloatLib.Floats.Formats.OCP.MX
