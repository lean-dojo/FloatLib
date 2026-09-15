/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# OCP MX E2M3

`E2M3` is a six-bit finite floating element from the OCP microscaling specification. The runtime
carrier is a `UInt8` with an erased proof that the code is below 64. For addition, subtraction,
multiplication, division, and square root, balanced and throughput planning select exhaustive
proved tables; latency planning selects arithmetic kernels. Fused multiply-add keeps
both a table and the generic proved kernel: throughput planning selects the table, while balanced
and latency-oriented planning avoid its larger lookup footprint.

## Reference

* Open Compute Project, *Microscaling Formats (MX) Specification*, version 1.0, E2M3,
  <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange

/-- OCP MX E2M3 six-bit element format with byte-backed storage. -/
inductive E2M3 : Type

/-- The E2M3 encoding fits in its direct byte carrier. -/
theorem e2m3_width_le_eight : FloatFormat.e2m3.bitWidth ≤ 8 := by decide

/-- Certified E2M3 addition table. -/
def e2m3AddTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m3 e2m3_width_le_eight) Model.Spec.add :=
  StaticByte.Tables.add FloatFormat.e2m3 e2m3_width_le_eight

/-- Certified E2M3 subtraction table. -/
def e2m3SubTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m3 e2m3_width_le_eight) Model.Spec.sub :=
  StaticByte.Tables.sub FloatFormat.e2m3 e2m3_width_le_eight

/-- Certified E2M3 multiplication table. -/
def e2m3MulTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m3 e2m3_width_le_eight) Model.Spec.mul :=
  StaticByte.Tables.mul FloatFormat.e2m3 e2m3_width_le_eight

/-- Certified E2M3 division table. -/
def e2m3DivTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m3 e2m3_width_le_eight) Model.Spec.div :=
  StaticByte.Tables.div FloatFormat.e2m3 e2m3_width_le_eight

/-- Certified E2M3 square-root table. -/
def e2m3SqrtTable :
    TinyTable.CertifiedUnary
      (StaticByte.encoding FloatFormat.e2m3 e2m3_width_le_eight) Model.Spec.sqrt :=
  StaticByte.Tables.sqrt FloatFormat.e2m3 e2m3_width_le_eight

/--
Certified E2M3 fused-multiply-add table.

Its generation equation is opaque, so importing this package does not normalize the 262,144
entries.
-/
def e2m3FmaTable :
    TinyTable.CertifiedTernary
      (StaticByte.encoding FloatFormat.e2m3 e2m3_width_le_eight) Model.Spec.fma :=
  StaticByte.Tables.fma FloatFormat.e2m3 e2m3_width_le_eight

@[always_inline] instance : StaticByte.Family E2M3 where
  format := FloatFormat.e2m3
  width_le_eight := e2m3_width_le_eight
  kernels := StaticByte.Kernels.fromTables e2m3_width_le_eight
    e2m3AddTable e2m3SubTable e2m3MulTable e2m3DivTable e2m3SqrtTable e2m3FmaTable

meta instance : StaticByte.FamilyInfo E2M3 where
  standard := "Open Compute Project MX E2M3 element format"

@[always_inline, instance_reducible] instance : StaticByte.Plans.TablePlan E2M3 where
  namePrefix := "OCP MX E2M3"
  addSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  addTable := e2m3AddTable
  subSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  subTable := e2m3SubTable
  mulSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  mulTable := e2m3MulTable
  divSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  divTable := e2m3DivTable
  sqrtSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  sqrtTable := e2m3SqrtTable

@[always_inline, instance_reducible] instance
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor E2M3] :
    FloatLib.Floats.ExecFloat.Fma E2M3 :=
  StaticByte.Plans.fmaTableCapability
    "OCP MX E2M3 fused-multiply-add table"
    (.throughputOnly (by decide) (by decide) (by decide))
    e2m3_width_le_eight e2m3FmaTable
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

/-- Construct E2M3 from a natural pattern, reduced to six bits. -/
@[inline] def E2M3.ofNatBits (bits : Nat) : FloatLib.Floats.ExecFloat E2M3 :=
  StaticByte.ofNatBits E2M3 bits

/-- Read the byte whose low six bits contain the E2M3 code. -/
@[inline] def E2M3.toUInt8 (value : FloatLib.Floats.ExecFloat E2M3) : UInt8 :=
  StaticByte.toUInt8 value

end FloatLib.Floats.Formats.OCP.MX
