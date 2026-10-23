/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# OCP MX E2M1

`FloatLib.Floats.E2M1` is the four-bit floating element used by OCP microscaling formats, with
type-level identity `E2M1.Family`. It stores its code in the low four bits of a `UInt8`, and the
high-bit invariant is erased at runtime. Balanced and throughput planning select exhaustive proved
tables for all six operations, including the 4,096-entry fused-multiply-add table. Latency planning
selects arithmetic kernels.

This package implements the scalar element format. OCP block semantics and scale selection are
defined under `FloatLib.Floats.Formats.OCP.MX.Standard`.

## Reference

* Open Compute Project, *Microscaling Formats (MX) Specification*, version 1.0, E2M1,
  <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange

namespace E2M1

/-- Type-level identity of `E2M1`, selecting its descriptor, carrier, and kernels. -/
inductive Family : Type

/-- The E2M1 encoding fits in its direct byte carrier. -/
theorem width_le_eight : FloatFormat.e2m1.bitWidth ≤ 8 := by decide

/-- Certified direct-byte E2M1 addition table. -/
def addTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m1 width_le_eight) Model.Spec.add :=
  StaticByte.Tables.add FloatFormat.e2m1 width_le_eight

/-- Certified direct-byte E2M1 subtraction table. -/
def subTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m1 width_le_eight) Model.Spec.sub :=
  StaticByte.Tables.sub FloatFormat.e2m1 width_le_eight

/-- Certified direct-byte E2M1 multiplication table. -/
def mulTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m1 width_le_eight) Model.Spec.mul :=
  StaticByte.Tables.mul FloatFormat.e2m1 width_le_eight

/-- Certified direct-byte E2M1 division table. -/
def divTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m1 width_le_eight) Model.Spec.div :=
  StaticByte.Tables.div FloatFormat.e2m1 width_le_eight

/-- Certified direct-byte E2M1 square-root table. -/
def sqrtTable :
    TinyTable.CertifiedUnary
      (StaticByte.encoding FloatFormat.e2m1 width_le_eight) Model.Spec.sqrt :=
  StaticByte.Tables.sqrt FloatFormat.e2m1 width_le_eight

/-- Certified direct-byte E2M1 fused-multiply-add table. -/
def fmaTable :
    TinyTable.CertifiedTernary
      (StaticByte.encoding FloatFormat.e2m1 width_le_eight) Model.Spec.fma :=
  StaticByte.Tables.fma FloatFormat.e2m1 width_le_eight

@[always_inline] instance : StaticByte.Family E2M1.Family where
  format := FloatFormat.e2m1
  width_le_eight := width_le_eight
  kernels := StaticByte.Kernels.fromTables width_le_eight
    addTable subTable mulTable divTable sqrtTable fmaTable

meta instance : StaticByte.FamilyInfo E2M1.Family where
  standard := "Open Compute Project MX E2M1 element format"

@[always_inline, instance_reducible] instance : StaticByte.Plans.TablePlan E2M1.Family where
  namePrefix := "OCP MX E2M1"
  addSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  addTable := addTable
  subSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  subTable := subTable
  mulSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  mulTable := mulTable
  divSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  divTable := divTable
  sqrtSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  sqrtTable := sqrtTable

@[always_inline, instance_reducible] instance
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor E2M1.Family] :
    FloatLib.Floats.ExecFloat.Fma E2M1.Family :=
  StaticByte.Plans.fmaTableCapability
    "OCP MX E2M1 fused-multiply-add table"
    (.balancedAndThroughput (by decide) (by decide) (by decide))
    width_le_eight fmaTable
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

end E2M1

/--
OCP MX FP4 E2M1 element: 2 exponent bits and 1 fraction bit with bias 1, every code finite, stored
in the low four bits of a byte. Under balanced and throughput planning, arithmetic, including
fused multiply-add, reads certified byte tables.
-/
abbrev E2M1 := ExecFloat E2M1.Family

/-- Construct E2M1 from a natural pattern, reduced to four bits. -/
@[inline] def E2M1.ofNatBits (bits : Nat) : E2M1 :=
  StaticByte.ofNatBits E2M1.Family bits

/-- Read the byte whose low four bits contain the E2M1 code. -/
@[inline] def E2M1.toUInt8 (value : E2M1) : UInt8 :=
  StaticByte.toUInt8 value

end FloatLib.Floats
