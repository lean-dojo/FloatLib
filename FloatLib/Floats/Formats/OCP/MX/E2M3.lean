/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# OCP MX E2M3

`FloatLib.Floats.E2M3` is a six-bit finite floating element from the OCP microscaling
specification, with type-level identity `E2M3.Family`. The runtime carrier is a `UInt8` with an
erased proof that the code is below 64. For addition, subtraction, multiplication, division, and
square root, balanced and throughput planning select exhaustive proved tables, and latency
planning selects arithmetic kernels. Fused multiply-add keeps both a table and the generic proved
kernel. Throughput planning selects the table, while balanced and latency-oriented planning avoid
its larger lookup footprint.

## Reference

* Open Compute Project, *Microscaling Formats (MX) Specification*, version 1.0, E2M3,
  <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange

namespace E2M3

/-- Type-level identity of `E2M3`, selecting its descriptor, carrier, and kernels. -/
inductive Family : Type

/-- The E2M3 encoding fits in its direct byte carrier. -/
theorem width_le_eight : FloatFormat.e2m3.bitWidth ≤ 8 := by decide

/-- Certified E2M3 addition table. -/
def addTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m3 width_le_eight) Model.Spec.add :=
  StaticByte.Tables.add FloatFormat.e2m3 width_le_eight

/-- Certified E2M3 subtraction table. -/
def subTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m3 width_le_eight) Model.Spec.sub :=
  StaticByte.Tables.sub FloatFormat.e2m3 width_le_eight

/-- Certified E2M3 multiplication table. -/
def mulTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m3 width_le_eight) Model.Spec.mul :=
  StaticByte.Tables.mul FloatFormat.e2m3 width_le_eight

/-- Certified E2M3 division table. -/
def divTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e2m3 width_le_eight) Model.Spec.div :=
  StaticByte.Tables.div FloatFormat.e2m3 width_le_eight

/-- Certified E2M3 square-root table. -/
def sqrtTable :
    TinyTable.CertifiedUnary
      (StaticByte.encoding FloatFormat.e2m3 width_le_eight) Model.Spec.sqrt :=
  StaticByte.Tables.sqrt FloatFormat.e2m3 width_le_eight

/--
Certified E2M3 fused-multiply-add table.

The table is generated lazily at its first lookup, so importing this package does not compute
its 262,144 entries.
-/
def fmaTable :
    TinyTable.CertifiedTernary
      (StaticByte.encoding FloatFormat.e2m3 width_le_eight) Model.Spec.fma :=
  StaticByte.Tables.fma FloatFormat.e2m3 width_le_eight

@[always_inline] instance : StaticByte.Family E2M3.Family where
  format := FloatFormat.e2m3
  width_le_eight := width_le_eight
  kernels := StaticByte.Kernels.fromTables width_le_eight
    addTable subTable mulTable divTable sqrtTable fmaTable

meta instance : StaticByte.FamilyInfo E2M3.Family where
  standard := "Open Compute Project MX E2M3 element format"

@[always_inline, instance_reducible] instance : StaticByte.Plans.TablePlan E2M3.Family where
  namePrefix := "OCP MX E2M3"
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
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor E2M3.Family] :
    FloatLib.Floats.ExecFloat.Fma E2M3.Family :=
  StaticByte.Plans.fmaTableCapability
    "OCP MX E2M3 fused-multiply-add table"
    (.throughputOnly (by decide) (by decide) (by decide))
    width_le_eight fmaTable
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

end E2M3

/--
OCP MX FP6 E2M3 element: 2 exponent and 3 fraction bits with bias 1, every code finite, stored in
the low six bits of a byte. Throughput planning answers all six operations from certified byte
tables.
-/
abbrev E2M3 := ExecFloat E2M3.Family

/-- Construct E2M3 from a natural pattern, reduced to six bits. -/
@[inline] def E2M3.ofNatBits (bits : Nat) : E2M3 :=
  StaticByte.ofNatBits E2M3.Family bits

/-- Read the byte whose low six bits contain the E2M3 code. -/
@[inline] def E2M3.toUInt8 (value : E2M3) : UInt8 :=
  StaticByte.toUInt8 value

end FloatLib.Floats
