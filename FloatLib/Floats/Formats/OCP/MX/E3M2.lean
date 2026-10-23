/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# OCP MX E3M2

`FloatLib.Floats.E3M2` is a six-bit finite floating element from the OCP microscaling
specification, with type-level identity `E3M2.Family`. Its direct runtime carrier is a byte with
an erased `< 64` invariant. For addition, subtraction, multiplication, division, and square root,
balanced and throughput planning select exhaustive proved tables, and latency planning selects
arithmetic kernels. Fused multiply-add keeps both a table and the generic proved kernel.
Throughput planning selects the table, while balanced and latency-oriented planning avoid its
larger lookup footprint.

## Reference

* Open Compute Project, *Microscaling Formats (MX) Specification*, version 1.0, E3M2,
  <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange

namespace E3M2

/-- Type-level identity of `E3M2`, selecting its descriptor, carrier, and kernels. -/
inductive Family : Type

/-- The E3M2 encoding fits in its direct byte carrier. -/
theorem width_le_eight : FloatFormat.e3m2.bitWidth ≤ 8 := by decide

/-- Certified E3M2 addition table. -/
def addTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e3m2 width_le_eight) Model.Spec.add :=
  StaticByte.Tables.add FloatFormat.e3m2 width_le_eight

/-- Certified E3M2 subtraction table. -/
def subTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e3m2 width_le_eight) Model.Spec.sub :=
  StaticByte.Tables.sub FloatFormat.e3m2 width_le_eight

/-- Certified E3M2 multiplication table. -/
def mulTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e3m2 width_le_eight) Model.Spec.mul :=
  StaticByte.Tables.mul FloatFormat.e3m2 width_le_eight

/-- Certified E3M2 division table. -/
def divTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e3m2 width_le_eight) Model.Spec.div :=
  StaticByte.Tables.div FloatFormat.e3m2 width_le_eight

/-- Certified E3M2 square-root table. -/
def sqrtTable :
    TinyTable.CertifiedUnary
      (StaticByte.encoding FloatFormat.e3m2 width_le_eight) Model.Spec.sqrt :=
  StaticByte.Tables.sqrt FloatFormat.e3m2 width_le_eight

/-- Certified E3M2 fused-multiply-add table. -/
def fmaTable :
    TinyTable.CertifiedTernary
      (StaticByte.encoding FloatFormat.e3m2 width_le_eight) Model.Spec.fma :=
  StaticByte.Tables.fma FloatFormat.e3m2 width_le_eight

@[always_inline] instance : StaticByte.Family E3M2.Family where
  format := FloatFormat.e3m2
  width_le_eight := width_le_eight
  kernels := StaticByte.Kernels.fromTables width_le_eight
    addTable subTable mulTable divTable sqrtTable fmaTable

meta instance : StaticByte.FamilyInfo E3M2.Family where
  standard := "Open Compute Project MX E3M2 element format"

@[always_inline, instance_reducible] instance : StaticByte.Plans.TablePlan E3M2.Family where
  namePrefix := "OCP MX E3M2"
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
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor E3M2.Family] :
    FloatLib.Floats.ExecFloat.Fma E3M2.Family :=
  StaticByte.Plans.fmaTableCapability
    "OCP MX E3M2 fused-multiply-add table"
    (.throughputOnly (by decide) (by decide) (by decide))
    width_le_eight fmaTable
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

end E3M2

/--
OCP MX FP6 E3M2 element: 3 exponent and 2 fraction bits with bias 3, every code finite, stored in
the low six bits of a byte. Throughput planning answers all six operations from certified byte
tables.
-/
abbrev E3M2 := ExecFloat E3M2.Family

/-- Construct E3M2 from a natural pattern, reduced to six bits. -/
@[inline] def E3M2.ofNatBits (bits : Nat) : E3M2 :=
  StaticByte.ofNatBits E3M2.Family bits

/-- Read the byte whose low six bits contain the E3M2 code. -/
@[inline] def E3M2.toUInt8 (value : E3M2) : UInt8 :=
  StaticByte.toUInt8 value

end FloatLib.Floats
