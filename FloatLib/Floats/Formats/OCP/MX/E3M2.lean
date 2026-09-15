/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# OCP MX E3M2

`E3M2` is a six-bit finite floating element from the OCP microscaling specification. Its direct
runtime carrier is a byte with an erased `< 64` invariant. For addition, subtraction,
multiplication, division, and square root, balanced and throughput planning select exhaustive
proved tables; latency planning selects arithmetic kernels. Fused multiply-add keeps both a table
and the generic proved kernel: throughput planning selects the table, while balanced and
latency-oriented planning avoid its larger lookup footprint.

## Reference

* Open Compute Project, *Microscaling Formats (MX) Specification*, version 1.0, E3M2,
  <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange

/-- OCP MX E3M2 six-bit element format with byte-backed storage. -/
inductive E3M2 : Type

/-- The E3M2 encoding fits in its direct byte carrier. -/
theorem e3m2_width_le_eight : FloatFormat.e3m2.bitWidth ≤ 8 := by decide

/-- Certified E3M2 addition table. -/
def e3m2AddTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e3m2 e3m2_width_le_eight) Model.Spec.add :=
  StaticByte.Tables.add FloatFormat.e3m2 e3m2_width_le_eight

/-- Certified E3M2 subtraction table. -/
def e3m2SubTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e3m2 e3m2_width_le_eight) Model.Spec.sub :=
  StaticByte.Tables.sub FloatFormat.e3m2 e3m2_width_le_eight

/-- Certified E3M2 multiplication table. -/
def e3m2MulTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e3m2 e3m2_width_le_eight) Model.Spec.mul :=
  StaticByte.Tables.mul FloatFormat.e3m2 e3m2_width_le_eight

/-- Certified E3M2 division table. -/
def e3m2DivTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e3m2 e3m2_width_le_eight) Model.Spec.div :=
  StaticByte.Tables.div FloatFormat.e3m2 e3m2_width_le_eight

/-- Certified E3M2 square-root table. -/
def e3m2SqrtTable :
    TinyTable.CertifiedUnary
      (StaticByte.encoding FloatFormat.e3m2 e3m2_width_le_eight) Model.Spec.sqrt :=
  StaticByte.Tables.sqrt FloatFormat.e3m2 e3m2_width_le_eight

/-- Certified E3M2 fused-multiply-add table. -/
def e3m2FmaTable :
    TinyTable.CertifiedTernary
      (StaticByte.encoding FloatFormat.e3m2 e3m2_width_le_eight) Model.Spec.fma :=
  StaticByte.Tables.fma FloatFormat.e3m2 e3m2_width_le_eight

@[always_inline] instance : StaticByte.Family E3M2 where
  format := FloatFormat.e3m2
  width_le_eight := e3m2_width_le_eight
  kernels := StaticByte.Kernels.fromTables e3m2_width_le_eight
    e3m2AddTable e3m2SubTable e3m2MulTable e3m2DivTable e3m2SqrtTable e3m2FmaTable

meta instance : StaticByte.FamilyInfo E3M2 where
  standard := "Open Compute Project MX E3M2 element format"

@[always_inline, instance_reducible] instance : StaticByte.Plans.TablePlan E3M2 where
  namePrefix := "OCP MX E3M2"
  addSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  addTable := e3m2AddTable
  subSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  subTable := e3m2SubTable
  mulSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  mulTable := e3m2MulTable
  divSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  divTable := e3m2DivTable
  sqrtSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  sqrtTable := e3m2SqrtTable

@[always_inline, instance_reducible] instance
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor E3M2] :
    FloatLib.Floats.ExecFloat.Fma E3M2 :=
  StaticByte.Plans.fmaTableCapability
    "OCP MX E3M2 fused-multiply-add table"
    (.throughputOnly (by decide) (by decide) (by decide))
    e3m2_width_le_eight e3m2FmaTable
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

/-- Construct E3M2 from a natural pattern, reduced to six bits. -/
@[inline] def E3M2.ofNatBits (bits : Nat) : FloatLib.Floats.ExecFloat E3M2 :=
  StaticByte.ofNatBits E3M2 bits

/-- Read the byte whose low six bits contain the E3M2 code. -/
@[inline] def E3M2.toUInt8 (value : FloatLib.Floats.ExecFloat E3M2) : UInt8 :=
  StaticByte.toUInt8 value

end FloatLib.Floats.Formats.OCP.MX
