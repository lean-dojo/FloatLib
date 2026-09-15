/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# OCP FP8 E4M3FN

OCP E4M3FN has a nominal format identity and a direct `UInt8` runtime carrier. For addition,
subtraction, multiplication, division, and square root, balanced and throughput planning select
exhaustive byte tables; latency planning selects the arithmetic kernels. Fused multiply-add uses
the proved generic single-rounding kernel because an eight-bit ternary table would contain
16,777,216 entries.

The binary-interchange descriptor specifies the format and its kernels. It is not stored in
`FloatLib.Floats.ExecFloat E4M3FN`.

## Reference

* Open Compute Project, *8-bit Floating Point Specification*, revision 1.0, E4M3,
  <https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.FP8

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange

/-- OCP E4M3 finite-number FP8 with direct byte storage. -/
inductive E4M3FN : Type

/-- The E4M3FN encoding fits in its direct byte carrier. -/
theorem e4m3fn_width_le_eight : FloatFormat.e4m3fn.bitWidth ≤ 8 := by decide

/-- Certified direct-byte E4M3FN addition table. -/
def e4m3fnAddTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fn e4m3fn_width_le_eight)
      Model.Spec.add :=
  StaticByte.Tables.add FloatFormat.e4m3fn e4m3fn_width_le_eight

/-- Certified direct-byte E4M3FN subtraction table. -/
def e4m3fnSubTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fn e4m3fn_width_le_eight)
      Model.Spec.sub :=
  StaticByte.Tables.sub FloatFormat.e4m3fn e4m3fn_width_le_eight

/-- Certified direct-byte E4M3FN multiplication table. -/
def e4m3fnMulTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fn e4m3fn_width_le_eight)
      Model.Spec.mul :=
  StaticByte.Tables.mul FloatFormat.e4m3fn e4m3fn_width_le_eight

/-- Certified direct-byte E4M3FN division table. -/
def e4m3fnDivTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fn e4m3fn_width_le_eight)
      Model.Spec.div :=
  StaticByte.Tables.div FloatFormat.e4m3fn e4m3fn_width_le_eight

/-- Certified direct-byte E4M3FN square-root table. -/
def e4m3fnSqrtTable :
    TinyTable.CertifiedUnary
      (StaticByte.encoding FloatFormat.e4m3fn e4m3fn_width_le_eight)
      Model.Spec.sqrt :=
  StaticByte.Tables.sqrt FloatFormat.e4m3fn e4m3fn_width_le_eight

/--
Package the five dense byte tables with the proved arithmetic FMA baseline. The tables total
roughly 257 KiB; retaining the single-rounding model kernel avoids a separate 16 MiB FMA table.
-/
@[always_inline] instance : StaticByte.Family E4M3FN where
  format := FloatFormat.e4m3fn
  width_le_eight := e4m3fn_width_le_eight
  kernels := StaticByte.Kernels.fromTablesWithModelFma e4m3fn_width_le_eight
    e4m3fnAddTable e4m3fnSubTable e4m3fnMulTable e4m3fnDivTable e4m3fnSqrtTable
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

meta instance : StaticByte.FamilyInfo E4M3FN where
  standard := "Open Compute Project FP8 E4M3FN"

@[always_inline, instance_reducible] instance : StaticByte.Plans.TablePlan E4M3FN where
  namePrefix := "OCP E4M3FN"
  addSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  addTable := e4m3fnAddTable
  subSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  subTable := e4m3fnSubTable
  mulSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  mulTable := e4m3fnMulTable
  divSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  divTable := e4m3fnDivTable
  sqrtSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  sqrtTable := e4m3fnSqrtTable

@[always_inline, instance_reducible] instance
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor E4M3FN] :
    FloatLib.Floats.ExecFloat.Fma E4M3FN :=
  StaticByte.Plans.modelFmaCapability e4m3fn_width_le_eight
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

/-- Construct OCP E4M3FN from a natural bit pattern, reduced to eight bits. -/
@[inline] def E4M3FN.ofNatBits (bits : Nat) : FloatLib.Floats.ExecFloat E4M3FN :=
  StaticByte.ofNatBits E4M3FN bits

/-- Read the complete OCP E4M3FN encoding byte. -/
@[inline] def E4M3FN.toUInt8 (value : FloatLib.Floats.ExecFloat E4M3FN) : UInt8 :=
  StaticByte.toUInt8 value

end FloatLib.Floats.Formats.OCP.FP8
