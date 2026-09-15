/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# OCP FP8 E5M2

OCP E5M2 has a nominal format identity and a direct `UInt8` runtime carrier. Its IEEE-style
infinity and NaN encodings remain properties of this format package rather than assumptions of
the universal executable carrier.

For addition, subtraction, multiplication, division, and square root, balanced and throughput
planning select exhaustive byte tables; latency planning selects the arithmetic kernels.
Fused multiply-add uses the proved generic single-rounding kernel, avoiding a 16,777,216-entry
ternary table while preserving the same independent specification.

## Reference

* Open Compute Project, *8-bit Floating Point Specification*, revision 1.0, E5M2,
  <https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.FP8

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange

/-- OCP E5M2 FP8 with direct byte storage. -/
inductive E5M2 : Type

/-- The E5M2 encoding fits in its direct byte carrier. -/
theorem e5m2_width_le_eight : FloatFormat.e5m2.bitWidth ≤ 8 := by decide

/-- Certified direct-byte E5M2 addition table. -/
def e5m2AddTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2 e5m2_width_le_eight)
      Model.Spec.add :=
  StaticByte.Tables.add FloatFormat.e5m2 e5m2_width_le_eight

/-- Certified direct-byte E5M2 subtraction table. -/
def e5m2SubTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2 e5m2_width_le_eight)
      Model.Spec.sub :=
  StaticByte.Tables.sub FloatFormat.e5m2 e5m2_width_le_eight

/-- Certified direct-byte E5M2 multiplication table. -/
def e5m2MulTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2 e5m2_width_le_eight)
      Model.Spec.mul :=
  StaticByte.Tables.mul FloatFormat.e5m2 e5m2_width_le_eight

/-- Certified direct-byte E5M2 division table. -/
def e5m2DivTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2 e5m2_width_le_eight)
      Model.Spec.div :=
  StaticByte.Tables.div FloatFormat.e5m2 e5m2_width_le_eight

/-- Certified direct-byte E5M2 square-root table. -/
def e5m2SqrtTable :
    TinyTable.CertifiedUnary
      (StaticByte.encoding FloatFormat.e5m2 e5m2_width_le_eight)
      Model.Spec.sqrt :=
  StaticByte.Tables.sqrt FloatFormat.e5m2 e5m2_width_le_eight

/-- Package the five byte tables with the proved arithmetic FMA baseline. -/
@[always_inline] instance : StaticByte.Family E5M2 where
  format := FloatFormat.e5m2
  width_le_eight := e5m2_width_le_eight
  kernels := StaticByte.Kernels.fromTablesWithModelFma e5m2_width_le_eight
    e5m2AddTable e5m2SubTable e5m2MulTable e5m2DivTable e5m2SqrtTable
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

meta instance : StaticByte.FamilyInfo E5M2 where
  standard := "Open Compute Project FP8 E5M2"

@[always_inline, instance_reducible] instance : StaticByte.Plans.TablePlan E5M2 where
  namePrefix := "OCP E5M2"
  addSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  addTable := e5m2AddTable
  subSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  subTable := e5m2SubTable
  mulSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  mulTable := e5m2MulTable
  divSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  divTable := e5m2DivTable
  sqrtSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  sqrtTable := e5m2SqrtTable

@[always_inline, instance_reducible] instance
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor E5M2] :
    FloatLib.Floats.ExecFloat.Fma E5M2 :=
  StaticByte.Plans.modelFmaCapability e5m2_width_le_eight
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

/-- Construct OCP E5M2 from a natural bit pattern, reduced to eight bits. -/
@[inline] def E5M2.ofNatBits (bits : Nat) : FloatLib.Floats.ExecFloat E5M2 :=
  StaticByte.ofNatBits E5M2 bits

/-- Read the complete OCP E5M2 encoding byte. -/
@[inline] def E5M2.toUInt8 (value : FloatLib.Floats.ExecFloat E5M2) : UInt8 :=
  StaticByte.toUInt8 value

end FloatLib.Floats.Formats.OCP.FP8
