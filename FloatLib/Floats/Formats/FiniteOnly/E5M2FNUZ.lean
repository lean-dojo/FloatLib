/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# Finite-only E5M2FNUZ

`E5M2FNUZ` gives the ONNX finite, NaN-supporting, unsigned-zero E5M2 variant a distinct Lean type.
That nominal identity prevents accidental interchange with OCP E5M2, whose infinity and signed
zero behavior differs even though both formats occupy one byte.

The runtime carrier is one `UInt8`. Balanced and throughput policies select exhaustive proved
byte tables for addition, subtraction, multiplication, division, and square root; latency uses
the exact arithmetic baseline. Fused multiply-add uses the proved generic single-rounding kernel.

## Reference

* ONNX, *Float stored in 8 bits*, E5M2FNUZ,
  <https://onnx.ai/onnx/technical/float8.html>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FiniteOnly

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange

/-- Finite E5M2FNUZ with one NaN code, unsigned zero, and direct byte storage. -/
inductive E5M2FNUZ : Type

/-- The E5M2FNUZ encoding fits in its direct byte carrier. -/
theorem e5m2fnuz_width_le_eight : FloatFormat.e5m2fnuz.bitWidth ≤ 8 := by decide

/-- Certified direct-byte E5M2FNUZ addition table. -/
def e5m2fnuzAddTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2fnuz e5m2fnuz_width_le_eight)
      Model.Spec.add :=
  StaticByte.Tables.add FloatFormat.e5m2fnuz e5m2fnuz_width_le_eight

/-- Certified direct-byte E5M2FNUZ subtraction table. -/
def e5m2fnuzSubTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2fnuz e5m2fnuz_width_le_eight)
      Model.Spec.sub :=
  StaticByte.Tables.sub FloatFormat.e5m2fnuz e5m2fnuz_width_le_eight

/-- Certified direct-byte E5M2FNUZ multiplication table. -/
def e5m2fnuzMulTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2fnuz e5m2fnuz_width_le_eight)
      Model.Spec.mul :=
  StaticByte.Tables.mul FloatFormat.e5m2fnuz e5m2fnuz_width_le_eight

/-- Certified direct-byte E5M2FNUZ division table. -/
def e5m2fnuzDivTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2fnuz e5m2fnuz_width_le_eight)
      Model.Spec.div :=
  StaticByte.Tables.div FloatFormat.e5m2fnuz e5m2fnuz_width_le_eight

/-- Certified direct-byte E5M2FNUZ square-root table. -/
def e5m2fnuzSqrtTable :
    TinyTable.CertifiedUnary
      (StaticByte.encoding FloatFormat.e5m2fnuz e5m2fnuz_width_le_eight)
      Model.Spec.sqrt :=
  StaticByte.Tables.sqrt FloatFormat.e5m2fnuz e5m2fnuz_width_le_eight

/-- Package the five byte tables with the proved arithmetic FMA baseline. -/
@[always_inline] instance : StaticByte.Family E5M2FNUZ where
  format := FloatFormat.e5m2fnuz
  width_le_eight := e5m2fnuz_width_le_eight
  kernels := StaticByte.Kernels.fromTablesWithModelFma e5m2fnuz_width_le_eight
    e5m2fnuzAddTable e5m2fnuzSubTable e5m2fnuzMulTable e5m2fnuzDivTable
    e5m2fnuzSqrtTable Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

meta instance : StaticByte.FamilyInfo E5M2FNUZ where
  standard := "ONNX float8 E5M2FNUZ"

@[always_inline, instance_reducible] instance : StaticByte.Plans.TablePlan E5M2FNUZ where
  namePrefix := "FNUZ E5M2"
  addSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  addTable := e5m2fnuzAddTable
  subSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  subTable := e5m2fnuzSubTable
  mulSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  mulTable := e5m2fnuzMulTable
  divSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  divTable := e5m2fnuzDivTable
  sqrtSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  sqrtTable := e5m2fnuzSqrtTable

@[always_inline, instance_reducible] instance
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor E5M2FNUZ] :
    FloatLib.Floats.ExecFloat.Fma E5M2FNUZ :=
  StaticByte.Plans.modelFmaCapability e5m2fnuz_width_le_eight
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

/-- Construct E5M2FNUZ from a natural bit pattern, reduced to eight bits. -/
@[inline] def E5M2FNUZ.ofNatBits (bits : Nat) : FloatLib.Floats.ExecFloat E5M2FNUZ :=
  StaticByte.ofNatBits E5M2FNUZ bits

/-- Read the complete E5M2FNUZ encoding byte. -/
@[inline] def E5M2FNUZ.toUInt8 (value : FloatLib.Floats.ExecFloat E5M2FNUZ) : UInt8 :=
  StaticByte.toUInt8 value

end FloatLib.Floats.Formats.FiniteOnly
