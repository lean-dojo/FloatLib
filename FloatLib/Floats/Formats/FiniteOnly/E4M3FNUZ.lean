/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# Finite-only E4M3FNUZ

`E4M3FNUZ` is a nominal eight-bit format with finite values, one NaN encoding, and unsigned zero.
Its name records the conventions used by the ONNX float8 specification: `F` excludes infinity,
`N` retains NaN, and `UZ` identifies the unsigned-zero encoding. These choices belong to this
format package; the universal executable interface assumes none of them.

The runtime carrier is one `UInt8`. Balanced and throughput policies select exhaustive proved
byte tables for addition, subtraction, multiplication, division, and square root; latency uses
the exact arithmetic baseline. Fused multiply-add uses the proved generic single-rounding kernel.

## Reference

* ONNX, *Float stored in 8 bits*, E4M3FNUZ,
  <https://onnx.ai/onnx/technical/float8.html>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FiniteOnly

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange

/-- Finite E4M3FNUZ with one NaN code, unsigned zero, and direct byte storage. -/
inductive E4M3FNUZ : Type

/-- The E4M3FNUZ encoding fits in its direct byte carrier. -/
theorem e4m3fnuz_width_le_eight : FloatFormat.e4m3fnuz.bitWidth ≤ 8 := by decide

/-- Certified direct-byte E4M3FNUZ addition table. -/
def e4m3fnuzAddTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fnuz e4m3fnuz_width_le_eight)
      Model.Spec.add :=
  StaticByte.Tables.add FloatFormat.e4m3fnuz e4m3fnuz_width_le_eight

/-- Certified direct-byte E4M3FNUZ subtraction table. -/
def e4m3fnuzSubTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fnuz e4m3fnuz_width_le_eight)
      Model.Spec.sub :=
  StaticByte.Tables.sub FloatFormat.e4m3fnuz e4m3fnuz_width_le_eight

/-- Certified direct-byte E4M3FNUZ multiplication table. -/
def e4m3fnuzMulTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fnuz e4m3fnuz_width_le_eight)
      Model.Spec.mul :=
  StaticByte.Tables.mul FloatFormat.e4m3fnuz e4m3fnuz_width_le_eight

/-- Certified direct-byte E4M3FNUZ division table. -/
def e4m3fnuzDivTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fnuz e4m3fnuz_width_le_eight)
      Model.Spec.div :=
  StaticByte.Tables.div FloatFormat.e4m3fnuz e4m3fnuz_width_le_eight

/-- Certified direct-byte E4M3FNUZ square-root table. -/
def e4m3fnuzSqrtTable :
    TinyTable.CertifiedUnary
      (StaticByte.encoding FloatFormat.e4m3fnuz e4m3fnuz_width_le_eight)
      Model.Spec.sqrt :=
  StaticByte.Tables.sqrt FloatFormat.e4m3fnuz e4m3fnuz_width_le_eight

/-- Package the five byte tables with the proved arithmetic FMA baseline. -/
@[always_inline] instance : StaticByte.Family E4M3FNUZ where
  format := FloatFormat.e4m3fnuz
  width_le_eight := e4m3fnuz_width_le_eight
  kernels := StaticByte.Kernels.fromTablesWithModelFma e4m3fnuz_width_le_eight
    e4m3fnuzAddTable e4m3fnuzSubTable e4m3fnuzMulTable e4m3fnuzDivTable
    e4m3fnuzSqrtTable Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

meta instance : StaticByte.FamilyInfo E4M3FNUZ where
  standard := "ONNX float8 E4M3FNUZ"

@[always_inline, instance_reducible] instance : StaticByte.Plans.TablePlan E4M3FNUZ where
  namePrefix := "FNUZ E4M3"
  addSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  addTable := e4m3fnuzAddTable
  subSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  subTable := e4m3fnuzSubTable
  mulSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  mulTable := e4m3fnuzMulTable
  divSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  divTable := e4m3fnuzDivTable
  sqrtSelection := .balancedAndThroughput (by decide) (by decide) (by decide)
  sqrtTable := e4m3fnuzSqrtTable

@[always_inline, instance_reducible] instance
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor E4M3FNUZ] :
    FloatLib.Floats.ExecFloat.Fma E4M3FNUZ :=
  StaticByte.Plans.modelFmaCapability e4m3fnuz_width_le_eight
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

/-- Construct E4M3FNUZ from a natural bit pattern, reduced to eight bits. -/
@[inline] def E4M3FNUZ.ofNatBits (bits : Nat) : FloatLib.Floats.ExecFloat E4M3FNUZ :=
  StaticByte.ofNatBits E4M3FNUZ bits

/-- Read the complete E4M3FNUZ encoding byte. -/
@[inline] def E4M3FNUZ.toUInt8 (value : FloatLib.Floats.ExecFloat E4M3FNUZ) : UInt8 :=
  StaticByte.toUInt8 value

end FloatLib.Floats.Formats.FiniteOnly
