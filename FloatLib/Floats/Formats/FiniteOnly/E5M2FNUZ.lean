/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# Finite-only E5M2FNUZ

`FloatLib.Floats.E5M2FNUZ` gives the ONNX finite, NaN-supporting, unsigned-zero E5M2 variant a
distinct Lean type, with type-level identity `E5M2FNUZ.Family`. That identity prevents accidental
interchange with OCP E5M2, whose infinity and signed zero behavior differs even though both formats
occupy one byte.

The runtime carrier is one `UInt8`. Balanced and throughput policies select exhaustive proved byte
tables for addition, subtraction, multiplication, division, and square root. The latency policy uses
the exact arithmetic baseline. Fused multiply-add uses the proved generic single-rounding kernel.

## Reference

* ONNX, *Float stored in 8 bits*, E5M2FNUZ,
  <https://onnx.ai/onnx/technical/float8.html>.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange

namespace E5M2FNUZ

/-- Type-level identity of `E5M2FNUZ`, selecting its descriptor, carrier, and kernels. -/
inductive Family : Type

/-- The E5M2FNUZ encoding fits in its direct byte carrier. -/
theorem width_le_eight : FloatFormat.e5m2fnuz.bitWidth ≤ 8 := by decide

/-- Certified direct-byte E5M2FNUZ addition table. -/
def addTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2fnuz width_le_eight)
      Model.Spec.add :=
  StaticByte.Tables.add FloatFormat.e5m2fnuz width_le_eight

/-- Certified direct-byte E5M2FNUZ subtraction table. -/
def subTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2fnuz width_le_eight)
      Model.Spec.sub :=
  StaticByte.Tables.sub FloatFormat.e5m2fnuz width_le_eight

/-- Certified direct-byte E5M2FNUZ multiplication table. -/
def mulTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2fnuz width_le_eight)
      Model.Spec.mul :=
  StaticByte.Tables.mul FloatFormat.e5m2fnuz width_le_eight

/-- Certified direct-byte E5M2FNUZ division table. -/
def divTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2fnuz width_le_eight)
      Model.Spec.div :=
  StaticByte.Tables.div FloatFormat.e5m2fnuz width_le_eight

/-- Certified direct-byte E5M2FNUZ square-root table. -/
def sqrtTable :
    TinyTable.CertifiedUnary
      (StaticByte.encoding FloatFormat.e5m2fnuz width_le_eight)
      Model.Spec.sqrt :=
  StaticByte.Tables.sqrt FloatFormat.e5m2fnuz width_le_eight

/-- Package the five byte tables with the proved arithmetic FMA baseline. -/
@[always_inline] instance : StaticByte.Family E5M2FNUZ.Family where
  format := FloatFormat.e5m2fnuz
  width_le_eight := width_le_eight
  kernels := StaticByte.Kernels.fromTablesWithModelFma width_le_eight
    addTable subTable mulTable divTable
    sqrtTable Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

meta instance : StaticByte.FamilyInfo E5M2FNUZ.Family where
  standard := "ONNX float8 E5M2FNUZ"

@[always_inline, instance_reducible] instance : StaticByte.Plans.TablePlan E5M2FNUZ.Family where
  namePrefix := "FNUZ E5M2"
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
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor E5M2FNUZ.Family] :
    FloatLib.Floats.ExecFloat.Fma E5M2FNUZ.Family :=
  StaticByte.Plans.modelFmaCapability width_le_eight
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

end E5M2FNUZ

/--
ONNX E5M2FNUZ: 5 exponent and 2 fraction bits with bias 16, one zero, no infinity, and the
negative-zero code as the sole NaN. Values are stored in one byte and their arithmetic reads
certified byte tables.
-/
abbrev E5M2FNUZ := ExecFloat E5M2FNUZ.Family

/-- Construct E5M2FNUZ from a natural bit pattern, reduced to eight bits. -/
@[inline] def E5M2FNUZ.ofNatBits (bits : Nat) : E5M2FNUZ :=
  StaticByte.ofNatBits E5M2FNUZ.Family bits

/-- Read the complete E5M2FNUZ encoding byte. -/
@[inline] def E5M2FNUZ.toUInt8 (value : E5M2FNUZ) : UInt8 :=
  StaticByte.toUInt8 value

end FloatLib.Floats
