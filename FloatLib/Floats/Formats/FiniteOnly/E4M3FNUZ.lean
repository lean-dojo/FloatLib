/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# Finite-only E4M3FNUZ

`FloatLib.Floats.E4M3FNUZ` is the FP8 format of AMD accelerators, with 4 exponent bits, 3 fraction
bits, one NaN encoding and an unsigned zero. `E4M3FNUZ.Family` is its type-level identity. The
letters come from the ONNX float8 specification: `F` says there is no infinity, `N` says a NaN code
is kept, and `UZ` says zero has no sign. Those conventions belong to this package, so the universal
executable interface doesn't assume any of them.

Each value is one `UInt8`. Under the balanced and throughput policies, addition, subtraction,
multiplication, division, and square root read exhaustive byte tables that come with proofs, and
the latency policy computes them with the exact arithmetic baseline. Fused multiply-add uses the
proved generic single-rounding kernel, because a table over three byte operands would have
16,777,216 entries.

## Reference

* ONNX, *Float stored in 8 bits*, E4M3FNUZ,
  <https://onnx.ai/onnx/technical/float8.html>.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange

namespace E4M3FNUZ

/-- Type-level identity of `E4M3FNUZ`, selecting its descriptor, carrier, and kernels. -/
inductive Family : Type

/-- The E4M3FNUZ encoding fits in its direct byte carrier. -/
theorem width_le_eight : FloatFormat.e4m3fnuz.bitWidth ≤ 8 := by decide

/-- Certified direct-byte E4M3FNUZ addition table. -/
def addTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fnuz width_le_eight)
      Model.Spec.add :=
  StaticByte.Tables.add FloatFormat.e4m3fnuz width_le_eight

/-- Certified direct-byte E4M3FNUZ subtraction table. -/
def subTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fnuz width_le_eight)
      Model.Spec.sub :=
  StaticByte.Tables.sub FloatFormat.e4m3fnuz width_le_eight

/-- Certified direct-byte E4M3FNUZ multiplication table. -/
def mulTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fnuz width_le_eight)
      Model.Spec.mul :=
  StaticByte.Tables.mul FloatFormat.e4m3fnuz width_le_eight

/-- Certified direct-byte E4M3FNUZ division table. -/
def divTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fnuz width_le_eight)
      Model.Spec.div :=
  StaticByte.Tables.div FloatFormat.e4m3fnuz width_le_eight

/-- Certified direct-byte E4M3FNUZ square-root table. -/
def sqrtTable :
    TinyTable.CertifiedUnary
      (StaticByte.encoding FloatFormat.e4m3fnuz width_le_eight)
      Model.Spec.sqrt :=
  StaticByte.Tables.sqrt FloatFormat.e4m3fnuz width_le_eight

/-- Package the five byte tables with the proved arithmetic FMA baseline. -/
@[always_inline] instance : StaticByte.Family E4M3FNUZ.Family where
  format := FloatFormat.e4m3fnuz
  width_le_eight := width_le_eight
  kernels := StaticByte.Kernels.fromTablesWithModelFma width_le_eight
    addTable subTable mulTable divTable
    sqrtTable Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

meta instance : StaticByte.FamilyInfo E4M3FNUZ.Family where
  standard := "ONNX float8 E4M3FNUZ"

@[always_inline, instance_reducible] instance : StaticByte.Plans.TablePlan E4M3FNUZ.Family where
  namePrefix := "FNUZ E4M3"
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
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor E4M3FNUZ.Family] :
    FloatLib.Floats.ExecFloat.Fma E4M3FNUZ.Family :=
  StaticByte.Plans.modelFmaCapability width_le_eight
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

end E4M3FNUZ

/--
ONNX E4M3FNUZ, the FP8 format of AMD accelerators: 4 exponent and 3 fraction bits with bias 8, one
zero, no infinity, and the negative-zero code as the sole NaN. Values are stored in one byte and
their arithmetic reads certified byte tables.
-/
abbrev E4M3FNUZ := ExecFloat E4M3FNUZ.Family

/-- Construct E4M3FNUZ from a natural bit pattern, reduced to eight bits. -/
@[inline] def E4M3FNUZ.ofNatBits (bits : Nat) : E4M3FNUZ :=
  StaticByte.ofNatBits E4M3FNUZ.Family bits

/-- Read the complete E4M3FNUZ encoding byte. -/
@[inline] def E4M3FNUZ.toUInt8 (value : E4M3FNUZ) : UInt8 :=
  StaticByte.toUInt8 value

end FloatLib.Floats
