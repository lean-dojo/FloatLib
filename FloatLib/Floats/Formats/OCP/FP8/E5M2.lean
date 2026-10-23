/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# OCP FP8 E5M2

`FloatLib.Floats.E5M2` is OCP E5M2 with a direct `UInt8` runtime carrier, and `E5M2.Family` is
its type-level identity. Its IEEE-style infinity and NaN encodings are properties of this format
package, and the universal executable carrier does not assume them.

For addition, subtraction, multiplication, division, and square root, balanced and throughput
planning select exhaustive byte tables, and latency planning selects the arithmetic kernels.
Fused multiply-add uses the proved generic single-rounding kernel, which avoids a
16,777,216-entry ternary table and meets the same specification.

## Reference

* Open Compute Project, *8-bit Floating Point Specification*, revision 1.0, E5M2,
  <https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1>.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange

namespace E5M2

/-- Type-level identity of `E5M2`, selecting its descriptor, carrier, and kernels. -/
inductive Family : Type

/-- The E5M2 encoding fits in its direct byte carrier. -/
theorem width_le_eight : FloatFormat.e5m2.bitWidth ≤ 8 := by decide

/-- Certified direct-byte E5M2 addition table. -/
def addTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2 width_le_eight)
      Model.Spec.add :=
  StaticByte.Tables.add FloatFormat.e5m2 width_le_eight

/-- Certified direct-byte E5M2 subtraction table. -/
def subTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2 width_le_eight)
      Model.Spec.sub :=
  StaticByte.Tables.sub FloatFormat.e5m2 width_le_eight

/-- Certified direct-byte E5M2 multiplication table. -/
def mulTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2 width_le_eight)
      Model.Spec.mul :=
  StaticByte.Tables.mul FloatFormat.e5m2 width_le_eight

/-- Certified direct-byte E5M2 division table. -/
def divTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e5m2 width_le_eight)
      Model.Spec.div :=
  StaticByte.Tables.div FloatFormat.e5m2 width_le_eight

/-- Certified direct-byte E5M2 square-root table. -/
def sqrtTable :
    TinyTable.CertifiedUnary
      (StaticByte.encoding FloatFormat.e5m2 width_le_eight)
      Model.Spec.sqrt :=
  StaticByte.Tables.sqrt FloatFormat.e5m2 width_le_eight

/-- Package the five byte tables with the proved arithmetic FMA baseline. -/
@[always_inline] instance : StaticByte.Family E5M2.Family where
  format := FloatFormat.e5m2
  width_le_eight := width_le_eight
  kernels := StaticByte.Kernels.fromTablesWithModelFma width_le_eight
    addTable subTable mulTable divTable sqrtTable
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

meta instance : StaticByte.FamilyInfo E5M2.Family where
  standard := "Open Compute Project FP8 E5M2"

@[always_inline, instance_reducible] instance : StaticByte.Plans.TablePlan E5M2.Family where
  namePrefix := "OCP E5M2"
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
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor E5M2.Family] :
    FloatLib.Floats.ExecFloat.Fma E5M2.Family :=
  StaticByte.Plans.modelFmaCapability width_le_eight
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

end E5M2

/--
OCP FP8 E5M2: the IEEE encoding with 5 exponent and 2 fraction bits, so binary16's exponent range
with infinities and NaNs. Values are stored in one byte, and balanced and throughput planning
answer the five basic operations from certified byte tables.

`ExecFloat.Binary (exponentBits := 5) (fractionBits := 2)` is the same format on the general binary
carrier, with directed rounding and status options.
-/
abbrev E5M2 := ExecFloat E5M2.Family

/-- Construct OCP E5M2 from a natural bit pattern, reduced to eight bits. -/
@[inline] def E5M2.ofNatBits (bits : Nat) : E5M2 :=
  StaticByte.ofNatBits E5M2.Family bits

/-- Read the complete OCP E5M2 encoding byte. -/
@[inline] def E5M2.toUInt8 (value : E5M2) : UInt8 :=
  StaticByte.toUInt8 value

end FloatLib.Floats
