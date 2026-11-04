/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# OCP FP8 E4M3FN

`FloatLib.Floats.E4M3FN` is OCP E4M3FN stored in one `UInt8`, and `E4M3FN.Family` is its
type-level identity. With only 256 values, a binary operation fits in a table of 65,536 results.
So for addition, subtraction, multiplication, division, and square root, balanced and throughput
planning look the answer up in an exhaustive byte table, and latency planning runs the arithmetic
kernels. Fused multiply-add is the exception. Its table would need 16,777,216 entries, one per
triple of bytes, so it uses the proved generic single-rounding kernel.

The binary-interchange descriptor specifies the format and its kernels, and it lives in the type.
An `E4M3FN` value stores only its byte.

## Reference

* Open Compute Project, *8-bit Floating Point Specification*, revision 1.0, E4M3,
  <https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1>.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange

namespace E4M3FN

/-- Type-level identity of `E4M3FN`, selecting its descriptor, carrier, and kernels. -/
inductive Family : Type

/-- The E4M3FN encoding fits in its direct byte carrier. -/
theorem width_le_eight : FloatFormat.e4m3fn.bitWidth ≤ 8 := by decide

/-- Certified direct-byte E4M3FN addition table. -/
def addTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fn width_le_eight)
      Model.Spec.add :=
  StaticByte.Tables.add FloatFormat.e4m3fn width_le_eight

/-- Certified direct-byte E4M3FN subtraction table. -/
def subTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fn width_le_eight)
      Model.Spec.sub :=
  StaticByte.Tables.sub FloatFormat.e4m3fn width_le_eight

/-- Certified direct-byte E4M3FN multiplication table. -/
def mulTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fn width_le_eight)
      Model.Spec.mul :=
  StaticByte.Tables.mul FloatFormat.e4m3fn width_le_eight

/-- Certified direct-byte E4M3FN division table. -/
def divTable :
    TinyTable.CertifiedBinary
      (StaticByte.encoding FloatFormat.e4m3fn width_le_eight)
      Model.Spec.div :=
  StaticByte.Tables.div FloatFormat.e4m3fn width_le_eight

/-- Certified direct-byte E4M3FN square-root table. -/
def sqrtTable :
    TinyTable.CertifiedUnary
      (StaticByte.encoding FloatFormat.e4m3fn width_le_eight)
      Model.Spec.sqrt :=
  StaticByte.Tables.sqrt FloatFormat.e4m3fn width_le_eight

/--
Package the five dense byte tables with the proved arithmetic FMA baseline. The tables total
about 256 KiB, and keeping the single-rounding model kernel avoids a 16 MiB FMA table.
-/
@[always_inline] instance : StaticByte.Family E4M3FN.Family where
  format := FloatFormat.e4m3fn
  width_le_eight := width_le_eight
  kernels := StaticByte.Kernels.fromTablesWithModelFma width_le_eight
    addTable subTable mulTable divTable sqrtTable
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

meta instance : StaticByte.FamilyInfo E4M3FN.Family where
  standard := "Open Compute Project FP8 E4M3FN"

@[always_inline, instance_reducible] instance : StaticByte.Plans.TablePlan E4M3FN.Family where
  namePrefix := "OCP E4M3FN"
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
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor E4M3FN.Family] :
    FloatLib.Floats.ExecFloat.Fma E4M3FN.Family :=
  StaticByte.Plans.modelFmaCapability width_le_eight
    Model.FmaBackend.generic Model.FmaBackend.generic_eq_spec

end E4M3FN

/--
OCP FP8 E4M3FN: 4 exponent and 3 fraction bits with bias 7, no infinity, and NaN only at the two
all-ones codes. Values are stored in one byte, and balanced and throughput planning answer the
five basic operations from certified byte tables.

`ExecFloat.Binary (exponentBits := 4) (fractionBits := 3) (encoding := .finiteMaxNaN)` is the same
format on the general binary carrier, with directed rounding and status options.
-/
abbrev E4M3FN := ExecFloat E4M3FN.Family

/-- Construct OCP E4M3FN from a natural bit pattern, reduced to eight bits. -/
@[inline] def E4M3FN.ofNatBits (bits : Nat) : E4M3FN :=
  StaticByte.ofNatBits E4M3FN.Family bits

/-- Read the complete OCP E4M3FN encoding byte. -/
@[inline] def E4M3FN.toUInt8 (value : E4M3FN) : UInt8 :=
  StaticByte.toUInt8 value

end FloatLib.Floats
