/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Core.Proof

/-!
# Static-byte table and kernel construction

Lazy certified tables and complete family kernel bundles are constructed from the
format-independent tiny-table backend. Proof terms are erased, while the generated tables remain
memoized runtime values.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend

universe u

/-! ## Standard binary-interchange tables -/

namespace Tables

/-- Lazily generated certified addition table for any static byte descriptor. -/
def add (format : FloatFormat) (width_le_eight : format.bitWidth ≤ 8) :
    TinyTable.CertifiedBinary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add :=
  TinyTable.CertifiedBinary.ofModel (encoding format width_le_eight)
    FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.generic
    FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.generic_eq_spec

/-- Lazily generated certified subtraction table for any static byte descriptor. -/
def sub (format : FloatFormat) (width_le_eight : format.bitWidth ≤ 8) :
    TinyTable.CertifiedBinary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sub :=
  TinyTable.CertifiedBinary.ofModel (encoding format width_le_eight)
    FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.subWord
    FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.subWord_eq_spec

/-- Lazily generated certified multiplication table for any static byte descriptor. -/
def mul (format : FloatFormat) (width_le_eight : format.bitWidth ≤ 8) :
    TinyTable.CertifiedBinary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.mul :=
  TinyTable.CertifiedBinary.ofModel (encoding format width_le_eight)
    FloatLib.Floats.Formats.BinaryInterchange.Model.MulBackend.generic
    FloatLib.Floats.Formats.BinaryInterchange.Model.MulBackend.generic_eq_spec

/-- Lazily generated certified division table for any static byte descriptor. -/
def div (format : FloatFormat) (width_le_eight : format.bitWidth ≤ 8) :
    TinyTable.CertifiedBinary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.div :=
  TinyTable.CertifiedBinary.ofModel (encoding format width_le_eight)
    FloatLib.Floats.Formats.BinaryInterchange.Model.DivBackend.generic
    FloatLib.Floats.Formats.BinaryInterchange.Model.DivBackend.generic_eq_spec

/-- Lazily generated certified square-root table for any static byte descriptor. -/
def sqrt (format : FloatFormat) (width_le_eight : format.bitWidth ≤ 8) :
    TinyTable.CertifiedUnary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt :=
  TinyTable.CertifiedUnary.ofModel (encoding format width_le_eight)
    FloatLib.Floats.Formats.BinaryInterchange.Model.SqrtBackend.generic
    FloatLib.Floats.Formats.BinaryInterchange.Model.SqrtBackend.generic_eq_spec

/-- Lazily generated certified fused-multiply-add table for any static byte descriptor. -/
def fma (format : FloatFormat) (width_le_eight : format.bitWidth ≤ 8) :
    TinyTable.CertifiedTernary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma :=
  TinyTable.CertifiedTernary.ofModel (encoding format width_le_eight)
    FloatLib.Floats.Formats.BinaryInterchange.Model.FmaBackend.generic
    FloatLib.Floats.Formats.BinaryInterchange.Model.FmaBackend.generic_eq_spec

end Tables
namespace Kernels

/-- Build all six direct kernels from the shared format-independent byte-table backend. -/
def fromTables {format : FloatFormat} (width_le_eight : format.bitWidth ≤ 8)
    (add : TinyTable.CertifiedBinary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add)
    (sub : TinyTable.CertifiedBinary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sub)
    (mul : TinyTable.CertifiedBinary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.mul)
    (div : TinyTable.CertifiedBinary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.div)
    (sqrt : TinyTable.CertifiedUnary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt)
    (fma : TinyTable.CertifiedTernary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma) :
    Kernels format where
  add := runBinary width_le_eight add
  sub := runBinary width_le_eight sub
  mul := runBinary width_le_eight mul
  div := runBinary width_le_eight div
  sqrt := runUnary width_le_eight sqrt
  fma := runTernary width_le_eight fma
  add_eq_spec := byteCodeToModel_runBinary width_le_eight add
  sub_eq_spec := byteCodeToModel_runBinary width_le_eight sub
  mul_eq_spec := byteCodeToModel_runBinary width_le_eight mul
  div_eq_spec := byteCodeToModel_runBinary width_le_eight div
  sqrt_eq_spec := byteCodeToModel_runUnary width_le_eight sqrt
  fma_eq_spec := byteCodeToModel_runTernary width_le_eight fma

/--
Build table-backed arithmetic with a certified model-level fused multiply-add.

For an eight-bit format, the four binary tables contain `4 * 256²` byte entries and the square-root
table contains 256. Computing FMA with the supplied model kernel avoids a `256³`-entry table.
-/
def fromTablesWithModelFma
    {format : FloatFormat} (width_le_eight : format.bitWidth ≤ 8)
    (add : TinyTable.CertifiedBinary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add)
    (sub : TinyTable.CertifiedBinary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sub)
    (mul : TinyTable.CertifiedBinary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.mul)
    (div : TinyTable.CertifiedBinary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.div)
    (sqrt : TinyTable.CertifiedUnary (encoding format width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt)
    (fmaModel :
      ModelValue format → ModelValue format → ModelValue format → ModelValue format)
    (fmaModel_eq_spec : ∀ left right addend,
      fmaModel left right addend =
        FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma left right addend) :
    Kernels format where
  add := runBinary width_le_eight add
  sub := runBinary width_le_eight sub
  mul := runBinary width_le_eight mul
  div := runBinary width_le_eight div
  sqrt := runUnary width_le_eight sqrt
  fma := modelTernary format width_le_eight fmaModel
  add_eq_spec := byteCodeToModel_runBinary width_le_eight add
  sub_eq_spec := byteCodeToModel_runBinary width_le_eight sub
  mul_eq_spec := byteCodeToModel_runBinary width_le_eight mul
  div_eq_spec := byteCodeToModel_runBinary width_le_eight div
  sqrt_eq_spec := byteCodeToModel_runUnary width_le_eight sqrt
  fma_eq_spec left right addend := by
    rw [byteCodeToModel_modelTernary, fmaModel_eq_spec]

end Kernels
end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
