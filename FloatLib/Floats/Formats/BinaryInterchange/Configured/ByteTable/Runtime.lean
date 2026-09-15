/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.TinyTable.Generic.Certified
public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Core
public import Mathlib.Algebra.Order.Algebra
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Semantics -- shake: keep

/-!
# Direct exhaustive runtime kernels for configured byte formats

Every binary-interchange descriptor occupying at most eight encoded bits admits the same
format-independent tiny-table backend used by other finite encodings. Table generation evaluates
the reference definition, while warm execution performs native indexing and one byte load.

The operation planner may reject a table when setup cost or resident memory is inappropriate for
the selected workload. That policy does not affect the refinement proofs in `ByteTable.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured.ByteTable

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

variable {format : FloatFormat}

/-- The exact binary-interchange model as a proved finite byte encoding. -/
def encoding (format : FloatFormat) (width_le_eight : format.bitWidth ≤ 8) :
    TinyTable.Encoding (Model format) where
  radix := 2 ^ format.bitWidth
  radix_pos := Nat.two_pow_pos format.bitWidth
  radix_le_byte := by
    simpa only [show 256 = 2 ^ 8 by decide] using
      (Nat.pow_le_pow_right (by decide : 0 < 2) width_le_eight)
  decode code := Model.ofNatBits code.val
  encode value := ⟨value.toNatBits, Model.toNatBits_lt_two_pow value⟩
  decode_encode value := Model.ofNatBits_toNatBits value
  encode_decode code := by
    apply Fin.ext
    exact Model.toNatBits_ofNatBits_of_lt code.val code.isLt

/-! ## Tables generated from reference model kernels -/

/-- Lazily generated direct addition table. -/
def addTable (width_le_eight : format.bitWidth ≤ 8) :
    TinyTable.CertifiedBinary (encoding format width_le_eight) Model.Spec.add where
  model := Model.AddBackend.generic
  table :=
    TinyTable.lazyBinaryTotal
      (encoding format width_le_eight) Model.AddBackend.generic
  table_eq := by rfl
  model_eq_spec := Model.AddBackend.generic_eq_spec

/-- Lazily generated direct subtraction table. -/
def subTable (width_le_eight : format.bitWidth ≤ 8) :
    TinyTable.CertifiedBinary (encoding format width_le_eight) Model.Spec.sub where
  model := Model.AddBackend.subWord
  table :=
    TinyTable.lazyBinaryTotal
      (encoding format width_le_eight) Model.AddBackend.subWord
  table_eq := by rfl
  model_eq_spec := Model.AddBackend.subWord_eq_spec

/-- Lazily generated direct multiplication table. -/
def mulTable (width_le_eight : format.bitWidth ≤ 8) :
    TinyTable.CertifiedBinary (encoding format width_le_eight) Model.Spec.mul where
  model := Model.MulBackend.generic
  table :=
    TinyTable.lazyBinaryTotal
      (encoding format width_le_eight) Model.MulBackend.generic
  table_eq := by rfl
  model_eq_spec := Model.MulBackend.generic_eq_spec

/-- Lazily generated direct division table. -/
def divTable (width_le_eight : format.bitWidth ≤ 8) :
    TinyTable.CertifiedBinary (encoding format width_le_eight) Model.Spec.div where
  model := Model.DivBackend.generic
  table :=
    TinyTable.lazyBinaryTotal
      (encoding format width_le_eight) Model.DivBackend.generic
  table_eq := by rfl
  model_eq_spec := Model.DivBackend.generic_eq_spec

/-- Lazily generated direct square-root table. -/
def sqrtTable (width_le_eight : format.bitWidth ≤ 8) :
    TinyTable.CertifiedUnary (encoding format width_le_eight) Model.Spec.sqrt where
  model := Model.SqrtBackend.generic
  table :=
    TinyTable.lazyUnaryTotal
      (encoding format width_le_eight) Model.SqrtBackend.generic
  table_eq := by rfl
  model_eq_spec := Model.SqrtBackend.generic_eq_spec

/-- Lazily generated direct fused-multiply-add table. -/
def fmaTable (width_le_eight : format.bitWidth ≤ 8) :
    TinyTable.CertifiedTernary (encoding format width_le_eight) Model.Spec.fma where
  model := Model.FmaBackend.generic
  table :=
    TinyTable.lazyTernaryTotal
      (encoding format width_le_eight) Model.FmaBackend.generic
  table_eq := by rfl
  model_eq_spec := Model.FmaBackend.generic_eq_spec

/-! ## Direct configured-carrier execution -/

/--
Execute one already-constructed certified binary table on the configured byte carrier.

The explicit table argument ensures the selected capability captures one memoizing `Thunk`
instead of constructing a fresh cell on every arithmetic call.
-/
@[always_inline, inline] def runBinary
    {modelSpec : Model format → Model format → Model format}
    (width_le_eight : format.bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedBinary (encoding format width_le_eight) modelSpec)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.byte width_le_eight)) (.byte width_le_eight))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.byte width_le_eight)) (.byte width_le_eight)) :=
  FloatLib.Floats.ExecFloat.applyBinary kernel.run left right

/-- Execute one already-constructed certified unary table on the configured byte carrier. -/
@[always_inline, inline] def runUnary
    {modelSpec : Model format → Model format}
    (width_le_eight : format.bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedUnary (encoding format width_le_eight) modelSpec)
    (value :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.byte width_le_eight)) (.byte width_le_eight))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.byte width_le_eight)) (.byte width_le_eight)) :=
  FloatLib.Floats.ExecFloat.applyUnary kernel.run value

/-- Execute one already-constructed certified ternary table on the configured byte carrier. -/
@[always_inline, inline] def runTernary
    {modelSpec : Model format → Model format → Model format → Model format}
    (width_le_eight : format.bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedTernary (encoding format width_le_eight) modelSpec)
    (left right addend :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.byte width_le_eight)) (.byte width_le_eight))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.byte width_le_eight)) (.byte width_le_eight)) :=
  FloatLib.Floats.ExecFloat.applyTernary kernel.run left right addend

end FloatLib.Floats.Formats.BinaryInterchange.Configured.ByteTable
