/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.ByteTable.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Direct.Proof

/-!
# Certified construction of byte-sized posit tables

Every posit occupying at most eight encoded bits has at most 256 possible words. These
constructors evaluate the proved direct exact-dyadic kernels lazily for every table entry. Warm
execution then performs only native indexing and one `ByteArray` load.

Dense unary and binary tables remain small through eight bits. A dense ternary table has
`2 ^ (3 * bits)` bytes, so the execution planner may reject FMA when setup or resident memory
cannot be amortized.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.ByteTable

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

variable {format : Format}

/--
Lazily generated direct addition table.

The generator is the model-valued direct kernel `Model.DirectDyadicArithmetic.add`, so the
refinement theorem `add_eq_spec` makes the resulting table a table for `Model.Spec.add`.
-/
def addTable (width_le : format.bits ≤ 8) :
    TinyTable.CertifiedBinary (encoding format width_le) Model.Spec.add where
  model := Model.DirectDyadicArithmetic.add
  table := TinyTable.lazyBinaryTotal (encoding format width_le)
    (Model.DirectDyadicArithmetic.add)
  table_eq := by rfl
  model_eq_spec :=
    Model.DirectDyadicArithmetic.add_eq_spec

/-- Lazily generated direct subtraction table from the model-valued direct kernel. -/
def subTable (width_le : format.bits ≤ 8) :
    TinyTable.CertifiedBinary (encoding format width_le) Model.Spec.sub where
  model := Model.DirectDyadicArithmetic.sub
  table := TinyTable.lazyBinaryTotal (encoding format width_le)
    (Model.DirectDyadicArithmetic.sub)
  table_eq := by rfl
  model_eq_spec :=
    Model.DirectDyadicArithmetic.sub_eq_spec

/-- Lazily generated direct multiplication table from the model-valued direct kernel. -/
def mulTable (width_le : format.bits ≤ 8) :
    TinyTable.CertifiedBinary (encoding format width_le) Model.Spec.mul where
  model := Model.DirectDyadicArithmetic.mul
  table := TinyTable.lazyBinaryTotal (encoding format width_le)
    (Model.DirectDyadicArithmetic.mul)
  table_eq := by rfl
  model_eq_spec :=
    Model.DirectDyadicArithmetic.mul_eq_spec

/-- Lazily generated direct division table using one quotient prefix and exact remainder. -/
def divTable (width_le : format.bits ≤ 8) :
    TinyTable.CertifiedBinary (encoding format width_le) Model.Spec.div where
  model := Model.DirectDyadicArithmetic.div
  table := TinyTable.lazyBinaryTotal (encoding format width_le)
    (Model.DirectDyadicArithmetic.div)
  table_eq := by rfl
  model_eq_spec :=
    Model.DirectDyadicArithmetic.div_eq_spec

/-- Lazily generated direct square-root table using one root prefix and exact square remainder. -/
def sqrtTable (width_le : format.bits ≤ 8) :
    TinyTable.CertifiedUnary (encoding format width_le) Model.Spec.sqrt where
  model := Model.DirectDyadicArithmetic.sqrt
  table := TinyTable.lazyUnaryTotal (encoding format width_le)
    (Model.DirectDyadicArithmetic.sqrt)
  table_eq := by rfl
  model_eq_spec :=
    Model.DirectDyadicArithmetic.sqrt_eq_spec

/-- Lazily generated direct fused-multiply-add table from the model-valued direct kernel. -/
def fmaTable (width_le : format.bits ≤ 8) :
    TinyTable.CertifiedTernary (encoding format width_le) Model.Spec.fma where
  model := Model.DirectDyadicArithmetic.fma
  table := TinyTable.lazyTernaryTotal (encoding format width_le)
    (Model.DirectDyadicArithmetic.fma)
  table_eq := by rfl
  model_eq_spec :=
    Model.DirectDyadicArithmetic.fma_eq_spec

end FloatLib.Floats.Formats.Posit.Configured.ByteTable
