/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.TinyTable.Generic.Proof

/-!
# Specification-carrying generic byte-table kernels

These structures retain the model operation used to generate each lazy table together with its
refinement theorem. Their executable `run` methods delegate to the arity-specific direct lookup
paths, while their equations compose the generic lookup proof with the reference definition.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Backend.TinyTable

universe u

variable {Model : Type u}

/-- A lazily memoized binary table certified against a reference model specification. -/
structure CertifiedBinary
    (encoding : Encoding Model) (spec : Model → Model → Model) where
  /-- Operation used to generate the table. -/
  model : Model → Model → Model
  /-- Lazy table generated from `model`. -/
  table : Thunk ByteArray
  /-- The table and its declared model agree definitionally or by proof. -/
  table_eq : table.get = binaryTotal encoding model
  /-- The generation model equals the reference definition. -/
  model_eq_spec : ∀ left right, model left right = spec left right

namespace CertifiedBinary

variable {Model : Type u} {encoding : Encoding Model}
  {spec : Model → Model → Model}

/--
Create a certified binary kernel whose table is generated lazily from its reference model.

The named constructor lets format packages use its table equation without unfolding the model
operation. The definition remains transparent to Lean.
-/
def ofModel (encoding : Encoding Model) (model : Model → Model → Model)
    (model_eq_spec : ∀ left right, model left right = spec left right) :
    CertifiedBinary encoding spec where
  model
  table := lazyBinaryTotal encoding model
  table_eq := lazyBinaryTotal_get encoding model
  model_eq_spec

/-- Execute a certified binary table kernel on two encoded operands. -/
@[always_inline, inline] def run
    (kernel : CertifiedBinary encoding spec)
    (left right : Code encoding) : Code encoding :=
  runBinary encoding kernel.model kernel.table kernel.table_eq left right

/-- Decoding certified binary execution yields the reference binary specification. -/
@[simp] theorem decodeCode_run
    (kernel : CertifiedBinary encoding spec)
    (left right : Code encoding) :
    encoding.decodeCode (kernel.run left right) =
      spec (encoding.decodeCode left) (encoding.decodeCode right) := by
  rw [run, decodeCode_runBinary, kernel.model_eq_spec]

end CertifiedBinary

/-- A lazily memoized unary table certified against a reference model specification. -/
structure CertifiedUnary
    (encoding : Encoding Model) (spec : Model → Model) where
  /-- Operation used to generate the table. -/
  model : Model → Model
  /-- Lazy table generated from `model`. -/
  table : Thunk ByteArray
  /-- The table and its declared model agree. -/
  table_eq : table.get = unaryTotal encoding model
  /-- The generation model equals the reference definition. -/
  model_eq_spec : ∀ value, model value = spec value

namespace CertifiedUnary

variable {Model : Type u} {encoding : Encoding Model}
  {spec : Model → Model}

/-- Create a certified unary kernel whose table is generated lazily from its reference model. -/
def ofModel (encoding : Encoding Model) (model : Model → Model)
    (model_eq_spec : ∀ value, model value = spec value) :
    CertifiedUnary encoding spec where
  model
  table := lazyUnaryTotal encoding model
  table_eq := lazyUnaryTotal_get encoding model
  model_eq_spec

/-- Execute a certified unary table kernel on one encoded operand. -/
@[always_inline, inline] def run
    (kernel : CertifiedUnary encoding spec)
    (value : Code encoding) : Code encoding :=
  runUnary encoding kernel.model kernel.table kernel.table_eq value

/-- Decoding certified unary execution yields the reference unary specification. -/
@[simp] theorem decodeCode_run
    (kernel : CertifiedUnary encoding spec) (value : Code encoding) :
    encoding.decodeCode (kernel.run value) =
      spec (encoding.decodeCode value) := by
  rw [run, decodeCode_runUnary, kernel.model_eq_spec]

end CertifiedUnary

/-- A lazily memoized ternary table certified against a reference model specification. -/
structure CertifiedTernary
    (encoding : Encoding Model) (spec : Model → Model → Model → Model) where
  /-- Operation used to generate the table. -/
  model : Model → Model → Model → Model
  /-- Lazy table generated from `model`. -/
  table : Thunk ByteArray
  /-- The table and its declared model agree. -/
  table_eq : table.get = ternaryTotal encoding model
  /-- The generation model equals the reference definition. -/
  model_eq_spec : ∀ left right addend,
    model left right addend = spec left right addend

namespace CertifiedTernary

variable {Model : Type u} {encoding : Encoding Model}
  {spec : Model → Model → Model → Model}

/-- Create a certified ternary kernel whose table is generated lazily from its reference model. -/
def ofModel (encoding : Encoding Model)
    (model : Model → Model → Model → Model)
    (model_eq_spec : ∀ left right addend,
      model left right addend = spec left right addend) :
    CertifiedTernary encoding spec where
  model
  table := lazyTernaryTotal encoding model
  table_eq := lazyTernaryTotal_get encoding model
  model_eq_spec

/-- Execute a certified ternary table kernel on three encoded operands. -/
@[always_inline, inline] def run
    (kernel : CertifiedTernary encoding spec)
    (left right addend : Code encoding) : Code encoding :=
  runTernary encoding kernel.model kernel.table kernel.table_eq
    left right addend

/-- Decoding certified ternary execution yields the reference ternary specification. -/
@[simp] theorem decodeCode_run
    (kernel : CertifiedTernary encoding spec)
    (left right addend : Code encoding) :
    encoding.decodeCode (kernel.run left right addend) =
      spec (encoding.decodeCode left) (encoding.decodeCode right)
        (encoding.decodeCode addend) := by
  rw [run, decodeCode_runTernary, kernel.model_eq_spec]

end CertifiedTernary

end FloatLib.Floats.ExecFloat.Backend.TinyTable
