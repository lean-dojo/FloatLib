/-
Copyright (c) 2026 Robert Weller
Released under MIT license as described in the file LICENSE.
Authors: Robert Weller
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Core.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Selection.Metadata

/-!
# Default static-byte backend runtime

A static-byte family's selected backend supplies six arithmetic operations and a shared cost
estimate. Refinement theorems live in `Backend.Proof`; capability instances live in
`Backend.Construction`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte

universe u

namespace Backend

/-- Statically selected byte addition. -/
@[inline] def add {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.ofRaw <|
    (Family.kernels (F := F)).add left.raw right.raw

/-- Statically selected byte subtraction. -/
@[inline] def sub {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.ofRaw <|
    (Family.kernels (F := F)).sub left.raw right.raw

/-- Statically selected byte multiplication. -/
@[inline] def mul {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.ofRaw <|
    (Family.kernels (F := F)).mul left.raw right.raw

/-- Statically selected byte division. -/
@[inline] def div {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.ofRaw <|
    (Family.kernels (F := F)).div left.raw right.raw

/-- Statically selected byte square root. -/
@[inline] def sqrt {F : Type u} [Family F]
    (value : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.ofRaw <|
    (Family.kernels (F := F)).sqrt value.raw

/-- Statically selected byte fused multiply-add. -/
@[inline] def fma {F : Type u} [Family F]
    (left right addend : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.ofRaw <|
    (Family.kernels (F := F)).fma left.raw right.raw addend.raw

end Backend

/-- Default estimate for a monomorphic direct-byte kernel supplied by a static family. -/
def Backend.familyEstimate (operation : String) :
    FloatLib.Floats.ExecFloat.Backend.Candidate where
  name := s!"family-provided static-byte {operation}"
  kind := .fixedFormat
  steadyCost := 32

namespace Backend.Table

/--
Run any certified binary byte table directly on a nominal static-byte format.

The table is an explicit argument so a closed format package can expose a first-order,
monomorphic kernel without projecting a function from its `Family` dictionary.
-/
@[always_inline, inline] def binary {F : Type u} [Family F]
    {modelSpec :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F)) →
          ModelValue (Family.format (F := F))}
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (table : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedBinary
      (encoding (Family.format (F := F)) width_le_eight) modelSpec)
    (left right : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.ofRaw <|
    runBinary width_le_eight table left.raw right.raw

/-- Run any certified unary byte table directly on a nominal static-byte format. -/
@[always_inline, inline] def unary {F : Type u} [Family F]
    {modelSpec :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F))}
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (table : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedUnary
      (encoding (Family.format (F := F)) width_le_eight) modelSpec)
    (value : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.ofRaw <|
    runUnary width_le_eight table value.raw

/-- Run any certified ternary byte table directly on a nominal static-byte format. -/
@[always_inline, inline] def ternary {F : Type u} [Family F]
    {modelSpec :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F)) →
          ModelValue (Family.format (F := F)) →
            ModelValue (Family.format (F := F))}
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (table : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedTernary
      (encoding (Family.format (F := F)) width_le_eight) modelSpec)
    (left right addend : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.ofRaw <|
    runTernary width_le_eight table left.raw right.raw addend.raw

end Backend.Table

namespace Backend.Model

/--
Run a model-level ternary kernel through the direct byte carrier.

This is the shared table-free path for operations such as eight-bit FMA, where an exhaustive
ternary table would be disproportionately large.
-/
@[always_inline, inline] def ternary {F : Type u} [Family F]
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (op :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F)) →
          ModelValue (Family.format (F := F)) →
            ModelValue (Family.format (F := F)))
    (left right addend : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.ofRaw <|
    modelTernary (Family.format (F := F)) width_le_eight op
      left.raw right.raw addend.raw

end Backend.Model

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
