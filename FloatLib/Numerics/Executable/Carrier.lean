/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.Representation

/-!
# Representation-independent executable numerical values

`ExecFloat F` is the public runtime carrier selected by an `EncodedFormat F`. Neither this carrier
nor `EncodedFormat` assumes a floating radix or an IEEE layout, and its runtime representation is
the family-chosen `FormatCode F` type. Only proof-side definitions need a semantic interpretation,
so noncomputable real semantics can't switch off code generation for the carrier.

Its nominal format tag is a proposition attached through `Subtype`. Lean specifies that a subtype is
represented identically to its carrier in compiled code, so a static format using `UInt32` still
crosses generated entry points as a native 32-bit word. See the source documentation on `Subtype` in
Lean's `Init.Prelude`:
<https://github.com/leanprover/lean4/blob/v4.36.0/src/Init/Prelude.lean#L697-L699>.

That's what lets a static format package choose `UInt8`, `UInt32`, `UInt64`, fixed limb records, or
another plain carrier, while a dynamic package chooses descriptor-bearing or runtime-sized storage,
and neither has to change the universal API.

Checks under `benchmarks/scripts/checks/` validate the carrier specialization used by public
operations. Lean's runtime and specialization behavior are specified by the Lean reference manual:
<https://lean-lang.org/doc/reference/latest/>.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

universe u v w

/--
Erased nominal evidence distinguishing the executable values of different formats.

This proposition has one constructor and no data. It separates types and validates nothing at
runtime.
-/
inductive ExecFloatTag (F : Type u) : Prop where
  /-- The only proof: the tag holds of every type. -/
  | intro : ExecFloatTag F

/--
The executable value of format `F`.

The value is represented as the family-selected `FormatCode F`, and the proof-only tag adds no
runtime descriptor, bit-vector, radix or exceptional-value assumption.
-/
abbrev ExecFloat (F : Type u) [EncodedFormat F] :=
  { _raw : FormatCode F // ExecFloatTag F }

namespace ExecFloat

variable {F : Type u} [EncodedFormat F]

/--
Human-readable formatting supplied by an encoded numerical family.

The formatter receives the family-selected runtime code. Because this contract sits below
`ExecFloat`, every representation can print its mathematical value without a universal radix, an
exceptional-value model or a conversion through a host floating-point type.
-/
class FormatDisplay (F : Type u) [EncodedFormat F] where
  /-- Render one runtime code according to the format's own numerical semantics. -/
  format : FormatCode F → String

/-- Wrap one family-selected code without conversion. -/
@[inline] def ofRaw (raw : FormatCode F) : ExecFloat F :=
  ⟨raw, .intro⟩

/-- The family-selected code, exposed as a field-like projection for format implementations. -/
@[inline] def raw (value : ExecFloat F) : FormatCode F :=
  value.val

/-- Apply a unary operation to the family-selected runtime code, without decoding. -/
@[always_inline, inline] def applyUnary
    (operation : FormatCode F → FormatCode F)
    (value : ExecFloat F) : ExecFloat F :=
  ofRaw (operation value.raw)

/-- Apply a binary operation to family-selected runtime codes, without decoding. -/
@[always_inline, inline] def applyBinary
    (operation : FormatCode F → FormatCode F → FormatCode F)
    (left right : ExecFloat F) : ExecFloat F :=
  ofRaw (operation left.raw right.raw)

/-- Apply a ternary operation to family-selected runtime codes, without decoding. -/
@[always_inline, inline] def applyTernary
    (operation : FormatCode F → FormatCode F → FormatCode F → FormatCode F)
    (left right third : ExecFloat F) : ExecFloat F :=
  ofRaw (operation left.raw right.raw third.raw)

/-- Reading the raw code immediately after wrapping it returns the original code. -/
@[simp, grind =] theorem raw_ofRaw (raw : FormatCode F) :
    (ofRaw raw : ExecFloat F).raw = raw :=
  rfl

/-- Wrapping the raw code of an executable value reconstructs that value. -/
@[simp, grind =] theorem ofRaw_raw (value : ExecFloat F) :
    ofRaw value.raw = value :=
  Subtype.ext rfl

/-- Two executable values are equal when their family-selected codes are equal. -/
@[ext] theorem ext {left right : ExecFloat F} (h : left.raw = right.raw) :
    left = right :=
  Subtype.ext h


/-- Two executable values are equal exactly when their family-selected codes are equal. -/
add_decl_doc FloatLib.Floats.ExecFloat.ext_iff

/-- Complete semantic interpretation inherited from `FormatSemantics F`. -/
@[inline] def denote [FormatSemantics F]
    (value : ExecFloat F) : NumericalValue (FormatScalar F) :=
  denoteFormat F value.raw

/-- `value` represents the ordinary finite scalar `scalar`. -/
abbrev Represents [FormatSemantics F]
    (value : ExecFloat F) (scalar : FormatScalar F) : Prop :=
  FormatRepresents F value.raw scalar

/-- One runtime value with an erased proof of its complete denotation. -/
abbrev At [FormatSemantics F] (value : NumericalValue (FormatScalar F)) :=
  { code : ExecFloat F // code.denote = value }

/-- One runtime value with an erased proof of its ordinary finite denotation. -/
abbrev AtFinite [FormatSemantics F] (value : FormatScalar F) :=
  At (F := F) (.finite value)

instance [Inhabited (FormatCode F)] : Inhabited (ExecFloat F) where
  default := ofRaw default

instance [DecidableEq (FormatCode F)] : DecidableEq (ExecFloat F) :=
  fun left right =>
    if h : left.raw = right.raw then
      isTrue (ext h)
    else
      isFalse fun equality => h (congrArg raw equality)

instance [FormatDisplay F] : ToString (ExecFloat F) where
  toString value := FormatDisplay.format value.raw

/--
`#eval` uses a format's mathematical display when one is available.

The text is emitted unquoted, and is parenthesized when it is negative and appears as an
argument, as in `some (-1.5)`.
-/
instance [FormatDisplay F] : Repr (ExecFloat F) where
  reprPrec value precedence :=
    let text := toString value
    if text.startsWith "-" then Repr.addAppParen text precedence else Std.Format.text text

/--
Low-priority structural representation for internal families without a mathematical display.
Public numerical families should provide `FormatDisplay`.
-/
instance (priority := 100) [Repr (FormatCode F)] : Repr (ExecFloat F) where
  reprPrec value precedence := reprPrec value.raw precedence

end ExecFloat
end FloatLib.Floats
