/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.Representation

/-!
# Representation-independent executable numerical values

`ExecFloat F` is the public runtime carrier selected by an `EncodedFormat F`. Neither this carrier
nor `EncodedFormat` assumes a floating radix or an IEEE layout. Its runtime representation is
exactly the family-chosen `FormatCode F` type. Semantic
interpretation is required only by proof-facing definitions, so noncomputable real semantics
cannot disable code generation for the carrier.

The nominal format tag is a proposition attached through `Subtype`. Lean specifies that a subtype
is represented identically to its carrier in compiled code, so a static format using `UInt32`
continues to cross generated entry points as a native 32-bit word. See the source documentation on
`Subtype` in Lean's `Init.Prelude`:
<https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Prelude.lean#L641-L643>.
Static format packages may therefore choose `UInt8`, `UInt32`, `UInt64`, fixed limb records, or
another direct carrier, while dynamic packages may choose descriptor-bearing or runtime-sized
storage without changing the universal API.

The checks under `benchmarks/scripts/checks/` validate the carrier specialization used by public
operations. Lean's runtime and specialization behavior are specified by the Lean reference manual:
<https://lean-lang.org/doc/reference/latest/>.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

universe u v w

/--
Erased nominal evidence distinguishing the executable values of different formats.

This proposition has one constructor and contains no data. Its purpose is type separation, not
runtime validation.
-/
inductive ExecFloatTag (F : Type u) : Prop where
  | intro : ExecFloatTag F

/--
The executable value of format `F`.

The value is represented exactly as the arbitrary family-selected `FormatCode F`; the proof-only
tag introduces no runtime descriptor, bit-vector, radix, or exceptional-value assumption.
-/
abbrev ExecFloat (F : Type u) [EncodedFormat F] :=
  { _raw : FormatCode F // ExecFloatTag F }

namespace ExecFloat

variable {F : Type u} [EncodedFormat F]

/--
Human-readable formatting supplied by an encoded numerical family.

The formatter receives the family-selected runtime code directly. Keeping this contract below
`ExecFloat` lets every representation print its mathematical value without requiring a universal
radix, exceptional-value model, or conversion through a host floating-point type.
-/
class FormatDisplay (F : Type u) [EncodedFormat F] where
  /-- Render one runtime code according to the format's own numerical semantics. -/
  format : FormatCode F → String

/--
Lossless conversion between a runtime carrier and its proof model.

`plan` is an arbitrary static index used only to distinguish carrier choices during typeclass
search. The contract itself is independent of radix, encoding, exceptional values, and arithmetic
semantics. Format families therefore share these inverse laws while keeping their storage plans
and model types separate.
-/
class ModelCodec {Plan : Type u} (plan : Plan)
    (Model : Type v) (Code : outParam (Type w)) where
  /-- Decode one runtime code into the proof model. -/
  toModel : Code → Model
  /-- Pack one proof-model value into the runtime carrier. -/
  ofModel : Model → Code
  /-- Decoding after packing is exact. -/
  toModel_ofModel : ∀ value, toModel (ofModel value) = value
  /-- Packing after decoding preserves the runtime code. -/
  ofModel_toModel : ∀ value, ofModel (toModel value) = value

/-- Wrap one family-selected code without conversion. -/
@[inline] def ofRaw (raw : FormatCode F) : ExecFloat F :=
  ⟨raw, .intro⟩

/-- The family-selected code, exposed as a field-like projection for format implementations. -/
@[inline] def raw (value : ExecFloat F) : FormatCode F :=
  value.val

/-- Apply a unary operation directly to the family-selected runtime code. -/
@[always_inline, inline] def applyUnary
    (operation : FormatCode F → FormatCode F)
    (value : ExecFloat F) : ExecFloat F :=
  ofRaw (operation value.raw)

/-- Apply a binary operation directly to family-selected runtime codes. -/
@[always_inline, inline] def applyBinary
    (operation : FormatCode F → FormatCode F → FormatCode F)
    (left right : ExecFloat F) : ExecFloat F :=
  ofRaw (operation left.raw right.raw)

/-- Apply a ternary operation directly to family-selected runtime codes. -/
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

namespace ModelCodec

variable {Plan : Type v} {plan : Plan} {Model : Type w}
    [codec : ModelCodec plan Model (FormatCode F)]

/-- Decode an executable value through its lossless proof-model codec. -/
@[always_inline, inline] def decode (value : ExecFloat F) : Model :=
  codec.toModel value.raw

/-- Encode a proof-model value through its lossless runtime codec. -/
@[always_inline, inline] def encode (value : Model) : ExecFloat F :=
  ofRaw (codec.ofModel value)

/-- Lift a unary proof-model operation to the executable carrier. -/
@[always_inline, inline] def liftUnary
    (operation : Model → Model) (value : ExecFloat F) : ExecFloat F :=
  encode (Model := Model) (plan := plan)
    (operation (decode (Model := Model) (plan := plan) value))

/-- Lift a binary proof-model operation to the executable carrier. -/
@[always_inline, inline] def liftBinary
    (operation : Model → Model → Model)
    (left right : ExecFloat F) : ExecFloat F :=
  encode (Model := Model) (plan := plan)
    (operation
      (decode (Model := Model) (plan := plan) left)
      (decode (Model := Model) (plan := plan) right))

/-- Lift a ternary proof-model operation to the executable carrier. -/
@[always_inline, inline] def liftTernary
    (operation : Model → Model → Model → Model)
    (left right third : ExecFloat F) : ExecFloat F :=
  encode (Model := Model) (plan := plan)
    (operation
      (decode (Model := Model) (plan := plan) left)
      (decode (Model := Model) (plan := plan) right)
      (decode (Model := Model) (plan := plan) third))

/-- Decoding immediately after encoding recovers the proof-model value. -/
@[simp, grind =] theorem decode_encode (value : Model) :
    decode (Model := Model) (plan := plan)
      (encode (F := F) (Model := Model) (plan := plan) value) = value :=
  codec.toModel_ofModel value

/-- Encoding immediately after decoding recovers the executable value. -/
@[simp, grind =] theorem encode_decode (value : ExecFloat F) :
    encode (Model := Model) (plan := plan)
      (decode (Model := Model) (plan := plan) value) = value := by
  apply ExecFloat.ext
  exact codec.ofModel_toModel value.raw

/-- Decoding a lifted unary operation exposes the underlying proof-model operation. -/
@[simp, grind =] theorem decode_liftUnary
    (operation : Model → Model) (value : ExecFloat F) :
    decode (Model := Model) (plan := plan)
        (liftUnary (Model := Model) (plan := plan) operation value) =
      operation (decode (Model := Model) (plan := plan) value) := by
  simp only [liftUnary, decode_encode]

/-- Decoding a lifted binary operation exposes the underlying proof-model operation. -/
@[simp, grind =] theorem decode_liftBinary
    (operation : Model → Model → Model) (left right : ExecFloat F) :
    decode (Model := Model) (plan := plan)
        (liftBinary (Model := Model) (plan := plan) operation left right) =
      operation
        (decode (Model := Model) (plan := plan) left)
        (decode (Model := Model) (plan := plan) right) := by
  simp only [liftBinary, decode_encode]

/-- Decoding a lifted ternary operation exposes the underlying proof-model operation. -/
@[simp, grind =] theorem decode_liftTernary
    (operation : Model → Model → Model → Model)
    (left right third : ExecFloat F) :
    decode (Model := Model) (plan := plan)
        (liftTernary (Model := Model) (plan := plan) operation left right third) =
      operation
        (decode (Model := Model) (plan := plan) left)
        (decode (Model := Model) (plan := plan) right)
        (decode (Model := Model) (plan := plan) third) := by
  simp only [liftTernary, decode_encode]

/-- Codec decoding is injective because encoding is its inverse. -/
theorem decode_injective {left right : ExecFloat F}
    (equality :
      decode (Model := Model) (plan := plan) left =
        decode (Model := Model) (plan := plan) right) :
    left = right := by
  rw [← encode_decode (Model := Model) (plan := plan) left,
    ← encode_decode (Model := Model) (plan := plan) right, equality]

/--
Lift a proved unary code operation to `ExecFloat`.

The executable side remains the direct code operation; the model equation is proof-only.
-/
theorem applyUnary_eq_lift
    (operation : FormatCode F → FormatCode F)
    (modelOperation : Model → Model)
    (operation_eq : ∀ value,
      codec.toModel (operation value) = modelOperation (codec.toModel value))
    (value : ExecFloat F) :
    applyUnary operation value =
      liftUnary (Model := Model) (plan := plan) modelOperation value := by
  apply decode_injective (Model := Model) (plan := plan)
  rw [decode_liftUnary]
  change
    codec.toModel (operation value.raw) =
      modelOperation (codec.toModel value.raw)
  exact operation_eq value.raw

/--
Lift a proved binary code operation to `ExecFloat`.

The executable side remains the direct code operation; the model equation is proof-only.
-/
theorem applyBinary_eq_lift
    (operation : FormatCode F → FormatCode F → FormatCode F)
    (modelOperation : Model → Model → Model)
    (operation_eq : ∀ left right,
      codec.toModel (operation left right) =
        modelOperation (codec.toModel left) (codec.toModel right))
    (left right : ExecFloat F) :
    applyBinary operation left right =
      liftBinary (Model := Model) (plan := plan) modelOperation left right := by
  apply decode_injective (Model := Model) (plan := plan)
  rw [decode_liftBinary]
  change
    codec.toModel (operation left.raw right.raw) =
      modelOperation (codec.toModel left.raw) (codec.toModel right.raw)
  exact operation_eq left.raw right.raw

/--
Lift a proved ternary code operation to `ExecFloat`.

The executable side remains the direct code operation; the model equation is proof-only.
-/
theorem applyTernary_eq_lift
    (operation : FormatCode F → FormatCode F → FormatCode F → FormatCode F)
    (modelOperation : Model → Model → Model → Model)
    (operation_eq : ∀ left right third,
      codec.toModel (operation left right third) =
        modelOperation
          (codec.toModel left) (codec.toModel right) (codec.toModel third))
    (left right third : ExecFloat F) :
    applyTernary operation left right third =
      liftTernary (Model := Model) (plan := plan)
        modelOperation left right third := by
  apply decode_injective (Model := Model) (plan := plan)
  rw [decode_liftTernary]
  change
    codec.toModel (operation left.raw right.raw third.raw) =
      modelOperation
        (codec.toModel left.raw) (codec.toModel right.raw) (codec.toModel third.raw)
  exact operation_eq left.raw right.raw third.raw

/-- Pointwise-equal unary model operations have equal executable lifts. -/
theorem liftUnary_congr
    {leftOperation rightOperation : Model → Model}
    (equal : ∀ value, leftOperation value = rightOperation value)
    (value : ExecFloat F) :
    liftUnary (Model := Model) (plan := plan) leftOperation value =
      liftUnary (Model := Model) (plan := plan) rightOperation value := by
  apply decode_injective (Model := Model) (plan := plan)
  simp only [decode_liftUnary]
  exact equal _

/-- Pointwise-equal binary model operations have equal executable lifts. -/
theorem liftBinary_congr
    {leftOperation rightOperation : Model → Model → Model}
    (equal :
      ∀ left right, leftOperation left right = rightOperation left right)
    (left right : ExecFloat F) :
    liftBinary (Model := Model) (plan := plan) leftOperation left right =
      liftBinary (Model := Model) (plan := plan) rightOperation left right := by
  apply decode_injective (Model := Model) (plan := plan)
  simp only [decode_liftBinary]
  exact equal _ _

/-- Pointwise-equal ternary model operations have equal executable lifts. -/
theorem liftTernary_congr
    {leftOperation rightOperation : Model → Model → Model → Model}
    (equal :
      ∀ left right third,
        leftOperation left right third = rightOperation left right third)
    (left right third : ExecFloat F) :
    liftTernary (Model := Model) (plan := plan)
        leftOperation left right third =
      liftTernary (Model := Model) (plan := plan)
        rightOperation left right third := by
  apply decode_injective (Model := Model) (plan := plan)
  simp only [decode_liftTernary]
  exact equal _ _ _

end ModelCodec

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

The resulting text is emitted directly rather than represented as a quoted Lean string.
-/
instance [FormatDisplay F] : Repr (ExecFloat F) where
  reprPrec value _ := Std.Format.text (toString value)

/--
Low-priority structural representation for internal families without a mathematical display.
Public numerical families should provide `FormatDisplay`.
-/
instance (priority := 100) [Repr (FormatCode F)] : Repr (ExecFloat F) where
  reprPrec value precedence := reprPrec value.raw precedence

end ExecFloat
end FloatLib.Floats
